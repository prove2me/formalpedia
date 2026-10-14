-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2322
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:21:25.312881+00:00
-- url     : https://prove2.me/submissions/d4e9fd30-3bf5-4cec-9611-fe5d3738fe07

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 417446043 ≤ n < 417625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 417447293 1250 417446043 417446053
    0xf0906010c0501020c0d0e0f040903050405012010151202030307032d021c050915070c0906060801050a050f01020606190b1b070f1a0d0221100b0a02030d0b0111 70
    0x20344c6c290002c4d580e0350f200b2019070340b040309403503468100016909070341d5011340802c404000901840d4854070703990140180420540d055600380814041c900002d406006c592655915040c042d007903a1658000001c1c40c161289003601c00c01500007a48078410850020305021041101105c03c00861002003641590305000300e549070441080607440c2c18000c074110706401c0d051034680280c0c83c010404d6551100014207002081c100348101142c00d079005010545011020307104c00100c5010b98002c040150906544902c00c03549440c00340007c881c0d4a4100c24410050243d03200c0b0300c1e0b40d0000d00c40b81d110a00726010760301503443c40a1405841d11b04d8100c3e40c007900001070403800d04141084050184658a0f08941c802076032040c0c0c00103184120701a620021180744400c2101c0614100940b2200c09050401403800c0e0041184023600e000400c81181c15114440402c030b1038180c07005202d8010f14844400034506204140002c3d202c1c4204003842525a65907410354010345d20401e4416450100041110 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 417448543 1250 417447293 417447313
    0xe0a050402120403111626030a020d12090201080403030b1311090901090e0307030f2a03020609071811071e0c05060f040b090d05030a031a0f0906010c0501020c 70
    0x510072000407102a00881c02c008442e401791140040c8031400e03d05a80c0400c00e0041c00c10080210005004c0144203560480940040101c0b10910050808002c540c0041c00c2d1258140c80107000d00b489491803009103440d000b0032344007503600030140a51155251400040c000d02a80000d01d084180045d554900d03440e2001512941016800820800804803411750041c0e985881503400c0d074440002e000030a410500c54240000e0080c000340e442e5040ea030910205514100581981d1005d0001c60003071460a0b01c0c450200345501840255040405039003d0091181131000c078003000600e107607000300d15030741d80d154541103e402c0b0400c0d980055800403009460100481480209001441050f1250490b04000041c2413030840200c0e21950045011141880e21341503500d40b542c2c01030215543c0109262102c1030005000380300600b551406500c000444084030500c4100c480704000d401070141a21400c1c03141155907964840b603010209107071103000100545403182c00390181200e00c3c6224400d9044c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 417449793 1250 417448543 417448567
    0x30a060e0105030d021e03040e0f04030f08070f0e030a0204050c1c0504050c1003151707051516081c05011802030f0402010315051306090b030d0f0e0a050402 69
    0x100086400d08920003900e41d0300d5104250710f41d09411003080142c1d11414050098a402c141c0108250750a130b41030364100b550b40c0b081040504400c640c010ba040200d2000c11007007503049503030244280007528140c8031a01d00b81c84041c1621080d8600d10040c02040b000050840c3e50410400c40e0381d580c0a442400781b8100704140c0426a00314059135090030003803c002c801030041d18481e80f0b05c9650440c004080c45001c0c10240700c61610080722040415840d90040035100d241c922031680105100c0c2401000010018055402c01c2400e03046540700c0c0444217190042e009400003030307400c0405240c2c0b01000c50011858241c900340b10340c0f00f001e10f41c116075451086c506011548028121071140d604403030510000c01c02102280300031281c41c1d4030301d544540401d0241d4888d511407409207006040103081151a01c000a500200301070ad08591b6071f40314481486603201500491a0300030094008104400d50a400504100141650f01c0c040190001c96106240c1e00c03018228014a0064411942c80a90f160310f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 417451043 1250 417449793 417449801
    0x14010b010206040b063d020f030a0315032003010606030b0a0902030c1e120a181518140d02060702070e0c1e070210142a07121103010917030912030a 65
    0x1250350500300d100c9a02241b180041020b4007488001d401952400701541c009070014403035400c0c0101040746042022001800b241007030060005041d000740c08040303402e001c140c00d50b01141c120100301424070001d0b03c81034032003095880c00d484100d800035840f80e07590350b00d0340c07020700034250410b00d800b203406400e5145980610007040b1400c0c0c802c00515441d034550040c402514003001015230480c0c40c0c1e140c010045151855100e6100a2160010910b43d4645050301c50b20032a0740f00507a501e03125040d00901d01c2ea0100301c5a1144143c50020302514500100003944030003231071103078243d1842e04000140d0329104070b46c211407580c0032440003441c14940e80c012401903508a108128047c0d151100c000924500410700500611794104000d440c01c0345026403088031044501013001030800308012141c070710009201c5480600480300c07800c09a01e00031704150f9090007408003084c0c040c1c0d03d0103031140e0110b1418590041407102d54000b4542d2511814200351a280f403048041007581c2000c028440c9990712904 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 417452293 1250 417451043 417451129
    0x50c04060312110d05161104050a1d0c01081603090203030d0915060320030705181e10060804030507020316080f0304050a0501080408120a0914010b010206040b06 71
    0xc1d07940c03142c1c81000c0e11159a5100c01c44050082101840114181841d8440710030685107e52880810f801c200b10110781034600903204546860345800c0200444080d111400d0112400d1800401226049500103480c802c000f50002e20303640580d01807800c0d80c0303001c0d42040b2801e541c047d0460f580c030090307002c540005082c224021180c0900b461000c00c200b0b1418050041600d4010501d15240e43d10328912031803d80c25410320300c0d0980900d04000502d035461585004222101d400200900d150694400c6642001c6915084a2550350307020300030148036005100701503800d10b0401038440c1d226414203a4041c020114001d61603c1064242d0340510f80c050003510844220a049030f104107007034580c040c4c0b2800b90f405003a401c5280600c00300301a6102d01440342d041406a0450b84c64254035102c06409410112610383c04940c45040d80b170104094030101c1000801940c00801c00c070903042c00007c2d1281c0000e0000f0340b800d030244020641ca55a160009902795402400031419421031703581117803041c0600d034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 417453543 1250 417452293 417452297
    0x40c03081c0608061504050702071205070306110a140d020c03030702070602060c040e04060b04110a170a06050310050a0b0409030e0307060f08011e0509010e060909190f050c04060312 80
    0x120000f90000001034058011101c004503901510042c6084c0300042030010982011880307801e40005540b0801301e2049900390050028114060460804100340c03900d03054040000c0c081005007840d20f0b90701100c080c094041c0c1c8031007542c0e1114403a1f180c201900601079034a0843c003000080c0f01c1c0040d0000b9a201c00c64146800792030082d90f0341010040e55001b580f0030343c12402c5030400000c001a40583c8448400d1070010400a642901c00742401c030143c00c150601008034041c0742c1c00c9145d01d0041102c19074071079000441480681d06080201c5e03251a4060800460162a040031503840350b815000b0512804015008029100150800402448007a5121402400703a040c2c0403c00600c01c0b030054007600c190707407075500c000d902e0460103500682e001d844ea5a030300480e40c6004555640d688840e140201107844061800d400c029042140c1000050a084030f0f0b6801014401e5441142818440101c0c1c0c00039020300c9a42424100729003000e07684260180e000c2d10300440441000080914141000007075 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 417454793 1250 417453543 417453551
    0x60f29040509070b070809031c0504081b1806010e0411090a0b0307051605070306050a0506040c090311010e010e0d0302061f1d07120606020106080c15040b03040c03081c 74
    0x1001610791920098001e216130001c0401012000c190300500404031443c0c041d089079402a806daa650000c4030415052000088001800b000041000c01100c2c0c6001c43e1481c1c404081480000081e4000041c3c0246400e0301040c0c8001521687c0980058100e03410007030400d02961021000b101d07419840075032440d219000c4800082995030900c420b880c8240c19640f00c3c1450030fa00214160030b441c0c4410021500e9114281c00800000c04500459000d621008808641d5003006000c000540d0701e16040281000140343c0108041401144404132040080c00c000b21b1041c000c0004071106904908413036000160038105001300f41d8001003c40c0300742003050070b4201041041c42d000f0100c845500c0f03003809828500f080d02c152101e10307800103600300d1041d0800100c400d81a41800c42929510f070300c1328000d41d54a02040110348002e110202d0603c03000c41b4420324040e484c60780b42074540114002c0002d1310b00c1c04000582000380000c040780180d41c000b500281c40c2e003580820140c00443c901c29900c8840e0078 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 417456043 1250 417454793 417454801
    0x12304030e030d0f1116090e0a081204020406050d15020903101113120b0c0d0b04090c0302091e012d03050a060605090705033c04121b060f290405 64
    0x40030030701541041000c0c800b8200c0b11f1500c0042c2014080c03425840c081ea015654883c000a81030a00811a94011040040b01442d0031300410040364030692241e0700602c2140c690000107488000b04034550030303582034010380714541030012034544041c00c0d20b80750b880c51902c05820300b40c0c0d410001902c0070001800d000b803801ca413504c0003044640326504000f000a0308481c0452202c200c4003014201200c01044000360100900002a056842448080d550a0030418060096007440f101c450752141106824000103070060300c1c1039024000c1480381c40001030781031020042d14611440801d0300da41d400031520452603140d0601d20703225045c05004075100c0e403030a00700040b641420300f0389510030709850300c81504555400d06d14841440c0314185080042c0790f014180c454562404040c40c00340000700c90101e0140c038103072501d403444010040d448414044440340c5004040c80c2d580020840310342c00340e404650029018000707000fa15568030316040107418401d00352202c0c401441c2000043d40304440502044e29 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 417457293 1250 417456043 417456077
    0x911060f0c01061a160602070c0312021221090f1501090605180109020703180609030302101b0f1115040327170f120702030609012304030e030d0f 64
    0x203a280c140c0804d030f0180858aa102003510840f00c0301c50080c90054034124035a69038000d8098190021207001d8080111607485540c1002506034091110a485140180c6880c2586641c2100f81c82c001c0f01041da10000380f1481414007140c81c5950104007101d0343d0540c4800c4e042100c0409016860034545840070014407850518502d00307424150510521460742000c500c180a50b00184083e0705000214000e20692403079200004010100c0399074000b030b4241945002802d103c00c00e101c0035000340c10300d070b0320307030042580c040d5120202440c03401d00ca80d03444050740341920541c046603135406190040300c00740d6040d0f182160080b8400c0748642d40f0803d6450243c4441d29a0112444a10080d602080c3e41440b030980c00180c440640c5c0c2ca007504640140380e801ca050391400310800584d0b551007101040d28030442c01c040000702d4111009100030322908010043c19001e07103010410f115465210303034010800f0701d8060346450500c55006400e0303030303050f030000c10002e00a11040c0300e140000807219021010085 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 417458543 1250 417457293 417457319
    0xc05040c0305061906120f0b0d080405010318050c06031909060506122413020909070302150f03190204150f081e04022e0c060b04060503060a0911060f0c0106 69
    0xd0110f488046c1c0140b00005401d00a203551000d06089030740d05c01c0f0150456a4039075003140b1a91044204590301c5040c41e000405880c54070200110340c0c5400340102c1700240011132941000079003600e02035103a503210b4002c00c1000041c0b80d24980d4a81c83c0050781d034188070441e004070780b041c00103a42000320b000381890150f64039030b2010245000340c40c480c041107080c0e960390016160021000f54910040107840c2d00014080003060320328582da940452001c00440c140155440e405090100340b9a05011510300315040b0391000400e0602d0500134803a000e04911240e6043c1c4001d00b07640394000e440305107421009040342183d05920000309451900045c1c04001d8082e140e42d07040c5031600e00c06c0141e1955401d20101000082400340c070195505220705c1404104035110311034207140d59a00c610303c402c9040000c200d803400d0f85150300460504405101c2500c0002d10140c2040b0200300001d141106410038130b00c141c6800c03800301d0384040d00041c0c140c01c28000d1400390514540b108001c104a50b901e5003020714032 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 417459793 1250 417458543 417458549
    0x50f0102030a18050a060e09060f06030703090c1d06090a0c090302152817060108041509020603070c0308010801140f0406024b03010504090c05040c03050619 69
    0x5074001c000c01d40101d0300c120342c5400c0103005065042201d903140c00014020a03100d8018a0006d641d035684e48503145041a66540c201500341c441541d070060680102c0d089102c018892000d041c1c8910b800c1c030802065414240041c0307040f44085020320480d4a22041100707055030f007140708103598408a030b0380a1a51042865401981d1600c3e80c01601c1c55080c0301b607e84070b80c0b0103800050814002c00c5940030b016042503c0c505100541040c68000190b00507005481144030b140201c3d40780c008000c81a45c00c20b80a80c3c01680105032840070752083c0c440b51010304451400250045004018025101d8111220941c4103119403281c0d40380b680c0359000d490880d480c41d202104d0318405240403804600900755660b40250003040003624002c400c100c00152040c1e5143c4c100c80d840a540c3c40503100718540c0100050009031000e140c1004c00049248618600041c020a0701c50390780ca0031107108001540c400b4100410016009001017445c0100140c02400203c07081c50082400c2c00d100550220700c948a541a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 417461043 1250 417459793 417459797
    0x90e0105041d0106031202070602010c17131a0604060902091e0607050f0a14031603050a170a060e09060702101a03030c010c1808030702040b0103091416050f01 70
    0x16880c0c8810080584050005060300d80d0810500b003221030020b02548024501881c900d8101c0b03404c0c408021b103030404542c04002164506069640c04a6100c07507481141c282c0c8404414841e1907070000300f410b06810010040c11641600054501d0f1768460400728440d081c11901040050b58031100c030000d030b100c1c40d41c0c1141d1001d00010401d44462210800200c2a807000d442035040003c01d544242c45c4c6885a0381d01155070748078928504c1004403688800009245040182d810004a8412018a1511140018148000815580c804a01c59203003481103000905580805082c4040b034070000b404a405085440c0704401b000440035200000e42c503000b055564002c05015001e42d060380010a021409080308518103100d404260360100040d0034680c3e058000003c008081d01c00242c10005001c02d02c0c0302040515000708a800004000e585c2510740664010903501c0b04140120020540480c00420240d642e01b0000a01c1c407000036194904a01500c00114043e180d07410412203255546110340 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 417462293 1250 417461043 417461069
    0xe0a03020a020603040f1205071707120806150d0e0d02030405030622140d0207050f010e040f020405040509030c12040f090e0a050607180f06271212020d09 68
    0x1c01400d0400040d41d11501a00002e1a5144d16039150f202440b41030755808002030000c40c2034402d1045241044001c030092150180c0b802c2002e540d40c400107603160740c95005105007100015125260001c0f5481140031070070090b03a66245440c5554024020140c3c0b00310031340300e5400d4000c00140004112800d82e40d00400400443c0d41c0c990a6a076208869140b12144003411401c12002403619940542c2554640c0094009008001d200130710340101c0d5403055104041c02184440941d80140d084454010150740206101500b000100080c0c400c07640600e820034a00410043c85120200140080291900654403844408108041c4038000c41c011070038010b40c41314041010b1200c0d680020a11103080741910410a00c98403000d00f0048100c0703852020940004014071009040800b49000d454205040e004050a210006101d110f1210403180c01da4141480d1385000f0040104020003001002440d0795103900901c0c0104042e100c0c5244013000d4070440c01c0c000180c50040c1d4005090724115aa199 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 417463543 1250 417462293 417462313
    0x603010e060910030804030f0b10060f0309020315040c05030609010b0303030703090f020306040305180a1a0703110316110603090a1e06020309010c0e03060c0901080402130c02010c030e0a0302 84
    0x40700b14409001d080101001d040008005011400500015030013200c111111a4031400c0800c40e03000002c00032a540254007209220144e004003400d0710148407460001840f09003440403134038014442403280c181c050f41404020420004120071703826a2015010784641d81c4445100b00c0c203955120464644c0754000b40300041400b4400d611080344940140c03980201c140300e82d000b003410200141c90076000070301c00054250b64013910a1110b0342410303040d120061300320b243c00200301070b80f405541401c401c014000341c80d100f4113103e06085c0b4840c012800a803030380d6040c415204011602282001c03612400c105000030701d907141040c183d80c4203004441c00340401411a0ba40c080c184038842e80000c0c000c001b0500b90101003041131000d144038114800001408088000e8090902e1014108031882a4030070002c0207004900001500c242460a003040d5103d52514400102010b0b42d20102c0e0007140e142c903094032002d5505411100d003592440c0c0f020051450305158540d11a070a01c031001e009070380658552 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 417464793 1250 417463543 417463549
    0x5010626120d060308030f0a0e0c01080112110306090303070e090421030e030f09120a0f17040b03090d090b0c0d1b080c150c0711010c03020a05010e0115050603010e06 73
    0x10060280b618900150301502d0b0394640044c0d0b0426158801010104401c002c2085024447c020000c1d640f100201504c1c4040780000b001500f050065007081440c0050080400c00c03286501c503440080141a20304a04d00329002070754035001129000c000541c50101c541c85428030004660289412152442110a06042070603020005400c08820150b840d403c041d0010380c140301030b10080c0c115100d1a69602c55040c1080000341c070503e5170444603002600901c00042100c1094050640c0c0700c40401c099056041102c0e11078010782d4455901d1074000400c001d040040410139042d0f140c00b076102c0645254803070700c24641d2405915610a40c40d40840b5810003407900076111110078220b80c50407406240016510b20f84d89170001208030300b0b5680100740070800b0004911a085c1d010281d840b40d607040007126184e42050440e5583c107603040c8a8400140c009151091120582440d0490001d11250000f0311019000304884000c0750541d1442400101d041d1824030120b904a800e80907205c10580c031141c0c10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 417466043 1250 417464793 417464797
    0xd060504050705070b15032d0106120f15061d070e1011160f0f061815201b01030e03030708070203130807050f06091806010309020d0501062612 63
    0x204250003849016001d2255010080800d044290b45a00c500c0039000d24852041c4d402c1e0f4448d80103082e410305200b8843c00001032100c8010582000c0008580d003581d0500750745400a40d42580f51150038040040380c4442810a1041c0c82180c01c0d240382410707611044101e82035a44a5049613009070445504001d41d0321642003c956a10004159806001c500010451003072240d80032842c068800c41c0d0401c40c074a02140000014581810702d180c650107c81201c600342200d40c004e109900c1070800e034a0034028400c0c00b00748002094080700a400581c405c6001c0d5841019890300d40340c500c084400261254460300901c24100760180045003952a80e110603541e09074000c100f0803c42c40700344202400752560b80c062000400d5443c02405e00d103800c01052007d45204a20300c40e0003540700b0844c2d01403035112251031101030023690500d81c0b61502c403e4012005001c0050300654040102c079100000d01c041980031204941c0384102e900014058100e0f0003450742d503521404107040d0000c1c0c075044604150040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 417467293 1250 417466043 417466051
    0x140a020a240504050a052503150f0e011a0f011403130f030c0201030b0d02060a0305060f0a140a1a1b01020d05130506011e0623030403050d060504050705070b 69
    0x555503094240101140200c0b10225829a0140d01280868080c84010f002d125446880f4a80700b03d4104101240310169a14922006041e08c5000802040c40c0e001a03000402842e40742c0b13010721070004048a907078040c1c2140681076a03107240745030701101c0c0d61801444c011446401038644500b080000040e042640c1c01c01020255900402ca00c3c0c500001c0308480b5102580d8440d45130300c00104600d000040c1112401d41c0d02c42d0003500417074125000359441c213040c0d0300031360007910340400d05070780d840c3c04109054566440c4503000b885168010a410b01d100800e940208026210304003031550300c03c84500e9150115220f00c10b815003c2000351000b0a007201d41c41940c005c0d8030700140c82c06054500d060f08440c02121940c5030b08104001710744c1044018404030b4010240004022014003c0c070303402100c00022481984103221000300420704035101c01000418030751565424540fa0728240c03c006d0500d9015035101c62200d454920701241900c0c041c400e5600a803503640d1240e0130126503a84031203883d04058 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 417468543 1250 417467293 417467333
    0x3090a030509061207080a060e010501080610020c030d0201020a1205060a03080d060e040b01081b03032d032a0f090103270501020901030c02030316200d020607140a020a 74
    0x85441c460419265980f4081c003010b50306d0002d039241020a43d0112001604140000701906004002a030380c0403e0b800e800260894220381644000c0070700340d00e80800640c90f10b40601031070800400c85501075029256284503a21928020694108490201ca0080320500d5204240350014008120444040d28001d0b042c050300245054441400d0100306004603821100c0f05004401805000400d010a4181910461010003d01c6118001948030300a0303814071b0b03040144010304000c007080324410b529120100036403001da49041142503030346480402c1e8400407030101d40712100344510901c042195520f42c2c1a01d034460500f80c1036001180a01080f8500300e00700750700301c0c464900d44151a251010224804d800050391600e840e0009029500d098203070805540041c01040603007403051104940100d010715103544046c5004400031038001805643d00e00c14490100c070b4400064001405902405c419156240340c0318041001d050359110b443c40c0e200042c1c0004041900203400030b06c405192000762 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 417469793 1250 417468543 417468547
    0xf18121406041203060b090a0302151e0a03110a02281505010e0a1418120301030b040b10140f0120011505091303050903150403120f0203090a03050906 66
    0x1140036803400c40300b90b5040c0c4a1140b1103903403091564040c421100288403504c002c80c14402400001360200c0e515120103405403991f107074901c9000d2038003011141540000300e1418404081c415100c9819005034024002280c1362055450f603280441040c0e514441503540205201c0041041c4480340100c060b40880d4880380490201001560703081441e140064400c82c001019854500309040104d00940714400081c9031007031b42944103c498030f8041d44029001580655240002c105034a041c104000c40c0300d18000102c00441040f41000a1a00541c040c50140d0130781c5c0c85030000b118034817400707204890f824055105607003000e0400c1d0a12124802c4141010b00840e0440c0e81c0d4400d400c4c400901c04422a55a03441203400800314590850142409841d240c441c3d1034010081025100c0c04d00f00a4248034020070000da05990420400740c40000d41080b501c502d00f400d00d4080c0444442804007041a81081450403c20115200752489480c3c41c600418022030a614142d42075800131210580000b03003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 417471043 1250 417469793 417469823
    0xc0703032d0c090501090b041e0e0c03040b0606120f07020a050d050d061502060f0c16060603031205090d0e0d0b010e100603180327030308070f1812 65
    0x1a5505101c0082403420124260103602001072500a5a8200074107001003803505005240d40e510035102a13900c0503450034064501d0902d0441e40e902d4a0b442406a401c001d0104009071216002070350050380708201c51060b6448180800a0b140115140b880e00d11380c4c004001408c0d00e030346044940c0c010b2294015650020050b4a50b41c0c2031045d0310103044040741c40010a1000c0b4145841100c0041c50b0520b011600351442400081d11408003800c00502a640e0401103003542d4004002c84400024512a1050b9140d0034039000018110620003900801d042000d0040a541d003809101e104100c060b000e0b100321040c0e13a00c20780700c0759002020690001c81400c0e0803000603100b800720714080c0544c0700307002e1454074100c940c05000c202d03241c109004250610b00008400d001005421507160b906040c170740610402010b4080c10310407005040107103000d50710400001e2641101e0213900401981d5125820710303480040540300f2002c3c0c0312410403503241580080080f0021001d010764840c1c803903099050b96031700c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 417472293 1250 417471043 417471101
    0x2040b03010f0b0a0506070c26010c02010501060305070503090a141921020a030203030a02070204020c060403030504060b0312040509040807170c0d0306060804020d02031f020d05010503060c070303 86
    0x10315250002680c0e8400e00b000742e6142184e6407000511045036010b00e40601503a81c01d180d810385101c1c40003504080082240e4642d5500795284010030030600801c900c000c0c01c000280a807100b0701c90800464038101c04501c00d0791040084921411030382004101c00e01031595444000a02008112464055840002c603050a900d600e0451140940c2051aa020341106181001c9440c0310014007598000d009542c0000e4000c02600c0c0c4c13002c04520f00680341d503400d00115010303115101640d00035024803001c000030150103038013281c0624040c034020400c800f200414155204000d6140b440c0c2d480b010303c41004140b0b01007800030303803040c07080c1d050b281022078541d81c10101d00d03d2141600355814010424029040f0100f041c07800c803004503c0c0c103001c1d1501e000b001401c80b8802400207402040e00902001c29502c04000309140d0040c40c001201007210092524802504102e620203d010b0400000003058034001654900403903540c8800b034a05480e558003a4018118080902080c40c440385403207003907003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 417473543 1250 417472293 417472301
    0x60f090a0213080a050d0809060127020a1101050a0b010c06050c07080f0a0230090a0807080102040518070912060b0604060c122f0708060c0702010909051b0702040b0301 74
    0x43c0e000203041e10402860010700b0540309004c6502000040410403240354800a0312504488803184c44141500c12101002c20500e82002580d20349400050803000540e8003680c0e1174100406400200403d40303a000c262425208000c400300c0c00511510500404151603601290704a82ca622a003480c2414558136907440390016042004080c5021a03940c000d1901403200d01880401c2302c400388501d0030318070041c03060300081300c850f1420a00d0204002041d500c401c042e420180552000b103542c2c0e82d03074808059001c2e502a0050700d001e80801c3c032000800000c071060441c001c485688607200700c5820801c0440280043c8901983c81a032203651170120341d22010028400340034103940c0c40c1d22800c0f03141000c500e40f010065409d0b04100c0f40d210050700302c1481c0c40764507080b40100045c0050341d6141c0d80c03004e807416a0540141c1c115000e01c2061283d4201ba620080150500c00c1c1c0f101100f841d99880b0040880702c08844170751400008096012160111400906007140700500009285041002180c00c41d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 417474793 1250 417473543 417473549
    0x50f010837050102070201231e070b090141070c080c0a0b370227040509030307020d03110f070309090b120a060e01090506040b041a060f090a0213 64
    0xb50b5030000d000020f6580c00060a1144815220380c51320301864907403285050302c200c0a1001100e030907409041500600e9804035140ca6030000322a1415082001c240360003040a41e090010015502c038000324410a450030480d00e1b40364041d86003881d60300c10084281800c00043c0160f040101d85000038000560f240041c0034014654001443c1035605c4d80b810407042170018044214220042d01464000010201c00c1008030780f130324801c1d44250b070300c0b03c8410002c4d010380072001c2c03100243d00d42100c5091204c441500020401214240321585504240d9500c074442070351014010b800a52007482d001d8001e80000480303081d0440d0380780c03407c13110701c15003241500120301c124000b0340200c40c20000e0028502603032140d954200c0b107544601d111601407a5958007903a00080000b520707450280406c42c001c1d4800b4040300e4001080d2281482e0034a042004c1c00001c803001c441d22584500e214450710a0f00e904607111f50720144c40d124109001000f00403405038010312108485801b0441340e02104c0d0880300c00001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 417476043 1250 417474793 417474803
    0xb0f1b1905071a070210060e060d080408030c030702030d030b0a0e071808030309120a050a20031210060206070804060218130204031502210a0908030403080a050f010837 74
    0x701d814413220082c14040c5410440c1805030030007005110340317004200340076005141100c05100000355842c0c40034030707400f507640030755400d00021402d0301c140e01000c0000d001203442213041d12441007220005804843e1071040d040d4110040801c28451200c03800b6030141c00c0000c505260321102c1040042611811444c3c105e07060f160004403c3c020907100401001004810324008107007000c45144000381903029010f80c0208000c00611100c80148a008440d01800504800e4a90350304525150324000001980c8000341081c42c1d1400042203440440c0f05d1b4003c9405540310102504c640c0c492002a4103d0560301000c10000542d0040555840c0c12046601d0141400540c9840c0b031424181010103500d003900c828640104002c0f101040c42c0b00103280a07000c021641d0145894216500c2c00074003e03180c008094920000030710050507001503066100f0074031100244a240d8840b541c21401220a200d850a287e10a01d40700c0d0420012210810982c54260070301c40ea41c2850800caa8001000f504050710 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 417477293 1250 417476043 417476093
    0x105011214180c041b12060f08060402090112170711040903090f0e0f13032303010e01050102010207050d0e0102150c0a030e0706020c04090602160b0f1b190507 70
    0x120211080c000000e20403002c81d410042e0240c0740c41d01441c0c01e509580002c2c108034400c6d07400d0300c0030350b1184e01c50400303060000c21100b2081d4440003415903c04e0305072002c2e841904400700028403645e00c8108041c0c4a98000106280e810004030500600c9d0041041103d04c881c0194030b0b400b10341c5640c812001000c0c06561248422403502884030480c00b010780040380090542c03810410a003c1036003d00d5001455841d010001183c94142213a442107001b0b02034000b1035900c155a000440c400c1d0185041e5074010913034900e282d1341c400040e0308078421900000c0a41d00110000c40c400d60280e20201d00911041c016503c41651070400a0000310049075414008040800c16541c4298148154294050050001c146035424840060358a0000c2e00d5110312640d140c40c4484204110380d010799100d890010601c100c044980d10300440c030004112228905440c075000041c0030015035400c814500007103400b0161901d4140900b00b03518000e890b00b61030500c4020440350001132030b0703481005051b0300d415600345 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 417478543 1250 417477293 417477331
    0x110114070f0e0306130602120f0a0b0d120c020303040506040602100608010603020a15030612050d030506010e0d3210060b131809021e0a09140105011214 67
    0x203041604021800030030082d2900c9505800d80740082c0003a0000e43e03025140341600340c03d16000e406880740603030307821403001c03e04288000410316450450003401c40080601c4501c1c5004140540021445070281c02082d83d1444200b2540c051243d01011070b0024064914054880c0040380c4c5c0c95010b94402d20040e8000070803100d15240030312a40c4081c118050003403006900d5074000811030000d90040c100c2c00200440202995806540128001c02c59100710301d52403600790514907210441101d01d003010a0801c000601d0542c07003501c10104008000342060207100060f02c4814040a044410000c0170880c0c02c1e0b1100d20107260302010b5002d8010300c00911701070040c411070320291851a4490050700c1000d01800b87c2140c205c8080740107403102c00040011803040c1481400c060516228007a4118514402300b5220180314041280c40140030b648900300207646207082021618180c10281e0724a5910006000640c07040c0306020303a0040405002c00c031003001c10f540d81d03030080003903500580300d4001c9040c1d8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 417479793 1250 417478543 417478547
    0xb04090b090a020a091b141e0901081005010504150302071a0907090203060108060105090d140313060207050303070209040f06020409090308010905060109090c0512010905060f220c11011407 83
    0x25010740000c24041c480345120420f00071509200490310001e01c808507c408010342c3c034400586004018924a000c204148018980c106501c10341415000a4115001800701c00307418a4900840e44103035151490503280095400c8242c4a040390f80c81010b408101840c0400d150002d92281d181845a4600d041d0802100c00340c50010345d0784c004154a40184200841a170f041000c1540c4684282406540c1d000084c1c006400d00303401702c00c000c0c0007140c45108070030120b00c00400b62180c1d00c03102c1c1d402d0328030580320203060342d440c02548102c42c2e059000300214001810320340d2089803c544100801840da030710355500c0c0e00590700190005403550380c0d0359070400145580f080038140103044124080240b0304282000a14500d00e0340924000191182090407a030380c454401c0f80d182440c40020000c032940c64910500190900b0b071100c520603d0000d03a013035858503100b02040f100080740e80a01c0380f020b4a9007086000707000d807000d02e9424042c40e1884412602420300942c40162400071001182c0e1504601c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 417481043 1250 417479793 417479809
    0x40b0702122701020f0304090203060a1d06031009020f041505030604140105060f011704020609060f031e0112031809020c0303060a3f020a0f1502030f0a030b04090b090a02 75
    0x43c0c11980b007440c201144c1e90b804800c840030f46800c0075026940380c4d2042d001c0340c000c07180c43c0c0c030650f5042d00100000140081450045001d20300850075604c07402008a82501a15071955020798821502410a08640b074560300010500748a101c0340000159500c001a0034400308071000d44101128224024900900b8480c80394400c600303d410400d41008000000d0800d409085d2400300c00c4a00c01c00704095540b454196030b031b80040100310b1680c5902070b0040001d940c01c15035850802200c181101482c503242c92480c0ba041c0c0761102c2014100301d425481c00c986035401c9401202860b070100c140413410301d400e80000c00c5020b000c50011642d03401e103c418085041c003c1c0d4401139070003681c809094900120310a07902460510405203074090b0081d04200440344042c1d0f100298800c49101c0002a40d80c4041851801c9445500500e445169480c1c0142e84921455040341e02e220030812074440c18601952016000c0c1c8005172000404000301d50b22054905d4060355090ba0690010011104510300010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 417482293 1250 417481043 417481117
    0x13030f050a091e1e141e0105161a011e060e060a030609020c1606050a0e040c050702040509030c0106170703020423040602070303051e040b070212 64
    0x503115140550110004100b0341e041c0c0900c0300400f0203e80b80f40e10454120007248003400400152034a003a0003842d4404400c00350b40b141d00302c82c0002180686043c41d1050403048822008061021496503120044403254800e80b07a883c21400c1480109010030b50707024010a240640d00c000b60401c1d410112451000c400c00c2501017100d01c1d003001c041c0806584503805803411801651002d890300721008055001c2d04c116004a83c0700e6202203585c104460340050b40625103d0703042e00c110a52a128602114148100d52125010a5100d030b4402614106036100d0604210b85150843c00c0085d01d50005040c4c1d8019103682d60780f030740041404940d41d0b07028801c0100501500600c50103003461a0381c00b5444600a10010b4415035407040340138081c51076030002000c00c0c45003401c20900e501e05481c001d0700a4014a40980000c0d140000264101d003821091242c00c0b51982607144060b034071076580c00c0c250351009041100318011000e00c2100d0081000c090300740402c4900c00540c0102e10308042c880030202100c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 417483543 1250 417482293 417482297
    0xb1314010b0a030803090c090406020405100c03080609221b0611060103060f0902030a1a06060c03031803090a0f0e0a060e0112020d02100203031e06060d02090d0b13030f 74
    0x1022407400c0e9072000200300840e43d00041e103580743e80c0c5080d40e40d820705500441e00c54001c41010100420003e5660082090b10402c450f42041c0d684110011130303924850765801008201c55402040c3c161500c05c500541c400350886425841c110101004451841d40c6103040b5a0f803881031a0001881114580020150a10346881480000100c101640d21001032001400c540d94507580702e44d801d20150840035085c1e401030102c0398a00e030340746081c03448650041a804103021201c1c0100d859450410103c03421241700f14002c60440c2c450300c80d59603411080a032604090b00c07040080d0185602c404040000600c0c01380f210710740f0140b60446110050300014200d00281d071512405011111540003d41d0544507004180d0f880d10103c0d1000c60b0b0300002c0b408010f503100c19904500746000c0d41c0000118030445074008515440c0394403030b280070390050058400300c0d400041440100c0c10b0700340d164080c041d00300d80280a003c1d5a400b5880c0c0303420300c1c007080d05c40e800090402401030080c142c1080c00e01242c40b08078 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 417484793 1250 417483543 417483551
    0xf060f13052403062e0f02010c090b09030709290301020304030906140f1206040c170105040207030e0603131406060a03030c02220e01110c060a0e0a0b131401 69
    0x100301036501c28100540b640c903880e01c0220100383c3e0f944440004002d80100b000200c40050305400388500051a05800e02000a401440ba0101d652043c02607800007805a2212100d5506203154507005400080f0950303014800d5450004a40302039000d61039070b03e040015040b02141226010800d0800c0d4a104640a6030040081c0030000b80e01402080448000c0e29004054242007183c00601d8403a8034900ac00190380496034108142050f40081d0248a044900700b12800741407000313550865258010a40c2840b040004001509094000f04109031103844e06800b09599880012803075002030f28104001000317140c0f040c0801c11b9159001f800034001d100180b0280c40e00b9800244140708a001c010b0401610708410800c6484516031100e2070b11281514220b0074a11b110030000400201c20540071940c20940b220034151244030403181c02da980c61000d08500d9541203620005080c0880c5076900901c107001400300410071800195024080340b560040d41c0058505081d5640419950700710b80907450 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 417486043 1250 417484793 417484819
    0x1515031504020a050f060408012c060405120319020408060906010e09100b13050a050714040602030f091807050a031103010501020303190626010609020f16020f060f1305 74
    0x601200c600854000302c5217116810f08810200380350b401950300561b180d43c20200b882c010002081841100d442194801200e502e14083d80c2c1b554500e003e81c0c0150454000901c1c80b202010550001c603488141404000503000c81207044004030303441a8012412500401e0a022207640244602401080c04e40c041c1c000c28180035220b21748845204100d02085903035220061a01e80310180800c07035400181c0340400451802d0380d15200505030403110100081c88403180806d941d142102500c081d42d40e0795006500380b00303d280f002c0c2000e40c81002030700c1e0b0014100c0c5440c401903150758505441017509070344454441c9203c040c02390a45500d142111038610007030006010a0360f001058a910981c500000da401b03624a5186e000204420b0b0040d07500401e50b005240303d400c00d51800342200c040000020061655240200800c80c015031142d009900002c00104e1001901c00f4850103041e4001050741d5503011605001400c40da01c60b544071008504041290700c69642e0201141b4002c00081d5510001d40750 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 417487293 1250 417486043 417486049
    0x70303180506252301020a120e0d110322090b040204030f0b0a06030507090207051501030209060114190e10030c0f05220618171e151503150402 63
    0x1403d599003220041520485414081d070140c0326014159080049418030700c1c1044d495010754080182c0402003410342c1c1c1f452090b1343c81031190382d0030155654040e10343c804580b1003c88840303030242c031050050301c824040c00c0c0c65218918100480b104100c0010340141d4507181d800c1e0150740e00c0002107441140305000c108040748c2e94807910014154440301170501ca580c0d0325000c034001c05039a00050000e1050040104003082a5401005078501840c219400300d10b02091346901c5400c04d000c020f4000d400311002c0349095026004080590707013444080340c1040c0c803164150013a03d5a00100308005000b54401480905082413600c10700040742c601440303110040080a0b00211201544d8000c00000103000110600c550112042c5403880a44480b02d09503140b400034019010034a82d9403000310600000078055800210554521480740c02510071165044811083d900c6110310110103030045620310b042861080384021f07c40ca2039410142c1c0458808424180307404445100f02c80c134458032000b4030016903 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 417488543 1250 417487293 417487327
    0xe180d02160e0603160906140405010b0f070206120f070e0301020711060d0b060d09031e0903030c03090504050f180f1e0a020a0e09060c04030b040b0711070303180506 73
    0x7541965103000350f61580000300b40340c0701454a201c20f0030380101001040750506a0820307000c43d400030300012000c91480c0200f000303d61080c4500a04d206080103a03114610004014202d6180010b001c90b04040c3e00451103009014202c0343d000d2000300c85010001e00580104095041d914164000c60a1000c1a510b00d82d24041c0c040e07039a842110041040000c2940b5a088a0842000030f03040b9915132400410140182540000031808503c0256108803d03041c051491f4030300b5030041d5110418a895514203850035015a0420b0f01044412000451180c6603805a54020307098204450260325100c60040d00329a038054800e040b5400038590000c4130311001820030601540b11405012800641000b54608260088000c3d00003100900000e403802244000600c100200c0781596441d079a1510780e02100e02c00c900008040010384804540490001043c8940c051120700300030310303203007465904146001000d5200710009a80440800311a40042008500070031003924901e040c000e015400704002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 417489793 1250 417488543 417488549
    0x60414210303130203070512160602031c02090114040311120607020d110f12041d0c1606060308031504150602190c05060d0c020610060801090c0201060e180d0216 71
    0x500201603c200750354042c4008402030100401400c800102d070017040351074100c50f030815451a0705210703001845a0010044602e42282070a4110000741084605c130000c1d000a0a01410050b03100c003034074416036166008001640c012145c1c3e500000000003003019802031212043d805400c80001c0c82401a00020303021808c04041c02d200c2344081e41280828a44581400104100d108a0308401c20910390030300200142d0312071042800004001c02203100001d0b101f03a61200807031070100040c4410140c420b283c0c040341e41c4100c03004201d6903034070707100da03842ca800650329819031690340c90765030060380f91030311944181310040e80c2800c969a1400c14040d444d12448081c0001103902e44444a080000c0d00b0f100802504000300655103c0b42d4109030500200300b480f4008000d442080c1c08160380c074403e41042e02c12a600c40c0d480e501e02d6828080e003000a4015011814155902c54001051401040c0740751845008091512180c003501c4070040782c544010302030b40300c003036410090f070707042054440c0c0340710f6025 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 417491043 1250 417489793 417489811
    0x191101030b030f160614030403050409022203060606180302090403050f0d0e030a03051e06011220120609070f050703170708010f06140414030a02060414210303 70
    0x34000810000c64103059080d20b0008590040b5031240d502c40d21354101410903a111039540c148425000343c9030340e0440c4401d58014010038800c0c04200544460340c0c0091500c80c3c0d42c0c0f29140322101d5200314440c9114025041202c404d40c4070301d41444403603440f52a00c8038400140c01c82d05085880c503008624140c002520140401100285003001c141e901802c82e4a99008541c0030440ca54600f43d40a80b0f030780000e50f48500180c10302c00030410200d04110002004102c102d000702d41c94462400640301c002c8000d5000350915103460245031340e940d001c5108196400c0340404660f40f101d01d2556070070001c0004190511401c15801031042960384084a14004509801d0141c0d94240d681015103907107400c00c0084000c505e40c1c9003044402d50f484180ea80c12100c0100c40c0d514003a8507400290b9441c034172020103804041c024403040040340c00a00301c3c440745640140940d410141e4940201349a43d01c2034120a03a640405a0001c02c50b00340402d40004070024124440c0300941c0e4000300c11b03128400680f010b50 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 417492293 1250 417491043 417491051
    0x90102120a0f0b1f030f0209030615120d020307061d1e0c09150108150f061308010c050a080906072f030c16050603042d0507030c030519110103 63
    0x20032400e03035803005401d1640207182484a020542d80d680100c0c00d004c00300d00000e404c2c01c41280c2154200c0c000d41e000503034011b0241c0299070b54020900b54420744009410350101d80c04003140c45004003032201c401100c0303d90f40950303030340da8141c01d20b1010341d00b802e0300b100d92003596100c4c1c86142e410007150700b0900d0011640140c800317a18014030a8034241d880701007298000810014003650f02c0d21702580002d1400f0a8803900c64954901c540c001494001c03007070300317908800900c1048500780340c00801000d620200441d47c0d8102519140e00720308569840740307860041140080c400e88480d81045640f0340c8600c040d00104110f00d441c42009020860310346002d0035074030040349a01080d004444401c203503600c001c0d04803600c400610f107080e5610b01c00d07600765501c04414040d0110300e9040c1001101c0c8182c0c0c000a0041844c414000040f66400116a1240815030402d907440f001550900040300194002c01075020036a04604082d0704000f01004c05400c5c14000c140c030f01000450b0303c0441d030000c00003400c0002d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 417493543 1250 417492293 417492311
    0x2060a17060604033201050a021b01061406070609290c0906042106090b060f03030306030c06070c080f03040e01050d050d03050c040b0304060911100210180b0a050a05090102120a 78
    0x20030508000c4982d8415420b21040003207036142c0d513010302b90340c510039100d41203480d000b103040c6400c0300c500d8000c039030004c480f5800b10112402c1071001071034403a00c03030580054080d03181d440300c10400000d40744410518044d41c2402d6250301002c400d00350496142468035141c20080400542c6510503481941140e403c20b81440c03070310800b048204d00348540c1108050080012502d45001500340849601e4413682c002c0c1a10381d42401c00106a911800c1c014000700b0800d803c5008100b0280c0151100f16201011040c0202c1c24810a200002507139540c40300650325203007800484045420140c0000d40150b410720300c0e20020943c00203203018100740c01c0c100012180c642240701d008522427a00100c1c102c500c00002c0c00100485c590007803541502512280c02c0c0340e5a80810418444001003002005910200000f0b1801300994040107040c54003440c1e01030761303154581e1501520f402c215000f0b10015a01c90401101c1c0395035003e0a60700400802c000c41c600448041c1d2840d41040251200380c00942d500118 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 417494793 1250 417493543 417493613
    0x7030506030f061914100305070f0e19020c07060f020c0103230705040510020312060301181709040507050304051b01050714010609090b070e010e090106030b0d02060a1706060403 78
    0x400140103007917900d0b1a452810801003802d11103507104c102d40a114030b807400916040400c2c100c000b40c0381c1d01c604040340c0d500c401e9414030f0188114000c0c55613031903007002481c008244c00c0004d5001440704da20b9a41c0d03c0c07080510040e0810500d040c0d528189030410720980b00c3c030701502ca0300320729409070b8480d150f07020780307030707041d00716414041c40d04030907007092118000004260300000604181010070f079504c2040d035240020300d400d0302c5055000b074274600c04090f060000102c80c1407070005882007512045013049102400241540c0d030035103001002c100c000042c8810701c24180100065400d2040d01c1a140809400c00203000d4420340c00064040e068420840c0110002900701a0091100700003e1000b4245814034441c00042903c2d10000305980719804030b81c40d400380407504000ca01c0141a041284c0c40c111055024040e0304000e0b55206140004000050b03603140050721166072141e41c0c640070502221990200e049018005c136118040c203101c00c00001e034a0300c0100c06020881c0880140820f030343c89013 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 417496043 1250 417494793 417494801
    0xf030f030b0901260f0c0111150a050105030606240d1407021606081909020117090c0f04050c160804080303160305010b07020d11060c030c010507030506030f0619 71
    0x10700b80c0c0000b0341400043c00700b40c0400e907402020800281c03184d01c40e200244d9903036281c41e03550000407140c1000c1d210700c0844d07004540040740c00810b80b013031b40c07041c0e45204200035120108a80c1928034a503a20010301a50408216850307104405443c0d00e00d0071103551801825071212400507106503000000c40700b200f099035805ca40302d40d441e26294100703542010000070b5151500c02d00040c0d06a00c0320840029000d2080241d14010f50324807040c1c4040540e07003c841d01c0504130010080c0d0503c0b01400240c0d07803820140308100d200c1d0107484080e0810814500c01c1014031401040d001344100d0414091148001d4180102c4810092240090081442515040d081740c040c0c0e41c0446a913000100800010191400307658020900701d550411031aa02d8141100040c05040c0000e0742003004d4819040029a1008008082e03010007802e07039081040400916244d030703010101100d0240d4460091003401038045c000e268100b1401c5000e4242030366024401642e036640206800039641602c9400b004495460344 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 417497293 1250 417496043 417496061
    0x190b040b090c221202150f0304050c010f03060609050d050a050f010b1009180b060d020403030e130902090a02030c09061b060f01080c010c0512030f0703060b070f030f03 74
    0x1c1003030224500b40102c18925000b03421410210740701500201d0400a490800c281503c4141901c0c4290a60b550280f1032568224424940a407104000c4080c2c0080e0320000b03544264031030002418254444030004002802500091042c181000750a10003103410066490980e14203482c170341310341121070402c0c504d4a01c1c013940251482c0a540400d400d040010742010b0042031003503d011000c4042a075046840c400386210340b003410b160740c2c03030140d070a5061074200041004000b080c1c05d0400c582c3e80c003a00b00300d078810ba0007100450070210501040f414404440c3c98000103410081144103025004101c01120090242c00b003a9070020000342d01c203982c281070b00d40d25000601003035200d03002841500303902c28030850102ea051040000264032241c2c001c1c2620305844400c0302038260010018019100c807543c0c22801c68150080c40101d88403420801d000e1407080292130302d08401810507900182c22030710745410a402c0d0382000c101d0040800c01c51442c901d2910348c0b500e1f15106285480341c0840040c601e0701 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 417498543 1250 417497293 417497299
    0x1107020f04020f040b180904020f090a090c060302180405040c06050f0f1602091623040302041a150a020703020114070f030801090c0230040306020c071706190b040b 72
    0x11402285d0790100714083c19078107880100311124440d800041180b40c99040764000d6100036003180200060900c3c455590b00a100c0c120007003a0b486441e0b65035680c0098035008800001d9010404400780c044031815075400901c02e031010012803c080d212919001e106001e243e040c040009140303000c0c41004404c0780c0b00034403500d101c107481340b001c00d20005690040302c405074440e020341408140702000d55080e03040c000040b84c82e106241084d1a40f5003414080300c042d8002018014400040075031100c2c01a4818216800c0156440558030010070458811189100281c400c003031140718042c0f0b400094510560307809080240d104031803120302c0c141610520b54010252640440c030081010f0f005100c0310306a80740008140f0048000c41002c80c1d440000008131245403141455081d1201000117502107054285d00340700d0b240c0760303c13500d890080e41d02240300b20440383d204141c10030910300c5080091302c5030841d06003c0e001e2401c24804a10400c402402c0e006d6400750755208102140e502d95101c06040b40340a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 417499793 1250 417498543 417498547
    0x70c080a060902090601030c0e1203092214040b0423030a02010b030705061303110607140a020310060b0a080702160f0e06030d09090c090f030b1006031107020f04020f 73
    0xd031510300003a0260340400c0340206000804603400d903000740540314040c01255144017070a1014001c1199408000c62807141c0c50000308921032203a190101c900014903803007918144001c52410103e42102d07000c0c0e080046d46801181070200140e000546d950300a504041c0c003984a280c107803907486c11400005a42c6e070941c0b10005071940070340d406411410044404500b03680701203a4901c00e102041c030405e0024043c1104d045070900000d400b1407414074050f00e0142c44079042030010760701c44400c00442034541210b5444010b00000314601004407650008034071500348002840c00e081c0000074000c7c440050240111580080c110074420840f5805820070510800040d6a0728820380c422407580307014948030b403654040026900d0600141d1200a00c6142d62025100c0c2d00e800c90450081c00362002d180d040104d100f000280c1d00c164a400000914022455a006828100c40d1110510000d610a000b4541402c40c1c118081003103805942c20b060b0141c0718004400140000503000344910708801d001d207080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 417501043 1250 417499793 417499813
    0x50d0332040815010503060105150304050316200d1e0318090e161a0315040203010e071803050c30060103020117040c0603020f0c0105010b0d1817070c08 67
    0x14451400284100075003e035662500b05150b12140240115034111860000d1405481c1c1d4150045a1080c000d0003941c2c20511000103644c041c3e0514001a07c0341c00e00c505d5031518517440041217003000030045694180009043d9103d41d003140000c05000c0c0e02c210030b0140d0405040c024080e2280c00c941ba84010200103803034414000c000c04030bc4d02d003076105220300d00c04d003003100c0441c4501c40156800c602c1c4010380207002c41139031201544021300f030140c10b003030002400c1d42c1e90b22540051030280c60140003030409071815200041400b0204801e1002185a81c1010800314401144080584c0400d0b108828980403810a68a0814031200d050f00c114039800c800044210340860264142c900c00d03a10103040040c244161031407035206480240418070200020000580070354002c01d1500c107c83c660303074100745d0b02c40314a40c2155000da0003009040c0c00000c031030159049603c00e010322a90403140c601c82260701d42c1c42e8560311455116041c0c1c00c0800016908040c05002c007581c50003889110111884504 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 417502293 1250 417501043 417501059
    0xa0e070e040b130c030501080d051e0c1c03020706290105030603010902030742030209010e040920030a1109041b0609031a01050d0201030f0f0f020310050d033204 71
    0x48244101406401110301a20b415481780c01200c2c48040689112f002a1036004510b0303406a01800e440065845902100c600e0f4905485011f0080d40190302c00584a40040c00c00c001580c1c4800030030100c664644c0051500b01c2a989151005d9130401e192164481ea28540800c1c0180f850b0300d00654144105200010f10710080000118111404080507280d0548031495158a181103024480356001d040440d210162180e0301416803440c3c1450200710501104020608441c1c7d0b8900a42e03090011a43c10301049081c0c4811030b00c4540e042e4028070707400c0c0103501c4c4c0d840b600c0800300c201403081d82898003007400d02003505c141e62145c0c0c025100d0b00983c0c40d900c21010b0101e01d404e10049411142c602d18002544c1250709000717040740d1000e801c140c0d0140742070b0b00450041000e6050421559500c41306603001007031600c42c400d0070307603a00311005a9038100400440c0b00c100c055400544030340c0310f0311801d400003940b00d5507800d80e4040d03420181e4100070182e0302881c01c0300030080c0e60114009011400090001c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 417503543 1250 417502293 417502301
    0x14040209061b070906080615060a0c030807140c0606010914030a02040f06051207140102011802100309050105191503081204080f030c0a0f0806091303050c07060c020a0e070e040b130c03 81
    0x420b032384000d6491400540280101e901070309002d42e010032002d0040b040403a0240005503400500c600c2c0010b000c00460714150f0f0140c01450202c0c0342030340000100034455070051a880c010300301c6030540318019101e180c0001d81d100c50301c0e14028042d40d1152401320700c61506800034405414010b0641c40c210100e003505613521076a6104a40340b0f5010320594000f954010b00c20459404030081d0700d82206e0000d50280309018050700081c104040d69007440300c0c0460020b00c03802c1e000e0380c410303c1c03210961101c40e0700c0581a40c1c0301005c04100754100100400c0003941c000f085885035010003000150a0f91181843e00883c06404284000a840041000510481c840051105070b2041d00c5580e070b0700c60910f104840300301e8115980c0b41c1091000c4c010410540150300d60900c03041c8246000c61501009001250070581c10398440404900c5400303501046107440d15a039000303420440141c00907480c1058000b4102501d6440d40d5000c0d45da9280620803075110001090784032034600c2d100344003040401d40014010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 417504793 1250 417503543 417503551
    0x40305011b03020c071a0c010c030e07090618150e010b07020405130f020609130911120f0703030516081602090a02040303080c09010e03070f14040209061b0709060806 73
    0x2010440907016150700078800e442011802100a041441c10103140e01e0750010b125481c403144200510136107070306070400d001d01c00240c95980e41c04100a00010119458260282c020151040c2081814000721022030b00808000925890209010840d01d822200b00601604240b074949000000403035803d110b0300003440b580d88256420003640c0c0e00c591890420201c1c800004100710510240440075280100181940600040981148a100d03c03048011075140082c211610020500341d49030f2403810000c134110800402025180500d80300130425281ca032540001424402d005c0344a030001c50091039130456140d809821039565116440d00484968903404040b441401860000b400450541c02071b202202e41c03680300c818440d120610703018115044610000d041144440342101c440d0740402160004081c90449418580e0502d03111408080141c2c130094051030040144005a0700c2d400101c1d140f807140c0029507000f60243d07010705800c2c0b50702540300c0f107881030510101080340b80f400704a150103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 417506043 1250 417504793 417504821
    0x5070f0206090607031715011e0908010911090603030a0c0b0712050106030e0d0f020c0f1305041401060e10030f1401150509130c051002030409050c030a0b0306060625020604030501 79
    0x6c40c0c0d204642c0c401c0c444801c020250004200c40005d07100000c10580d1864854014280b83c40c050361640c200d9401c691520340b00380e50240029403030000c0da041840c4042c5e0002020782c0614641011003001030410610701c24004c0070007903810009940248203940b9a100314050000501035035035101c40c000c01a0011001c0d52405000c0c01c500c84020034000c1d0405800c4178159000707041500d195504218944541e00505078210740ea5030018000c0304118452035110340d2090303041900d011001ca140c50f00b180c0e8240c2001c1d4400854105120811000c225031004a9a1001d01561624207d1030312650008484d524084150700703110104000d4501e030468602502e4064600c001c25a1310101a2400001400b1000d08144200c240a100780e04000c040703065400500c0c01240e2a05640f40c80396800ca070000ca82c0400c031401c0100501c070200b182d07801407940300c040840041180f4100280042ca41307106140f0f40071102929000340c0000850003008030b030401038004190310b85071507503810514007808003c4c20800c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 417507293 1250 417506043 417506087
    0x90c1401110106031e0f060c02240405060a0902030c120c01030f0203060a05010302131e14010c200a050909031206030a1a150d060b090c0a05070f020609060703 70
    0x1d0403020501c56603040b603800ca03e011950712000503100381c0700c910080c0f068441140350744404000c518075008400c80f80301303298001c1503400008811101e80307404000000c000c0d002044140b0001c00d2001945a07080242c808000800b40707000e1002a1030031491690198000d820081800f10050011950400c3c0990a032030500001701a800b8010072848210380c41580b1807560b85050051394400d9000e482c0d143d0702105006581c94903051220350006080000200300b4103545024407111b035412108030415071080c2000103c1034015541e00c0b400d02d4001c03001220315041c80b040741200d40d594100c08001020050b21700d584508111900a8490780032021200f0b404121401041050600040742c9040c2e5402c80c44044440f101c00700352041001c0c010b809400340090f90060349410366144030306002c007244a02c81c009108025403051140c01c0e00c0c000d1000018000c244240701d059508501180c12143d0300880b20b41070300c00b50f4030000d1424024030b100e494002d040403440408068020104003c0303801104d40300300c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 417508543 1250 417507293 417507317
    0x1501060f0e1f02010c0e0307031b0b03010b030604150303020307031809090b0906011a030403030203100504021602032503150e0f030d11210711011b03060504020f040e0703090c1401 79
    0x501c00e0706c1340005403900340c0d0000c4420000b24444a4620f0011507c0a00b102245650743c904440036800a821140b01c80d40d00100380b040c9441d2500c54524011a900c501c40707261441c58801940f24001d41c5005002d100030314060000922200e01c100000d44140c06080007000180c0c148002841070450301d4002c8d51281000100c1c91102034454441031700001c070411840d560b243e81d41140030f508040d04060440400769004581c958481c00074011900100300d0442212403203004061910068904201002c1060b480012141c40341001003015250000d150300c1d070505074001c1c1e21000b840f46181098850050800c00f1009010110041c4110f907030522085c00720302d4910030b45000a01c83c4401030035000f00c050300444004940c1c865025400105070805c030b00c91010340c50180342501e40103500070126080c00c503907501c80720b60548a10005820259003c5003803004000700540c042c40b0324080c50309070403003c00008507414030a401950105034032001050801e640ca01403280d40200c5003c0060200341c50744205 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 417509793 1250 417508543 417508547
    0x6170c0313080d090f0308161106070302090303090a060309022d010c02032d070f03020a06050c030f0f0304030305010e06011709030c0a1208091501060f0e1f02010c 72
    0x960701400340740484060710141560780c41c1c081c2e0700180040d43d400d62208551404100f40c1d00e00c8510007806601c901c240c81c5441801c4240308100c05003424184140d0700c06003151506d00280316a4028603a040041e40c501c0c1180009255005500c07965500c001c0c880303804520f1907819040500d0541c401d49140300d6a01c0011450503c4580c081d211200100503281081c50541c410340c1760715503031400501a00c10000300c028125a00e031240b0001c0100c00a98280c881110440800c51500200348401d50441801c0c01d40d070008483d90348038440c9808214021910040202c030620031170f0044c101840b025a80c40e07840034850680307070b01704841c2580464540000001c680d0b021031462442004140e6a07445181d240c101100210036015000c0000340c802488602c074140020845850400c1c06200038464000c0d80100c001e0800f0002031a02c101030f084100c1c004548603107580150306451007400c012070081c0c186201101d99105c40c0c003005910149034584039003019102480c00c2115000d60b4000d01480e02c040000f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 417511043 1250 417509793 417509797
    0x40606090305060f062b02010f0e06030a050903190e01030b010504050f0d06060b0f0d050711060a0e0a080f12060604150804080d09141515010305090106080706170c 72
    0x1d0b1031600100001080c800301a110568000341c0141070140c104c00c41d84030007158204032140900d01c001152040d000755030300300c1ca03949409210392406c8059004c5003004200c8501002d081412110307103d07808125100342c28401c2d078005400309403403901030a03100000204102c45d2501d000d80481d151120044c49544a40112401c0d00d80c00740244107000144002c2c0005c80c0f0003d8000c2d00c0d100e0703907030341c0100303010302014000d00c00c80c001000318684618070b22060904a91001c0c09620900c1080e21a040c106400440c001f40c1c03042010340001000c600144569081401c43c1d140200b104a0010b851208100c10310054403011610756400500344c0d441d00c00f844010301c110f0094108c0307440180d44031007610b0300c1243c402c0da02070b21954210b0f050084002959003500e644007030071502508000710780c0020710303c200280c5000c1e50141c42642c0050a191114080607801200d400d8100b5072110b0000d03800000940140c0700a000322012602c400341d44002c001c14000c24a141c0000ea0220000440d08003050b07101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 417512293 1250 417511043 417511049
    0x2030708010506090a090609022701081f0e0a020705010f060803040b0f0d050f090d0c0309090504030c0b0c03101a040504020306120a03020d0f0c030c08031f090b04060609 75
    0xc40300590307400c1c2801c11180d60000c01381503038001c50400003c075070300b009409a100101080c0c103001d40c485036113071500c22019698009240c44d0405100d0100000c1c1e0707020a201c0c0e04000c950000c040d9641c2c030b1402070050a500ca800001c10050b01c0c100b8805209815401440d00f01d016070000c0005c004000000000d03901030744501752060b4400e00040c00361400143c0180b0030710220a803545c0c501400400000c0030b840c8210fa16a2100b0320180030803e48090600c2050b035200280e280803050a0300d03554015103403c0090044c2c02100303984900003403c16008040d940001600b003450807203249031080803411158403c0712240b269400001000601500500341c40d00383d40d0101850754207050402050100075040102043d40c130040082803141e1859090156054050080d4003419084980c181c02401c500c0382c02d1404801c020071400d01d0000319034041d151009841c1d0022046640e41c035411100044100c90848206090360300010000303c4403459404030b0015402580d0902007aa5285001d4807040407505c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 417513543 1250 417512293 417512297
    0x306240e0f1f050904050d032f070c051806010f0f0215070504120b0603010c0503280b0a08070e01050d050d0f170403050d0f02090d170d0c0906030609020307 69
    0xa400b0410241948a40380403850a003040c0000880c0d0301e40000300d42c6401900c2c156041d801c0680030ba62015418040c48000d1400c0040c00d071100840d004601c00403144d036040c16040c083c00820800c1c01c01032402e00d07460040c54002c02d20f0846501c0542c000042c0a81030324120302169140d4440f0301030303d014480350b08041109801030011a00c4074140c0d01d44802d0010400e604010b810000450b0341c0c1018040e58046d24000c0092058900e880002e047c00c4498072100d40061202c00d204000d50b415490900d1561950b44491645e1214140c0546401401c1500c140c0d0750300069812011400500c000f07005e808907820701c030a41600da42d8840a100b003401c0c407220040d015408c015a0000c01500601c07034010190403d00e8800b650803501c0c4c4d17025200117420b44003100085d000140d64603070720f1098014103040181808045192003c4a030004078801b9a01800400700c0e44044080641c0804280a41c1c40484104900384049244104010140600381c0549404203203013023404101c0d02198401c0e24400c459607 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 417514793 1250 417513543 417513571
    0xa11270a0806010b1c18050609010c0903020a0504090f020901080c0f09090309010c050c0607320303070f09090f02091002030301050f13021b280b04020d0c0306240e 72
    0x12003440a0498900c114540c8459259208040c0601d804040f030010399000c0da01030008c40c14850300142c255a000f41d410401c22807107a100740050390325000709a04440d01164002100150707450400c41d00c0c41c1402010b50f00011a6000040c0c206000c00e082ca003184080310300341d100010b14401c0041241c401c0d500030034250710500c12800103500a8070b403054040e010b82c089580c40b190040004186900c90b000444118410340d600d54a4004018040152450250500002c40240d40a1590340b400001d003078804216200e1104034581e40910002c03006031100c0760301031081e000303013841060180d1300000030503024111090b6001c0f009032000c03059034182e80c0010052541e803200d68007000602c0d10a9130003541d41c6542042003104141c0308103001c404440400001e4808414140c081ca40ba03c0c0c0d0202d00c00652089030201000003032842c1200c9503000d541254081180700c101d050400d00d00c41c003a003004003c0c610306030364020394072903610f0b0900021080ba000c26070542d49421000481c418140d84111021001e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 417516043 1250 417514793 417514807
    0xc04150312050c030c1e0d1416050712032c0103091104180b391c0222030803070309021914030d03060e0a11270a0806010b 54
    0x40c0035482007080035250250800001480031401d55000405a40c00c90b03021501c03d0600f50030b6034070000b140c4500c01c0041e160115000c13902030804010521495944000000c046a039070703410120310440240c10204441419442c1c80000707403026107001c0190f010030709020604000101a4000d2107005011080c40d0b8a0b801c0c14800541c05084488012202407000c4044038460f07884034030940c440c114210700070540d40e401c00c0c1018500b80b14003030070b4071188000c04ca0703103d5500c3ca072040c107610388590312070701d0025541c1d07547c402c84900d8041d21501801c2060700c90300f45505181d1607006410104902c090a0120091035001c2c89540f100c103110041002d02e045c0b002414642c065031115500b6800a0055000036040c110441012900d54101c2030040d0440e55214226080401c8282d0031000d076801d04024107410498002198903000300f0031400107031940c040a1003070703220310240c1e41e8005070960030360180d03c081c0da1a0f55180c21440390b514081c942c5d031840000c4a1000003080350484801440741464410 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 417517293 1250 417516043 417516053
    0x203040306090f0b0415061406160c0f031a060a05090f13050d030e0f060603120f0c06011403010b090601050412140a05031b0a0308131e030504080c041503 68
    0xa000031090f030b0820707801d400100120b00c1071002581711300d104500300703000b651030103c0c0d00c000c032074140d000214544410340b03540f001901d8000c101c03000c050f140746d102d83c01c00c103a0745040508174000383c01086070300034045400401c2000c0400d114a2501c8240390b03003506c07540c442080c1320301e0380b099226150b40041050007240810030842e841c20b4000301e1005640c1d24581315522464500946c4910480010b5a1446490721155061002c15440c0340082d01900c1c0c54209000000d41e14090a00810300040e00001d03404200903c9004580e0810001c50a9612039a0740b98104200200b81000e041d000e5420440c00803500c1c50240007003442504161540340c145400d241d481d5945214080045406000628001102000800c440b154103441751004559031149081c80320014035588840c0300007070f4004118940020b42104081d90f111180041441d180740c142d040c00031740521f401c043c92010740c0c81c0a90308000d0660000050061351040c1d0120f41404916005000c00c451010445800d0300074220313000d000041d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 417518543 1250 417517293 417517301
    0x90703060e03130605030603010606080c09010e01120e0d120903170703270218091c17040f021f0203031623130608060d14011b032a0203040306 63
    0xa10202d030300f8501070a00d94107100c22513401c0b48001c1070021040103414030b4240504400390171a03103014501360800000340307280d03400f4014099040c00b5040241409076489481c0c0c4e521b03c0002007006010310341080c2c4a130307911011401074010000e40390000030701c01d4183c113000e0820300543c16075507924000000c00b0007440c1034401030410300c02c2585a000001c02601500c100070311002c085500c00c0d505201a10401c00c00508021a40000209410400c2044807000c64071812084040c904132101152140d006c4400818844000d403104045034140828051034500140c03c071707403003035406c03c280410160030f0310320b004404010741005a104000060b13003074034a00710412802090307080070405400030041c4c02d1590140038216409401c0701042105034804c14844846c010800c0782080011360503d0130100d940804114005003110a41844aa01030007095118141100241c0c0030121306403401c0000801034800a60210805020a111500134080510404840c03102c66002180744c03500d143c0c0c8920141c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 417519793 1250 417518543 417518561
    0x10e040b21010b03012406030c0918020a11061317070c060f1704020105091918290105120c0c01020301060314150120120f090a06050309070306 63
    0x42515058030440d03515040c0010720a8800c1c100010030711051610616007119031000030604481049400f50203041110b41c211b0b0203130341980c9000704181618907030603144a14113501c0101150801020705a088502c0da000d041c0c54215035940480d5038035903446a81c3d171028240c0307031101c08015490f46070000800f04804c100c4014004004c2d603040448c1600c03001c400911075803020303010403110450b100140e940a10600a800c00d2042c1880c03141c105a00024154060040d110f40924101c18030314048081e407101c4000188003640d80601c03c07003103221200d40030b000d1088038820454605045440c1284814030680314894040e92034505201c107440041c120220054a01c00503038078200040f00741d4010a000460217811242c80204080c5030382a140f20b041d1a00900141102c00010098505030782d2000d10b5080c0303080c184620496840b402e2008500308055a6115035420b41c0000741d0480708010000a80044c003003c0302e203510728a584123029a9140b0080740c0c0d4441d05c4d0010300003800003032803952295001c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 417521043 1250 417519793 417519799
    0x9030809101101140108061e0a05070e032d010204050d0b070c060c0f0801060215270307150b0306042a051801030512071a06010e0d0809011d010e040b 66
    0xe01040315a1036400c460007114075034984c41c40d030401400041410001603810911610072056071082c400b44911020b07501610308080b90341c840b00071403240d07882400d60982102005003034a060724411700c410001c040300c00c11007006803030ba41c61442d00c40d040c044c400d490449802070300c00c014036095940c880e000488010404418400400c20150208403540700d11294620180c40e8202080c214007000307004e80d14140d11104c215803100c091a42146c8440d81680c0e04148070b820505144450001900b403028158400410a444082030180c24010503441c0801d208100320401c104080c40c1c5010f1640b01c40301111b02a010300c1400722000100d901c60505882e035200c06c0f8824450035a15000044c2c005842c00c1442c15054044c017005000b808014400f034200c010020400e285400580c2d60340c07902120700c1d903012040300e4000c4400140342da40900140495136100070140000803000d450980400e030000d690790303400034a0034070b00c480004160002c0c411140300140c40e842d00049195081001030f1400e0034940360 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 417522293 1250 417521043 417521057
    0x6061e03150705040e0403120f29040609020f0415050c3a0c030206090d020c040f140106120c080c0415020c150a17061f0908100c0f0903080910 63
    0x170301c0402510154040c1e03103c2d540c1d980842c03203403030100c02c1614003113205140c8841c64590780b081c800710078000401c0385218031400b07101c0c10224000000c2c01040c4a512000200d400020301e002c80751820b400401c19921142d03482e10060600d50300850701400340440403201907001d2621404040400c4011000000c4080d01c03c00c0e00c550800703154003000004034101d03c00f00e82c686140703030205501401f10642c0200b940e0010400c662951030029990860810300074012583d0f21103030000d540d05174000c003103c0c1d030542855070080d5a480d00000e1400d182c09401481c3c1c14501180c15a0b07840c030588041303002d04201c007c1181810709003180b03204558000c00b034140c19440340740700d90b500e107807140c40c0c0408005c01103240640d201c0400b250050b044a80c081001c01c030400e000000c0007046d507940a07416040e0098a82c04c1c0102c0c0307940c01030982c0d41e419150003001d0310b4401c042e440c00c1c607059540c2010101c004542e03a40960b04a0100041d5100103860000419102050154003a50b040542c0900348000b1715141081c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 417523543 1250 417522293 417522299
    0x4051302210a1404111507020307030308060102060907050a06050f1e1c0204030f0f1a0103080414010e01021f0914070510110303010515040b0c06061e0315070504 71
    0x80419446000d544090701c05001c020b0389074140c2c481c1030803440c107400d8200c44914081e6a0a02040307510300e41c181c40344031926582ea400c00498000d98000e16806000c5902098a9080281c200300017281c40e140144070f1207000a002040214a210858030050f0240c0b00b0507041000c00d84060f0001a05180604424402c2c400190311000c0c0100c106884900f41c00e994002c820706d40b40d400c0c100c5030b00c0e8214180c0100010400140c2d032080501c44140c0041036421110302505c2c02c10380d006440038040004e40d800d000084103005070711000700210380405071601040ca80400064074041072660312540960802e1000c0011071100c0368000328985201c10b00000d05120540c0d80000900c004691641c80c0d43c8800024046810415164070f020b01c103e041900000801c1c9600a5a0380700c14010b090040108401d50b8400381e10721000c1d9805051141103041e180d150340d101c0c3e181d84084c1251860320907641808030444180c402195001d28050103000b40c28818132249d0b04889041000d401d040400000300400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 417524793 1250 417523543 417523567
    0x5010b18132a06090519120501020906030109020a03050105040c0512041707031d030109080301090b0103060b030a0b10080615310303140310030b130c090c020f0f0304051302 76
    0x24550310388002015402d20b802c1680050081101d9000395009060890303481c4018100201800202d0302c22021040b0881901e05c4d145029006e444d44440e00000080008294452690068686410140e404000036a62003003040300b580e0311210402c002c40c0081145018950360400250340c050b0080301d943c0c4071401501441072840c2d200200a0b00002d5054034042080c5407080d4081d080140110000d00c4101c034580c40d0303000c07944818421400700302e55552010805034000e411880017080e00524980d00e03881c00c1d50b4040007900c1c0d841c80052044001003e1010218005c1d1400ca0060300017800500720340a10040d032020035031000d4041b2f907031f6444814a0030340d081102b181030032400d00c40c050326904280c0341d0300c1c01070000c4450a84d001c411081c24130400c075400540b00c2801c0101d9800402d0000140c60f0300074268800846c076100a002d2040e4004040707244100c5800210600200b0744c00c54070000f200c07421807525803180c02010a52034008000400c01440c0c40401c40103161a0000b0040c074000c0232980d2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 417526043 1250 417524793 417524843
    0x40c05030408360307172a04050703050a15061e1403010f0f0b0a020a0f060b090901020a020d03020306090f060a0909050d031b0e13020f070f05010b1813 67
    0x20f040b1051140260200c2e503810244008802007460303080c50090704950300031650702da01c141c0e116401c0041424009010703000c034801c00341c0b50f02e880242c0208941d0a1014000b4040d15007111215901c41c10454144025190820135004071107840d5200004107007080510010740c140d10425500f049003556030303400e0f60488140214000c200b0011405901441d201a40e01c01e8a582c1e448490000c50521803082419008240b15101c20b0340800c80303809118545c40c205006005003164a031b0404d007404100248010b0550040c0a001402d4080340c15480718223004a050740310072920507400178641c45c00f0440040c5c19083c0309402c40c0b001050410120744540e03494048400214007550b003a4000190300c4074082d018804e0100725106042c0d0882002068a4050081c1a07040232950207142c0614100c2c021001e141c0c140e0328040944d9007165904c64150074401d85c0c0c1c00441800b581c5a500e0301549051f40e1908050080072500e810b070800d5001d80e280c86080c13a400303811010a0f610414082c0c85540e0100021391 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 417527293 1250 417526043 417526117
    0x4050306010e0916060f0c150f0603051c090510020c190501030506060301032418031d0108040b010905151002060412081b07020f06030c030106030b040c05030408 71
    0x40701c018038203c0c01c03042c41c0030540228900f08500c1c0d800140003a070b6110a50806d41280d5080c685400f840525100c450002e5460111405501d0003030b5103850a1225044a4200e038050b2003140d009080141c0c80c03200e1117020f1200c02022403000842000340b4281110b490001450a0056409141040b400315003941e4080480100032a202da10501c00d0350b80510505802c090140c405501b903605560703e40d0815030180e48100306880d0126204408891290068402d00400815102102907146805130441d0b0094001000c04074010100040c5548185c0c9c1c0544100d40108223172180e039182c03042181c02024042e001158040e0004d00d4482552255103d0341030700b21280c1d00400b800e01c0c03d0304202c2501c40100e50220100304403041405210b00041203a10a00c126420aa0303942e50884d100007029003101d1b90701c6540208001c420005285407020146040f24511746090294210940c1044115031b00340b41c1c0e00000c00c1342400070602045191029000c420380b2000c481c5415182e8000c0f20300300e40c01ca10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 417528543 1250 417527293 417527309
    0x10e070b040905070503010e0a0513050f2a01020c010c03090506042312032b1a15040b0d020307200106060e190e0c3609040308010501140405030601 65
    0x14003000b00c45124415598406000d01d0700380e0441d4140302c0003200c5544060900c81105844801003400521000c1e458103080c0e0b4070504852060300700110441d01d4100c038003200c0d0101e405040349160320f84124030100e40d5101050780944100060640155140c440d0254141c04002c4c1c62a00414144c50b041e00800c09070256107450324a00756000c40c550304580c948084a4024110350220884c1181c000049d1788112152400d2501120b00b000361005007030102c0c1ca030340304501d0700b4801a50b441c08050015568400802d039440d40401101d864080390901c180d2095070000c40c0c0401010b80c40001d1070380610b80020192800310803240c9180400000800380f8610f00c00d00780d6590000b084443d40100301c0f491102c8058030001500b5201c0341d810432586040340f00703004080c136044002880d60507100084401011804d40300c0c131603e440c42012150404849820446100e00000c5203c00626020302424440c3e44d0560f02c50401d603003001c00444000c0c030401c003004201d800600c00401c10f942d0031712445010f00300e11 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 417529793 1250 417528543 417528547
    0xd200406090512150f1801020f040806060108190216080703020601090c030b1e040b190519030b0718080304060512150a1505070c080d0210020306130905010e070b 71
    0x401040f2070205a94500003030b07a4405a40c1840000500c2c180541c4412003010001c0240e0310700601d24504007400d00d4100b482d510005400711494003000c00b600a4032040e400b11080380c2d40f0603005440031402552004640201c06140c400304080c590001d080306103495821180100550707580700040e0300b201c00110f0160f085000148080426807141052400552034203000703050303c4c8000701d00030b907100070751843d01c04585a5903003409403103941012a03042d40c082c2a0107554640480c090481424501460f4424100c040d000b001280c000b1a01d902038907000506010291910340c02640c9400340c036580b024007012040400150000140082c1000300120f403035441d40e40010240844030217800601e10b103a810006003c175080d1780c07110409a001e841b2035104d240344030081c0c0c200a0b1078600502c000100500541c0c1c4000c0f0f00c1072004100004409000d800322601c10743c016092a05034001150010b4201d240c0c5680244095555004070034150301440c000030305403070502080303402d0080c9a01728800d06240 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 417531043 1250 417529793 417529799
    0x60712020d0302191d0913030813020a06031508030d0c03151d1506030a020d0509010b010e0d060207150501081c0c0201050c100903120e060c0d20040609 67
    0x40c014649051182d1034114a03004203181c1d10440900300d21024420444c10080c09a4110a8001101d1111000528105a6140c0450003035030032014044105c00190aa10114102d0500300701a801c3e8980d00030044598582420310880c01040c981260810101c0c002e00e00042180c014001000d00000c602c1000c0750400909038007605441d00880d0180c96007004040403c01c801003da41903015440e5500caa000304d40f504000d20707060b4610300701000c0e402400003050107642242a80200f0203441c00d41c3d4180181e80d51030101a00325900300703820501040ca00503c0403014545a096240380b1441142c0050800416481c0ca801c0e149089140c0001e42e641d440040c003e059081250359020710120103203050884020300300800e1403051581c000d0501c500032624100d80c03101403081600c0081040c608002412842c00d00510200e0003280c982c2c03002e4903041c000740002e00c011030031501c115078481c49989800e881f500c000005002c002580b00c0c403a5001c841d40ba2092001d040244014206955000f040d641 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 417532293 1250 417531043 417531047
    0x20f040f0606090b090a0611282f0402030a0e101409120405060f07051006030b0c0403020603010e070507050f0c04050a140402040f06050312040f0e09031803010902060712 75
    0x100310f41015505200904c171416840c0d0354121000b00392446444c0444c40c003640c200420b860a034030b5049440303203141a030703030000000c880014043e94864040c0d030408880c0b81240e60005245034580000b002015080c2030070841c0c906181e001985c0240c00e08600150100442007094248007e00182c2e5040ca503c800302190300070141042a40c0001d8200080c1c01d41c400751320b800201c18491486524010040442c0c200480001003040c0c5031010740100c1942c81c80c920011490004004c00d020480f06000310384049040f101da5541901c096a6001d81607501d140d081528501204100400c07450070011f0401c0319400007001809108014190310000385150b0104030104030660b4002064070007510314184040004050400300d064000350150b138002444a0f00560030740107040c1b9078100a0b00b600c104070b0700503181c80e0444028412a5607020644100c5502c80758086125a0f0641f1070f8071540d84107200c050040300700b00340d0a07a0a81c0d4014000902c5078440c1d0b0204005800c801e90607180341c00c0540304460015 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 417533543 1250 417532293 417532307
    0x4050919060e0d0e09131a0f09010e031603030f0612030801150e09011503060f0803071a0403020c0613150e09130b070c03020708030d150801051b07020f040f0606 71
    0x4000d82410140e481c4c110000c01e002c0349004026142d0741e02400b204600f402843c240c0380301c40f40c42c84001001a864800c40c0600480010b8944c0c2609620344801005001c8000c07040d6000e108416403504500c85c001d4500328041c1190f03142091880d44e6503407001031052550800c200110348291900c0101790300d05482110707041c0358909404188071070100301144582e11051618190742c483d036203200d100800080210000e00643d04455144602d007280400c268000001415150303115030035200c032020000941c415240c2c02500c005001d80d004201e502c46524110004d410b0340c800320301c4c1d082030007903644400382015485055800c000c03400042c600100c83c20640d9020781d010111101300100904079030f40301c045425000f01044108402444480c040604c02c1c0300c1c4a00400091040b17030384807525880d644000384800f0b84940c3c11134014000000d0304e6030040c010f040c818141003105025805032000b0503240d0b07901507801264843c00300c00070041d0315640c5126503550014141c600040483c20941d0150000c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 417534793 1250 417533543 417533563
    0x703030f0302160f05010b0a0303030506030c010320070f1a040201080f0402130507030b041e05070207150e0f18040204061a1801030603020a090f15080c04050919060e 73
    0x5401040110708030f621240000742c0b11a0302100d4040074030071505215004005100707205602c1101d000e40082890b5154016900802c000c80c259158041c1c00001901280d505589200410032000710616011000b2400307002c800b40984c0d40704a40c481941d65910030302920040800c10800c0b1403081c403003176503802001745074499800c1da13815216041540004035100c500105038100d20751100005000d00344203810000c0c27030200103001402142b011654680c1884420341c103141c1610f160000240584e4030001d61101150500680e0b04004904200d00303c440240040d5010b070807000e14000e0f104142c8502070b40100d480104511420315080a2040005407a410b600107124210001c080e600c40340c074814119004c0c0048182d80f081c0c0603800d100140e01410b0380d680042d5000400d902c00042d0303031030290421500c1c00b8946004020020f51003581002812081c052012503911070705074001c490034a030344450340010144c4200e0b00821075400001c031030705a0200781203c0950311a121114528030400928503c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 417536043 1250 417534793 417534797
    0xd14010b0c0a0b220507030212070501170406141503010c11030a0c0203101107030801050d0305040501030c0201060b0a090608010902030609041b090f060815040c140f0406080703030f 80
    0x40c08120003415a0768a0441c070b00541012801c90200b081100d4a46100c00015501044650f8440142c10241d84070050791200386c3c060400200000c1903040301217084c005881c0140c44100d6210400e0046048415000b00200e545a1340d4071124030b480c2d00018600342c0728207249250742d40815000c5c8141829110100f10302030504c040e9081320054881d0102c01d885842030180380009007058940001781c0f90400c03c14083d000321b883c0c5510b01280401203001011014000d444107000d0b41da036001440001d40d000800500055814482803281e0362007900400c0d441c1c011031001240403500c41081c2c803559480109c07100042280b0050401000d0741000b01117004002c0050110300794540741c000300f41380e0311004100415151105a1b44100d2100ca0005040688100342d820891010903400310b01c001e22103800781156900c50040341007800c4482e039a816100700d5014024090603882c2224036002c0900081d2825031051104844d0b15441d06c562013208003c4c298100104407440c510700300500b13030365406910582 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 417537293 1250 417536043 417536047
    0x1b030a02070204020d05071206060e010318060e01061e030302030f09280609080c030a080a0c15050609090604110928091101050a020a03140d1406090a020a08041211030d14010b 77
    0x401ca4100780464903401d420308010840c590310403140354463b101264020724203490300392005061101544084203032014501c0c03030000d40c00800c0010107680300c10311009005900030058010b0000c44c88010380404000078141000d482c0480c03030340f810b907050700641c10713682c40c0c205610070002c0586c031910500041000c440900703201d0121001181d02c40300c200344007815203c00041d10b10a180d05c40c6004c1150b20340c10004924282c1c1070505010b0150005440641c480d8484070041a0a031a000c80c2c41e0b805250301440340000c45942c281405500c010007031000030030100d01d078002c1400c4010040c68106541a5407000162a0300d5454000c05e0401005030701410800e09109911045400090300f03c1519094200380802445400c051443d52041205030300115050002e02d4854001103038004c0d000c0c00c0702320f8100b0705a66071030b0360460490003060f0340d81c400a031420010401142c0207000c0035405603001e2604885022504c8a294955444440900c0c461951400340c5895090340084560151020070f400078 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 417538543 1250 417537293 417537299
    0x50a020412020f01050c1006261902220902030d111e010609091104050702010b180a06051206071706090f060d1205130b031b030a02070204020d05071206 67
    0x155074242454000380203001000700000982e00400644009106810489202c003414402402c00f800c01071182c102c0c4107031310076160007044001c03908040816003c00020110154004260183c82c019400b09982152070142101084a403246860800040c564000309810b101e070b2050520306407900c1e401d441044240c2c50300234964003021840c440291f0343e8400d449201407280c0b094a0040030f580e809540039918048040e010020032000110005504980810060b66002402e0b421798900360b85c00c0343c0c880c900e05c00c24008420401485900008443d90000c0d40a8690f80031480c0204003890003240c550000d01000000e60b44502403a0720680912418040d504119011a00b802c10150100c5003007600360001807000e88030803620386a0789420559140c026409410081c00607480000a4403400842c2403000c00c07240d50100c100da011b0807d0315550342c20509445045012600040c0680000326020001c00c80540e07600c0c00580f86016115000103100c0c01d0905003d0510302c40074100008080c2006810 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 417539793 1250 417538543 417538559
    0x13090c020601170c0a12050d0201410406270312020d14071128020603091023060301050403020a110d02060f041a0721030209060c0a020301050a0204 65
    0x79038111009030344600d00c0c0640d04400141030103414690700d43c22048803600004c0810001907100b981500420684400c240c17013241c205d0907158501044000c01c03140e00d105100004e0500c40954143c2110199122000072540c03240c00140e40035241500c14a464800e6103500d010b110110354242c0100300c0d00e240d00340e8500e070b5000d010b06031040b580b136000035404283e10120b80078681103941c0d43e1200c0107070002145400c0d40080e05034009002c1d06506d91180e150010307104107100746c012011074021812800010034560030490f5552004081d078845000c0c00300030315140d01d01d0b40211041b0b0b0061042103203241014014125034140000d2049200303a0404046c000440e401091401040341c012100c40301c408100705c0802c803007a9503036000079004400081c504c200c0300b8280e000b40c4140c074803901c1070040c605401c02c00f4240c6801814000b512800030344120390080e0035030008035005410103080142c103040e296400901103422800c406000c603005408a6011482c1c00c1c410b43e680140d50307440440c1880d00b00103517 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 417541043 1250 417539793 417539803
    0x1801031101030203062704060608010e060115091205030405040c05070b060d1e0b0a0605010f090b0a0c08071218080c010e030c0604030321110a1d090108010213090c02 73
    0x281410305a00001195280d1500c464409403030700d21240e00d025208114000b0101d1b00811101944c005290003c04180d5030018056241c1442c5010024041a402c00c01801c00c3c400540c1914414040c04040c00980350034031050b08039825000d80003854845103000d06000546d2980e500b075500300801003100d40005503191001e00d400250584480481013081e00d004da03400c03501231282d804007551010240d82001008480184581d16403901032100660f10070055416002404c0b40402092740003c1c184105c03c0f0f1240a04610780075441c2003000510b07180c81d0b0280300d901001d001e5400344c14802101101c140c200701e801c20340407180702451080d10b01d407035459511100b4840c2c09a040144240c40d0306c0700e5643c104000c6250040c000c00155030f65030707689030250032400d01190040750401c21907006600c8070b0440c410a0721070030140116514140d1030200442e021900c42030322905140d58100168100d0b202c0d901494042d20004000507035440090364504955617030303940314030409400c0c1461701040d9503002c42c3e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 417542293 1250 417541043 417541073
    0x30c060207050d0f0c0306020315120703050303061201093819020a09050603091e01050411041d070618080c0604030f022403011d07090608190e010b180103 68
    0x14500d40c0c6550b0524040961117130310390000e4042400030080c480c0200c05003a105842c14021101502d2010320030000989600051201820035081413001a00c00c0c10000c1c00c06410244003800003560003d1652500051310807220034540101217620610040e0004410603401c60401d15041d410720701d8405100c98050380c440c88000c10b007076000f251000003540200b0580c0003500c0014002d0b030f22031514928559854130711011400204115580c030008000c410b2050a02940d0072644185001d00c05606000281403042000c158168882542c5068440240160741c084c0003280c0d241041c8280842c00007481c0522031300010882d4211007007404071541d5003011982201ea0003000d80711004201c2c00012245601c0341c1c001182480c15600f0030030080489e0000794103951201c03106644046980410b000c0c54181102e220380130600c455400d1284038000c40c4e0290740183c0782ca0f0010084145d10038080159140b81503900b4650b91a03004c0f8040c00c0c03628400c500402130105c01883d101c5e41c9035072240d601c40701e1103c0d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 417543543 1250 417542293 417542303
    0xa0f0e070b0a0e030105040602090109060c08120402010c200a150504030b1003150b031b031911100207050901060c150c020c0916030f02040b0901050904020903070f030c060207050d 79
    0x5508050314001e0100f0350301e00d0302c014002c01070781c0342c141404406076006042050000f20811004074405000381c02860120750010b540701c2c108804000e0440c1d84880140091303042c0040000d0080004602001c400d9000c8600c201141048031060f0500401c01c1943c2c03c07080754044448540e03200b0031380c0b1000b5102101d400580e1180141c4030980c0710022942c0f6030f000a8126059000d00c24600c3c5800c1d004010703054002c0c5e0031100d11901e0310310b190340415070029681d989500000f18150f085140c0382a06c0907002d00441e807150081d00302c000041c082004942144025030000c0b0000c100078039001c00c0300c900400d62820003e0301d0008540d245003140d03051030500307a045582d0340c034225a024401c000104042002600c41c03009070401203507030908070359103080520000c0d0030710080d03e60048450003546e0441d0f280500050400340101c0040d2555040164420303080b0b40e007444044a01c1e40d040114070018010700c90b1406d269811070510034001406a08507805541c8544010441c3e41c441040d1451300725048 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 417544793 1250 417543543 417543547
    0xf021005060409170c15010f03020d02043206120601150c050d09051e0f011d0a030602090907030c140a050c0d08100e010e0a0e0f03030901050a0f0e070b 67
    0x210300003002441c00b510b000d021511349418842480c250140109002c84050b0100d0344400b44400f250f22034a02c090140203c0305d91414001c00040c2018400c800c0110b2008001041c05c0401c1040380480c07805e4070320301a0303d800c0664000008400201d40181c1c002030180c2d81e40c24100c0390740081030354421061003401ca0402484000c25001131180c1c03144041c166102007919100e50b0f44107030050082c40c00c0d0050314030402c0c641034500500e1036002405044c0c441c0107844507100c44102c900540c1d082c0400c0320080321048004d034020403540ea500c0f0703030b20010314400d400040c1c44040d510244408500c00a01a10505150820040e121034011601a044090300414070365030701d000400480d5240511100d0201503c10410351904164120544c24440d14840480050995590b025121152401e100d58881c00034458003080c01c00c042a00600c1201080000b1501c0d80150039966a103154411109070348141d541d801400341055140c0a1051158460300302840038540703203000e041d25a022445030622950300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 417546043 1250 417544793 417544801
    0xc0c2d03060112081308030d02181002100c05071a0103030e0108010b04050d0303020c100914030f040915080604030e0a0e07020c0d140132011206020903100c110d0f021005 75
    0x1d4014803000e002100d0647c5c5d213a080c0150804042e410020704030041c85204003039032041342041d800f000c101071203940c001d100c54210050800010001c00444604004040240d180800d4064242c0030080c00c01085031041585036080c010035141440c5182410002408010440303180f00300143d80641e2401c440c1c0030310114041c91301b50020310030342c1e500407180d0091104004141d03030390340d0214445502039205122850322113203a21361644106001e034400d1840c14003003840030751116400040c0d05d039102d03040c888000d6122000c0b03078030300b4000722030440024007411010700c068104610904001c000035003000c9060b0a01c0d0a002c0e449212a841450141220000b844140003d90340344c0071410500f600208850200c82d1040030144214001043d1725610b01c02c6800750304000034072f005048407416070000b015840386544000c0a94004084268503100d030301c4088980349114032502c030301c0c045176440e000700c010000000142058075145a6506000901c024810326079004180501e40c03c2c0310000002d4507a907 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 417547293 1250 417546043 417546067
    0x40303120204050d1113020f0d0902060d02030108070807060f050301030f0f060f09170406080408030a061a0a120501050f0105071511031008010603050309060c0c2d0306011208 77
    0x1d5038040d660141c40020300700c1c1805045419080c600c0c0c42a200d6645046d0303040d0701c107401e0740305404024082c01410880502e5484e8150b000c42104c1e8401000a4175190300a5070f01300590700280c01141c980d4000540804c9024410050280141100c0c107144071030540c10711307018049020520000d0101c040080b03510040298040d0064811640314400300070107244014014010000604101c56141ca14507c44c00c1030035507038095404590840d96551042c0e40d03196240756458001908143c2c03003540318030010940c22546a503c401404250880d2171b100c0c0718483d0300510800c0404e01d0030400a18080051129031121350302165070175000c1c20140da80300c0300f41c41d101c2041c03e420700080829030329008050201c00c1e0500000d5006200c06509141056140c0c02c40d0390880b903051200511070f0b8000c0210310014103240001d4440c52640900342c4201c0c052501c04036120000d840111641c03240d856a04034007143d0802c5002c0c8031128194010b11140d8184054800394100c1d01c04060503001e404280c2c0d41981d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 417548543 1250 417547293 417547297
    0x10c08030916030b0a11040503121e0301030b070905180604020903120d09060b030f06010e15030105070c03020105151c0501110f03060406090e0d11011d06150f060403031202 76
    0x2c00c6101078500321540d20b003010a03803a00c003a00c5a04440f400c01c00a03101014030a42540c1c2030300d0000300503100d5261105001d545942c088140c80400b840020320650011002c40003941c02140119191a0b44d454032040042c02da400d21f4011a101c0c035890325140c0d183c050740000e880e9100b00c044d1001070b81c4107003000001c0c0c64198152600f0011180001d034080980480e90041c040f1548070b01818000140c050041586500100d1106c17419940700c0700042107482081ca10550b0804d100c0f02c0b0318000d01c801c10022a095032011120310022995414010b8101682442181d5100b03e820348203415502c400400201c640c2011801e0161940101e8401c6d41441000e6028450300c5004a086507070310402800c074600a6002100c00601c0781c3d24009000428045a0080907201d1001001408950964110a43d5185105901035000c0c2d940c40d000141070048003280c10004542c2e0000030300492411f4000d44200c0100070f4401030042072190a42012521000250f400f52a4142007000c00403420071aa54028 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 417549793 1250 417548543 417548563
    0x60f06061c0c0504181a0406080a0f02061b0d0e0603060a140a0e0910060608060a0302060d0906050c0913060b040e042a0e07030b01120b01020f010f0209030f0c010c080309 75
    0x116140840350340190341c0035484080c9506d11344159a80704801c4508110031582244107a04580e0003094150380052482080c2d40d04051008000604041d0405a41c0f0302502140c0c0b4035a01c0e80c1c0c07100c1202d41c50070b03800c9458035042010031240c0d1480c4ac46c01c0b0006c24084c03401071050b03a04411008502107110b981d0442d40c0b40140800d00385096892503c2c5001075510503100701e074038503c2da00e0b003034000c030b01d6511030f140e0144154005080c0e00b4115242d0750070311601350322440307038040d0455803080301400080f11400342c2030041c058080740303540350302c440020020213030300c0e010f000c042d001d1030300c0010170050152806030b074200c03442c5410031740c2703641d440b42889612810809090088103204500034849042d102030044160396544212412075944c0c140190100ca51041a00340400d003040c514207540085074201036503140041c81560f041980c12440142500c00c52243d08214070340211301e1248609080003801450141c160007811122000c0340064010907107d580900302010010002d0030f0140b08200040741 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 417551043 1250 417549793 417549809
    0x6081810180b090721030801051c0c0311041d06040b09150108060a0501060201021e090d050106120b071b120306031a0103031202070c0b130e09060f06061c0c0504 71
    0xe4a0010011038582c50f040c0100081618400c05d2080120550100080403c1e03140c0c4074003856034241400c0007090a21440c0c03c02040701204c0c42540090325864035a0011807046112030102c1c404001048191410040310201c4103039262013840300d04000043c1b0a422982000c006d0401c2e4603040c0c411400c040004081d21046004040000750030070002a001380301c1d038022142001240d0300c0d080100d080c0d10032071010181e80302d10080818000c0140748024404060b0080c8a041810503d0350380c0d60070b5403425403000e080e05200041c2c4406208041e24110f6010300c0d240f410714000154842c100044125428000d04542450b404403204207000b94440805550803c24000d03880d01c104000c0e08000d2001d0008034000380750040c03940d000001500075145010b500c44c0030001510f050141003610b6030441d071410102c124042c000010150003080310a4050f24104c00509058640340050300310700707032001e06a60300a1f0340405c0b61b40c0c498404822154a141d00c612400700d4105520181181c0c1401550401e0503 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 417552293 1250 417551043 417551063
    0x23090603070f020c0418110a0815061219031d04060e2e060503310c0b1c091104050a0c030e0a030c08030c04030c09060608181018 57
    0x581c1c1c03908140c04228424440e0708a03110201c01105100a4030140c82c01c03200341c400b040000c07500003209660404c01c803207070160549000960304c2d0101031800032065011051594441c2c14031400741480c4c1c100c4152444070200030040700c205a07203441c40007170045201908203e1681d43d0721540358500c00030100b0380c2d0b50040040c4000380c1c60700142c0392914810341e00b20015030f01d626110303d03054489450190f504000700216031304480c078200044c2d440d50300c001c0514000c10110503c051421041c8400a4843e003580c01060702202d00c1440e2000c60901c041d0050030701c41d2024014054640d602110a944aa010040202c0c80c81c501d4688202a00075146410707901c035007008101b1031114680da204140c01681603074180091085041110385807070030100080c0000380507003501070218401c0802950480c00d60010070780f80555984900c6001c0f606074110758a83c507102c5400704450750b072011180c0d412013242d080e0150707183e4512034040da0f40e409070713116240754a80b10301040318040e0711484082e18140d0840308404d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 417553543 1250 417552293 417552301
    0xb060d1b0b03150a080606130906111c0e0c10030e01290111100c09080f031c0e0705040506150403110114030f0a1503081306020606030c0123090603 65
    0x15100d5001242d0801c3c200c04001d102c0c5000c0d14101e00144121000200030f88540d45074403091050000c03070040205002600d55103040c002621900c18142541d1100a1aa0310381e400a8040d03080e0b14125a00001603a0600038058008400441c10701000c0c0c0b400c1b5400810481030700d5080c0c01404d52440001c07041d518008400301c04103490a50451035112101e07000c5045c502880040d03640999542603210300d98420004a0b0107004151720281c40c40d01241801000b10f551846103518040c01030701c08030b01e00e41021070030308000d01d00d86001c5a60a40255401d000500308400c0c1d59030740f0b030000d100d503d02c2944c841c03011400d41d48a10302031720036100c00d20b8007041e80c4a85034201040a0440140c9086c00248100c407001c00c8184a40c0540b4040c8004038031480b0340b5280c030780329203000e405180c41e00280c03030031844030010005036400000c00c0380c0318811000c0440245401c501901346240200041d009400445200c041c5a03400303001c00e00040700030701d5504502d03440c0300ba0310315140c0100020a42c000c04000148 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 417554793 1250 417553543 417553559
    0x170a0f020a030c1107180216120c1109041a040c080717060703050403081303030f020307080702300c0120120601090b04030b180d09030312090b060d1b 66
    0x405509810b44914180b940b8a20041d43d54080c175128461150071181d94030802422941c006200d4a8012840e0051140b01130300c07814040ea90442307841c008680143c12113000c00c2100f601000300340c0e10481c0d03421581e24042e11480c03154684d030b0300083c4c84207203e00005410051181000030140000600702c07440c150700c8010b507525904030050761340018890080040c89451003405650303c50303581030751040460b484e142d820703d104c2e8406544c210f060644894001850101c2c0f4400755114403250381c0e500641c0d080402029080174001c258900c902d1014148a0031155940c424580f099011013610a950310b6034014600c0c010003000e90440a555090058074544690340c501510250384440d0003a81d03035444000042d00c623441c0d2480f890080d0301d01404100046600c9140903540203401645d48040402027200c2c00c0d04029030304070140042420710360107005156010014a0701884820010812040d4540701c0b400c21480060039248a000801194070030401a08844c40b00030703880d00e481e0040c1c651140c00d6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 417556043 1250 417554793 417554801
    0x70c080d0c050609060601020a03050d0e0a060b0910031e05010e030c010203010f14150705150414070e10050d050a0602040b0a0e18010608180604082206170a0f020a03 73
    0x50320544181000718121302d40c045802401100305800501414001d80d400781c8098100c446030b107000c0c903503c0c4120f01680b1000e020900c00c49124407800101c60b99039204203d001000a08080c1c142625000d003400010000079402590703004003011005440d0b60b0f46040d41c09001e43c1c0056040c03500000c0350390b00607400c054000e541030302c0205d511080c40585502c0513910107011035540700d80c800d600303002e81c02c1100e803940c008203d40c80c090015076070b44c17001030002807945500984080341c15480455049001da5014050315001d4208042c4182c181e0400245085003e03009008252140c903154043c1000c11004010f0f6090040d400382c0c0039501c2d81e61364901d0f110340f90085102440810000e44001441c1c3c0741400000408211500060020ba42044422104100000c1140182038100401c0415054007040181e110380c2c4601a119601d61000c1d0400c01c3c05861059481803032140c800c0d0502116030004151540a4211610110183d9640f08818003030802c80712004036131403002400009803030340750300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 417557293 1250 417556043 417556067
    0x11030403020c18070c1a18011802010e0423040803160908060a0e0f030d020316050309060a0b0105090904060b0f01181412060112060e061b070c080d 65
    0x98a0819882d181800010b042900601003c03204040003d40329500030b500203440075021b0300c1141054a54121903100c00e040664000701003042c40d201014807144240140007808044000c00001403006034006800723419100c1c09107100f0350712002000400483c000001005651b2894414040d090a00b41222640e10544120000900104403c0d48583c0603a40706000c5400c071200a024650f41c2e170780010020500500040814000c0103020100c29070100003401050030a000300503524200b0200c1040d8121030b552130708041c01303c1803040028402010402e02d600040c0414086003140d0f260f00100c50b00c1c0300b06184a03a01000d07403010302092000700d030311200070304500341d520342c0c1c200781c4010054815641c45011440e1160460b1028000303102084042c0254200141c2620050904110b126081ca0b00c06d800c802241c4113101d001500707101c024090a4000528840030f0511410300d01418950110f41981c1c0000d01e0f003000400c1810421449445001804540c059499800102d04002d12050140b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 417558543 1250 417557293 417557297
    0x3030327080705010e061506031506040602150615070201050c0a080f041d04200f0907020102280504091d01090605070f18050f1305070327050705040f0207020411030403 74
    0xa0307030b21661790300021034902420f140851444100148000c0158030341c40141010358500c0d04184000a684034400a003000e400d29401070100c1414400c1c0007844018003e100794820b5001d261a40003103002841103d4000f034080c64120303942e0b0400c0c1c03282890314003500c0005004480000d842e0581d00b840602620603105140c0c01c0010b080441044094a07a0080e100600745022162032050b041907901c9480700c800b10040d102110f80e43c108000138543c203404507020340c0544d40010745d06000100d0040d10280c0030000305010380310f4600080008015000380d0269101d100d43d0b680e0f0b0080224800c0440c2842e05040c44020f0040754110702d0304401501c41650702002090501c010300c19064010286201d40402100221600d41d24060070082d07026081401e1f1070b00240b0404d00c40b580c0003518080d07144951056200072550021040c3c0d0b175248500c20320822800c20001030720031400220046466021030341e08480c0843c5003065076032040020b2146c2d080082d031091501d419418402c98071405103110301e0103a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 417559793 1250 417558543 417558551
    0x50709080609071706061503180604150608031e03100801090f020108010906050f090717010f0501020c09070e0d05010b0402040603090605010b030f0106120f0c021609150303032708070501 82
    0x1c0f0540d42d038940c0305031040f503031200080000000c100d6807900030f56030186085d2211271050100c10b40850900344241c40607100e088144611811526490107440002d1800c500210310b42883d403041c200c0c1a590305a104060444004081142d01041c2d140341c00142030030300020400c1c025a0314080043e12040c1804901095201d0000078040030503110340000c17154040c0c0380102e01e6500310104400044000d083c2000e0281d190002104110480c03003003406004602c440031249802c140c006403034080000e10b00c1d032182040c00108030003198828201a1840f80541e0402c2d80040b6a04d030150141148096040c3c220380301145c00101b281d03041e000302c2c948a000e11020031159032100411b400c2403000311212004010403100410100d4400c485000a9003184080010307030340e01c4500008283d4050152140040c0e1003542520850707600c44110900410480e00c0400040026000c0c0c1d1903030103d1840050103142e40c0358010010084912401c9824401d041e1003a2080d040b20314144203250460107040d40c5039032030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 417561043 1250 417559793 417559829
    0x70305070f050a02070306150e040b090f03070317090a35090f01140702090a0b0f030106030201020736050403120506010813230d0f0813030305070908060907 69
    0x3101250a107083c9030740901141e03404c548548000c1c0c02610200c0e000b1404001c8000380b0000316552050207a8401d6240340c90030700305100039134603000d039507880b008054004002c0d40340000d800040d0745030151503003006040156101c0040f01c0c00c2920001c006440d4104103880144030021020000c1c192455100500d111240c00407164100707401103102580d0040c20550100c4455030007400d14160041d00d1400e243c1ca804d0095002c90344494081e14802440b50f29107142c4011403034089100040e03660150001c101481c90350300000c0d502c0d4a40d02c504602403c8090700d00f03181d041c81005060036005018000900c42d03190849450040000b29026800a05841c03c00614040c00b8091b1500900c0c05075112840345d01c1c1d00321003440103410088102c03801c49102c80001803030040d000075000405d0000c8044c20040300302c2a005441071075060f00e03c84c100003040c070070030160011244803412120b030107280c0010599100b1909807080041c5400443c0365110b000c003004260340c40000c0b6003040d02c41044541c032580403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 417562293 1250 417561043 417561047
    0x105010f0c050a0308100f09060e0c0c06010b09150c0f0f030a02071401050705100b1f051207030603020306100812040b180a1206020408010608030f070f030201060e070305070f 77
    0x1a072060041a5800680c003500c00303e40b1510f400d84c2c02101c0c002d280c00340076599080d0303010340480c5540002556611104200103000000b47c10903482804100342500c0c0543c0081030b10744035407050113020740815000c42d2090503511a1071400c0c100050f03400205980c0c1c0340c0001080d40d181020108002603109007a0311440288020060343c0c09685d040d00107004d82e50400307010319030180015800b00c1c10050240202008100304010000801202203000182412140c00b03201d115030308048800c2c0304940c061500c0720541d80c420102d0345c500e504943c2507079243e11020411800391403d903101039490721a00c0180100c60005040200171101401d00300d524a4074140100c010500451243c40107281042c0304040384410041281c0b040090020300e0386c03020342d1f11361200090803401c0d03441c04d886455000c01c0a01c5100f90910840e009400f04400860401101310b0700080b09105005000786050038800c81d01041600035089003016040442d0410194031380440010000e01d0221454000195070a0101440303034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 417563543 1250 417562293 417562307
    0xb011202060414010507022e140a0305130b0106171f1e08010203071809050903040513110d0c081006090b0c120a030c18052202070510050105010f 64
    0xc0c0e016111608140c9460b504003c695890300902c0e052100801c100801a80d0751a40d20014420400305d4000b0b1058001090142e400621540004e00055001d412150285030081d11408569460086210307a1814864219581c00da000200b081a10b81d001041300d0b40c00c000c3c0744498005001d03200b01180d8410082e00760000c580e4162810071a0b141c04d040c07202d00607041d0700507120b0260780821030030140d650817034900f240e20407258000050b40190701d11902000c41c90300b0f4070050520302030621581c2010385c2056241d1050303100f951301c40c078000382444082c0d03512900200d250001d11012241c507040228041c0c0060481c2c07038132032030000300e040700012428100d041c18242994650799031685000c0c1404030542c0d16501010340801940b091200b04c0c51000441d03401401100c1d40c1b0340c5c011411000b10500500980c80b029103041050f05051002d00850702d07000901301e25100898502444024450f1414000307100e502c0c40a4400d016004c4d5508414502da00054122582030780c91580104d0081011503080c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 417564793 1250 417563543 417563579
    0x100503041a0a09140105090f0318101209030e0f0d050616020a02120304050103060b04120215040815040b01060e06090402070c1e090501061409040504080906070503070b01 75
    0x620299490010040711a1002940c00401e1207000148818a51a100d0309804001400c00c0700d42c0d1520200700c0440b90601c115145040740000079420310785a09907003010521160000c40c043d59606d00414416446a06650b00f50303810800304000c8100103060080200c541044030318011b0503c844131025038280f082019a000d42c100c006056161038080140401410307004c0c65104600c214101080544c1d44c006c060000c07040c0300c10087d640c0782d140000140546030306030b0014031501401c3c0810801100c07803200360416194100d5100c002e403211020310329002c0c080c13901302c040a031180b00035484002c401080a203020324003c0120f145543c0c0c1c0c43c01d0840f5600c01214109403c944c040c09680c01c281099005031030158440d03550342150503100c4c00782c01940b0008040069030724515007810032041c5450310480740581a5480d1038010b00c0340d0448810000d101d0380ca14640103580d290000740c144600801500c44c5c0c2d04001380b0f910303a9210103091460780c1c0c1e045100140d85802c40c5100004490b03001c03031031354445 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 417566043 1250 417564793 417564803
    0x309130507410d060801050a0f0e0a03050a051b0a140721060609091209060c030504270507030608150631090c030b0f01081f1d0c10050304 61
    0x8070450050000e242401140c2052858080502036010b4240c0280135040241110134000201c43c9404105481981e034a40f42e40301011f80b400c0001b109542d40031509002584c1c05041942d6200e0044004403441d10921580c4030b07204c082c01c225280f4a500100d05407203c64004c4d0b403052080002103610301e440349140d00c112286080e620910240306c04007028101c3c034240c0a001d0000d0b00f00d65812950003500c2c020201103901c1007404d1000c03914079400848070401340245140000000307c9690340501148128000c00d81a40d140030010620004a40081c01004146460500c502d040804010b03000c2c0505000305800c0340940102c01510f40206550503103d080700411000c0d01030700c180e07180c1e4906400d0842e5000951480341558803401c0003802002c08651040c00e02d02065455818821464400030308a2604100e00c1c01c01080003190010b4242d01c82450b60282e51110305006500700300030a40426048895403040401200044e0045035041d00300b01c05403081000e2812013401200d440c48101d40c0181 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 417567293 1250 417566043 417566117
    0x7080f09010515010f12050901090308090303040503090d060f1b02010e011401032915150a080703020a1b08250f0803060109091a0406060215041101020309130507 71
    0x86588079000010821701281088070100d01c068254030150380b0201c42191281e034454504074101a4440074036541f0501c0b0401550440c2840d6455988911840080300c1c0710700003030b119940034001c250340061050410400300300f042200c16468490321051b00091140554030b41070b01311500e814103000e42d00c503e90011940158503800c0d55103c1d10b000752135061900e031101024004840c154000194107000f9019440160b87c091443c000300702c400c100b142142000c8003402d00444603002c0d000880306820010908015845003d07014007107440181c11032210b40900300e0b960038603051068220041880c2240d0081c9981c10403c400501d089019003000b004107079021190343d0201044800000e59048141490801c2003603513200302041c00d482c0b811030410080e13080b00d40b04080034030b001d1182000170708850025115209005c039a114070604000c0c0003a1011101203c80841603200384120b136080ea02c014042419000c10300d00000c01418102d40b0500413034010100003542055101304480c0b01e24550035061 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 417568543 1250 417567293 417567331
    0xe0c091302031e0114071110380a060c05060a0b06041503110409020a0210050601090e130f05030706060602030301120809030109061802151207050f1207080f090105 72
    0x25420f411050355800d543e100d400003850446441801e014403c4e96a41e6071840c46c485d404142000c0120407003e80043c58030308d0802000a08400f1000083e480d180c0030219119610000c0c8000603038001100c3c0d02464040e8046681600a403034845100e0040c4115110b65648070710140c02c40340c807000e1240c2d0101040c0810040400000c4100307407115400d00e0301145100040a520095812580004010700e801264503981e469042090400103412110140410f05060b0006003c00e0100e00481040d4988100001d2607000040c007603400440d4000c0020a03081030074241039032650883c80303040300c030b1074240f0f81d0004480303100109590503507802001908901910750f4a0880c3c580c2f00c086080c0d010354072a1000000710b07203140f240120340c0550030814040c5c04540e1040228448041a031a140b10740f0a012662403c0080000903600c0360b10f07420035035074552441407030003280d000303455412194001c00c0080000c0c5030f52285030f0b02c0c001e450a00d5242c08c0c0d81c0b26100b543d400d03603904540707540070050950740310 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 417569793 1250 417568543 417568573
    0x6030606080a171804050103030924050904020f04051302190c0506071d1207060216120305070f1407050907030905060a052a04060e0d0b0105130f0e0c09130203 70
    0x2c00b01d00c0f010038000304c0031428400110701070716000d17481030700800c91000081081c00c2d958007a010f440c04000b01350217a5104912005409400b4140140b03000f958042040c0c00551071050403107000d050000e01e04602020400540006980840d10221240d21006030072038000e4002c00c0d500c40e5050784140070346115038801d40202c500c020207101c00c2da462240241d040160f07450b45003c1110342c0c1182405080145c0c28000013903d86103568045007440c4000c103004002451036031114540e4254545010360740c40742c1d50305140e11a806001c1c0040e29144103140702c155a902e00103000402c50b403040c2e0301c266140e0b0fa001c20640488200c00d2010380a504140300182001c580d9030700c22940041c06050885064016031111079003a804902648603408001400348407241c1c1041a6240c0010f040720340425899941d44c9a00b00030b48184162402913081c04048684681c02c1c3d0440303904078512403820481040503000d400c2e510105000030600403076590012031242901005900907803900a070044c034012500140e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 417571043 1250 417569793 417569797
    0x4060209150307020f07060f120504030e0907030204140a120210021f09020405010506030c070b0a020f180a1a070308040807060219080c070c050105070203010b0405090106030606080a17 81
    0x152a4481c40340c902001410080720061805045181c0c018520300c4041c060b501d142c00301c01e0f0842e405010188604540c0740794011400b482071482c980012489460714036003500d800c880c4501c210ba005558104100d20158594007410131140c01c0030407411070010507000e00401601c58010500c0d40c01d0100681d2015081840d5699413400c8140304131811041c0088042c0d1002c4440a03044d002c9503107804401055140601409000d024121201407650801036017024040c402c0d042c2c000c1801403507400003680c110007581610049820031211a99030348030404400c1c604102c0c00015840303050000000324100b15801c0010481140c0411110b02d002c880d600d003a40c10040040c021665a1002c000010024100f80042c00f10b10510305505031000c101088040e20b890002000c81d0ba01400c244011004160b122401d80203c840030300380703155141200d0000c40c4c0508002c00d20140c00034240000e10404031015480582220701805003040300d03e03282c3c0c4800b51585c120103806020520603102800d824000100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 417572293 1250 417571043 417571057
    0x50a0309030c0b10080c040c0e0d05010b0a0906060210090c0506090409080c010207170a02030405270408031008010e03030a110403060c0509040c03092301060b0d0c11060f040602 78
    0x4180d10034100310380d01c450703544070f00300c13070300102c290004c03030b040180b000100a051036050007244c0900c0410a102c1c4c004040715a041078003442000500d2040090101c20342c06245100b00c041c02c4281e106449103440c0340a800781d441446c00605c2104a1580f0039500d078803a9240b1264007500c82c41c0d01525140402035240c101608640d4010b550b03001b45000030300140e0041181440c00000941ca0f0300f0181007500c002030a107010061b400b0340400c0b00b40d140d90340c044111000e50383c04803912031800110340d40b201c0b001c1e1a1004040c00160418052000340a00b00340911310582e0300003008040c070341c1c584588500ba20405900c0d059680c0c014004504c82641d82d0708480100000583c500b4100790392a01e900080c0c8100c2c0c0c1c40d242c08200700150004040c10640103c0000400c54201070218401c140d981600358122501d1528030550343c002201b0302d115003900528010400c4040c6c181c2c076140007001180060804034803490100b4042c4014038800780000c207145110344041011103e6a80e12030329074801943c800c01c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 417573543 1250 417572293 417572297
    0x1b02150a02010b091801050609011d0406090f0302010501051f120b1f0309110117040b1801090b150d0302030f0f070c030305030a1d07030219090c171006050a030903 72
    0x441c018101383c90300c6441c54410405140200e04046400d0246401c492024004501030120080144000c02e003410300c0e0074640c031040480e0121503960741400c2c402020a02001400f20340075103c042c6c02d060341508410305843f021244c220602603031002c6050104e998005043c0445e01d09000b41d086485554441a464000541103010b82959181e2614144104404000209903242645014804a80440c9040c16420b090884042e5420120b20a5210000304010304610800001840e00030f1400c3d8100a280485070003032240e100180307050b00c0001c0003282d403003e960761030b0464104285031404a00c0d00068050300030b10b01d0410029441c804907448290302c440300310b1003040b64100003004d1100c82e4000b14020340d10707291a805c001c803842003515181c17000203000e05140583c0d403007101c0c07020401c10b0880f03038100e07541100c940061900c1d2040c0c4045a01060f0350914000c40781d248113402501e48a0031040c91718115100340c0d50003040206096035400381e00000f481c28814429030601942c013103c00c82c0d0285c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 417574793 1250 417573543 417573551
    0x19030e010b0a0b071106180d11120304031a0609060d0f0203030a0302030106020c0406030b16030603060921020304080601060c03020a2f04020915030c1201060c031b02150a0201 77
    0x101c0e000c1107004405520191619100040880501104503883c3e14001003c481807841c4c03070092104031304100303505a0854030510030074281400304400d40c0020f59074514050f200c101603010080025031250414071080e60f00d1645545900f0b040c0080c1c182c3c580c0f003000014074400d5151299014495100d4117540203d8207950519006405682d00b040504a0030780c0c40d03507000d0303a070750b051090007400d00b0348005c1c1d00c0380503a05004c01031001801044c15198400f242410300c0d50f90034003101c000c401400d003660028102034a06030210081c4170030380001004402101501983e10782d616a012a80c1e131043c1e100300e4440360011001800114807036582c240c0d40358001d1044404102c5207840754401300c02100d21003040c44144d603061300104680301c004400500d504540440c285400312010500c65134207051603c282c13000000010346460441c60a658900c011a443e0f00425a1030307030380140401004900540104d910410074403231250b403284000b000e4a5002e01880e0140c007488003080219000f03420048155522 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 417576043 1250 417574793 417574811
    0xb3621070c1715040623040b07050d0f09050105010306060b040b0a03090807081318151403010e0f0105102705040602040512030304020a290c0a29090319030e01 70
    0x107030091007402a409004002003d06c0030001d050f03106004c08840c501a00c43d10000c010114500c540074507030014090a0065642502414440061461112520b4094079010200013400320543c400d905a03481131800b04401525542c800805012303070703c142a10060704010b9000914400d81010000504c1107620f6800c042e4140d8900316150044034032001081d031201d00402c845880155060070707070041b900301003182c085c10511000103a90315004011075141258240f00003a00c00750700c4410090b41440a0755400c3e0304c40c18059020b018280c2e038038003603480003006c085090403201402c03c1a01e540d844103c0122085c4070480005010002c10968289509010000300f03500c400840f4018a903106003c1c6540745864810402d03411466041a0b601810182c400c9030000c101000d0480002004c0f00c0d01c0362180f10102c8410700e000c84403034004151848803d0414400d04032074503030340c15425030344001131042e6484041d084d590740140a00c81c446074000780740e4080d07424060b60100902c0b8034802e00110320508 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 417577293 1250 417576043 417576073
    0x2160807060902011205130f021305040506090d0e100f030e0708070314030909060909011b030b030c0d03020d1b060603030807110a0b3621070c17 64
    0x100005660060302c1c1c1aa050456a000503034515801c4007880070030240c1000703900003c41d500b1454004212003101c20341c0c02c095540b10401e44030ba4031703c082c03004d010314501803410740e0721801c080e035481d00103102d072048182c600c5010f01e19260982c1006017501060803207001045130001c00c1c6082e42018155100388411081100b0711000c030241c4034040c024602940385103032036610b40700c0c00e018141c0e15810a20110744283d9651141079000f040443d807003482d682b100104a8010b110703264807000040600741480035030f150140c1010708107010440544040e80a10002d1000d0415000704c000c0040c1c120540c011812406a60ba04d0f00c0701400202c40c044014031503840404449190308244c010408040c10480c3d8654030010700070321035420201808141d0781c10760301c1143d000d030b02601b0054011032005680354a0f242e041c82d030303104001111000384159843ca84000381c0b04c0ca441941d1124242440400c05440030102040b280840c0c0d008100100b10f928001303508a440008540080484c00343c071041c1c26000d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 417578543 1250 417577293 417577297
    0xf0c220605090f040e060601050714031603080a0504050d03110d05010902040f0f06050403020d1a0f010e1f170c0a2729011e03090b1b0706021608 64
    0x444503480d40c03580d944511042143c2121080759951042e41450fa400c864071401180c1644c1092080c00c2407602c42c4c45910341901c858081c0c1d02078411602c8045141e420005284a4200d20036000f620780e2015500c9008201d41981c008aa014205601402c5119131403403103540b00d01d002e04400c040407400c01844c404984c013600c070b007039100f074540b550046002c5c080b929003030300d0082c02420340c04004080185810805030a502031484040e01c51114214090107000e01c1d000c07420110ba0411595003d1468a1555842100e9003070240701d108803092000190703a21245000058800302e45000c60450300d1901031300040c0100a245a08800e028814208a841c0c6074103500c0c1c0060b0040002294060703050404c000380312000110080c9460303017000001d581c216501c0103131b400300030b04404070704000c2c010510060b20f48204400f14200c400581c86028096141e06900c04200d00380308416080c00d6441c1c1d02c540301c0840f501c40341c544c84000300c200307c410002046940184081c41c8810481c00c00105151904d041603 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 417579793 1250 417578543 417578549
    0xe010512042910060504060f2708010905060907050f06030910140a0f020a0c0209090a0506010b2205102006010909030e18280f020a0908060f0c22 64
    0x10400c1800583e2040061040c0079003030700c0c0350060404c1e141c90300061444000001c02c500740041070f180481c485103d45007840c503d0006440b50980956110802802000d0840003075400780170700b801017034105001064400485000030102c020031103102d01042800c0e40094806030a603c5140b4a107070400b40b90b030013403442103141d4140d01419860900100f00558104c0c03405600e50503c1004030f001c000e40c1001410800e150103480151080e0399a00045241c07920444000d822445090700004d20030887c0c0c001400100c04001c0651200c40c0003034040c601040050090550000040c0007101003684507803018600c40b1f0492501d00c0c0c915001c19009800c2c00000c0c0c00070021a80c0b2115102d09040e00800e000300392200503108885110b0104601642c0030f80f02500200c42c41c04920f208600040c1000301d0000041c1c1c030748204000e041c1c0041d000c00001c1d80554401c50106000010000b290074012582510030032078582000789642d0742e04100b2083c0c2d03001c040c020890411529136010030801c240081806 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 417581043 1250 417579793 417579863
    0x40b04060e0a02091f2607120506030307050105190b0405010803040b032505040906140a060302160510090204060803030106081f03080720030109050715090e1311010e01051204 77
    0x400946c141501e500d8410f072000c1e004064000d04c00380a5420351006941d5404404910001202d4441000007030661142c481c029100b036090600340042043e40d034a000094547d500e00c204600064131050000b6100f09218500e244d0700188820421600400e000b0359008001030480c0c0105462400640006244400341e400099030200e8240001c001a200d844041e05e0402500082070001100141c442015805441c0c1015000b1803000c0000f0340d120618002142c1c0320080c1e0f0f0920900951071002820300003000d038401c908002c0005100d040200440307050f5039007540c910b9244d984442007e00c0c0c14852240b01c00900018420000c0031510400c041d0015038460103440403040d00820000038148681c001c0144242d1401c0d900c40b0000b0fa00046900032134050303155940c040c41c60700303109540c41c2070154044000c034a035003820005a40e05c0b0034144458076208000ca88042400c44004544058041d545540820420840a4209450040b059900a121340d1400d082c0030848144003410706440005410 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 417582293 1250 417581043 417581057
    0x6020c0112060311150f16150509061816031104050a06050105090103110d0e100c02070f030b04050a02060a02160b16120306080a030905040b04060e0a02091f 69
    0x642503a11403455076031441150030a2080504603240e01301c00900e14a01144680c0c0c001c4454050409082d0a443c9081c9100c01c2c16a26801101c1206a403419485c0c01122a4000c50442909040d62031044c54040d00300c80005007066512101c016103042420102910148038101d41100500384041c0c00f04095440781060b50042c2c81100e01b030000380c50001d0005114942031640501540e603004041da004000c003440d003c103508400c80e5840d0030f10b100d240c1d00c001d0801c0c1400020290ba050015101040d000740c0f00d82001034035a03510040b6190b4410303020b00e213481c006886040011808845000b40c00a018100b40c3d601c461403507000603030a62081c0040320160b004040f4004c8904101e901c540010f203d0030038400c2ca4103200e80ea424600f0140148000d106210701c10600400d14440c0c3d204001600f070741c13400c45500780018100540860030342d10405102c0c03820101e03661100d081c14003c2d0801c48450900340420f507101c80c410b10700a900000d0000c4d4119031404c0c5140280100820208580c40342038036041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 417583543 1250 417582293 417582313
    0x3050c0a0f0b0a0b0f1e0a03030e12011802040e01020d051005030d08062b0803010b040e060d020112050c0f031005041803020a0f0c030b0a1a0301060308031906050a0602 74
    0x514034000080003075041c01e01d0700d1000c41c480d0705d51031111010100304072688010480282e030155141089100c0607a000140710101200709038208007010245101228038421110204c2c065a003aa803031800001c032004540040d500040c1017036000542045807001c00541000c407c004400300b04c481c01c90710b2030014400224100294102401000092a264038001da0315107070410108401d05800500003040080181072001014003403100314043d02d501c12f0b0841c1c0e40b9650707001000c800ea0414010304074541e00311000315000d4179112040d80d01c1c265040c0c42e4014804140d0022600800c0000d10b41d030418103081000e10824010940110721a100c07603080e030340c4801e003008148021520301501029554031002600f0002c41e800003407010342168000458500146685803111030300300582d100038192603024007441800f4080345c21610300e030f04400c0d01c04241e03401e0790740c1003500341e0783c480c0320207403044000304045142030030913001080903050b0107000420842d40d074001292144442e81d020380016003194200f0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 417584793 1250 417583543 417583553
    0x2010e040b03071703161401050f16120b0d06021e0a1704020f06071101080f010501090303030b0f030d02031e13060e040b0604090c020f01020c06011203050c0a0f 71
    0x2100090009450030800d0012910119580b2203880c001d86503030b1001d4242c0340b84403160800456000070b40200d03942202d03c3c0305150210030150f00c001c245d8425404c1c000054494405142c01a00c6441c2c041c000445c9035201c0401503c050700d50308040c50700203444521010050303c80c142003681d0244a10303001a52441e00c5505101070b4980c0708009803040804100a00d0710395407155900180000e905091083d580b51440081c80c041c50b071050054000c04040b40c0b42c01400800320070204a203000782c0702ea107000d82d9100d40801890000740541c60210b4003005050020034461390180705404409041d40b0444920b8400203490543e040c0c400f4401a071000480e4a840b51000401e071005d1070961041e03900b0004001c1d00d1150f07060281c002c0c03004005228044501c02d503141d4202c4041000058945c503541c40e200c1c48804007400d0f5884a000c09480342c042c6901c142c000500c212008a10614068032040e42058400858121200c2c030607030403c041403241c100711410038055640b115105a1569054500c46c0c500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 417586043 1250 417584793 417584807
    0x212103507150e031c0905060a0e0301060e0115020a080a1b0209040b010330030c021005010f17030c060103020d050319020d090915150306120b0405060f0405070501050a0c060c09030201 81
    0x3d1713201740a1603132500c1a0040c1d0020b42a4058941c21220140c840f66501d0044600915101409a01d582041800aa0614000c503414165603583c41d600101290036003060342c0c0c8014540340200030b11020454140303640d114a00f03078002030b840c002040f2039444980e00021440030040c2c0d819558800540c004000f04260b141c41c00082c0c0403481081c0b5803072103401c2d10000d03881803a400c2c10b00c00e00d6281d68058192910030b20080c10110304841c4104040d5031030f84000c410710b600d180980b00c40c00400001c250b4540c03100006072916480e250b0010300003030b821a800e0161002c0000c0086900e4442402801449101403005401d0000b55900a00244003050801824880d0540c80510b245244c042c1410b01d5542c1c080441d0f056840450607040003002e41d480880080c80d09500101c826600134410380d0403c207281e540070380520700034030458000d601c2d09241d00100050954006045a00c401001c205c0f41d4051005402c0d1070703540742008600c60b030581d203400d03040e20b6100709080001843d801e030034030444d80c1040d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 417587293 1250 417586043 417586063
    0x14010c02070b0405010c0c05090a060503061b030114030312090c030c0a150e01020f010c030515040506030d0c03050f0d0b130219050d0f0212103507150e03 68
    0x40208441450b100380c5212901c264000c0d24108018501c011040c4800483d01d04001d04025100007203078900203107040700828881c010700f0701c01e00920780407138141c103540320900c0350440b0790030302851442c0d19181d5044c594402c440d05040e0140400d03c040340d00d030b132142240e89100705c0540d000f800014140324101402d00414540c024440e034410001440b040b40e145d150840e0341e1007141047c503154129000180d21745001075030105959801c2c500401e0f01c040d403642189000d0148a16450f46244441c0100000e8401c11682240c01d0360200c0500003141e446085a542010300908242d1b2804c890a9003003400ca0384051440c0c031155890301c03c01c030114206820302010200741c0b104110b003041c40c01019011070742c0c1800d82480400c603010030301242828141d070150000440b03800c0110b41d14004152a04038890040b95801c03031002ea41600000c0036108403522954600a915001c80021510008103043d03035104c0741c140c00f603842070140125100080b201c81c000c1da8900f82d114960242c01d02000c15260030302142c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 417588543 1250 417587293 417587297
    0x41b1e0201022a0f2406040507140315090411031507020d0c02060c0d08010e071107030201080403050d2c1b0108071107120201110c0f060c030c01060314010c 69
    0xc0c4940306400b6580340d003100100c1c4686010740401182c106184c4003020551403214007807420400291a0b441d940c0c408000d503c0c802114103a5981404c100480c0c0084852101184021000c1845800d0fa08002c1d54040d51107101c013640c01c050701c004141d03404003c40c1e0440303240c2018000010249010045904c0361300e1901c10a0026107070003140252910302400d040000d2040070030210b411965080240c0303540c50389540071103440300300c07908000345003950038032a142201140801103000640704184a10b090311381100280a1980f0b1a070046070032460041098040220a001d0245441400e0040e401d0b4606031344540032030000582100104100b881065a0f034640c00181601d81c2c101208491865401090030407101d11ba90300a030954000ba10398038407061900890802003040d40200b103a1140f50307070007039980e242c0499a101e540c40da101d07050b010b29a84121000e078950010b1410600030700d200740c0a80d0a480c2800307506106c540c250740440d04110f41c00e40010094410360142407107098031f0040e0314 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 417589793 1250 417588543 417588547
    0x80d020304150501141e03010e031804051b1812010c03061e031502031e040c15050f09040519140a050a0204050907030f02040e1603060e06061602041b1e020102 70
    0x101e000112409074006d169240299000c20120742c9940c00c1d44448907956850382902c0c1c1d14403d60b042c5000003812030004a10607450400403c0035116082c1c0210f000c0110f981e1498506454030240991802c20030413150361010007ca0710021184080c02043c05107082a10041038080c14940401c2e4a190700e070b24200709544035846d0400129107004040d008152281c0c0006030f40344c9800c3c420010003aa00c181040d106e4064105010412041003d000125804072800c500030401c400e40440f801d1050300100c1c034a030a02441003c0039460f1a51001c1c3e00441c4081c0703408466400c0145000c00d51700801400c154010b150000c025070300500b40191503100501420452805051000080744194094685000c2554885491849030360341d41c1200e005d80f07a60304012a003071505943c14440d0814005038403001030b00b02800010902d200340310242c043c1800030001e50800e142c6c0d1000d1064400b0f1032405030703886516503491451940c10761088071901d078503503942d40e440a00450501061404416070b010116841 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 417591043 1250 417589793 417589829
    0xa0909051b03040203160f06030f050f0412020a0501060602150903040609061209020916030b0d02030d0e2106010f06080103050c0d05031207020c040c08090606010c080d020304150501 80
    0x6500c107070500d2491080401e0382ca035100c500110380b0705008200710020b9216801c6011640b03c40c105c03084004c4442d40d580c24004250104141d500741c4100342c2e000740c403e180c8003001c03c000640d400750040418000380b0490701e11060548074603081d1400c9505c401e0140c2c001c5101c0404040000312170f140c2c014864001185030610b0040c004090413440c2c8150020030080322190100c03030b580da8000c000c0d52600104400301034180385042c40d2131034102e940a500424640000700c40c49003010741340341440e00d40040151521072034550050322103603404944603070700207a801294055051140c00d070300084c0350b11100428156040207007070311141845030000b00c01d0080e10001000081c00003c4c1e1041075813010b4410200782d00b2949400d03840c42c042e14084940e50341d88a002c2010710741d400102c901c0c019200300d60501c011181c1c40340c00d881d01c13503003a03500302415040f6400040941d402051044d58480c400c5491914201c1072003481412030700301b501d08a921001c50b113146000785a00d40111400f4040b00c0c00f02c0f11034400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 417592293 1250 417591043 417591061
    0x20703020612090f030a0810140a050103020a1403040c08060603030c061311090a05040201120b060301030605040c051f0210020406050d0c02010e0109080304061107020d03081b0f0a090905 82
    0x41d041e1501111540b0030001540f800041c00280c0000b0307024001c5a03110f144000b4003409024040b14400030180e100c0c0070009d43c450f40ca08040034080d8000d4510780343e040c1401c00440296003d000715100313001030030105140d014410001103204d1409002110507103420048010300380711000e013420f44645c1c410720414a01c54008180ca58201051286028040c000e0303240c80d13440008090341c170541c4003e070f01c410040305c4e40301904800e2149100740c0e07544e1b205503003105265049038002c41140350010001e01c01070000030050383c445078002d07010b021800070261b981e070001608158180d086440c1008405a0b0440e455010480c140d061944c03850103504207400d1900080c00d40c00754152001c115a141e00800d84414000e610801c182c2004000a04c0324140d0b41c02d00c001c6550003035230102d41382860700e81c1981d02246800141c81d070040e0b0040031000107030190789048440701c20240460700c1c13000c0300112841d042c4036107100901103000a240d4507900e076900c00d80e0280002003e54401a102400c150070442015 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 417593543 1250 417592293 417592297
    0x70b0f060607080406031e06030501021b1b0d260a0f02010b150304031e0302040812030601020d120213060c02030d02010501030b0a1d2d010612060c05121609060207030206 75
    0x1780704c0e4075000540d00120703503805a407114903a00400307046203001804020f10030107400501059007a203410381003561940340340d2036132076540030000c1e034594580140c1c545071031420b00c40d640041c601030041d0040480c0e150010786a40d9664601643d40c1c80d00000745041140d0300444945151603980c0000c0002c0c03420f0300041010b011515100c101e02c1d8000200150405004890306610349801c08441042d1403800503001d00294030502500500d032242c2610a1030b048a040c044900c00c04041e0b0141240036905c01d400d540ca0744520702d485100580030b11000100e00c280100c074100402c050341e600943c0c20598018035042014800f040743c21641050300500115641002094212595150005030480c03030b2149418140040000b8813510b005132180201c81310810341d0318a00441010b0501842a00c100403514201d64442c03051801030013030f050702c0304042000390380140d075114124242540b80030201d0400840f03a2004442881d00600940226021658060b00c07000162001c2d000030522903003550001a0b580c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 417594793 1250 417593543 417593549
    0x405031504051903020f0a050d09081f0903050403150213050d0b060108070203040f0b0703030510140f06041e08010b040207080912070f06020721020d110a0b070b0f0606070804 77
    0x9038800c81080f104140c400c000c01c480c2c50f4095815165112118034040d61234104420b0342e100011048000071403c0100881c0301c500240d410395500c5c10318035282c420a009030003000c006400f442030030301000001c1104d822031105035001c2c03d070005aa80c8241c9903d1003042035039800240c041d170808154000000d401421241e0440c82c02d00703040364283d88500c805c82c50740c4a9030308207405061041230006040301c54240a090301e02d100e43c0342400070b0754403801d1032a2031a0361445286640412402d00e4841420545e0004804600280a07140f030607440c0c240281106050305e5201c15110f03400711007046400d81c00c0c8945016900d040300d042d460701016480e07080f618060001254455000301c00c0c0088400c8040004100500b060381c100742c03000703076152406074881411784680c2c2507041003014141c441d2840c051444003141e0b40148030703400070020b940364140b640303200000c3c203038020040f4a004500c16806201801c0040c0c0b16096103441d40c0341034028600900c070b001d172209020307000034000b40001412200c292419 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 417596043 1250 417594793 417594823
    0x408062719111008190506181308030708040c080c130b060403060e16090c080115030b030714030106090207030c02060a024201050a181b0302040503150405 68
    0x68030526041c0070011400600d1038981c00755400408243c40c0c1e4122000038402d00d01100c82d484108403200e070560030f03144101e030001c1c0e1200c80c0154202814610311009600103640d404041c43e101203d554082c01e681c0141d6500002c65000420441084000d40c00c1d071020b05030080c080c0c28a00ca000c408284030706000501508034075180d42c281c9020340c0300d18003524001e5800110a10014082d5044217864881c60400d40c400c0c102101c01c0480d00382103038003450100360b80d2603441100607072a081501d01c400704054098000c158840d54214190b45d420070800c8041d014031030707504d0f54800310f107410142100d03000e0340284522070050010502190700517400344030f107075010b9910755591041b16000300d0516241442c1800340303400402d401000031000e280c1d13010440d09000041c0c140e07000342824642420000b40b003081e40c0490828024400b44440290001c4060303030303012010031a1001c2220201c026040c003001d4038006580418100940c2c5000c010082c0c41032003140904c0c6040c103045c0c03980303911a484103c809072 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 417597293 1250 417596043 417596083
    0x60504031d18130311060c092701030201031a09041b0e1005060702150406081006020105190f0e030d0e010b1023120f090616050d05090c030304080627 66
    0x501d4010848200c00601c5c82069902500c3c10042054140d08800e9900d8001c502c84500030500e2400c0d003034000d1a2011701c1000a003160b10710b5004401803c0051a8043c50b001035004425031904d5500b5900d0141d442040101850708c054540b5101034022a031200002564040074010b07005240300031501500c03802c2e251a036590314a400410794824103d8a401035031040013400040b00e80c0d08c003e80364081c12140c2c0c0c40e013004035510a4100d00ba91829102d400c0d186c0310840143e43c0c3c000903580000a210074208000c02c1102d0004810707400c54101c80003ca80312602c42c1c42e0300d40700742c2007846500c4107843e044a01c6122145066002412a10b000b6500310f6640da1074031205051201d0202500c43c1c444d4901503e00b07251924100c200200202a10481014402d03240031075040b2800340e801c00c0d090240c0d541c96a08140d1100482005058090000d443c40c0c00790f45a80c0615482c02e00050000e864100c0083c4641e050001650400c2c00d0340c500c55407800b16100c1065400c030480811205076038030303014105070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 417598543 1250 417597293 417597331
    0x50106080a021e0304060e16060201060e01050906010804150e010203220b160306090c020d0306080607052b0e0f0d05040f03031107180603020306100312050f07060504031d18 76
    0x40142218240d07c1000c1c800d001e42e60308050010b60340c0d84191902076000b401140d5442016685d045020f000e169805400e03800041c0c465482034005540c0709000700f44840407429210515000c07a112500700782c040741d400104208034204440050154030f6070055603000c45840c00d80311042016809880700e40014080542442c00303034400d8200101410a942040040c0000c4200296440c00605c0007400443d040c000300042d0740801141b014414015602c80c14135015181c802c0390204141c104002440720f00303805001003200517901c02e6581c0e61403900300070230100010782c11f0189005c24611304603081100070041401405a450005401c69505062803ca17002a0500450404a003a0403d07074034018420030480d10142c0d15008102100d009a05403455502c1d000e070701c2070350f0a20900000e44444112070090340128420002013024600c12800c0506018290b521035041da4426a02500000c405100840c42d200b90b0741600d48000000715403481c0d203d16030800780292010000c2c000300d91441008050 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 417599793 1250 417598543 417598553
    0x30c070f06110316210b010203120c0408120408030d0903032d0e070f0303080606160501090c0e0603070303180503060108070f0501170402040b060c01050406050106080a021e0304 78
    0x811450754019000d011502c601d01c02000c0035082114841e46044803001844a41802000500f25200d0202c4603908403100a001100182c000300250904501c401c002031142d207080d2191481c0103090f0402090340d960318011700e6a150500c40c3c0c4680d42e12000820040003a4500007040314042c10090102152101460500382c0c01454010810002ca264210b80c0c449000c20340f0071860f0001c050200304000d140064074505580c0d03001400b0340c50115000c6181880424060300c542039216070010001440d107003d48012883c00d014059080310141e443d00558410050281c0301080a8002120325041600e08a0000307561a4030380c0c440907007407055000d80100c003694050f0051f8060240034040f5050303540c0d200c00306580e443c0680704024981d5080000412070358892400c8522580e0051621811910b850302004001c11040c9241644401c04008100c1c00c41001c0c020244642d000d00c03400610741d89070200142500070024600c030f070b641d441005100751850020100380d101a26141100703490f56198584 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 417601043 1250 417599793 417599813
    0x304030305060d0b0a090b0a0c0c06051f080304030b0601030903050904200a02071505040f0e07020a0f0f0c06110304030602180414100807210c05100906110303070203030c07 76
    0xf02030708000700e1808011000354241c2040300c070325100c4d182c1a540c40d40e842001704126003900203158000340141aa540214520350845a00f15411840700210340d100e040c04820410394076031004215030000315040040c0125550501d50020080c201404211a40d07600200544249107000340300c1da9540a8a10310302c8856a400c01c0c5010b020104995600144400a9594000c522402080a2003984000d01c402d11640c203503001c842050604804960038500c076103400010007801e400440c42102c10b0007010a80140604801718055908003803030800604103181034a8a82d0440e00034042d8090103500c00c1c2400100b241c04694100314016141c0d00790320380d0701e1403144094036025405424141451183d00b50110a50300030700c44103140f8441c05540380381d9142c4680e0070303205024800901e001051305800034034070314005062040c034058101607150710000b50078244900c00c00d00001d50400c2d0512555410480d0001840002d00c011401d42ca84144001d580b0301c00240900050712002c1139410030403ca10031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 417602293 1250 417601043 417601069
    0xe01090506190609061d220807030809160611031c05090712030903140a120f02010b0105040810020f160308070818070608100308040e0405070803040b030403030506 72
    0x30544050303040c9030598052014400c00c8840500746040381c002110307100783c0701780011500d02100019400c030407100b845034800402130001284080000c0280041c41e0301105c6a00468880c20415440751242d040003001100018085c24040e4403401091982102c040c0b8501e040b110f0707615004041214414403d07040d801201d885c46181d4454078100c07442c40c00d0300c1c5c0000784110140300480e002103075150050000b12440c1900600427644214092001c04d651442540d140001c060071034125080d40da8072214040d11500803007000400c0c00180070700b42a420700544910340360918207076041600781b2180715210704900c0d6111084690016000790716240c050252461703410980c603082d80786085401c0203040e040301198800009405c60340001c0078502c1120000d00d001c291400281906810414151030a000142a80d1611840da010010000e01c003c4014406820800004403143c107282c0380080c03070620135030804655904144014024041c907003042e640d00c00d41603e00071600b82c4071200480c042d400066 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 417603543 1250 417602293 417602303
    0x10b0a0504080102071a1e13020a030b16030b060717091f03050916181d010c0c020f030601180513020a090207020f03121e0c0d0f020d031a040e0109 65
    0xb0600720188004451121000fa0b400c146001d5147d640da14030505403496240d4500034805800302180508102d0740340c08485501c090a00320a603a00c0b40c8a82d000154212201030801d072200705103007031460341402656011001602d10741c2c00c091403962610b80c1c000e01d603402c200e50203034045038a0586a596016072103141079503071024510f0b9885c01030010007800c422a82a101c034840c5000003400040c102c040802110b80f0003222403c40645901c0403c090940c0c1ca2a03150070640c600e40020109901f84079040714100c2c162100640c0d4120751050000c120300c28044284079400001c0100300030f80210899400744100c1c09400034103682c8801c81420100302111010390800e80126010508900650050159900850b03903105400e003a07204045c1c0c1c60b66001180548042c0c2070108800c201580220544400c4100c0c1926003410855041249400c20a4800200040303c15810094103a0180200d445000b403502c0c090041d032448201803081d107260b040381c080c0505e030f03a910300b04d401c4542984044240d541c00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 417604793 1250 417603543 417603547
    0x6090103200406020a0302070b130e070315090b1c0201021e1203040b061c02010f0c020a05060a02010b0909070e01271a10050702280e09010f0e0a0b010b0a0504080102 73
    0x90360f00030769824040508501510030b944000c11125801c005a40d070188180c40900e91243c04d088030a00c28000c050025000e043c0c4882c40c031309803400720b20580d00150440e84800102280c0a0003045500c0511090803214150715001101c00760364042000c0811a240010907400000031a80c2d4518004041400300070080c00401030204200680c002d25001e07442c200d88000001e44d80d013820701030500b50007138028046100c14040380c1910340165414099a80010491900d01d955107012440710352205104c2d00c0103075502e4102180d5883c0024200782c00401e404000e16055061083d60120003506008112060516100d501ca90019000d0719615805d09840188442400704040500c04103880f0410381c824070056100181c45031249088c1c800040e0000c00c5001440103010316511140c80703400000300f60a44440c0b021401c20300721020f1a0041d94000300008800c0e030525040003c80c2c020125003403290304500b0920001c0303140030510905581001000c0741d0b64a0704081c05844502c00e45d405a8665400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 417606043 1250 417604793 417604799
    0x90606030a050903071401090c080d0804110103060f0306050a11031e150414090613150905150f0a060e070804060c0302091507150c022802041107060f020306060901032004 75
    0x106400c20000305100f24107841e407403a114001c2c25110803030400b8bc407001a55080c000350110300100031a070740d400b90604000030110f40f05c0c0c031121400000c64100b50b031904d44480c1403001d4400b05214208440d83c04000030760070b5003000b480c2407640a02142c1d4070900c1030340c4c0f03030301181007010040c5a22440030b000034010031200000c1d4004844c000400c41d90a1418054000083d424450203283d0084169110411072640b04001024400801c000070017503034603115044892003040e068081076400350100e60030b040d4403031a15031003200546540d40c2010400d81c2c092001c4c8050590890032860b00103600c0040402c081200c02c500b14000d0103180045940301001030581d61144040d60010113416000314504220808040b1041701034902c144404030040e03010a0440411782e4030a40750301003c2c6000e02001200014540010f803d0701c001c0810303012006000241e100070400540300382c408113034492409504516054002500c54010260840d051544490243c820950015801310440001c801220b441d03d403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 417607293 1250 417606043 417606083
    0x2180901090c0905010509101d06030f0f06060a050906030406090615060e06091c05030d050c04150e0901050d080403021e0310060b09131d0d030b090606030a05090307 73
    0x288402c8400f0644065020680d54490011030f00f1800d00030b000d0700c440e603001740c034200c034000b00c9142c0413011f00d454910342e880159203000003103000c0d8034081c80c100d0682c18000308202d2482c0001c0e01891242c001003101b419050b802078151100d0b0101282c109490b960f1f5030070424040c0052140080800c1d19000c3c41942d82c4d15440b0840b015203001d655080c0031540d044e020b110140c811031041607031008200440441c850751250840b611035104e40162030410b0300503209082030b104c059450180d00c0c400400d051124404800e0304555201c02d80c640010f400304040040740e14450180203140c00344101004030004d000030101250002c6501424941180780600e000100c4100505e862600c03e000b22071119080c26080d001e003405450104007184e21381484581048404610314012008581c1c03104260340540056a080d0f01c13480c4055005882460310524000303040758016030b8090310950706c040910095448800559500800c148400a050380710003641a00c0e50040d40f6006089103c0c1c80c036a800485 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 417608543 1250 417607293 417607301
    0xb061207030803160c020901120206070f03080106080a021309052208221a0d060e19110c0a1e020603010311040516020606010e010917030316051c0218090109 69
    0xc043c40391311000705506184201c0b001082100080d52210354032005004041d034011496410701c1c40200070500e090034941d03800c001940242d2054011880b00d0004100664120302030310b41c0550741002c00c515019424001e003601c2d28042c05079945103540c2e00001005400c1c1c1e8101410241802c03040300000c1101864407401a0f441a074130800100007400d10f400707445d441c522080069a040c03107161050302154070407201041e00302c00c503488809a01d03140300150003004054014041c03a41c3c0380090502c4804102c1140589146910f850384004041100d03182c2d00300040354003660b83d6480114006620b190f80c0c05e000b400e80010300042d600a10000c000402c00020258030145600240d8040c03299a8488020803444028a400c6001503005200001d9003913200322001c0b81480d07014142141896141d1051540100012104074241e43c00041131180e000c483c1a480b11600c01d442c640b0602c6d00011a201c90191100794260104464010821103405280c049001c3c8801c980503000c410a5a9031361001d501030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 417609793 1250 417608543 417608551
    0xd0302070b072a080418021c0f092003010c021902010c02060d020f0705070f060903060b0a09020f0d0e190b18060a0906050a140c090607170304020108090706020a0b061207030803 78
    0x6580d296407130311b035816a40d0098800c8510b50841e05114181e40c107980d040a44042514440304650301d20b18440090107007070700c650203613540700d40024092040500389801c40c1d0507204c000d015544058449800d0101c07003a001001c0e50350a00e4200c03041c070010b01c041501d90082c02030000170a4000300e0390b241d2580000015065070741c0a40111410180e852145024a07a0076021300400921540020310104819070414000342c0700c0a40012001661084c54404030f0304071401103810124000744050080b2003078085c403180040a0b0001d0b19600b502c9089402008801100044c221400c400010305410b41403043c3c03000240c1e0f43c03c00d607940741c41d015140e440148101c2a04868051410002c5000200584540e000072910501c880c0c1035915041039141040d040340501a030300000c01c121410002d1040d00310700c81081004460306490b030405200141c05841c005001c171881d07520a103010480c8503070020300303000c109810410750742c0c0d2034980314003051f02d4141100c521044c520415400008204c030040046102d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 417611043 1250 417609793 417609809
    0x11e020c13050408030a0b06071221020c03030708180d0e0406060815150408100204091d030a0e040605030d020a05010b15120a0617030406020d0302070b072a0804 71
    0x10406511840310498400f0340c0c001d000c020090000440c5d6a00301e912070140c1d1400100314904100e070903546d210740c482c04020300c180002c004015480040c500ca510206a80c110b0f45020b50415000c800307111b179680401080441003090a1010a002d51400c00d80f03522f071410a0b00c04d58a0009006901800c6e0200c2110b410f0301542c50807100003083e910401140b800382d43d01e042c40c40074016554081000c052440010351208500030403000070110010013000030300701c0380200c0c090b880d245000c849a080751700c00d00f04d003507482c002c074ec018105558011080300c0013402541030041040c074042021800909490700510341512450000100e40e0343c0006200c0141c5114000900150345083c045c170050000709000c03204030712000d201001070103203000302c0e8550007040b1100018a06680f46202c07000e00702009030782c3c007041d00009020310582c0d50500008050410904081d403420100340d440241d14140100b11800b01b011100c0d00004082e55400c003130014110010113010005c44608002900360310901c10004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 417612293 1250 417611043 417611059
    0x50108070504030f0b060102030c0d11250915050a08060a06150f030f1407170f150d020109090e0f1905060711010216033515011e020c 59
    0x10318420411102a02d40c03090081800f5109562804040321000d4070b810b041d804144402887c22030200000303248911595100d081d0000389100103410b20301d00d0159080341a03400d400e801d082c0c0800104c04000c0724140c1d1700005408420216642210b030762074201a0380180040700010306410300242d4031740106020501040035555130040c030381d41002c8078046080404c9403010555280343c00b0381e12000782440000310224001140c0a542c06800004591410101d080c140b809550074081108480e408449640d8040c082e0404407000000b00403e605220720810450384104116440340c0700b1f0b05d005055503007003417040016006501f0b40f140340803044400306108460603042142c01c442031041c0301e82d03042009800345485a0000704c80700d03540901070f94074540d000c0042100710400e040d40d01548038001c7d600c401c5000e904822099040f404204201442d90b02400101c44089000020710381029000a00d00b160907600e10058924181500c40400b000c4900ea075124031081e00890a21085d01d03003107030307103034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 417613543 1250 417612293 417612301
    0x3070c021819020c0c1c0b090303010b250203060a060503150c09270c0403060501090b010914011407050a0201020607170109091103030c01271e141204050108 69
    0x40303a000c81c100c1d8803030051201c5818620068180ea4010040b01810364155080d00700284042090044040080705510f61000116420300c1903d08803540c1100f02c0c80003541c6154500305002d0701078001d07900c11428440c0b001c5260400480695440084140c0c054140d07207803883e010750078100508552045c02d000c0d0051800440080341e07440d07000d82c8074460300321106003415245010701c81d00c050b013038084410000c0b49501e401e1842d1140850750384141c1c1d42e1500b499071141585402d1054601c1a031100b1445810043c128404d03a80107030300e0314207580507900000d0480c00c0d45e00040701c1c00040c4888400d050000041d14905001010648004450007038003103c80c43d4840709400c4900200900043c41140e28075801400090380071741250404c207000e010909107914141c00003e046500140101241d03030741d071358040031800ca03591001a0b0500c401c0e8808039503089460b20f8190303010102d402140e4503022141c0380c42d002c0201c84a0300b019001c0f80e501c226a500d01d5212227100c000d0780036015003808212240001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 417614793 1250 417613543 417613579
    0x8090a033f0f0e07260f030a1b0206160c0f0b090f060702180901020730020708030a0806041104030b070e0603130f0f0210020109110a080c01080907030803070c02 71
    0xc0109940c03000010420a0b103031180e013080e100c05d1500c181550300080060072007040e80411484418a0f00100515032320501c1b00c802903d41601102e0411200600c1000b031409039a43d00709a8032588400658001101090f03d40940d45d14083d4010400c003030126800820201d00407005080c4010b4141c0345030451200306801c0004c28056030b40700940c04904503d07aa01c0c3c085003644003039040040c0b140094100741040d61444441070608203080107442e903d100e00d840d076141c4401000801921400604880750a01c1c945603140c1c41000a6031052000b00e82c04210142c640e42c2c425110700040b1000341d40c8540d105e150482001c1015204100000c140c8034201e01585442422240624490740780800a00c603156580c0080c0200520251340c000d084803410009600c500100c1c2d42c5400301035000282d90842407410003501c5850f42841340c083c1c2c200060a1140440010302c01d040d01c402400c14400c181d1b5a06802032900900d600010b1030103001105010b90590030007038100405208680e80803451441e0340413 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 417616043 1250 417614793 417614801
    0x9010204050d080a05040504020a050d0f050708160e090901090b07020c0f010c08070c030503030105130e0d031e0c0302120106020c0a050906061209061608090a033f0f 73
    0x141684580900502d50006240300c005182204043c14854205503031500090200e80002c6844000300380001002c10034440540719040c801c03907100e03900304098105880c0003040c900c030090aa01c2c05441040110012501030703c0c00036003541000b031002c809464241d070340d54040c203100107003141c038200300c00003044195001107142480444064035400307509071160011110b080050f80141c4002c1c60401000d8040340445508001640c001c50007550350b5403411080c80503400214808800030707850704140b181e200e00042018042d111142c074010036105808a080704c82e0450b82c030f010040c5281b0b4846440d441c00d4064001d0031150b10414a103202c140e9a50100340d0710752204154544e4000392212040c041880c00c2c5401c9908070402070032540c2400c6041031007445604007503070070f0031031580700508202c2d661003e45440b40381143d80b031520199504103404440e0f543d0b2034075200181031007541e00f0030b9003a405240b00104d80c0808508214003000001100511242c0c0e1000541c64485040c40700d43c020450207801 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 417617293 1250 417616043 417616049
    0x63d1b05031210120303150501090b09061e070303090302011a0d031101150314120f04031502091018080102031b0c0709051609051807050c3309010204 66
    0x40954a8001901c0003042c0240008040845941040ca00480e00111074003408001e5840f03514001001ca80041111620101d554051810400784000c148081345948080e9003800d41e007a141300d6103401c4103034560020a50035a1700240b12075000301d4960141036044e00b01d03642180c000e130000c225504000601d8034902c110481c0710b58120b1042060500024403c98805441d120700f440006628021410100403c8100c0c4d03000741c48885000c02d001440300c0c0c061141562000c7c11211440c88c2a83d5007000401d180030ba840050301c44900700c041030314800401d4048652000c40184402140620040c01500f0301079040c1d802e02111040c00c4010400316414800c907402410320a040f08404403c28440b049140c0c042d402048403809000300001d880364581c0511030058003000d8100303450220300384e00107005c1a117550149110348212140c200621310947c107001e4014049141440c1d90300600d2504c1c07403411103060500c00c601d103050080b03142c0b940100045200f10712030384a003841041c0c5070014058207030700442c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 417618543 1250 417617293 417617303
    0xe0121020909070506040902040f081b06070302070308040e0a0c030c0e0d0f0b0c0a140421031803031d01081e060102120c0d0e010215063d1b 62
    0x809080054980300d021a684500d4a1045030441e40e150800300d1540d4002e50310071414150041070070b001d00341c601000d1030040d101c803030000d01600b00740218030350400c03981c00400d034000c01000507c1d00a00d4070038070075080079503001005507a40c0c41e038540004045a100300c43c2c1c10250307031800385a8103d5511902842d078401e40240e403010200f0840d41b081014800d5000403c485040c0e00000701d00000c1d80d281e45840c45200c01c44011503d80100000160851a14014500020364100001c2c0079011040ca280d522071418282c20341101c500d54030f002c5d0f441e110b1a448031080e4500c0c0c3c040000c00c0543c020100c112401301c245240381003030030090040d01e007444d041c3c0300c414207205004408040c800c0006261030303000c0d00520443e03c1c82d1605400c456441c0d4003055100310303941c01602c04504510341010380040320000c00e100500010611302c0e00060440d0b0040c114901c51140700c03c181c0d08d608072224440d4642090707200e81c4c840940030410805010071504008001080d92415002550026140405a81c54000b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 417619793 1250 417618543 417618599
    0x30605061e092d010302030114040305030103170904090b010305010c09030b060f010c0b0906071b03050901030506060d02040602070e0a091a09160b070b0a0506131802190e01 76
    0x21200b00800702000400e0f101e4010584800300c181d454801800c1c48100031951064126035040d40181400d60b200c0010000456810006001c0029801011641180c3c0c00104041c9820b140b046000101d10546840320b40c05802c1c034001c10103000c080041207048900c24002003000c2048030505658500d468480501921001c40005d04142040544c83e00440340515000280c40f981c1e0f40d0300400d0540c20344108107154440b40421105981100c10329001003200840c0c00403a030529a80180301d403007080d840301e04250301c40c8040f034203541324003050342e0304814902015034a80e903e03010021358a0300c151142200c04101c03080802c0b031b8824180f10b2010a5500b001043c000c45a0041c0b040303205000107040024180b18400e13040406480c0410420050000c3c00d000e41d684072060b041a4030b0050000e8501c48406280105200190381d41d10701e8900705600c4100d0100d401c510040244003d491540d40c080d4100403e0100028984012820700f4262804004580000e0f40c89440108903800090140011070440c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 417621043 1250 417619793 417619849
    0x30e070f030311070b030915060d020f010f121a0f040e03030f07050702131b020c10120905060a060f0602240408160803180606030d0f0909020406020703060506 70
    0x108000c41c1414a003054111100540d03184101d46046c0c4c422a407080c0b00d6005001900c402c0305400800d00c0d000101252108007021450b000500010714000046041c040428a4004a14014688182800506082000b5594086007022001240400607030304c140c941398841c800f140391034410b58141d0001c803401141169120300a008001030040e05200c14040e052104200503a1205042c4020303008240000c11910302031420f4003840714400000906540003000401603a03194050002498003a82c0f40018590142e03000b12002401c0110010b0418090741c41001541000e41c1c21400c200c40103114400b44255413201c080341c80c0c04540404846454260700900c410b40d2510244582290003114041d10740fa814496060302064280c500b110041070210411200003002d0b5881e210304603491002d400b552408800003a1500008085501401140e101c02c1c0803551250740200080c1100d000c046558644889010307660b400d1604c0304071139480c2048001002428103451032100b4107414620b011501074 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 417622293 1250 417621043 417621047
    0x216120c031704030c090603060c08040f06050a0209040510050a06020f03040b03100b0c0105180a020325210204110f0a0f110a03090305010c050301060c0f0314070b07030e070f0303 79
    0x801191600703610b00080c0700c08800f0844080c4c840008100d01540055030510350b1401c00300341ea42c200c80c50828040d501081001103400903c14001003540b0000000310f6644081914009001e08680d45801510303010401038070740d4200078000c0c19034204540110712a9a1100100c1c1c0ea65040050b07241950414401000304020000186810000e440764040040b5101c2c00411150307000034600408907034541c02440f00039a80119400d241304a45005030443c00c0e015004a80c1c1c1310800600310360f4a070803640300c2e0300c00b0055030010680a000e141100c0900108605c007807100f845071410302a48502c0c64605500848403a0404450301c207070404030782c03c7c280601001d083d140c2000c546a5081407001003c0d0118590300207000051107244241c44401100c0d01754180542190710341c0c1000c80920100b000188903640d04203c800d04015400b2008500b40c640c54a001c07203440e80d441000ea0360032000890a0400c01c00d030303524100e2150b13519940c1040010a248802c5580703102d1481344d000400e0089005202180c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 417623543 1250 417622293 417622313
    0xc07050a03140d09060c090510140d0213030803090105060a0e060127090621030203030f040507181b0206100501032d020403150603020105191e0216120c03 68
    0x100319540c0d0b00d4201408511100c05aa07618041280c83c59070340c0366603a401c40c0c0c120000310b0107008280d480c3e0040d400080b10203000d203a00018091550040826421060400c540498003a000c250074045000303039503440c141c00c0540050b1010031031542401d00044040c05c0483c00c0c0001c89030342e4079001800f5114a0010364820302024011034034050040001c20207041859204401410200000200343d4078003100c180d56012468030704461083c480158a000c00c0d8004152501710b00741003041c0f5032940700d80c41c2580c50103007a5807000300b2800d100c26817882c2c441c60725800b011020f0030b465655010b102c401d000032610340340d048508180c024030106007400325510940c048a10064002080d409541c2e4001c481881d5542880b0031141d03040c1c0003d002c0c03040003240c23000b061b8446180c034070031b002042c1140e0020341140100700c064286080c011721000040ea10505151044902c000e11601d0340c1000c200c8001e45818882003950720040d180c15000810746100c02d0341d2699160484803800001d803d6661300c038101 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 417624793 1250 417623543 417623567
    0xf0307050a02101b090b040b0301050f0a0f08060106080c03090604110301092001020f061014180406060509181009020102010b031f0501090c020d230d050f0c07050a03 73
    0x14403800484092104041c0300310130940d402075070581c9078074809240082c010343c0190030050001900b40800c110120944042d43d064950440e200c0f0004215000070841050362503100407420300351403400164114000c110300307042c2e40c0f00fa66151000d503501c400c1002070b444191249107140e1701480028010448481c54407118103801400414403d4144e2604440300d03c04d01700500c0f94180e0142e01040b15030b0100304942070688400c000c1c0503a450300c984c0c46021041c0701d1207a84030a1100d40401c20301030307542e0640c810700e80052030289941400c00d4184040200854012503000da081c40c800302703601c00250b001c81500d0340e182c6001808000700c0b009c8440c0c080e0001640803810b6640b940724045155406005a64001a00c11440c112544040250a090394010b90001804a00d08200d09901c1075011550f22282e078020309001100b03001e50b810042a0607002c2d80d41c482c01007804151128003000c00d030040d501410f028841c54100c2c0d00d0b0160804220711138102d000f403041d07114820020009024080c80a40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 417625899 1106 417624793 417624797
    0x1a0f0108040b041506030605090f0d0503060f0103181406070f080f0f070e0301061d0c09010512040f080307030207050123071d0d050304030c0603020f0307050a 70
    0x51100702510113024840b6180c000c45555049420880c011940100704000c07500d0702c020300a444a0b55802c904110740501c411300901144240d00b030fa409804014000b0704524a0030005400600811052240340144492241e001c500440d14105c800010301002d01034502d840c140c002e120040300042c3e2421300c9400d1052116481030885081d5218000101c0c41c402501c0300c0b401039a003001c0c9002d031940c1c150f0912001013410000d10b050002e040340140c0340c101007a1a000040c1140b0300030f0001d0640041c0041c4081880070000030b4010b070304903004815403540c2d10100c0e1102c6005a008581d0754022a03000591042000424030904a80010141005029400251a8003600ea03005000d01d02040201610860071621000c81c03142103c0d00200090000ca0b868030b01079440360801e2200b950401001e141c005007070343c00b0780200d88121803940181031569a41c003005a0b6590809405102 = true := by decide +kernel

theorem cover : BRFrame.Cov 417446043 417625899 := by
  have h0 := BRFrame.cov_init 417446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 417446043 ≤ n) (h2 : n < 417625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
