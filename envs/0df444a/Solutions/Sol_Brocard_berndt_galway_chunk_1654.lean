-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1654
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:04:32.997298+00:00
-- url     : https://prove2.me/submissions/72ab39dc-803b-4245-925d-6019e4bdcc54

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 297302158 ≤ n < 297482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 297303408 1250 297302158 297302189
    0x2010f02010b041503020418030903021e130605040b032410170601060306140d060b190e16090f1202010c17090a05040b0102070e130c03050f0d1701 65
    0x40d00030341c4030440d4800b02610911000709451200c13403070542c941c00201c3c45035240001a00d10381c01003401e1517070b4040d070640798100ca040c00c580810603c1e414051803004030744000703501c9007050340728081c5114100241c0c0c000421410b0401c01008142e0b6200c1e8202d60003503000c04607402038071005168110026601413420ba1942c1c40eaaa40b440744904140c1100304541c801c409044d0f04c110300065640d040351190380d070410100342c942e0340b201c2520b0410a4a1130340240c01c00d40740c0c0b0100300d403a0f014501c4500b0051014103000018281010740740740b5a481100300b43c9106081181c100c0d0248242000070150780340c04030001d410841c194079914403500400c89406203c0390614110390084501301001030300070640b02c45000500306041c0480d80100041402010030440004050901e8000d144010005030041c0007001e003070400070480d00030002c00894248c5031800d2401c01062407031004d81c001d1406840600366039502c06040b507142401140040c000c114007d100e10280c3c0e81c9468046055403001102c40340c05 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 297304658 1250 297303408 297303437
    0x206130b060d020909060702060106020c101805191a1914090a15030b0409080306042f040302120703020d0b060103021309020d0b0a1202010302030603030d020d0c09090510030201 78
    0xe42e40e5050029000110001804100d5400207040c034815069a801c6034900c0e070300c03504226290220f03085015040b404c3c1111003003d45020380d00300c4c02c07110002c440d0303500c2e955600c600003400501001ca94009481d10814207001c42c902d01c0d50881000c010212981d45000c0b42e00050b01d00000c1e049070071100300a034110350710030700c400181c04031000179a0041c5429409620f50b06080401103105035401c0c04a86440d074810200d04244c0100c441054002481e681140c2d03071102400040e120008142c1030b10308000760561104110580450580580d2500064540c1e0541c0b06106050132010348001c2030343c4c0078650410044e03450090604606900009140c1680c6459005a029000e400b4210001c43c0748610081118001e981c0603007040c0340041c0041c00340d40206401e000c0c1d01b0302039001e00c000b4150f00d4621400954001d400440c0c015402604891500c417070648150102e070040b0060205483d220303100c00d18115171140100d005482c14020401060604624101113084103100003410320a242842191 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 297305908 1250 297304658 297304669
    0x11120604020a171f0e090a350304020103060f030803011202011b0605150103020a0801090c09050306070e091524090a0b031f150c061e090c05010206130b06 68
    0x5000e058a083c000240c140f10310000c0b0160751500002c8851909440c0c00a50444900c92040c010501840a0f00d00b98440352640015403800d8480c0054982080c125000070032191034041c8290000c0c0000b41d516410140700040c262011070703201c40c0d40302a00075001d001140c0c40c04201c1e03044850349400007001806900c01a151000358000041100740d903264003405002c01d50b08061302c42c981a445a4940126441c0154200d004140640c030008005200601407107240f50301c43c41940e0f1030b03400d00701000e40d602c1000903d0014211220400251120500c00450a0406041da0800c403070814070548070200700c02203210391006540e40404030341080396210720103032203c04440260034058085000140c4549800c031315617206880d01405900390114078864100e600001d4003d44411240040d0580c02e660b40445541403402029a42c072951360420b150314441021008801d425802e4010a90300381c541085075411406a00580c1590440010050845c1540741087d480075440b03464112103031507900c08681c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 297307158 1250 297305908 297305927
    0x403062c1b010224090f03160b06030307050d090e0702030a1403070c0b07111c0f0809150a050103110a0303210e0706020a0c080d141810030e0111120604020a 69
    0x3e00c100910800242d10081301242c45011032078110f9050150034140c9954074403800c0c5c1510140e040c00e0500400161099580300d401080c000d04482c20070b0300b40d4460758113103002d13050090b000c61100c0c10108103004554410a81c8542c0034009581002c0400c04050130300d1148a8100d144d507880000081d00403402123007011001074100d0001c010301d242413080030f0546d0108403003480c030304d2252107000c002c1c089041081c00d550b181c40c1d03a10a40c0414140ea0181d03480000640245010302a4501c0e60383c0c480e8105079214440d110340400803420354035506204407485090a80c55001d4090050300b0710200e40c0013041007034070b01c824140004002001c0170024006104249400105020342400011119800280700420314081c0f0a0305440e02c0d940e00720030f6034408101401201080310502c030501c00d0541d010103170845010340c2601561a01010300012030a00c0d004190401096407a0b2500e0f040f1720f002d100c0c080c2c41240300c401092038a0003511510700303610002445644502d40010781072000c1c51040c0e1404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 297308408 1250 297307158 297307183
    0x1803081b0102130609081e0307030e0612070306030308061e1e0904080a14190c02060909090a03030507140f0703090b070b0105040c080705070f03140403062c1b0102 72
    0x3030707007203544481004286405c0e6108030800c6e4802e1640c605445420b40d0b01d90a03541900c40c0040d8500710503a5416210800c0709a03485070311420512a01645400050340d1034800d031300c503940c000344c100d0551030301030700169001e804540102c01c150708130b4000003000000480500b10888031a036140c084008044079080d10400b500d070300646202d00b80020020318902030b01e004540390b16030704009241c1c801c00300818011520450200c0f03103100e402072013640c0120000078444d400030b04032900c0d0414580200300060003d60b43d1501c1c0c0d6218079400400c2c140d040c4107094100f48286810a00003803e801e019560f400398005110440d4400100142007600800c2e03484024078005905035141c0d11182094850000244036a900482c02c0c49080f4040c54803c080581c03013162280c40e014100052901c0307180254010840c1101807001c00e03880000100308150240c002903124140c0800d1140e82148114003c100c05103006081200200b04083c00c0310b804500c445441d580300720150484034030280101d142118a0040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 297309658 1250 297308408 297308437
    0xf05161b0602010608060c07050703080a120905030d0c020105091f1b020d0210020a0c06050613020408010c1d0a150509100f0206090d08060607021201020c0d1803081b0102 75
    0x7001d5030190012030454410000342e8245075600000c5140900c03944070018101e0b0000310083c00007800220282c0030700560341c500f40019256044421040319031104d41501e05901c0411841c10403481c50143c5804442c1c0e82c4028451800c124601681e40d05520071849602142c40010700d03c41d180a03032100e500c0f01e1941c1c078410f40d10880e4140203500d5009a40c0f1001c0140030340f2106031101e074100e0003200e101c401c00b42c3d1520813030407035510f86030f00902028054583c004441c229400d94030380140050300c00b500b40300b000000c01c0da10301500501600a4844100160001d00d00c480140340e8441c00e002d02150703400d0340600310b22140e41404580d03030b10030b2000080d4020003526100762015031100c0503030300621840d001c0302c46645540010b00c0da1056040310a10005500b2400201c181c103011014000451000e003070046490040f100031400c0e6048020720301155440350382c0c00c450060b130160f130703018100107a02080344500d4116190007030144680c10368004104883c0c141140314074004d50440b00c040004007031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 297310908 1250 297309658 297309713
    0x40e030c0a0f030f020303151003180b0601030614060f1c11090103061e140604091e1407080a0b0d140714010504080c040b06040b0d020304050d0f0516 66
    0x7421030200d5030000054000a480c40342d80244940004107d90146440802841c005e02000302000a80d884580c0134204050320f0300940030401c0c8a50f050802443e01c01d081c1d240d110315020000400300d0b885544592071458258803500110340303900045840c03803100414202c1d6964000041403000307801410701d180c1140d00d04615a00c041020102800100400b40d07001d100340f5075560000a20f8007441d1090300360303044d0450000c00c074031005586010008507001e04490f041c0780c2d03221a00c10131030700006104142c64441728074403a0424414070560320590300c400100031482c1090940105502c3c0003e04607400196100e0400d104c42e0389079800e00402e03540c400b90390588032517500c00701178840946215142800c6060341007444d8a601800070741d0140d4100e02c00a0a48004040c2040081e121000b81c10750006020800858a6440200204aa410035840240c1d072801d051800903e07011050717600400301701d012400029610740c0f200894881d240700c111403401d60b8542d13060454540c0d4088400c6180c00d0907081 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 297312158 1250 297310908 297310913
    0x906030c0712030b010e010f0201150e150405040c03350d0b120a080f0906030403171b0301030b060a0e070201060e090c03120a030b04090b090606041109040e030c0a 72
    0x41880611800000303003808207610b000d80545000d000c1c4e40d0701141c00c4500c005074951250204280300d800c103100103d850384800711010110415138003d00c81c5007040608001418280b0040c145004600352820401440e0984ae004101000d5000061400003411642c41d80c007402c901c0715951400760400660713030305000510400d01c641c0c0324841e03450300c1c3c6040c410010345034503004209141803040c250107000d500c02c2d19034a80400781e003e042490a00c220a224101590310341c0f201440c030840c86522401c00481c4481100c1e170741520b006060341100c0c00d1305610310b002840c0c4a02035904483d0701c88400185525000b00003000156103803c082140304210301000507041c0c0c1508020211003070752404658030784400d50880e8880024541540d050740c843d0013400340d41c046040051039860740317501d000614040c0301e0000405840b00040706681004401c0b050080381c050a005803074002038112010031401040c0f091a074078600805040c90300c107070b58684a1120000c0140304503107d00c240d4030156091040b851 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 297313408 1250 297312158 297312181
    0x71502060612150a1e0c050409020904020c0d11060117070909020102010902131d0a05030a0530040c0503011a151209011505011106010e1503031801030c051c050a02090603 75
    0x462504e1111200c84c614019032000611903800a46c0c219901c15141a0400c048040030b5405100000d0304207508200b5044d050f0824048500350020030342c0d17901140103030700b8962481c20710182c00000c2007122000c50711542e0800020a1400c450f02e0710b1000c1415812800180c2c01403c5c80640030307402c90381604242c4a00701c10b03640b01e400c10141d00d02c0c04103401d4605c9284540d440c2403600b002084c45c1d20400401c03058500034400303040c45594101c0100c4000b40a801ca0048800080001c1d40c1d445144106200070000c80e00040406054180d001304a000300c10048046078002e40c00c0c10900907840f9000d6001d03540921000c5500c1d001c444a1840010308202008500070103440070042d02c00d031460680461203600c210042c4e540b8080c4000105503590130603001150742c4601a010100005d052908031189880510180841d6503c000c0c203004404d454900140a441420708001c0c02c0020800020b8429500b0729018214107240d0840059503030b9900da0080700901c51400d05950110002c010401c080c03284 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 297314658 1250 297313408 297313421
    0x51608010c020d0e0f0a210308160c030c0501110c03070b0f0f0c03070e120d0801050a150518040618150315051504020301060306030203071502060612150a 68
    0x225008000315862031400b00d89501d041448640040c01e4402c15902c5403a01d418901203400c4d0007081030384260365512a00d40031804070038500310080728a524082c10f1540084800d1b80c81002e0f02905030280d082ca960040c4035020070800107080c44681d6411400340a401d61025408440080f10a5921440394840c00d17640d4001d01c0044901100f0309001402100d05000c5460094010710f03105019901c82000c890002c0d00010002010000c1e18404030b2042d035104050f40c080c103004003001e0007203481c14540003042d88805800160013090400300c02c0040e0f1061030740c0080d1114a40c44e01c251140442002030b0030085403030841c554001c1c10400d000c01d21602000c00082c0042010404000501c50345440700c0ca08030301c038400508440c0d6400c050140751100f40d0411036019504a006865411691000800300d0f0001e03040b00c0002950351400b8001c5040400001000c1d0250309a6218001d0540b07100a40d01e540003020b850040302649003810040c2020030040d03400b042d9042d8155041d2800005101c0103011 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 297315908 1250 297314658 297314669
    0x11d070509100806070f032403060b090103120c020301110301080d020601170c010804080d090804141e010e0d050106080d30021303080409060602010c050a020d080a06030516 76
    0x3060021030649240c81c01a07000300ca00f600090103460361600c4040d1041040a01c1c0c030020704d600e038a549003914612694a01c01c18000c0100004010b040d410110116020100303050f0107025014014000f04038031045200c000880e500d0560b0f8030110034400f113409030203070b0913000030b4180c008000801d004201041690032520035030700f15003081ea6210f5000c0d070440140310400d00c0c43e40000e03207440c12035403203101401d40c005e0084c5a014605014046042c08440342050300743c1c1c030040c01007801e01c01c3e040c040c0d4800c2c915500455641081c1d014070a0028072082e81c1d808403e041c0308421544201c5511040102c091181d0801c008000803036076080301544540746655007000086807188164052a03803100880786888007000409581c4100d41c4542c0c009500c00007900c2104d881e60400040013854620050001d40314035003020071140e1905e4000f0b400c1d50103280050090010a21107038050341c2d4002180c4000c03c865140c40005ea84909105d44000c2c0750641000c0c007d0701485000c440100500201d0710110340 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 297317158 1250 297315908 297315919
    0x50406091202160e0a110705010c02070f0b030112060b0913020a0e0f070f03180c050a090b0603071b08070f05060906151e040204080615030a02060a05030702011d0705 73
    0x404660103c0e10350701c1d10280340b5051104001c0912443c5190100940d1010107244000b480051302d81044500d9008880c08940c140e440e504000e442c1c545c148980c40c0104000003000301c0f0207040c070780d5248103400140a560702c03440a110006043c41000d0300420344080028244140343e0402d20b010040304e000e5503109902a040c0f0020014035600c946103020301c2071244490100140e201d001081302d2040d0012001d5041540710101c07065485030494032400554401d154541d81c0900e410309220107071050f035010360035251411270065216140e14040300d50000700c80c0381420449414040044800c407402d14050960300c0e011a21608000565035900c61607030180d4102c6026a482100507580c81404403262070300510300f040042032038101404080b1820360340400f0000406003010100b02282c1050740003a02951288091100700d104041c9103200c0402c0a401514540c0703920b402181d494804c5401d103108106002001030100c500c01c0d0300004080c070700c02c0000e0f4802e0b00d01200c0c1c280d5a40e5180102c51082 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 297318408 1250 297317158 297317183
    0x2205010503060f040e0a0b1305010f020703020307080c1204260604031e050f0a05130f05100c03111203070e040204141519030507030b031b04180605040609 68
    0x1503010344107a0b48502c500030400d40e1100d912400b0f00010300241d2580180910642c240c0100065484107054850f4601d9030404401e91118213244d03003540c22100128501c544100310042c00700354040102c1e4200c5801540c080c0d5107824400041e0301d005c00b4940c00c9612442c0101d400300d0000c4005c2503500402c80242c5110101c03600c0303281940c5e11560180c600a0200b089540f00390104035403c1d0038a280c065441c00d0840c1008081d01003071885910400c0c600c00007500000702416081d8025044101030b0040b1140d42100b00e00340004500d664025100c140b003804000c015080815100341c160440c81182001940c1c0581d05075002c080c46500242c500d50041084011000080c1c100b5209941c01c850440c03401d4054410301c5010711035808050040321000030380400c02041844110490034118404640d4001030034541901c0c0101203880f42c2400364400d803c40308140c400c2840c171000c075260100f42110002181c120031b694414582a60000c010400b80c2401c0800040c03150079408403284c0d42c060036100540 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 297319658 1250 297318408 297318419
    0x4050c0d0c0323191107020d08040303021c080f1b1602040c180512030c06070c030f05030114041104080a03020a0b09070315050907050a2d05030322030822 68
    0xc402200c04240d015440131640a068415030040d01004c0f80103003000f80b51040980101d01282124201039440074000502042050350402602e4903840704c0300000c040b45038800000403c1448042d0103e100c4290900c0810210811002e1143c40340950541c0a03039500b02032b000700c1c20441c0100d181603204e50b24041003004203500450784030114100c0f4152442c0030b142800100150b820410120611030b120501910072a20b500708203007030248099444048480d0440c0c0b40080817006028401001c114050004001c00040f440703003c050540c04071000708250010042c401c0182c0166071080c002c0c0d01c602140320701072680201d86401c800d405a600340d4003075569484440e40e5030619100050143c000c01080f680c94950b40e6028a401080c200309442c201c036960f6000510ba29000e400c0303010407600300005850b401c0c1c055944c18600060644c8c501803120b01d17040c0040d071240117045080011030b0b404201440004411040742028540c400c0c51281c031131171100001c6203411184180010600c0c0e004202007007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 297320908 1250 297319658 297319721
    0x71808150601030b180907031403070c050303090603070e01020a0501020310050109080106030b041b030804030818040b0307060f021006060203031014061b0a0203060108060613150504050c0d0c03 85
    0x1070070313100603002064510520340e906440110003444d181c0b15006000021000404102510550205100003980c0700d04480c100a03802403c60360129109500c2003005003074039222a0300b581d511641600306126001801d42c010307420441e20406c01001fa510000400c00e4081c5410b20140c10f884081c1d139818600b64550100e14221015800007400310101c030707400940068803140c0c0c10f518541981040c1c41d182d41c1c0e40d0392460055002904211492032006c65a6441e041a081030310002c2c400456060050340501000710307489581c2801a403041104100691000e00d0081082004c0003075114010041e00f55a42002512904280c0d844450701c2032450001498a1541c036011540c140300070420340c40d1062414200441c10401c0e880106035024007100c620250341c062180303500904581003e04420700d0034400f001102a450401d44803064a409070b401d5102c802ca8040304151070042e1400600c54440342040b59481c040c040800350140e04001e02182000d40c19040007a8144c6010300c080b11030135020b0150f14 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 297322158 1250 297320908 297320921
    0x71d010203130308090604030c0e060f04021c0b010203121003030f090b0d0203042d0b010503030408072c16090b0a0813030e0307060306050315130b07180815060103 72
    0x8004100b071000600110788100000c00036444010002840c2c00d90b241c0d03034098220340640c8241d0140e04180104a01402c2502d032004074072034216021480c09038851020301c09013240203481c44030a81d440d4404501c4e80d0080003150101000c000410b08185401e03088544c05a400380030840001e54040403010110b0301400200060340d456120880c140450088088001d400040c01030f0b9114000b4540340e40350354031500d40c0d6000d0318400e00c3c0c003100c2d008850504a0518006078086400384d0300401041010460100d401e1080e10010288000c1c803801010505810b00500e501c0c0d9095451680180300c101e000c1c6503040d002c0302031582c5a48481d2030b0795000410b96401819007140100301e26100048103404044c801c1c203046403081c00c20b5000045d00c4404240b6103c01c94024001082c1d8810341481580b03810854607c220466680140c0c15140c0141d003001418882040144a00741e04004a00c0e40c9c1d001d0400c40003c403035010307100880160f40c1e51450b40d03a00c4010307040c0d1408800303140c089402c5520070300544 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 297323408 1250 297322158 297322177
    0x9090606150206150a050a0e0a060501090501050901080a0207020604120b09190f0c0801181428060f05070302190906091e12111305041e1406071d010203 67
    0x3454a6541d05440034048111021456031040860001048a6031047c0d03035000900321844404030359150001c0c7e803508682003500103d040c0614003608014907a409421100b0415080c03800350200d0715030b082c2d000701038000e0404c025803140c4003142c081641e0822041d04210103018110000c0b10344c0381c007041c0780c0d00c51a882242c188465802c8510002184447c00c818284511401c560400140c0d5080080c2c00c42e21603012042d45d8013410320303207034081c080605103a40018041e2005801d034202c035160921215006603d841e90300f026a0401c2d00d050220507485520f600f00b054600740078920385120010000c0d030201e044c0d1004030070225290f126080c854127a44090319000d444803030f140c03802c081e40800282c0f032003081e0039920680b008020070061101001d10740403511a40fa44084001c02100f0442c180305604101040c00385403400f00301c00b14806011141c80b202d61114031140119041c10300c8136031209000d03600b1510744079640c284086603a100891500c11800603428000301102d5000481e102d2060910300f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 297324658 1250 297323408 297323413
    0x909010b0f0909040f0204061418090d081308030408090901080307021003180c150915020601060c08040b03040b01030c0b1e0c1509061012050a0b06010e0a090906061502 74
    0x2d0701c1490a10701c0907290028064158003003a00050f40c00101034030099000844d25040742d4020041c0d600b4803406a00c4c1030a444244102d061504001540d03440100d140900c003000285004201c210104850b22509603420480b110b40d00d2030b05003851801580885100c0c3c1c042c0a15500009500304080162849a540207010390f49511540c1c20840103805103118650402da41d2502da00005510458480010140d0700105080701c038078510082e02c08403d617445880d5460032400d003541003c1c2e001c2030361410342d2100d0030104403540b02c1d07040c2201d07240074030380045905c410004140700501100d00c0070309040b01d01c034020a1019646584040c15640554481e004031061043c0b18107410710151005403e0203d01e5004981c00004040300300c40c803035501507441404a401243c02d100901012104442c050144680d42c91000e50242d40c03441d03a42c04403800c02038040c030309540c00b080c0303240c3c400c19441c0a05100240062080c0b03803100c4105d4018444444201c610600e0082d000032a00c0c03040805031040c00a6401 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 297325908 1250 297324658 297324667
    0x3050601091205250504090609020f04050108060106050a02120315030c0f0a0512031201060804052e0207060e0601142d090405030c03030c0405091e0106030b0301150602030909010b0f 80
    0x1a04240c946072401c84000399132640e0045101d80722441451050b41c01084e01003485d8485005000000001444441c011030514006110400e4009034450440e00c4034948690384007c00e220413800c200c502d06030304440a40000c248102c55081c00c2890444100407070a80749500c846a080107181812002c101d5006005080b04012615002100400d10221042074a241c2a04803400214810f000d80122001c01c0c07401013844140b22041100320b051000c050404480c080c11b00c0d5001d00c80d0f40c1131200e030391041600003d00c0c00400160343c0000001e01100f000b04d84035035840b41c0131444428114010580514041d030484c454490400700382601c6050020202c440740c5410314140150340d24010402e403268402000184c00031030080000718480d14030144a5030b200e0b8105020008180301c068224038818488080e443d100c06564030400781128813604001411080b0038002c64007414440321030012080c0c91348000502560040f00500260900304d5142c4050b80e00c400da001207034004d20b0035208a0541c10710 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 297327158 1250 297325908 297325933
    0x30f0610060e0a0801060303210506010804060203070507020907080a0c020601050a090e0f0303071206050102030309061f0e13111c06090305070803090a03030e0c011b031e03050601091205 82
    0x1909a4100100500031603c03a540340e840c10340c01d44190740d2045001a9070384980c41d1903c49401c5000c601c106602606000d03a00304403000030400c01c1c1c0900094141036001022405c10b6028404035000c99074068107014440c42c0c1488003800045040341c19403401420f021aa81c52a0700c0814524107031040100f000d44100e040c2000b04004081c3e84030003007858412209001c620725000c0018610a903510354480d00685400c013900019075540740c0c8094159441401072100040c00403a28552001010b40e55603510303060240c82c0179201070f05900c582d202c840d01c8010f1182c2c00140e00003014425000b5682118001c02810501243d4400a84101d031103d00c0c810703600000500359002191920302903c0c1150511105032140c907419032098030b210401e0b5024814800406816028404450000310060584ca001c1c0700000b034000d0383c4628000c0d00103009120100101800b4a0f400c0c905540030941c1c40c604024201d5014000742000d80b101408142c40748000507100008a070b02018896124018220308003818 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 297328408 1250 297327158 297327167
    0x608090102041a0c0a20040c0903050309010804081306050723190606150e03010608070b1c1d0a050f0d1202030601091a070b0f0c0301030b04030315060806030f061006 73
    0x248007004607008170556200440c2c1100074029000c5802c940050a04d0080030800003202d000c0f102103000d104423000100041503010064403d544000e003007003c840c1e0b0321031500390410b106101c80820f000e5041000803400c644d001026021503403040740c10310b0703c500c4400d03049250110f4420300729490303600c00055404000b07254140007645620a500c08100789850340380b001d02ca562030b01003401c00142c072880c1005e402e02d000d0041c00000e041100241c00020f003007401e07904040c462074950100103065031444110410700c5901030848601041019203802a2041509031100d500e04000d5580d0303c90407041d05544070020039480c03c491407079240c4040c8001800707201030194000904040c140250300710005041e080110401c450070120f00e101c190344054510300821540c1d8040c0800c0c0f42d20001e0820404044000c01c01c90b0305481d0404c0c0b41c000b1a695614048024050110040011040d84400003400603000741115000e00011010340d014000000401c641d11842180c0e24031449403034003020014540035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 297329658 1250 297328408 297328417
    0xd050f01030b2206091a280b031603240c05030f1312200102031e0903040f0f0306110705070905060303270a0803071109070c1b0608090102041a 63
    0x401c0039072490340f42a8844204a5100741400d480031791107032030003141d42041c0b1007032030b5031048040391582c9181040c4c1804002c0c84c013203204038005c0b8a0b44e404129084d541c0801071940a0103043d500350346a1074032803812007a240e4161100a1203040394000c5103c4030324482c01003142c0c40070681e81d0503003035580b840328020510f40c0141c81c880441505c40d28000200e00b20b4407100600100075242c000741c400144100c02000300614003c80c403d079105006224040501c074004281d2081c070200341d501c85071650641c0a040d880780d9404041c0740c1b100b201c40060702850f03800032102203034000c2100304034918400c1c051001038030483c08020411780200600b800700e1552a4803c076000100a01201e0900c0f1030b00410502c4000403401240070003c140308101c1c11490184410806001800044e60611100746d5031803111040d0403c45900ca039582e400019540303481080c0d500c0213160000010120103000c4180414002401e0045500041c0c0e143d0000b01501414003c03a400c0300c0c07442c0c5a090003504000c90138540d0303410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 297330908 1250 297329658 297329701
    0xa030203040218041b1205030304020d0614090c0a06031424040e010e0c01050a02100e0a200301050606092d0a08060f0703140c090d0c0b0d050f01030b 66
    0xd0740300390f100030405980b240d220f01d209242620b148204801241e181c4002540070710f5034980641c1d4030300002a00801665046981510240b10441c00c6141030380180004213509a00350302c0d44810851350301d80014480f1800c1344151118002c0e00d445101c21030a41c0c0d00c003003949141190b004041141e0800b801030403000780c2d02d582000080c03c401c0328001380681c1c00c0e2140f480030a030345031034000f68a5030050043d42c2100b9070074200286800d03400074001c1e45503140050b80e80ca80c1907469041d0000100c003486189401980300c111000c42206444810600d1442907031014003a610744000600301c0d003004002c81c0c20b2580300802046880345620524100341404240b03e1214010403002c261054a410a00c60090b1119101034845803802e81c485108102c0c000307211004150801c00014842c0f111020100d8004a05081e1140d545016501155410204101c000c0070500643e1000864008020241951006d001000d0045454503032099140d400b084c0001b411210f82d190100b00c1140716041101004c44 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 297332158 1250 297330908 297330919
    0x50f01060c0210030b220f0c1b03090b04030602031806010b090d0f06050c0c1b0904020904211e0215010b1c0c030b100216050f0102070315090203150c0a0302030402 72
    0x45c0c5c03600203d4044180503151090b030b010303505114407501602e4096864074201d0b80d40104040c1c50180c1d03005200c072075a841803200b00341c5070324141424588502074004c05010155000f41e41c441d96440c01e03200030340c0111040690b031080120b280c84100800b05486040b100003041c020b0801303e41c04208030714281010411520f400b250500030001076000d02070303030340b02e2145c0344206074813070003032044860812884203110000c1c0c040c03184198002e5502ca40107260425011f0718080c240e0798480c03910751000e00a1280d2031030300d11382d80c600c0a9610350b403060340f0030a0340c0b4508102041c0400da0800981c0c4c1c40a1b0406203040c18141c1380010b001095180e006004100041d0740301911030010b001012044598148222000035111852800181003c4c180c0c8400d1400602c020300d0100c00b800b04111000c03001c2c0c02428441c80a40c81c40001c2da030301c2084210041e54015800350094092620090020000d0340c804034000c0c000d041c0010054210240d040c0e100714004654076290000c180421402544003d204a030705c032 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 297333408 1250 297332158 297332171
    0x6040c0509121b10050414061209060108190b0f070203090613030203010b0105190807110d0810050d12080402131a010e030105100303031d010c020a06050f01060c021003 74
    0x1da0311082d050544002141c09060360700e00290707462240c1c0500031841c1d8011115803940500c0750381c3c00707401c440450fa9a0600c610326004e01e94000f42c2544602804003c21420b00018400001c1c0040740756812159980c0c21101180ea46006c040300344981000d0107001603880d4170000b800c01c01d50b000c205901c10101e1055924120420001a6141c3c00c0400042141610440c09004500b02442811014002428014100340c40401c1061021403c00f04200030050282e011810150007a81c5064402c00d018054804841c20814005d2211000316003070030402d9103441000415081c4000200505500b252502c4101c017645101540e2002c130280017240c00c07103100c0c03002211900c3d045c4a16210f8030640c01d0005c0042503030308001040c5000040bd5907110364900070074020800701403100103040380e501d07081c00309996810310704001c0700b4201c1800c5039145508080d0401402a404103482c1545ca100300c20420281d201c01512040c60b20090049030301181042a07041c1c05481c01050100c00b401e030914020414 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 297334658 1250 297333408 297333427
    0x70f030b041d0a111f050d092306130507060c050f0105042102070819030c0501022b0603030207170a2406080c0d0f0c09050903030402090a05070806040c05 68
    0xc0396001c1e002c90941080c0c250008001c02d1032000020000105d401d24041400c64540c40040e140100e540d03000c4c44800903541d1021886d68003d200c08980090041d400802600000c90740c1100703080000c2d00c0c60140c000000e141100301d00c4500e0a094100e130050241d2414001c0644001d03d1106040d0784502c10f900e012021703c0424000c030341c45184580401c0c81039442d40080b030300701a914444900c0564001350028001a03c0c0000e98004a13084900c051421540c2824251717481c0c2840100a0425400010542424102023000446400502444d006400d010540403070840340c00e40402001a0002c4000704036091044413000c0300841d2080640b122035000b503941a0000c180d03641a00421490002000304013032035031003a54002c1c81224090a07009011000040d024181000b0060805017005174043c14401c6403000a405400c015400f0416403d1031410580d0b603400c21102248500403002c0010815066070291501600b040e4903582e045840e94010030024042007050303601008024400140c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 297335908 1250 297334658 297334691
    0xc11100606030506030f06190b04020414090f130206030406021b0d020c060f03010e2508041509032c0a030b0415020c030301060e06120c180306070f030b04 68
    0x5481186080004019141c1107010b0183c600c02868240710390044032145984420100c2c0d07040d80501d001d00c1c0c2101010b01d0101c441c000b0304800c0c07031184e0494408034004c50407101c44440840b00c0c103000c5549059560300d0f40e44400840404403050401305410103580b0700103050038000366400c280314150141c00c04041e80415400488102410181544600a4842e15503018840000b851078255240c91900b01c00085c401610f00c018420000340002410014060080202d03282030480600c3c40e514000c071140c1d031350042c041101035605035001e9000b0b40540901e120076100b0000b031154561a8400f04240e10030990382c440c541015080d03052520000307900121750b40c0d040c19a0145200e03081d0001281860b091201c0e145840345103940302a031040040791840710707002064904488d1149030407502e01c00e03030b03e0104031940074104c80c10703a0310480075084c40707244031242010704210f1100551030382c0361086040416990340c0b800e0340c131200401c00040501000c41e220350402c1060b0310000c2d101040c0000300200d02c0701e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 297337158 1250 297335908 297335923
    0x8031b0c100606020105150f0a0503031306030b0109030c14120607020a0b090c150a020109080a030209030f0c01080c0d0603020d210c020906011d04090c18020403150c11 74
    0x440e40d002205501c0c14803034244108809460944001c118924141c40441c9103001c40c241c60a11418480c5d0440e9220390350305441c0c002070400a0103a9440b0030b9411400301c1d03081518010700c1c011a050400c501001d522442c102812241c0040c4008045840c1c1602c41140060840c0300d5070304164a0406030f640e4a004200c6980528055801050682e015042071844148040c2c110000c98208108011084da243c0e188044150301850700c0a9440d04991010b9004202e0008010103030f0902081301c030040358165000e032824000540544580382040c040d165165242c80440c94003145410020402810240010702040030142100040b541c0d03c0e034002401e061105141102d040398403004e07090b81604080d5098440031460305241000c03c0051f8000740c4071908c01040b00703041001d5000707000350003240624a41c00a1101400c204507000340c0d824442d407003a085004555980c941842c2c0b2103001a1030b4400c0b182244c0c0c01141e0348040720854201c1b0000361149142d28401c0000d00045240300000c01c0c009003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 297338408 1250 297337158 297337177
    0x40b0a0f09051b011d0918060916050103090b010e0c0706060e0a151518151e17010b0f0f0409020405130203070203030a0c02070807030b040501180f08031b 68
    0x1042d00e000300406614290752009541130401c0500041800085502440300710b00c40c40444207030f03640e6a03031001407241080d0110503900c042d1180005010081c0d00204014072522000c003440d24820b034640c8010340030381d0440b407002040440a00010805d03c050141c140d03400c62003600fa540d10346400c2e515940260390385504400c4001000c070042c0144180288180f10745000c2900a400c0402d10348031801c0741c5020308911321b100344105483e006100c040342428840141c079101440c0c106800032000d00900342e8014000b024000b0300c2c2c0e00306c0d10b08818054030076040c03104050b85640180e40e00380ba84803409034008840c0c104580500b84a541072030f041c42400317007005c4c089080b4010780350303460b1030100022805010003043c1140d1041061003505a804001c032036000c14641000310302000d007244100c0c6411000e0b40940341e10302030740d0f00100401018282c40740c020381c0148028001880f07410549040c100c10710800a02003101450044001203055002d0b607440051303030215120744183c5240d0543d082d032100042 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 297339658 1250 297338408 297338413
    0x6030307030c032f0c0a08191b0810141003030c1a2a0a050901111e010e15010b04260109150e070509060613030f06061517040b0a0f0905 60
    0x81354190f4104010200f6450030032224240d8540c900041c1c0c0b501d519410f048107040d20560b55941e0280040113400107602d8000000170300384e85a03260551922806a180034000e818101605400d845030b103043c2080c05885c05240c16240285103a4060725070000740c090460b1800e4188440c00b0500700b035900c0b0548100e013022040205004095582a201c003d800c807066002141480420401944030058868600d400c0c20f125403c0d03039411841d945409510740148900c600e41040511501c207041d085040034440110803600480d8103100102e55202c024001c5141108080c003040103400d055000c14030301450b01036048105210380610813400e6481003182130302e44042c400010050341040d131041507103100c0350001410300c15050400250b882c90000d0314040c0f0501020400c1410300640d200c41000450340540040071811072454550050006440713203412100d110b0303003848600c60040f10f008611310030181d080c201c50758803551008590341e005811030070403c5e81d541030348400760200d2160801c0507000703000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 297340908 1250 297339658 297339737
    0x10e0403080108032109013b07120602070312050106020303100b0909010611030405041514010c05030a0c0614090a0b060301180602030408092d010806030307030c03 72
    0x30090151070040e880003c65900070000c480d030000481c800d1289510100c2c185070b8003900c0b10004035002d4080341c0ca40e812a070700d0402483d80200c07150b10030341c143c492801660810405071b4100032500d5503a58070804601406000c035460006001d60f0061065070300c64185402801c0c0c0e001c5804003159800d811200c013580c030010610078808100c0e0407810040030440c0308a8a0001c01c2c001066458a06103c0c0c201401806000d0503c200803d105460180c10058005c2081c108803034684402c0e400c0c640b0450052560b11840048075500c03511081d00311a400038015032a100c1d803000100d96044141c2c50949080d641c85002d62181c41c80207009501550b588402032075505180d003044a8041070140c030445c0309a2401740390b0b6454007a401021614540c000400584035912030030108038500c200008103510001ca03121000020240389440030324000121090f0251013688030056400c3c44069036100c1d81030313109000140020748140401007000b80b1034505403044000b00010b00307001070705211020714114600740 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 297342158 1250 297340908 297340913
    0x40f020a24030b04090f1704090e011a0f01020a110402090a06030209031606140c0304080601060f1d0904020d02030715021e0c0901151803080a03180b161106010e04 72
    0x503d9149281151304010403081661202c401a11005008295841c00900310b1009050102550300510f1002c406000011404100ea80246400100203264082031034120310350741000c6445400021068004114440540d150100180c0302104210303030068082041c00c00a0316020550001070510340c5001d41c076003244104140c01c2c00100c120206200c00038850422449074402e01490140360425481c96881528000b00c504510468000b480c1ca8816000002099075100c001450340c1c5c10b190740c82c510607032031503412014803501131030701e43da4400120030100f0f000d450302d008544206440181125503031070342d0b00c1072401200442219072000d030708002440c01e80c40560801034400c8030400b10141041443c900c0000c0d01c03280c41070089000c1803007004502c84055028600000380c050300d2883d40b8403c15924070784030200d075000001c0c080009052101040060055604d841c00d2150700042440e03081d96101081401c1b032075040c0030041041030071580055000e10600010f0b001c1c10480000e610189080d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 297343408 1250 297342158 297342161
    0x3090d350901060f06030b091f060e0127150e030c060c3a0503130803130c030b010f0803090f06030907090609050105040b011706100c061509050705040e040f020a2403 73
    0x4119500e270081410150414101c45078a25080d42c1c96420608070120003a00121041008104241c4541440f48240c10580c40200458411950b103105100d003580d0340260102c0c0d000000c1d481458240d03225a00a02191420360068a4046810300488031111802080070000f4444522110400c1850b000c4000550441e0088080e139200c10703091240c907608046030005428060300c40c02030301900d000300c00318000308a1121b031040000c1d0030078200d202a5449050022800d82d0a106080440700d12120009e81e201010007640c6500600802d408000e51843c402d10125610080844030b032805138010104a0440c10300c0b6000c040c2100d00d0300040d2941c1080f050108071161204068180401c0e0004455490703c011000390740460f0584000c002800d2591041d01c65981800004000d0703810564407602003c007001058088034210324050046450740402521a48568012400d03070540b0200014042440b0502c1400554070107407a01c1082e95a03070440c038004c60140200c1503030880000b0540d81180e58103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 297344658 1250 297343408 297343411
    0x31a131e021003090b1305030c0d0f02281506210c081219021e0102070b010b09010504090e240103050d0815090a1103090d350901060f06030b09 63
    0x15080404c88a4543d407214071940c1c100401c1d0010f03050b83c054010302000414425a44520012012551071455461b07000d014204d060000710018800c4420103160688005000501e081e49028814001c440545031088028400d403403003200d041d03d880d000203a46000103008001c94001080d5600308612a103407820416240e03510074002ea602c090b207555083c4050350b0440740c4000d540000d00c50300d256022416801c01d10005050710340c981c8125100d0054078030640041034460b11070000300a06a803101c4030040c050250a500e01e002039803e00050295004a6001c0024503403918100c03100340c140341080440c294001d940f8000c2414a03000104104902000085c0c0e841045081441140c80c200c01880c0b0140c0d0342c80c0070180b0400b0808003088400309140c0c004c108003045014411355074a03000045680c0c50b11546d1441c000114007501008400101d52a200c0c108042c0030a8581d40d42c9043e14180c0d4603040280520502d550380d080e0010300000c00c151035800903c3d66032000f14111700180204503010070b0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 297345908 1250 297344658 297344689
    0x16110d0f110c0307060c05010906060306091103010c02061f030f0606061d01021b040b0d05071406030c040302040b060c060a060603180b010b180301050a090209060307031a131e02 78
    0x401d2031030b429a00401e01c001541c0b468034101d00442614106103014000c3e0b00006090030b4a0035a0200900940781c2101e04640c2c002c0b4048001500366006050803903a21895010050308000042076840e812803242c410280545410f503240d068880e150940340301c250f0b1004071000380da129410420300d07800007690000c0e40460b40030781081030320600010351903900320710700c0100c240d02d1481008501d9036941d1200626183c0a410560340c1c80403450442d980b070009002d62010b5142c1900c100805113010001caa00c102107007032810742400e1a541c207100142441090003907004030284440010b0850400a607445407040e2400892010714107080681103c0c440364000000100c58a001c3c0049210300f07030ba0b641103902d080d640680e42c407030300105c400d9019044003841d5459400e000a00c0f03140d020540001c03103014000c035000c44064a80100f01550b07404107110051440e030030b1000b04035400b4814614154840e200340c000e40bd42d41003907a17800c140d000320843d104551440a810035419820000014500c101 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 297347158 1250 297345908 297345913
    0x5070e07020312100819030e0f010507140718060603050c030405030a0f02010f020d0b0301150e01031e0b040b09210f090a0b04080304090e07030b16110d0f11 69
    0x5020900035180d100f0006040800040c034008104c4003214540383c00014200b41040d01c00300038800714429400d000c05803040e0000340d03840c10381c0000c0d841c00c0100c40380224030586405240c40c546a460041c83d801e04800804203003d09100050100d449034206ea0b10701c5d0030b81e040060041d003000d00c0a0111a00909401100b501c24030421001980000c03c403400404582041c002005400b64228090100c1201700b00380039001003150440c03c4d10603000300894810480c02808440340e0300b54040791110700d0348541a2070032946001000030038005c84e207000c2d903003020b4807000030109c490b40c9818120307010580341110058041c508201c40803a083c0152451560108100c110784010780800101c54002c8110406650000159401b03140d9180d9210000424110b88000e03140d80d9a010243d40306d1b0880d107e502d0915040c2034010301c0411000c50b4010a030380d071118400203140c41e0300c0c07201c949a1000c00c1d0064140b180f403944482001108002850003802c696413040042000b01d40c008040e084009011507055 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 297348408 1250 297347158 297347161
    0x3090d03020414090406060b0a0207030302070b0a0f080910021201090b040c020d0f020705031c08070302040302100c0204090203010509030316080123060f0d0b0a060c0c060806060d060b0705070e 85
    0x19120a2100040700a041318a00e0702d85e02c56082400041000b0b030702070780072058005100e680c015004600314084038065004c0e4bc00c040e5880200c150140300340030b80b100025181402c80c8241c070b402504010713000041907044440d1146580b04001c2207074440c248180318401010010000c00c0c401e0b0191080e0f036101580c091000c904144400b80d0740d1020307592400c0510061240d16000c1910800000c00106401011513a4008030303140155a603a004241e00000101c03010009402031780070f4000c64003101e6002c3c24030311000e500d2104c111800482520120303801070b00c0d00c2548025950034010746010310080d00283d030b92030414420203482d000c1403105a5040c80945401008800c041c103080006d164069800340e0395001d5040c0020f8060f20803140350032401c010104400e04880d40e5a03000d04441700b426030b00c800da55510344100307840500040000800d0030f00d1a10041c80541d20424007550040f401400766410501407131442c0040d2240c60b00941100318020a904080c85402c01100c002060340341c003005081e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 297349658 1250 297348408 297348419
    0x40e010c080406020c03070209040602030601030e06040302030d0b040209060a02010f2301030605060402070b0108010b0a060c05060613230f060f06040b0c07050d0506090106080d050412151103090d030204 89
    0x407000e0007031010b44402d40c0030036a48400e600034000c482800e03900034020740035882d180c0342c80002034100380c850350700082c501126070401a1001a500d03001d650150000d505003010f100d0301c01c015020072a00c40f50030a0b024025982c00e0b071540d0015283c502810380011134181604915201101e01c0c00707141450007803e50b011044241c180491040c15203401c2240401c0750b07507a14010501070b10902000901c1c00b07111100000d03036101c1c10b5100d009404401c503109501d0340d0f030791401200e164280b80406815a000140031075070514244c000b2040c1e0203580c06020441d80b403150404410480b0205009440c0069442004035207605a88029440901258801d9a808008001c9003090250340113000c400d1038009a8040501000c100da140140802840c00e00c2d40c45040c84e001d0345030502510107040940c24100c0105204030040303400e881c40790b903035516035050070f1405048040640061300140d400c1c100300490b075078440e8518010310004441c06012a6500c2c00d291000e5854416442144001c162042c4804d02a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 297350908 1250 297349658 297349667
    0x2010c080a020315012a080c0c090f162001060501110d1b0609080304060e100603030e10030212150a0803160b04150f0b030114040215030403020f0109060902040e010c 73
    0xc0c4c2003e191104d00b0380040700d0000103c0c03a254007811200031512291108001e4100c2c01454000010344c00c0c1ea030500c041e0800d100210384103849500480e2034440c00105081e5280700d01103d0b5900520300703140c01c1071021081502c4c0c41c2041400c40340a0f5103c0d0010302c03041d40c20460300e200070b00c4020004c004911940c3d074024010140f07007604500c1501c2c080209818070120740c006041054201401990741d0600346410002000c802a40c0e5416001d0500c1030b0350350074507922440040301e0b0142c9420200310145400c000405146150403028980d0911140f201c0740811200d013445580d0000b00c3c00081005001001480241c940c4100e007182d00801030144100d460080150301c065024090b0541515245484440a0540114240510714040721514442e1a0360131000b59074406500810080310360400581c0044422980607400c90b0001c1c8a01c10201000700c019a40140644140d03284004600703c1d16094503003848040e140c0c1a125580102545094480c1004148041d0001c10411640c544040d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 297352158 1250 297350908 297350941
    0x5070e1903080714120408160915050405180a05280c0501030207030e120c0a080705060319021201141f08060f150f0c0106050103020306011e030b1002010c080a0203 72
    0x140044038852140045180805c820180d00c0d0a803a2010740741c0b900e0f25074080d600d40b171460707488101010b40600001c00300c18a10549003034140404000d000300d410141400054030000d400e9140401801052060b044024000c01340858270403400303021010544e038034801c21012400001031a0550f840d410f1701c0040d24011700c0c10b04032230080c02d0258440155007410346544400d00035807608a414101da00c1c804840114070b031413955030b08440c0032010355102c51440d582c81c6c58a016030b50b00501c0070000f04070b003482006210941c114215001510700000c08103160342c4480e003070740451005d01d20701070040d040346030401550b0001920200120705000841400414101c809080d050065048841c40d04654540c00090800405030501c5583daa0070b43c0c0032101002e13071042032144010352800202103001d600c2030080780e02412059403403000d2481000f541d10760b20303c05103062a052580e81d0104180503200c0d8406002d400306c0301c1e0000241079081c03c6000d001164020304503001144108100085000b040021303c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 297353408 1250 297352158 297352163
    0x10e0615130e0c04110a020f0d0f200d0207090f021204021c14030c0712081b010e060412021501350610080d1b0609051005070e19030807 60
    0x110320b01040a50690901c5040b240e2680c011307041840429149105200a10300050654202c0b441180a105040c0d160305844100c0300005008414481c842da100314520404000c0c401c0400c44ca01c8903c1c8840b51071701c0100708a62001da044140100241c40c1d20b4482c210079400001b03011b51070301e07000003106158801c00034002445001000c00300d80107120302503c01c140107a480603581007000c0030b812901d5520b41100a14501c0341c031840f41d001c20840c41640f42000c0d481c0e40041d40780c1c10190200f000c41c900450002000485660303841d0406541030701000468000c038003901c038541c807000080700000e060100110725040303000c03034803001000302a14400b00c1440004403091403160400465210045000155504400912448042c080c0901560000302d00315040d0f1000c40e0386000071001c0541d5000002c802c004020701540c0d4911000c03d003d50000348880c0e100e070096a00074603418101108640c015030344000002da9840c5801c515003031442c0c800c41c2c07d01d40c502040210510355580c2503941c0c440c12a00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 297354658 1250 297353408 297353411
    0xd05070209161b03032018060307120c090303140307080c090a03050a0b07080108060c03061c1b0f051c06020702010905130524030a030c0503130305010e061513 70
    0x20b06042c1c9100b0071901c1003080030032840c1c07590036126081c018060305003044000c0c0c0e00c1c02c403010104c0800d0308036001c07a440803c01d40340800b06480e09504118064100508440c2840094078060064000612074078a220034a5254000790b18118180201030041040f501202c4c091300300240440c0c03030307044030300d0301c0e801b0440354185172344d902124010608180060340000e0103885400352400811800a1000703100c0d000c6a600d0140680ea0f074049659605002d80b0b000c42c1e210410400302d9420b00701150396800003000c4182c03800c02c01055603121107007603810308800d0542c010204c1041c4002988003a801004020844942901201403418200c00c03010700b032401018a9800647e0f0740459000341941d070700900d0000d0200d1a0140b005101e1005800102c6601c2c48155814910b18200d50a685d41c03a55004e0000c0e00420000000340d6080e60402c4078440c080d00c01d8403040c0441382c800d500c0c081440c5c01852080d400402c400c454113201c90310f04403010300074076500c1c81d040d4000000c1e626051040380c0000b112010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 297355908 1250 297354658 297354691
    0xa02040501023408030306100519080403180602010902040b010201050601140913180510051e0406111c06090c050909100902120f060a06141b030a020703050d05070209 73
    0x41030560030210303035100d101d01104a4000380304c45000c400380d40b14a005852024181d0003402e81102d040c0310b00d03001e448036491840e1400290a1007401402da1140c881c0c10003c54200740c1e02c0d290001c20540351702c040c005079160303030030003017181440e0144a0541100380001d1026090500010b0300071075002c2d8450f4000c030b001080e85507059442c681d154082ca040030b14100109000340105901080c440001901c2d1442902d0362403041d00d50700d2080b1441000309024425900440448100e030603c4041c1065a006440d1131307000021720901401441e4110064020700c1c20000e46086c200151000307a4031034002c4c82e1034aa00e135000d841e081021129404400c1ba1501e000f0354422244d08605141c40d00000f100380d101154120034150a0812103000c2c449860090903a43da6541c100182c2c00c1c103601503100000c0c018041514060210009800c6900c4c25206002012406c65009403541d00076110f0f50005902118003041404400d01c8900c6009000f8a04603160184580218920701030140007000300c200702c0b40c0e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 297357158 1250 297355908 297355963
    0x20a0c15050d14060a080307020a0512160e0a1514102307060b0915040b0d020d051c140421080d0912021f11070b0118050a0204050102 59
    0x703049800402c5511020400b140e6840c0000c103100000301c459038000c682510000ca42c0680000a130340005900801c038418050421044c040070700d2040103000690302c0380e4250580032060340c840c410040c04402c150440079103091030b050700950f40d00140c96066015400820302019182040700b012242c010307100800783c0c1202c400111500000b0306802401052095105c1b002043c181c0c004181c428004d40b0140140039510702046451802a00e41c041c82003170011983e000f60429400c04284440001c00250105410340c001c20035808e4104030494550b0044144107044840b0f4004c0c0c50b410203107510b80004030300c0782039070307600a01d110f68001c40504050081158920b801c0c600921000e441d81b180009072100500d00070361010741b01c7e00200300c0f4041001001d180c1d2943c80000e0328421101d81c0502000b41041c3c03000750200901c1070356024080c0301d00400243c001324041051141c02041505036044040c2e8400c40d81d00200c42001c3c1c255981075004000401080ea80020046104406501004034203140903 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 297358408 1250 297357158 297357167
    0x12030c0c110a0b0d020705070b09010f0c14120c0607020f0a20041d010f0213091a06070b090613020d030e010c05011505010e090112030c050c1f0e01020a0c15 69
    0xf80d0084689400005103420309007031070b40143c40c00c24440d4007101d0940e03850350544955802180041703400120b030002601c038030510640f0102c42c00e90040c01c0c0610380c00b81c0c001109041c240070511800850740d0000b01c51740a4502002450b600101510207030246000462029850317840442020300882001002d0500c102c0d031141002d01c40a1005108000d00c4540310000311501d107000b44e40071129440c01500c0614004c25000315481421840c0c01d03a02070705d040005000041103001360300034190300c401ca90400146c44000040080f075008844004003803400c64402c614003807000382103a104000303100903140143c581d211011903055150a1031100c043c403031401211507000541025040c0e600700803c0e44107200c510769038402901d60a070703561005184003c050202800081c801d2011a0030044400b5000c01c0c481e840039a12948101c00340c84442803c040004d0741e00c80041b1200c103a04088503400105079811000c0820140000c2c0064180070ba403684540403614450300c07070060844550407540d10103601c00e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 297359658 1250 297358408 297358429
    0x204050306100302130501140103200706052d070c030201180308090708010902031519060f051807080f090f03040305030301080601080a080a05090a2112030c0c11 71
    0x1400700c803880d24001d1088100140703030744030036405031100b1103204010410381c0c000d41b8103070b4071846117204014490200450041c02403040d0281d4002c4071203036400350410420002c10721a030040102180900b01009440540b841070042d016804105140603103500e528542c0da03c0e402a45420a00d05149403401d09a01520444900010040b2880509c0040507008000d550240042c00100c4141d182c54680203401c03125003000195166001d800101c0c561030288108070b038011000c039052154400702c4443d10782074510b0354000d086040710180d01031115003003e000041d0340202c00c8154201e10f00340320700c01410300b150143c8906059206800000d0143c0010007030700c2a800c1866003140d64a5689040a41d1a50401e000c1d8411a0150400010b070115001035039a40542d0842c044034504101c2c40f81c2514a0360107050b01c5030b04200130001c00281003002c50600031684014001490240d406440d00a001c280802c2c100b0040c10b10700460001c81903404840d80703d80c9548001401d024101c1d86000501d011034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 297360908 1250 297359658 297359669
    0xe06090a05060c060907120201140c0115030305120c07020906040906200c0d18090b1f0201020712180306050c0d020c0d08071e050a0309120905010e040e061305010204 73
    0x1900201c0d543c1d00003078043c40744012005898102d030701d403e0800360043c80c2e070001030300003140d41c00b441842c0c1500200400c8080044030001a080140c1d64030070010350459070054000c200c2c0850314003000c816002d00070364004140b0102610740b906da680001e80585002d0b107054044d6a2b00d01c446d808000c4181d01c183c509141c1103030900c01e014210980da600903400300c548014030b8000c030100741202d640100c0b19000300303c85011a055400e400c2a41070300080100d5065107500154040d5101828091a28040f6400d01d0385e900142c0d41d400d40703050240322280c051400d4400c00403041520100801c0d0b0150f40b4059961110300461251621950b0034014000c07011894006840095980c1000100084200b0320500e60b403211040382c2d50754a811364800043c203000100d00c084185640c55810700c00c00c01080844064100001d08400584844094643e13201285000c41c54071681401a076800008482d2110021a0709001c1003800455440d2a0b0b440074141751071106451307101d0410848290142d801421 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 297362158 1250 297360908 297360919
    0xf0302090307211e0f0f0f0804090507031a030c01030b0a09051005010809011503030f05070605010b040603200d200a030501033005090a03080d02030403030e0703030e06090a05 77
    0x103c04008902ca102d1100c0011646880024840640d0070000d2441c0d10341c003500304000154900842d1a5044000e039001800c03a800000340b90240c0c0080c4c0f00c0c40292001e00300c2e5120010322031610031001307012208010309101c2d03050606911036a840e40c00086800c4011001c1c40c01144200c4540302041a000b11504410a41070620040001c0cae041d84103840c034100e5000b44d07175580241d104d043c40741e4200e82000c5001c500f0800306c51801d1000c070303000314400b1380404494604540307000b01c0ca454510854100381c02140900000203020840b455241c014401140310000048108504400512507944182d00c428181e450703d0300c89502183e10b800c246465844032010442d43d5501108500a00400c070074081100c400324100446001c6d1062a50022402c048034058a03225951602c016200307900302c0036561380c0c00a8120000303c00164000094001083c182d07902580340e00306440c015058680d1581e0442c0c4940c841041040800e40c0484603681c1803001f9100c01d603841000c0000b080c0d0030003940d0801900310 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 297363408 1250 297362158 297362189
    0x20d020c0102130e1311010903050604030c0606140105340b0613020702032d030d1a15040e130605010612062306030a090f0f060507050a0f0302090307 66
    0x10320040d0003c04120465000d0a01d400341c44030a62400808103489444a04107071811140016190b041c014407205014100840ca10742c3c0c0c4e580f130518000c0300701e60480026a41c14040d0741044818014200036115600d48818000e4071000000e00c0b50059869035600411000d1018071080d041c0010240b03901d03549402d12028051600f01180e1415042c0c40c050b00400f0100102d0844040510a40c0c159035802005040000440c41d9074000120310002e001c503900748011a1402e01b24402c0009200c1d4403000e410204801b0203c51542d15005036010400d8029006002c61429040b0348404981c02e40e8800c012044c2140c513848800900b00311801c00c01800786141400103d60f40740c01030300360702c0078841f061000d00105442e803407503800540d65504005840410502c80c00094030340741e0069984107203219400100c00e01c040d15201003020712254103590009800a130101441060b00655900000b0303410100c0c60800d1080300208150154041c91003010b038003103980000360b5014010035009003003400c0b80c007640 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 297364658 1250 297363408 297363427
    0x11403120d0b100c051501060507030e0406050402031003051e060402090408070203060a020c101505131b03020403021008090d2d020d110604020303030a0221070e0f0102010e0a120201020d02 83
    0x400c410004103172114030440414500c0c0418040d81c0d036060300c0c159681ca0f0b091419039541a2002c8078007061032503000f500c801001c0303020f44a5202461003041540843c51b00ca03465410001e042c81410484503142014410709a280342100241070f81d0050b45c140c0e21516556201d08040c900f500806000079410b0085a062004241032074010b00f0780e00122005079182c440001c6248400c880c06410590659640141e0070032080c50180501001034140807400b140039640100d100c1580010428040c3c04130340c2c040340c00c3c4150b060014120f04201f100d810503170072604019107082e9641000c1c841050812800b540b03040060054440e001c002e1081304925200440317400c1c400070b0745070031030441540300003903102040320403500e400242e55000b07a40240c003451440c0c680116100c080c0d4420082503184004c804240e801c03c0003c03048282c80381441d0399922104c42040c0c01007005000d01404414116070400c82a07140402c0c0202e404240e84c0c0c0c0c0551300181c00d0f2145002070b0b003e0f006074410080c899201140b50b41c2c1c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 297365908 1250 297364658 297364667
    0x30c18091e101d0d0e01020c041431060218030102031303080a02130512030c0a0309030c05040509031206010905120705100201050106020601170a1e0b011403120d0b10 73
    0x4000000b05400d0207011070480b4910032008000310012060f0b400030265009460050b51100d5680c0c1c018419141e0081c0640c010a0503981081d8400c0010f003546801c2000101c0355000380e400a10000854007566103400342c0440002a01c0c400c05862980e0000311800a14040c0f800c030031182c180a00259102c0c90304140d5100752200000d400d40c04a46020005003882a50b442140c100c4070300011000101070501d03041c80100c4c04100e49140c60391104000078a0100020080789003080d1090340c44003440c604502e030003040144682c0c021f5000303d0500c003e102c9405004426581e0303040141207180ca07259522401220b249405134800c035040700144060184e202008210304d020344000742c90f81e8944003200d400c120b080311800d00c070340e10040e040600180120545200c00529003c1c030a01164440c080b1511614902c0103403142e0784840c0308854100c04200310f00700d0605801231081c50110b500d000d000e080841c1e00c88110341e8102c0740a032400981c0d5454042e0035030081c5201840136040140400c05404040c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 297367158 1250 297365908 297365923
    0xf04030605011d0a020f040e10080106150e0d0c120201030b0a0902040e10050108010b03070203040e0c0307120b010e1c0b0903031e010501090e0c0c12090f030c18091e 73
    0x201914607500018498203da40200d034110f0101b031440502e407500d01041c06124100180004c41440e40400340051036003424003a4034040c6c10316401e1150280d11404014000709041c80f5150b0107020030f5100c070008030700f104110a0440b1161144000400e140344012070041821001d010350124141401103450900783d4050000e48001c019016107e8440307100381151132800c1d03ca070900003114030340103028100d501805541c001546004076410a030711207521568004045410303540030388004c130401c581268824140c000401600d242017044004050000345104c0940c1c00d601e01603551168901412800c10101c03024580e041190009a0300304031510a0b00da500a41c0c800c0d246903c1d82001e0b90b28001c090300038030b048410584034003ca5a141107549103c400b8000e09421109034144015401c49506018144140e14400ea038140d80301500d208200041426110041c0a544040540c800980320030003104c3c0c500f500682034051656604101c80d280c0100781e0345a4a002c08000301c80d1032800070003c2d480 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 297368408 1250 297367158 297367199
    0x90d03030608100e0c0f030a0602030a0b090a05040c0504110c0a06090204050915190b0904030206090f07120204020705030c0d080f0a0c0813030207150207090506090106020706050f0403060501 84
    0xea5401030143c00001c183c03030042d103c0c0010f50308846210342c41e40c40c000c84001240075020341502e04e000030301d0b01c0d15012a00205e8000e42003940380c2815403000d28082b11000d501822422041045040c01d8a91013047d1380c290180c240210b5031002400c1ca00810f907002d58003107030802e108030b5189105501d040005812804401c0740240d041c0301c0891070101012451004600003400044510703a10f036010000300c000108190001260344210b18480380d01d42504440c03059029800031300590902c44110f900d070814281d81c110250b04010418007500710b2254001c06501d80440b005070b10f9a00c01c2c00c0860075441160103804891041c0424562482e0300003546074454a40580000620358076145464241c40d8084403040c000355813280062840c2003545840d000c3c1d140a031049a600e19210202038900c01820191140940d212080400c00c6d0742450203015401902030710055501d5150440180d0303115590f00451040c801d010880722a1421110140da000b582c00441c28040e07075a558400c10030080a60411 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 297369658 1250 297368408 297368413
    0x316080d03020705061311040c0c051005010812070812191406010903290a1d010603050601050d03030e0118030e01171f05041b0801060e01080106050f090d03030608 72
    0x300301103500030b109a80d621a0010b028295641c1c0d980c1c20b01c1520941c200048030340812080300300d409911580b20f01c410050980d21040c13101d803040d003003082c03410b002d0990141c82c460030000140415003012410720b03c01185043d0640d1102118070308034001340603500d54140744030384c06010030602c9200d103c03141181d2450a03804100300403c4840600011400310b4200d400f0a48904040000940004540c03a0132100c40c02c00c00303507001d05100c17051050402980c0c0b00f680c80c1d845440116a61041000941e0705103004002041210315566509403110701c1441450701c101c000d0f042d44401e00d4001c2d0070201d074108103c0020804000300d40400e0301005d0072404250005000d2040481680d40581c580300c102000c80e0601d00d0641e0f42d401340448040860010708030dd5024410070018454460380200031070040b00710440f9640c1d9001c40700041c42401c050340201c02b0000d07808004880303640c001201e0b13415100180780503941c80c41803402040740fa1080b10015a000710003100ea1600345035241e0b02c01416116400b09 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 297370908 1250 297369658 297369673
    0xf01110a0c0e0c0703050906090402130806101220010c05010e0616020606030a022b0f0b0f071710030f0302071802040305030f0901090f030605060f0d151109031608 72
    0x841c03800d401404d200901207007080107105c80030301c1c1010261a1202d0003d00252400140c0b038040e40e01c0c003940b0b034008a40e80d0b201070244901121181c450341d0282889100c10340e00c101050322030800c0c449050218242685170310340e070303910b459200e18500c0c0c0243d6000f90017800701c0c5142c04070b005c1d0b55480c111070441244000e07511040c8282d1020400d14080c4500030300412450390382e0f400300404003085021a84024043c1803224000e0115014000c000c075004103000040300d269800c148040d20300c020f0004e9100c103100c00403c607000307400001e00d4080c224807031201c40b030a58030480380c0654412183c1010703009007008005001015800a4004c0540ba010498242c41150b0601180141e018601000301143c0007404580741c41916000504040c610525000c400030b6034680b0b81c00c009101c0d42d0010307541591910100010750a000f003500e800228181c03611a200510f54440c00d00d0382d6441130140c5205d90300c0c0c07032640800702c42400c1550304031000202030358460300700c40f00340080d0000c1c0c40c0700385001d6000b0700d034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 297372158 1250 297370908 297370921
    0x41a130e03070c0305010b040216030f021c0e04060602160e090309060d02030402011706060d1e150e01060c0201170603120d0903030b030303012706090c0e04050a0908090f01110a0c0e 80
    0x90f07515499072b0f40e40c5010140860b5a094500460103110f47c41144100b1442e032411004580c0010041a542e8660104104812007072000390f410f190030900c02d540c054040c650354804030104081c200c0361503210001c0d1548401d15000d05601c80c1c003200030f42c40800441c601e200b1103410341c01140200d1003601c88200600b44801401080517088031090f80c401c7c018004005010140e03000b0500640102103030b1421044c038800041c4c100d4400411120b030100c041c1300144503c442c03000c2c103a401341c401414490403110841d400200b61249964001e5071000307044010941c542c0701000410110002e10b24240e48030008014508020884204141c00080c18826041128200407044038185c812008d2221002d00b41c4000e640b0300f4910350340e2811580ba5845500043c0c2c1c110a1099480b281c40c0d80c0d4502c50951078100c00c0000740d420103065541214600018040098200c03400c4800e81c03074080c1d5080c1060034070b0b20300585524890301c000210303501901e00d08004002e5006c103140152031810000b001c140d11402c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 297373408 1250 297372158 297372161
    0x91e0609011a070204020909040b06030f01020f04120f0b1920030c070201180801050414010b0a1703040e1303020d050a09120c05030d110705041a130e03070c0305010b04 74
    0x30b200d89071404000c089806000c96802d00240340d2103001520242c60004070501061100208882c251021021501480510b2405014000080c00b0080096081000d988070a4800b0702c00e80c07180b0303003490b019241c1210410818011050b410b6401c003034440200d2034503420700058080e82c481441d000301d26014115990105c0304407500145410300720b4090860303807008a40d880c5607000da03000fa410b100740500358101c0b12600c10340e014050a0400d0000c1094101450249800d0300464003c94059042c144420200d880d8102260111070104010404410309100c03c541103204903002034811400c42c9007042156911125209812442907003282d039007500880c0100c03058015400030724006107115404000d01e078006001402e041e4010001030703a1107666000040d00d0a091084010049090310442c52599a818000b01c001020141c40c140300b85c1c00138600300f107207001c5c0160714136104807504d9254070b84207c81c603400710100710718040480b41c0d00c0c401d81c10703c0801c00101d44800c0b900c5600341034079002d050601d07 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 297374658 1250 297373408 297373411
    0x21080a0b0303072a18020c010f0506131a0618100e1305060102030409020a0c03020c10020322090204030507140f0f010309020d02030102043b07050703090302091e0609 73
    0x1c040c011007501c6407000034034003000c07404400c40303082c01c11900003182d41d000c02c17a2403005070181680010b80e076100900c599400d6404c0c000000d0304292524081180307540b0395a0000400c09011000010f5a504050740c2081c0800103005050b0081703402f02d4440b640444030350515140704411a0348082c07848404c803040350440121402d182d007040542601c1c0c15000c8603070300500c1e004201401034030705151316045a10204d0304151111030000340d0003001003003419018081d480c0c01c60000d03038100402c41a2820065501e104000d0076070909040c05c2c088420005422412401820b00b13001d06640d40d42d640d041075603032007409019641075078104405464070f5240c10541c025001c6006000211240300c0305006600401c00a24266000609020381100581d828401000500b007980a003a0900c01d070082003140c0c02c6030480d041c034030340ca0b17420141c48500c030203502e06240c2c040610b180541d0354850600d0100d440c0d46242c5d100a41044400f810301401300408004402e60f141d000d0181441540c0c0c013070411190550 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 297375908 1250 297374658 297374663
    0x50613060e0304080a0f05031207090510090503120c12030a090c090b030a06020a17010f2108070210021228050715020a0e030307060902120706080c0721080a0b030307 73
    0x440c1c01800184446e80d04442035406901641c1c186001095050302100040781c60038002014102c003848030f07181c41c0007044030b14260b03440e110b00e82a08010210b07a0301c2000c802c401a141401041c1600740340010041d00c0031086070300c415183c503802c01c0020350000c0c0940c000c04a8103c0351445010440c44028402c2440c60603009006051407422a2100402540442c5a80d410072225906032085030501460b003600802002945d21801c030b01c1c100f0894800c0254840c500d44090845100e03001007002242074950590701100d44a4140388100304c16880d218060410440d240700100d443d0384210306034803041d100c0a2050080030424288020101e0385403162000003020190104042e02c50b990503030340a041d031641c0c00e0612112502039040002d146400c00304044400546800401d8214240b402400c950a801c038401030071110300b028405454200010701406121401003140300030301054040d1610050010083d00d003222021103401008818102e0b0215545410001055a070707003000001c550300d554 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 297377158 1250 297375908 297375913
    0x117070302010507060b0301020703020a05070b07020f0603070c021309120c03055d06061b03070b2a13050d02040603021203040306050c0a09050f0d050613060e030408 73
    0x242580d0066411360000481503d04540e100b01c03000080d2003d00c0207040d00fa000b81c004180380c210616041c0d2602c4d100390080003401d5001d20510006031510110f85028071002c403801d584903664aa030468945c401c1c1c002c040e522420070070103021464091340c00801032034095040002450184003041d1001608a40000d00040041010201c10300000c40c10343c441104118400e05414108101c08450b50003035a584c03c00b042d01c0719020713054101384441842c00340c1160710003102a8a0100001000d500445001141a041c810140390030280309108407202d19a00000001c22410071070601c211070f0418083e03d1b42c84200e0068035200d0490101e055404403a10102c09419050a250901070445074070b40080b80c001e0384958000c00161b83c1d0702c3da0394100c548004003c2d9100c03071450600406031203000d44114009507040103032080b1185d00585100030b0341c0090b9070704800302c0c030313901c02050040740105e0024205c0e000c0d41c420300000020108030502c1090061005009044841070b805880784120702c80d020f01503 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 297378408 1250 297377158 297377173
    0x50c010609020306010c080a02120f2d0a0c0302070f0f050102060f0c04170c040903020610121101050f0d1406011706090114150a0c0c090912050d0204050a090b090117 73
    0x81ea0f003070088c008a8120b10594400b206010034030081e0f504034100890707901d4800b0aa410f0603c000c0c0c450b8a60041858800c41c4000003d03051000640c49154030348030070880c00000c1d440c28580200b00703200c0107000300310f41044100d03aa003013040c030002000e000f07150060080d5400b00340010201e9490034029100d005c41140f5161601c000040201c02040b617480007405070030070a00e802d580d144542c19803240031390041d001c1403912400c1416100d0031a04504210701200710a40b011410b049242d404180080c02c2a65132002d43c1d09551460b80140b94480300f0030360030403440240610452131202d0144400388c0342c5003691100240c0b52404998100d800301c2e00080400c004020000e0700e00d040f00980180a0014081003165581515140d0b010481e52400308151102030020007200003140c00041450350384c00c00c4034090680e55418070032903100d0b16030100300c0081030128126001ea4129001008014203640106944400c1d0b03401420400866510071202c040000a4545403031216961402c0d0240c09004503 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 297379658 1250 297378408 297378413
    0x9030d05090a1a0a1413031803080f030c0415112116080906070309240f110c0414010e0f1e04030e0406181505240705070303050c010609020306010c 65
    0x828400920900c1d0868492560b5031245d01400e102c0c3c1c2c01440019400303aa1614141000b5007101034a200030a07031058070038400c10100311003805566200009080d0165203446050000407070740140d030803036a404200303420406100c03a040b103102107203140f0074020b4600400407100d078108213040b0343d48103081003201045902c404c04c41c0441101d00e814440c1c0390f0641044512000300d1120b8000e89005c40219204480500a035040d03c030300006045148046000403d10645c0020903a001d19045c2405002030a0141203001030300340400d482c0c80700040c0c000c110060300380d00a07281110b801e1107210701080141011039504926103440c0c0d0b102e181c0018401c280501841c20700444032100400981c1001400079415005036114045d4000401010201ca003842c0c44400c000b000311610301c0c0794101036002c040800c010703e8981e98030b0010400448484040760508d802901c802031710480b03070000e0441c040c1c12000b104141e0000003404455400c580200001034070385204d03204070300c41640c98501003144000d04000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 297380908 1250 297379658 297379703
    0x70905060612040b07030612110d02030c040c030c09140a030f14010504121d090c160b0c0403030906020f030315030a2f15040603020c1509030d05090a 66
    0x30041409404203241a031a0340402c0d48000040c0c82c00c4505420350307402d0100da541e01d80030b5030016140249513490850320941d2418000918022440c1c02119407189800940d40c042c030030381001c0400035000344222000403034003c0c014821031a0300000700300464408650760b201b04414069060f40540241c01d02d50854480001840c0e0140048501140c3c00ca040e80d030001c400c0c01070601030362145610303800b030100e2000c0c06407048078091440c1c80481d103920400480f9994000300c1170f80101712055443d5032092628100744448442c950f002d4050300014060105000d40d003001402240c0c029900e4041507922020100e03290141c41144a4480c3e1050021031880a8001305a5054100041c00c0350080085c1d030f900d00740040e4142c0c88501d904094104008103099200001644100045851f070510303d034807600984403401640241010140d021884450700b100800c84049100650303040d0f40f42524054400a075641d1140e111065110700744004074500220010b602c42c400b503070000040028640c4100141c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 297382158 1250 297380908 297380911
    0x103150203060d0f05030405011b0c0e1f080d0f020706020c0108061309060f0b04020a0c060b270105010315060c030e0301111b1b180a060f0e09060f010602070905 71
    0x1948200c4140101c4009113001c462480c3c0c130b900c95070146031103d181000250601d10321a42c031403002d0a506490500050070401e4690030b440c0c00d08440b0882d5150001c9000055031492004200a0b606c4040461980c1000410084080b0180e89903441100c0703051080362034100c20310802c00542e000004600e00c42d8041c2e8082c3e82d00c0300001c3d001d0307640d4403000c0e240d0303406448407600c00b41c40159640d10420000b411a009440401005441c15864601c0e21036006241980515000d00281d5070340c0d5a0700c0150f0350381080030754502d068030744148012041d0307540e0760400c403828402d0381d01203403801c800c01c2c00c510803400900702140d0860b1660b8960101c82d843c1500c180c0720304521640d02d0355840e40070105d6261000d0103080d48005506002e241400a555104e25220080c420f102d030400c891200c1042960711151100328040d0320489180b01d42e11401885406050b998000c076908007800c40000c07900e0400e2000c110312400400f021603040d602c0d20b0403500143c540c01c5c051400142c22110041c06102929007216 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 297383408 1250 297382158 297382171
    0xa0b15010e0a0b0d051605070312090203030f03011706040c0512070306020a020106090b06040b071b030c18180302030301170c060a0c0302100b01090302040b0f1206010911030103150203 81
    0x6004001c1c500107052200207070050200e03100c0c04669540012454404d940c1d12050b000b401010901d01d80f040031b000341c010010018100b20700035103c1c0c81509010307004180019070107011a5252040207600d40303140c3c1c1090141208400d8000c01414005400058032030240c1e4004000780c03410390404042c45000d4404800c00e0300d0030b02c10070100200003001440100140d400700c0d800002c3e4903092054890a603119142c1040c4542d00602090140c403070b5540440c0c0503035501800e010b10300740c002d408050b070015542e400540381404c05400010342420704d425465040d0108042001410341c0b0301c100006030100104041d005a00c2400140002d412100040314000210300484089070f0f0484005085503100e00312030000149a400c0050406404101503039022810f0700003817055840c400d00080c400c210320710003e40314030340b134480b50201500d40702e42102c24500042d10051700b440c400080c01daa118420312841c038200f480e011069807801030800a0301d0503030794080b4840022420f9042000060340010340803 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 297384658 1250 297383408 297383417
    0xb0f0405061c0311100213050402090a08060108010b01090e04030f050d0603021509090f0f13020609040c030b1306031a0405071d0a1104120b0403091805060a080a0b1501 74
    0xc89500360b00110304880750b1003580c4505003403204d04c211074100032101158070550b50050002140104035015003a0a4540c26940140c844400ca4006441420b40c1c0e402a0391500514001185000f41900300e40b032808000c1c1c0b00c0c110f0341c80e0740c0c03606d001110608560140000d2200c404140010780310f500100f01070681d01501140d01e50f12030300010440301040c8002940b0610010340e454090402001c4180d205850b0181c0f01141d02c1c011010442d105402401c5402e0303954045801411503407800103407070312450003030020000b001c5000741c094002d00074299000d10554200420b45000015405000c05403a4044007401200710b29442c100c42e242c402800c1110300b40120100842c602580c00404248041c06502c0483e19041252a1004031230031943c051325545407c201c02c0c80310342502c007507100d10030380d001d940340d15540d82c0ca04084541040b160040c0b400d4078404a0300d001c0d05141c40c2c200500030507086132039000c43c943d43c000c425542c040d181d07030040c50f2807a4200041c01900c0900001000440103051 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 297385908 1250 297384658 297384679
    0x912040321050f1201090b010c0c0b0a1806030209010905040c050d0506060706110a0e030d0806010f11010c0906020f01090b13061b120e1f0b04060305150f0a0b0f040506 74
    0x1056030f81c03500300d10218591812002c00403c0742d4081d50040c014449800c3c2000300b0a9000b5844070300e10f05050340114002d00c0b4000640f105001e12881c811070b20310064074501004e46417503100c000c02035441200344070b00203038800340082000c2c41c082c8240b684c0d11003d9107416190502d20254035018040060040740d003c1c0081c0802008100c0f01d001d07841c01c0d4205500b12550341c9140600141a0320072091039103001e540002c9030035030780c0c0760440b000030b401000c2400d0a645440b001442121540f0320100b041d100c6500304803040800c20b4000074000309481e100d8081d81c0c111240b61a40070308130740000344040c01110b12000454031050031490070040407800351401190444422000c0c00176900d034519405c0004110044411154190380318014071110b10368040d140d14003684421904104408814511a07a80c600c0100c00303981d071320780c8008011603001040d6160151100b4000320040703c2142c0703500301d120a09000410342081827151000340003004000701d00c0b182c00c2006001c020300300180816003145c12101d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 297387158 1250 297385908 297385927
    0x1119050c061303170c0703170c1f0c020f07060f120c0503010914040b04080c0a02030a12020c01081e060418051b04020901020a11011403040b091204032105 68
    0x510140362801449440c0b640b841c0b5040011151a02c4e40f400c186405114405d000308000c51800c04076a00141510480756800140c0c2e003c0d4801c983d109030140c0302d80d0705c8941904c0ca50b4200381c0255503c40703004205080155405131380b5941d01c00003456050b0454041848071a01400c0348400f040071510700564206c0da800c403590101d40300421001d003c034101000402125045014100c40340c696420b002c02d850615585003d41c094010304003c0c482e41002c01c1009501e60b080000d180101e0f0020304480b0744580505141c0000a1004080001401344030a00503041d401903100d01e0041c0c1e4000c01c1d551100210461001c2110005003a4541c01522072840c1d040d58240c0c2c070b8000d10040c0c019009030690100302151139541c4040e4401c5940a1401840781400682c0c002c5803070400c1c150006040b4088140c1e2500407100000d03490191004810040300340014882c02440c018402c2d401081103030072102561640307448a0040d0300c0018518a2004480389045108032180c5002d84900c1c280b842c204001003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 297388408 1250 297387158 297387169
    0x90307020d080c0106030c06032406020a061d0a0f1a07020618120a0e100206060604260604080d0b010203070803161103180f041a15090627011119050c 66
    0x1a440032000907198480000142e01002d85144100544032b040210303a480e002d0003039103c0c01c400700003400301c0781da031207054a01003030455504d2040402c1500b0381e460b46110b4070b404c0c50400c020910940d49613a903086000d107202624410140141d125030020301c0325640d8a03e0045c541e0b01007050200640c00748500a1480801b0140904100c107001c0c1c69140e0996000307014003d070384449104250443d40101d080c002c254445038121015664a448043c003a440d90344405802d52a844440c201e56226040802040c00b014201805901345102024803901418000490740d901440e5806001d602003000403912841d40c0584055802185007410054140b82ca00118255004010480a10310034222032a07403d00d4500c07040c22040e00200e40400c22920383c4040e541014291001403801816100381030244c00040d4000c1e44d40000c03004003034580d03440c0441004059000c1c00d44103600040701c0d401d0885107660145102c00e413284004401086104070b1a010104c3c054041a0140e0301405101400c1e411038892 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 297389658 1250 297388408 297388433
    0x1e01060518010503010c021c0c02030708070605030f0903040311010c0201030b12030307020c030a080406030902060f0c0a02041118040c170c04140604060203040506091c0609020405090307020d080c010603 89
    0x14100c41032290343c500310604d425128104021011504a5481259000313015841c4940c0e0000c18035201c241d290841c07000c0780c9080d2032500000c001e44280400000e00d160b00030002c40c0315003982c04205501d600c0c2c0c006502d9807030089000081118208208103081075200701c04c2007a4180c014900440c0c1a030700c0b8004503000c1a04907480c0c4240c3d400010803c8260341e0100f00e21081c020003903005003d204083d8030741180307502840c000d01d403c05490f2012001550f4440050395044420203904590781c1c0c035081d05440d5241c2c84010124050380c10401ea10b200c1540b400162070545030800030000c8040740383d404120050066600a4041c0038101c8560580740130741a21140c884c001c4c11200668403410540c4081c6014909840103200b02c10401c4180815507000c4240e0701241c2c010350315562108401e000240918100381003100700380b504d045928050120343c0d086408811b0080d01c040103d82c48034071aaa40b02d125581029422100d01c07481040016211001450104a24000080e8060310383d070b11640100c22 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 297390908 1250 297389658 297389689
    0x1080c0103180f0b042904080f1b0115050907080a0b060f0c060a200d1802061908010902041203080a090b01150f0305010e160e032e020307021e010605 66
    0x80d008200000c00141c081c0346e40c40c0c1c240c92103d1803164001a00c3c010004d03140144014100640400c403204100070280595640380c507525011006034605d04400c9009100c1c032005c84601c84020b9200050b2418281710541c0240c4041d0383e8000503a40d400e14003400340110f1001300c2c1e0450310820102c0041104140a00b8500103401c0161015090200c42d8506807804401c1117040300c07030000e0031455004d036544110381c85140036402c0031496090540d1604044d69042e40d010b500140009002e60842240d5100390307200c0b40780307074540c0c50059895007016001ca01031030103070900c07054000580d4001311780074401e01c41e40319501c010042140c00320340e07440900e044001e912000b0a00d01d10300c804040c0c56002510401250242c0ca0200910361505900f0040100098094607400b00c80312802c07800b031442002c01c00c4e5582d001504407898508201d22900d414a0307003d0b659185162502c1c0f0801d6020400c0c0200d901170469903004180e4140c800d007209508070560b540620b000e40d038501000406459114020582e0341 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 297392158 1250 297390908 297390923
    0x3070c020a0306020429091008091615170606090105070c03021203070213090203030a110307020a140a09061a03190504051005090d0914010909050c07020f03030301080c0103180f 78
    0x10209003040c00c3c014206c100904144400d002900380c1e0b8985c03021442d028402898042200d40f1091035140c103155002c0064402d903c0c002d2000300328607040d03034801403482c2101d60381c8641c03810f9850001031b5801400e498240d4402c070308108220840d0b01c02d0002d400614099801c00803420f03a20b50000c1c03001c112600d40048150000300d40c0c0c105518103498004905902d0030b03010b201da44078603400241c82e481000b201d1824010f850500d07905070704082090340c40c4190b0190650351a00d480f425544903440604000034400c0b04c01145c003180f43c01c0503004000803100c40708140b003e040080507030b100369500000e240074000d01c5103400f80e10581c01c490080070f001f240500058007540301691088820360b58010002d00050b4005503000426981c4400d50004480e440b81400b80c0c25182a8012110880503038031002881d401e001c2441840e41d0a207000703024151080f41c00581c50f10192090503121b000034411100c1c29003005004d490b80b07502a070888141c22045400c0341c81c0400650b80d9005c43d244c9042c01c15078901 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 297393408 1250 297392158 297392189
    0x12171608061e1909020d14010506070203031c0e030f0703020d0c0210030b01050d06031a0901090b0f0903160305070308100b0f0903100606170709050603070c020a03060204 75
    0x56044a240c54202800b40c0e404480c9007a012100e40a01c41d0140c15940500c481c440e01c0c0301c00700c480c109210094110140151342d101c01814451000c0d110026170a49110720b90400060715103402001c48034916405409581020301e0116458680d402c2c082000100c42e4554441240507002407000301120900300407125190113040c140245800c400300108024000e880309000051790360802204031071119842c020605070002401280e03203003d201e1501d0308180c14004040208403682d03840741d02000303020744030480e15680d0907c890309803505a00c002d4811078030b400c00301e1720090151011950281403e01100c1c54502c4840c203a0703582923140001600044c6000c030340c20040640c80351506030007401404000320b2060502e048400c592241c2442130103140070000d4600d1203510184100344250043e03038410006169104805418902421111102c1c090f0083c0080c4c1c46500402c2c030703402a031b100585450f0a583c2c4404082d0780002d007030042a03074400c00d104400400134060740024030152180c1144080344 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 297394658 1250 297393408 297393451
    0x218120a05010c080c0d0e0717030403050c03060c070201180803031e0a110d0c231908100e070201022205030705010306211407090b10020c0d1217 64
    0x2141c1d00390303943d00e0402c84202c06200310003680205490280341d07040e6001900c0c03c400c2d20464640401a440000c48078a4030200c21206a0080083c108481c013a60a0340c0c020700e850010540c0300d000c01c54104014900c24031004001d54807071802c4400010b406059000c01e9600c0c2e80c040380c91608119001c00e000182610038042c0c0c000c03244240c036000f541c658402e1002683c81101d1342c24078010400c00540050351402000309861041002045240c0c0400036284009030741d00301071100d80e01000e90624041c0c0e44040c2d1a840900c03d00e0200e103d4460030582c604828144441162540400b80012085640030b001c00e28020300000b00090030480208040c440c81841e01c070a050520f101c5520045c141807034444200801c1d04001900140039500c803405c00088a401d14283c00c0b00d110040d07024520380709400001c2506459a030202007a01411150b1400035007035050200d0355000c400c0081900901210303004400a01c6119000c0700d00c00ca80d086c01112001c0c402145124584102e33070b81c00100070b0081303d0821 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 297395908 1250 297394658 297394661
    0x5060a020712020a03020a0602031005062110080705040c0c050d030518010c020c0d030c17030a050105060327010e010908030a0c050307021e01060506030703092102100218120a0501 79
    0x41882e81c60015041c040a1910060b4850001712009409140c000000905104840e41c400c40078110060100d9181c4800e9030102c0c4d26000390f00d070020401400200480c286142c4003400c0c0d03040b030307405000620900b0300f0141408080c000490f8403109110b400720032080090b02c10f001402c1051655900013070340f03140807a407a001c9404540d0240c1c105900d440304500c01c1d65400700d003c00c0124000d4030140c00003041494115210703c203001d8080c15034a1074010128221041800940c000c0b15904000e00150340c90b401040903500c0140c1c0c51074045090306203209000100d150b07412034400b41c4c100c0001030400d40c12820303c0c29140100c82c2103801c13903030000070003a00d4a614481c00522081c6440c0090443c0742c030708000fa64991035060009010714441000400d84c5009403c01c0f006414080c10407034482c10000000f402401d6103c00c21140468018140500040000e0b281c01d40118507a00030b10300d00603002d40d01c00c000d42c48802654090001e14001003083c2d210000d000340703080c0c2030303c005195071031072420000d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 297397158 1250 297395908 297395933
    0x1050f1902072403110f1209060a110a031a0a15120b01090506031008010c120b030a12031107080403030509120a0f2409080a121418030705060a0207 65
    0x48085010200c03003030503c150340010200d03081c10006a0104004100c80075409000b000e294861030025000844900d00c100c928056600345080750303850785507000e500095440303c46858101d028103024140d2554465041012001180007084001b6000f12000c41c403621400e0304201d050407443c00d840324090380d200441a00701c0f110000c0410500014100091640482c1c0c4200340c86a5004008142c0e8a01d070b408480c1c00804010000b000b003582041c501401085409100c403026601c2d040c1c0050003401c0218403280600c4d8070845890178014050015001002050000300c12914144041000a0884d10091003d90301030f07124181c441e91184200400c462504200c000c09411a180c00c0000840561400c0c4440d54014590141480400180c120313881e40d50860940050410180c0024090140020160000d4542d01c0c0001d0030051740110341070303d0ae1500c00703c41400c01c0748000755a60040080415204116609a034a8130b01d20307407942d601c1c10600b6203011003c6075000a41c0b1040004080c07411 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 297398408 1250 297397158 297397169
    0xa09050111030301050d02270103150c0e13060b0403050c210307111c1b080705010e1302040302090c0c060f160806150705010501081005040c120201050f190207 70
    0x1148580c00768000e8a407240410b108407402040d01a10b40801c5588032a6518a00c000c151000711001c040100c800152013003e01c0251000010401ca07010750364528018031403002416102c02c40c10340b050205102400383d56410102c281c55803080e02180803c0c400c0018001580074800400c098149041084030301d29110641201d190b00c1c000d0a801c100d08080300340c500080d044078121031030780c4800c004076103480001c0807400c0c461580ea160000030042004402d603801c042191f032640380380d83c540480c00d58032403103400703914003103450f58104102074505111440018961180c0240c1050350b241d004c100c07000000d541e84270010102045002c09030b07004000955216803020b2184261f8201f0000c025030341e12100d03e00f60108949180014007588a05200e00d0010741d04200c810340d00d61403404c00070b000300300a01414685010380500c030004140b943c000c0701e00554120125550a0b490440d840250311808a412814080c0600003a07500f07210f00300160010041e00540504620a2040020700308041c81e0401c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 297399658 1250 297398408 297398417
    0x70c0f0617040803040807021305070e0f03120708040914070e0a06082d0109021c09030e090712060909020f0a03080d0207080c0a03180608041a06130903050a090501 72
    0x1d0782110010704001c0d400c5500304a9580e901c1c1c9617401d0403400c0d0b00c212003010b900b224044002000c0e034441540300394030480d003990350008600c580d0344c100800c1e01c01e840340c134541c998082600c0241c0ca100702c0000f4a4010b2043c254540b07410380e2450058169070a18000103012461a4100710768140c00c000c07012414541220b10a00705414818040c0064501a010781407407a0010140c2010360350342c190031004a035040c01e01c0c480781e41e511401c0001950080522002610071a060040355400f0340c0102c924196164940080b010301c0036051100b00307000103010704100b20286000e109004502e21403000540288100862074040074014007003644010300342540175000381c080403c003043d811010703039403000d015440c09a03444144d070034060864040c0c5a0040d2050007032000c0c020416411440d40d49036950300820490215940360b8003500d82c25812580074011b440510428821555141030b420303484500100307400705030541e07480500202c500d0410120081140002c0d040480d41d04403e420004103800d281 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 297400908 1250 297399658 297399677
    0xc12030506150f0a0e060c0601231915020313030f0606060e10031505060301170c1c030305100b0c010f150305070e060f060304060501030312020711090c0f070c0f06 72
    0xe10083da108800d445010441d211503c00d003e80e940c80e04803142c62006408441c0300e561507100d001d0003d11044113000e4901500d901c0c00585050400e0121009a580001080c0d51441d1160340716884503404146003c40c081000100160400a6500e0001d103028120031144002c50785095411191260010824050009a0b011141d620814004003e07601803a000c01c010342c41c4c404241042d1447d0f00415840381d0040000f00e40701640062940c080c80c80c0303204460701c05100c01c00348494a03014003004482e15800c034500b60042400b80d004107400400117000100c541d543d600010b003c1d9041030481698907512049440b135811030f24040ca000e0f030319201c5080060186559252036546000340b0501203028045000100b840d50764045800d01d02c100a0103c079a24074140c60420b0041109003c200c0c0419640070075885202400d1099070070259015030142504402541003029080e070007003507042040c0080041039130400d006005000b1071032080d40c1c2e08600508000b0100c034000754030b4000c02c0070440200b4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 297402158 1250 297400908 297400927
    0xa02060a0b0d1218080f1204030201090308031f030b0613151707080d090f0f0506030f13080f040501080f060603190b040c1e11100c0c1203050615 64
    0x41c039042034561059900743d800d18844810345005026200c0300701c4041081c80e000501200200750103206200306404d441d1541e0041a407601c06010b40d001c080c0c0020180003050000400140040d600b00036107098400c04202045161038440c4130f01d400c101e9002c41340c4824807040781441c91807200c000d40c0103403084c08130090520140541005511503400d41140102a03100c0d0382505008807800741c2412010344800003841e84014090904a100f25034150000c190000741341032840f80c111054540c001d20030303403840d107401a02142c44140500f000c03019070790208000d000154260002c1034001c841203503960b221032a00002401b0200020b0440e40c032615018100f014540e40c40d000c80c2d5000c0005a0701101943c0361010402c0108000e1a074142c22529045940801c150800c5208a0f04041c1c0c014040e5098142c0b201101c1c041c3c0c0e0356944180b43e5204490040200107540c11881145140d4907000040100540b550808042a0301080b8040381e07465003400014140f1408292003a0700c0391007200d01d00264007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 297403408 1250 297402158 297402169
    0x1003060b15220f06091a1305010e06120f01080d03050402060702011b0c0f090b010302090d060b011202030406050403111504060c051b0f07050103150509070903170a02060a0b 76
    0x2042003012050100d404a04004440c0b28090200c034a007851455072240303000307070000845010341c3d0038606202110803105001d41c001c4418800251100c004507502e4440191034000d143c2c2400c5074407542c1408801c03040c2c001480071522940074003044217220b515283c0300c0c40c10b1091424801040501700300030440540c0350b000803100d4a030b0382172074404200d002c03c0031225412078600c04020820300c411407001452100c0c0e981041f050320300c252020003e84507400010760891181c4500d250f0040e02c204240c00109040b50f00c05198000d041c100220700f10428040482264030490b422100103036580140410705510003151160701c07483d10001c0840380090300030500240e00007000102a01c0d25a03d40002080c0f18030152444a004404100c4212039034211103900d400d4014652002c6100d0060009644d40c40703400ba21702402a5924020000781c1008248407000388028515070512031032400010005a0010405111081c01c4400c20f4948441c041c00070b041c09000303000558a142000c12091841d55076 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 297404658 1250 297403408 297403417
    0x911010207081f06030f0501050403030b1e04050405010b0a08030408060901050c0f09060702060d09120e06070618050a08040609090605150c0f0316031704050601060f0311031003060b15 81
    0x2014000e010702100c40c4200006041517420041044000900d480c0400405410880c040c0e48662010320038410341d481484540c03048111f0303220f0700000c102114116070070180d00060300140104008902503854201140d844049035011a07220340c030001d070070440c3d00310030703c1001e4015400c80024007803420034280c94219806800004900c115001440302ea1540d10303001182d02c541c0d0302502c0c00d5100c60401e4001001804000030a0340d4003c0040041c400d45449860204a040030003800c0380c1c1400401d480300001000600d890700c440000e9200020040380d001c01000c4465446541c00079541c90400c00000c10104c0d0720f52017000704500b03020007800742d0f94840c02a00e0241d155041c125803a810500c80880c038180320701211482d02c0c007001480f030780300940903540070100600070789840c000c1d0225500c105d40f0a100c200c0e00645281c12160040c0030303042c46100b03c0c80c07980c4440d10b0041030016050721180c009a209841c8001514201c10040041240500540419401c100c41c070320310154940036044014480c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 297405908 1250 297404658 297404683
    0x1b0911181302070507090b03160305061f18051906053f2a0a06032a020606010824060a0504030615030201080916050d0215030a091101020708 62
    0x10600d4240c040744a80c1511070b00e0b500802150011592103441e6002006001d034494040e000e07d0400000500710100090100d0360b1000041c07100f6520111084158000d9805654180a02d40c1d0700181c80e2500e2041c00d1280c0d040c0000001d00c1d402c158006d0112540fa003610401c00328101541040320f540d4840484003680d60002c50705040c1841000e0401410460384520940b01c100603030745152020300081d2202c40e1f1300c0b055050000040c8041465034004078180e00700fa80c030003148681809100d10030740000403400c0c500a040300101a2081509a00580c03001c00500103070b1014040100030341c8e0020b4516000000415500455180150540139044250044a0142c18005101000710348120100d50042d9003122080120f030f180c00c10b840220a0f410301c420307400100e4210100340c0c20980800c03048240710208400340d561525220510a4030941c8040a0f64040d885020440c80b9194000042d0300c110a2001e00155031500307460300503042400d000803a030455102c00400d021280000800c10135000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 297407158 1250 297405908 297405919
    0x9100b190e190509070f120807021302090d050a05160e070f0e1203071b0e0a110702090103031817100506040e0f15130b0406020d091b091118 62
    0x580c0d10400c48a404240c40b0320b0103000307203072608002100b00c011801a044d101107407040d18400e65549014041c481e1144c50141c00304100704120001071800100c1d902800d0744e2a1005400c0c00603080010340c116035416400d44250b00110b40c500b0030001c050000e0800f5255002a0341245400e140c0c0e1501c2015000b8919028403101d4080296224018a07287c594100000e1400d4202e10103048450323240d4005800c1200e00c0c5190a000b030300c2034000c00c3e01d40717001d03590415444c03511660780541c090081d001e007280e0f551181da400c000010150b180d82040d24069070081c0c88210303810300c0d0124201d07012821a0f020741404c0c0d10207010b0003403150000c28802d0500c0302491000c101038486200180c000c152089203050988960018201003038000300d200703180d03c21281040749566842e24400c03580d540403650000d02080c180d034001000140503a016086d8507142c03079400902c3c2da542c0d540380000e0000c9500c2c80c00700300b050b01c03504200061080c090501441d041521207424080b108413160817240500404503c0780 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 297408408 1250 297407158 297407161
    0x30c0a0c0201020f0d020a03022107030810051c03110c03100b01020c060307030b011d06030f040f022e050c07290a050403061404020102100f0f0509100b190e 69
    0x6a100300080d8044083c20070a0703501c800c5217100040e541d50010302c0224050700454010700e0340b44861104c100e000c4c80c0d03c9207007580f40010030341e01168048001042c8410340404400e02040079141c0c0d00a03909080015040700c9905501c504000c1c12052482c144014950320062180c041d644020036000c1d400341e1600380101d214090000140e00713041c0c22615494010703002008102c4e13140e6160300701b84c50481d02170300c80c44001b02c540e40b0040d100014001c5850307040042000803e1109800d4007009a0140c011181c0d4511100560b000460200030242c80c1507a90310082403030321092090240e4900310f00d02600344146040aa0079941b81c8640c458401e699a0b03141e0b000440c0307403128807000e0207040b11956800040c0d0b81c05000002404641250009030389580c900a52209200600c040c0c443c003540d0142c0041509030850700c004c0c0041c1118118019085446218403840400e2500409000b200c480c000341c503040c107507089005c04407002002158031504044a6080140814411510555440c0d1042c20170a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 297409658 1250 297408408 297408413
    0xf042309071d0d0204050c091f050a0e0f040e010b03010501090b03070308090103140f040b010e0408121009090507031a010f061b17030402040c0203180418062f030c0a0c 74
    0xf02c80014501a403c24142400c000d0b05000640c000c140c094811074001009032445542c079010038041000c1d41020030000c0144414080c02448840c4d03240c08014200d454601485011030240c2d13038040003000e484e86d100c030986011407a0a000310b40c0903090220701001000f1100000940d20b90391840054954640001c4d00e600c0c90b4800d410040d22320700c52558500d4242008101d00049820440303060340c00110120002c20b0071043d1586050150340c01408031420f0035101d03800305100b0200070300003060200c91070388009100c480301e02175007220758016000b4200c09417460500700410707095844180700c24140c690051185d000341050340405c0d20b20a01c0c2030001c00b4440d4100b085008100741c4060042c00300000c1c0b160800d80c1a070029803240c1c1c0301303603020311207030705401c4c02030f640d0b40034a40b040245d10750003680004150400c0c1e4003c0c01c648008541c541e0000b4484d072503130f0045036005035140c24416402510820080f0003031805035502800f034241940785182000740b0100b50300840300c442c420000004101c406 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 297410908 1250 297409658 297409669
    0x60f020d031a090f07080c0a1e0215010906061e050f0714120405040b0301060819020307091407170c040303080406152d0e010e0c0f042309071d 63
    0xb114009080401c450508030140e04080390222011000980d41800099041d0581030545860b407002d5250b5051140410030a549000c5d81c1424550071440f0780303c10900d15044524406009000c60ba000150705824014000c00c1014442030700c02d800043d00300305603000c43e884070031211000b14055805440e6240d81ca0300f80041c5010402d110814410320902000360b850b01c8008008440007180c04000103456141030600f620365500c50550103401030303000d000c541403040c0aa07a031a83c3c8010140c890140e1100038017022540c910f410341c8810700c2e80310108001c050b000840000d40e0140c1621003c1c481c54071080354861485280070080c1000703c3c20740458100302c1e1a4101c800038046030071040680070388a030071609040d040024241031102416000038000380d800f80500054030304c0e0350120801c0da07082c41e10107040e010340548117240d490020000a0070090b00d520242010380b4840040070a046401034180440010030140540310311511001d02030360741d80109580040c680a804214a030000c5a40001d8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 297412158 1250 297410908 297410951
    0x40602090303070f080d0f1515050702030304080d080705070b130602040e0405060406111206060307053f010b0304030c080405061c06121709040b0d060203090601060f020d03 76
    0x1081c2215480342c920800c045d00c0e01400c24850850001c000d444185110402035072a41420285070140c211410300c4090340c241813649005055080c410700e0030340251f01091466200c1d43c80740540f604280da4170001c40e540726001e1600072005183c6a03087c070780161600c109058003c1d0458004010192017113041104940680300100500d074440519483c15041c2a5202c0302d04480441d1081e01e84907003615080a544282c5400441001344406070b951008180100c036030001e0b06da901404000c0c020002d10740c2012405040b11203840e454440f00b0040e003059aa8104540c001015070000300c41d0040c000c00c840b803070540b41e11540614281881c8049230500d907201d0700c90343c4c024030703086000028401c08a440c94260074140c100000c80c10042d03255111507081c0b0080c440c020091809425107600c00403000c0c03010292460407001000003406140b84030000c0c61880d4034038401c0b24440d8012007000710351b800c1031050b0740c01070202d82842c4d00c00341c41401c0700a480320f02c1564160149075807600e58011200b1107040c1c05 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 297413408 1250 297412158 297412163
    0xd1113090b0a120602130f1a09040b0303041d06041406062215121103240307090c0e0301060b0313030504150e0a120206030c16020306040b091b0904060209030307 71
    0x419411542d810060042d6000c040c0350091401060f100007a04105450708004503a42c06085000081280c00060110741c461012140c0c0b040d16802f019866075002e00040c8003d0442000c0560301d01043c0251010210009100e9480303603113440c0c8502282c1c804800416403119084483e10740c0da04d00c041c040c000118504600300c221884102c80866003000004000e40070581035100c548816486100d4001544c0e0306600d03115403060140040f1f4040d40700c418005007107000e80d55281c4001c0c40c06d0004645030855a074800000f00380c0f161445000a40c00031450002e0702004c0e002402460304080324000c03244005480c110802d03605488400c10706200b20103950103000e14041d0b9680410f4403040c014282c500301180c240c4102c1e1450000a00d82c2843c075030b22005198080d107060300310f65581c855059581c00900c100300c4114841440840169001d0259034071503803213465074490900384260524604202270158100400e03503004504600d070b0b543c1d0b80340c03070384a5403001015a85d80c0c4e400010030308502410500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 297414658 1250 297413408 297413429
    0xb0a090b042904050c0d02030f0109080417030a08010b03061206040b040b0c030f1303030e2d03040e15220204090c08010302010c060e120f0d1113090b0a 67
    0x180301c200b00c002d200c662051140c030000c00342c9042c0c0e400c2d8402215a03095600803d00e500a0710560030a041901d94200c000740000c0a50b030003100307002c3c002400c0d41c4404400310340254000a06200807286410103c0c868200b0000650400c0020540034102c0801802281c02c1c1ca1000700c002000f940d1407100410850040798262070740c50510303240c2503013810703030540703040719440100c50005441c03c5d504003e0300d01c00c0180d80424800c2e9203811130001d030914000c2030164105078641a040380d492804200c90304c042d0b8605100108580081001d1070003500b491100b20005400c10001003281d101c0480b1425008820912041d0500ca4004001a440e8040314481c10040203042040c080180f4035a0240084a0443e5001d0001d504182411680c4400902009002c98005548000418102d41c4415101000d0344200e070981e040100980c080b50308454111141310b2000901b082090f2418011451400300d820007160810150651285103202c50707010f540300450769041d19814964400300e1500050003907044 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 297415908 1250 297414658 297414661
    0x70c1b0b041401020c0102120a0201110423030115050402090409050601120506010603091a0403090504020c0c0307120c051302040b07150b0a06141810081605160b0a090b 74
    0x2100d2800d0700326105030000202200c450711001e5001007403884000340164003410a01907050100c020301d070090b035503510840d9030b5803204d20060b201c48001003001d0301c0d040c42e40c110181c84002c50141c040a0210310103000e81d0421814051f05004040c0aa080e40c0341142c01680740d24480d400300d0000e004140d405403c41c4225400040d1071910000700b6450240240180c911582c3c844400741c0035265034070700060940304110f8030400888440c0403081d410500c03a01c2d10843d080d40e2100044c05a820ac5c01e009511608900e550944900d81086048010b111021707422804000584842d00003140d58807486004080c05113500302b8000e03031036048502600041000603255400382c204030180740d800e5080d144c140c80c80c1041805151030440c0710581111156074500b080030024452a141503009100d089140c10b40c0d2048030000d82c0c4d01d160f0480749040c3c00b95110140c40c58403031270003046411041e459000717000301003107030150100c0c1046000559a400078003500454031a4200000240b401702c034094813110340c000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 297417158 1250 297415908 297415919
    0x11040207050c040504110909011407030506120d3203010b0a020307051506040b0f090703020a090512010e0d08010f0b03041509061e0b09060d08040305060705042c070c1b 74
    0x340d061a44040903030303002e01e981d911452230601300c42c0303607805c240a400300b5940040c4034a840380d00055480000500342c018a0609d107400e4624100c524203021020030100040036480303134640200f110110000d80ca080081020445007041684018000c00400c82d50024542c60b4240c020801c455600d5404801c0790840ca5803055695405030301074410900c5282030400c40119442d084404044641000307041524ae6214403070180d0096103c5103c640502415540004559503400b0100c40108075080010400110b070741090307030401032154410001d2000900c01840030820011207141074405281a4580e02c1e00d43d81091100260a540c6260390075050ac0590360803c04183c005a034840204006200a40403c10300c0b041640c6103203180d00d40103000c080010306a413400e076041105041c000c01200340ba16407640c56480c10900121900300110300001400c002c82c0c0d20600c1c82000f11540e2a48441262040b8130a40111800141c2000c00300040c000300f04e000e0041002e4000c040d2504001c640c1c1985942d03c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 297418408 1250 297417158 297417173
    0x3080f0f030f010504110a0f03090c080316060c1404030b041704080c09240d060b21070f050d03050a0315060903110909030a0f0e0a140f0301060311040207050c040504 73
    0xd010326801641886040448104c094061f14400d8003d900c41c44545500c4510450040429440c02d5074422007148002900c001c0a1005022645081c2d03000d03c450003403800c00d031041c1e88041d4040d0742081039580c80c400b8402112419941500da00136010041501c840c1001c40da14044545d035078551181c001400240300c80c001622003207080080e90202c01c155a030012078150388020591081a83c02c80c040554120314060280d050420301c90440003d0a03462034020803130410f0302002d40c04503d002c442c5643d0710148100003920041202d12000500705040c0004216070b00040308005050150201d031200d6500d009403c20029140300560400b10391b0b0361100001c1c40c48949200c1900c0440c2c080c00c0d400002e0130140c100f603202d00746000c000d5152074200c0d03100f15050a515240802001142100591203aa40190003401032201c00020b08038403202c0000c01801007058a6464030a80c5491810400544036800d00c0d40c400004035001602e501c0c1a082250812140a0003913920501d414100000c000c4030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 297419658 1250 297418408 297418411
    0x92a0304020103290409030203120114032a0d0201200303070908030f070807080d02130905070c020a0302010305070207080a1a100e0a05180613052503080f0f030f 71
    0x1d80e020b01c20890301200d100d80f8913503541120540001c03e000c0348103c030305064000304006886841101d01d840420b01401a440801381c014041081e1282450441460104020085103180503080443e0303002d100305440b901400d070a917180c007885050030040250b80c01104419078002c3c540c07003d40c3c00460080c40f0329480303510489070403010440701c200104542100006a40215000340c0700c0c00d142640310384818142c1d0f00511000c840340841007040007160342103800600a0400100b1010001c1da0401c10355009407200140120300b00040540223001582d602e03501c0c03800b1241c0a08002904e40c81e0903704a01305840e98110030858030070b40d030710502000502c20a02c50712001c20030a01b01c0c0c5494101d03c04036140501d125412504031000b01083c00034400c0d501007604004a90200c0707107141c2e00719445508080080b5950285080c1c07252040e400c1c0281030282e00030140b10b91900340190405800c0c80580c0d8002800041c0c000b400124203207810000d1241142d0302d040000c00040d48a252401c18843c12100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 297420908 1250 297419658 297419663
    0x150302090906220f15020f1810050909060f0120061e0105060403080a050714031c1803050d0e01022209021305090411060a020102070317090c092a0304 66
    0x15a2a210360f0070454014045a94456200e0300d05a010b80c40ba030840d501680f810416032582003141c1161000c4480083c058615003110729030030700c04480100010070785001e82d810f007884010440c1078069960902e805501a10880740c007420907058000489a03081409800c0c0380e03547d05c85120039840c2000042c89440349280740024090880c140d107800d54508028802e40c0c3e0400001e00c41030000035045406008606080c3c0b50483c02c00340039466555030300074800e466407095000004c001d1140d50b00040216612203415400740400c02c0803000c5102e650903d201b01404121000c1402c42c05940d80360400200f9034469002551901c10301c05040380159040507503484500009040024078503414000c1d500034244110006410f945031400380440560001c00495032030411038456206565500080d10261038603900043e01c0c0d107000e01d0080d00c0030b003c4900035130000704010100100610005680800d10b0b13403e035480c0b541c90700c1d20721805510302e412054009031541d840640c0c410761001400614400c60 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 297422158 1250 297420908 297420931
    0x2011b0309060506040e280b070801090b030f03040b1804090b06030601080105090a061a0a2301020a0c0603020f0d0507020607080609040209010b1c0f02033304150302090906 76
    0x7204c030380c20403048400300d00203505560001721404503c07070165110340c1c440c00710b240c2e403100303500e441550780d000b81940403501440400c201c0d50040c44002c0741792080900345141503000340086040103400382d030742e07024030f02c100d48800b9400207824580c903500000002c15104050814420581149022084040c040707584170b010303100c0c00e800013818020501a09019640c81c00140c030b10043e00d91a1807001d40990740341d038440f25000e4001e2140688848848000a0103084c0384200d044d002d24010140e00080341044504562244a1043c04244000b515104a5201d070038016501e80240b600025030307008010342c40d00814a86000c20102c180c0100f4410b1242001d6503401c00ca50b50381208100e4a40002c0e0f03006504440d0700801480b03284d4040707008000020902c800c580340c10800b84003181c1513607030086519448680101c144084442c0c00d520402c3c910040c981f2100183d10242138090949902c034164070b00c5240c27144d03e1004003030100e24040016640241c00e015441c50310701d803c0d5a03a00e909680786921103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 297423408 1250 297422158 297422161
    0x617010b01020a030e06090d020603040b010f0501020706021e12070f0203010b01030603330f140612190224031e1501032a0f030e0c09010501050a02011b03090605 71
    0x940c40414060041c03070380b50705c0c0ca960a1441c203081c0030281d0815443d59811002002026015035542c034059841a48141074600c0c240d0304001c0c2d544001b140e01c0d405030703066511244051018a402141004540844119035038451150104243c40e10a004d2400c10609000040d0362050040b01c01c85982194002c0d4001d00c5049800d80045003241c90603c0090000c5500305054040716075004890790b0340b40011840c03074015030058001042200d80d486241c14203c0da40e1020101c8560303104414542c8140101c50020700001d40780045901e6041010220f2002410008000b0071507803103182c404100105901c00005401c505154152150710035660300c540400c049c118605101841c0340f03803911643d03d101d401503013403003a10010360140c03600c80d01a5009402030840c02904403d00c01030003000c0300c120346e6114414034203804090b0441e60410550815500f180c020344050f40c55551805045a4080c40e0956592404402c00ca00604032a29100b017400c0221602801840c1c1c10740000342e142c1d019003000c0025 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 297424658 1250 297423408 297423431
    0x901141f0c150603080f0a031104030314090102070e0a0e0120120c0d02030408220302100e060d020d0b011205060a060c020607122106080c09270325020d02060c070504061701 76
    0x1940212f00c0018006194080780041000c4400701400038001e041c011520344071b440d02c98443d682402240d0034642c071503036003540850b9100c00340a42103070f43c00041e003514141c0c1250a2410543d01c141c111121100d180a80802c64182e4030000300c1e100940d41410454583c01e09261001242e404a819036001001101d92400c105400b204c0307500840b40d000f0950b10000303400003400e60b140c401c14110154130000904c18000240c20070b0000301001009420b0006d8800400780004d401040b000003078001d080e00d00820031000381c40c1c0d250000d00380c50943c100300280c0000c0b880060414403c0c0b4100a01814011440020154004101d00200354106404048501186c075183d02280c195101e45400346e030100e1035444841c10701d5540643c0054031140c20361010744203521155488408404060255840010390010b259000f24684105846000ca00d005020070b40c1c000030945010190060320500d000251201900030402003d4024000600144005662000300905102a84040c03000c80d508060b0030300301 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 297425908 1250 297424658 297424691
    0x50d05011d0f0702070f0f08060c040e070804080c030d05090712030912020105040e10030b06040e0a02042c0c0306010602150403031a0901141f0c150603080f0a03 71
    0xd044981e018410025a03a00c144003414400152101c01940500040464805c0b03c4607102c0010300240404d8180d007614007642140780400040900303501e400c05010922030055074844041d04800c2c54604600c8545075810003c030640300741720840a0324031001904414030221900028400d50200302550346843d500e0024035a80c40410340300a0024640c050b0900001140100c0b00207201d0040c075007541015291a500100c500003074504003040800c003c000c1041001024642e0344c80074041c0e50502203480c4424000742e43e4400c0b80c1d0001e1091392184a94022a8110140741000721107030400b002ca0341215000785a15a0b41ca140a240640146800881c0c00e0f800010b00c0d404d2803c070400d4840b02a80e840e10110024880386101c4800314160150790049562182340d844c2c060489100702d81c101e5030a1200b0060062520480c211011080202505195800450300c2d10b20680000c54441400300e40088400209802d4000401000004c61005003410340c1300040e060074042c0d070300c0821840880710a0440d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 297427158 1250 297425908 297425939
    0xd14070801020a2a0204060617090307021e0117010906140a08060f09010603050105012301020a03080c091c05030a090e011401052802030a090b04120b0601021c050d0501 74
    0x80869105450394100c00c094818000c03e81000340c4d4000703000340c00c50f030025040e03521540c01080010020003005030321503281c03036500e07030001c62007001189090302c1039000c106095030011204501820b00c0e5681c25948c0d00421600c1c0d50b501007550351004a41e15004450010b1003517020b20154203201d02a0703036041d4280b8018400548200c14003c00b00c41d40d4002c0d00030b20f108001003584c00c1e995200c03180040001c40074001d450107400007010b400d02d10140b161085a01c5081c10700e50034110f5120440000200c4d410001143c1c106041c000003a69580a2a000c151404410b00300d1a801c4c00112060074107203d404406015611201d80c4d80c806615554101130070a00002c0c0202c0c0424095003404120b075601442c014250711031071038140c00600d40041680c8800d500c1c4071415002503000081d002d80c08540c041c1910001d440300307540042c14175051a00030081608190360040100c2d0b20100810002e0b8020440f662406039a10f081680842c80d515000304103411052101c40740900744070000c92240348646140 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 297428408 1250 297427158 297427177
    0x20f030c1507261f030c0509071e08010e06042306030703050f01020a030b0d0c06210e150108210c0312071106220209250503011503050105011704050304050d1407080102 74
    0xb4441d02d0301b40b40230448031400203000e450a20a002508034401c60180880c00000012500e881583e50325004111241400c000c1280e07210b5460321900091440d01c0403000185030640a2070880741781e54400c082460150700350800b502c0ea2103440707403030818081d0540042c81030346402d039814001e1113112004d200302d80001c1c40c07004141d028505070610000d4492104003000c401e19000d02100502080c41180c1240c0c0800e20b1038210344c00802007a0500b0701513406240c01042014020682d2070301c03e907811102c000c1340e40300c2e230212808000f610a504000400590303c1d02c05244a104502d400e00c00300c0071b840f110841e010f0709400d0141c00c00013130000d03528450f07000e00c0700d241040410599546900b003003041540188001c1441c0003052004145040031000d0302d480c10001d0320384990703035410408648001c03598400c00300101410304005000599101c1404080c64070702c40b10450300ea0f141c2c4d00c1c0190848c0107a03001207070404240038000c0144080164495049020350341a140000d442e40181420717441804142d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 297429658 1250 297428408 297428423
    0xf010509121204060504020402040509070816020f21040f1701231f15030e01050a0902030304030f0c08030712030c0e0f06090301020909040501060501020f030c1507261f03 75
    0x1c02244c110b402c200d40c0144000e20051030a42c842c0005861142c3c1a18a08001880102005145034103c0c849005000c10381c0010710080503000f0b0150ba40d165640c0710481c01e42c2426884405a1860000f550041c09841d056000303842d0b25140d60f03801000f202c1c800d6001c42e40c20102a221465030025081004040100380c107480b80d038809019904610150001250b08680c401001130407281c0221103c40c090201e65010400c040c1707007000c2c00e0a4401c042c085d20b520301d142c4510840140e4000086504803980701c00c10f07907806003031820140c0b61060301d98015907040c080050201d0400158941010212581d070301c0410a200301035900315000349400041e0b80d082000301c82e298185241000c0944406e07600100098a800a00d00104600e0382003a20122140c1e1744954051025680511402400070b01c1c03e001142010020074045030f85041080c038682e0507000107004141460310030700142c03203174800030b0383c0d484a00c0c265840300905000c0c040b20308034000341c03000b1040c000c0001e001405600700d030382040f803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 297430908 1250 297429658 297429661
    0x80901050a0c0203070303080106030f0e1902030708070b030f010611070506090d1a06030715020309042310030b01060c02033301030807060606032c0f0f0105091212 72
    0x5545a40c00320340d0700014071404001c54030050f82d041103001c001d14070980d581c410b294900b500103016510300c040010031050070182c1283d002c00001581c0c03880c0459070310455401503441d0001c0380c2060300701d0b003224295008400c40420300103074175002507020301c054041d0341c40700c1c2e0f903180001c681b00c04001401082c5908006c074200007a1a0000141070b010f42c00034503017100f044041d9038540c01034005030901c00b0000707075808c01c008141c9014440c680007407140104c8405ca8000245000b5180c1c842c110945108658039058035040c18075000741c0080c00c51407002034203140d0070082c50342c01c0d00c60b6603440f0840b45114014004680c1c244a0700b88400c0803940500141050b81d8034100d880454401c21035040c0040c07840c2401d008017504002e90303550095005080d840d6a80300e150800806031410394112005050a01b10514101011380301c030f8003440d0312050400700c01e01d001d94155509090100034800e00502c55200000c0f210001944480e0003070900310100e0300203801c80c06903070301140187c500e0701407140003000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 297432158 1250 297430908 297430927
    0x6031b030b1314030d060302040608030307050a0305150a182901030e2d0105060d150213030602130f1403060c0309160611160b0315120a0605100e0408 66
    0x15452000d85106490b0f05040c01d102401d0316103140c001d400c004c0d400c1d40e2100010029410f1621554000c2c10500c00554654a012a0701400601c030313902c405020156543c0000b260b01d1160007440499180003050910710664900d54007200f0060712100c5513500b440c020800c03402d42d44c50f000d40d56001000001886003c4094070054000784201c043c1d11450b4010b85081405c0700081c1e007850300800924811506c00440b00c6401c1e5400c503000102102e000d00499882100401c0d0440161a8a205803440c05030742c0d103440144041d86120258002456140045669484a02001e4540060710032440f030b01c82c020380c3c4e2100d1014100302c0c144800c80e0103410200c0031608941603000159445980035040f00c40c0c444d500b03080450b04807210341c4a18002505048041703641c100c18001010301244141208900e541400c004496a01c0050110301c3d0101d550303420140c2e5a114100441010300d408400c0c1c0303021000c43d06013000500811240200e507020b04100100e2591035504c44d07203005075007041109082c0881007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 297433408 1250 297432158 297432181
    0x51e04050f01080d030c05040302090f0f0f010b0316050d0515030d140702100c08030403020a0303060e07090e13020604030c080706051216121a01030c020d120207031704050106031b030b 81
    0x41b1051010480104408400741e00d40408071800350b0070800a80001f4940042c142040440260141079036406070401048420848000c2c3e90300010350110301c4211010001c01515548510030100040500302000c01000748061044501007103800c1d82070b128090810741c412111080070f42c0c60034140c0709041c4100400b60801500c4011001c202d400c00e4045202181c42e071140ca60403c56080700148c0c0510b442d0010554540140001080d840b2a80300260400e04406000141107002c0c040c0c814031040001407038502038241040841c0d402170f0242c0e946549900b40020044002d0103201000d200f41136000924074401c908851051240c080585800d03202da0030555881c51000c1035400030041c801c440032810911034841e861609a09002d90840c0000180003d01a1041c41001c02e040d50001a02d100c481500400242d4541d150a039006a5601180c034080c0c40a4038410800346504400400300820400154440700940780250b0343d03250300040710b65503400c80d03803403a0000030055000c0101042e01000d65 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 297434658 1250 297433408 297433421
    0x306050405030403020603040f060b0108090d1419020c120d05300a0506041a24070c0e0403031109220906021911030a2304051e04050f01080d03 63
    0x244042d0381c41c00d40c2d40d40001d52a07800942e420350b17146000c19030500400005206079042e840c0d080c01d100b441071502c2ca01d02900e0b4101c4da10100d0074480f010b28030120b50049a0100d8103584c0545a44842106250030b00a582c0c42046d25181d005000502a02c100c1650018054039a05a9070356014600f1200a102450580c258060311f0725a00e40ca000300341c2003c00c54030410b44100c011030000a401d2819908000c02e81e062038001c01641020400001660380341c92444d00d00c40728120540300a48000000c0c5450b09204d110380113821122110340c0801d410300c0d4180414040c9000c1c0d50180910048008569100c2c4076440c01176900510340303512101a10140c000c12081c240b034006000402c89065110401a80d0003d070a044200982018400340d0980114528201101d00c100a605040751001d02800074880da2008240f1440803161140001411030700b10350140501402044040760003804105105101a049511442c1804005070f080c00c51920180d0485001f00001c0c040e100300e0349010340042c900c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 297435908 1250 297434658 297434663
    0xe012105010e06070e090f0603061812030702011d0316060504050328020d020114060f0613060306050f100e090c0409060803180109060c0b0a020d0e060610020f0703060504 75
    0x40341c0d4400c4802c00c0c030078081180f1540468561280e80780e0b1a808002154000401d134208000045c4c043c4901e9480025100d94410079501941d03010741c031413111252800202c46901131110000004006e00746a06400405842c0010a14001116000b021140e280d0140103100d80ca0a4200c14109010404541100d90054003031415030b807808440e50710901c00b8002085108120001030f20445403180d82c1000356014020f043e1000308050a07000e182e00100050142150740708034a81e4403001c0c45542c40c00100e031030311019450b172100819550807000d4040e001a01c1341038480c480300d01348801141042d10b00704941c800300b660340000e91403120081001819001d0034000e036040e014440421042050b00c108009030803842c0046841c3d40c5880c0301c003070080500200c07490421490a4040001e80e40051840440c1540a0184d00090351200c081e40000c0c02005030303603412117040c5401c030000c40c140450842e00075002079070314400084000c1400c0c2d075504000c050000041d480843d017000401c200e680074a40051 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 297437158 1250 297435908 297435911
    0x2070806070c0f06020c10060509060609010e0d1106130e010e0c030f1515030603070b04030804060305042d030e0307060906260f19050402010f0509041b17010e01210501 74
    0xb050003503241c0c0383c40d60407c00814500e83e10b240601c440d161010b102a801401100c450340b03010407840008000d816842441401a500e02d00c1000800040080c190329000001d01543d45400590340301c0c0c8400e03121845600d200d030441c44000310b140c59012003230305e10aa4071150b10500d992604000d0803003101000341254181c0311070904c0403045541d1007040070103541c2503940c0e03240c503800d1160030503003402050340c418489010200010400a01e02e00b042c0d8044480500340000c46a0b1181002c020824000301510030002d010003001d001455002d445245050103656a856409070140a066407010140a06004507056a01c20444503201d00c02d0a043e1508100481c100d1903403030300940d41655010360708a041c6180344800c000046d03c594040003038010540405101e41d0903d50006080c2005406031402082800902e2881c43e40340e07a001400b2000c5c074549000010709040c68000e0000c3d207484103900c0a400c44800001c1e80c4c0111300403980c1a100c020313220383c030180caa52841400000c141c050803030301075 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 297438408 1250 297437158 297437167
    0x41b150f11160816050a270603080f19032a11010204141e1c060e070603020d0c090e01051023040510032309190807020102070806070c0f0602 62
    0x40d105402c0000040c8000030041080d904400c1e080e51500102c0d82010340104030045040000352410381000c1085e010700300001d0b4421400b140c94001030b1040c3d40010b4003041c40000c1c0048041c109034020000500c1903150116001c100d4101142a5400001880900d01c151045009043c03c81c8103a01e100301410b046c80b0325003072094640182a41c100b42d0140f5010300d540c00710b131001c44c10081070340319402c100d02d400c54040b50590300000310320000d8400388280410003034241e08100002584044e0b0880d014400f12a1416910040140031b5802807a00103101410709400b60505401000020107580081c40b090409a080405000705002c43e00d42e490104a021401419040710b6035104402c205032808509035998140401c2c400e11700011040002058a0841007101300c3d034041070270001c000d0300c107034808145440b510003982c40e084482c044100e0400340d4036408410800340000403c07035580300b81c082e80c008039601c0401e141c03600e03021034544012681001602d0b002815800094041910808006040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 297439658 1250 297438408 297438433
    0x1b03090a0b1003022e030203060a05120f0c120615010c020901030303240b12060619051c05040507170316030c2a03020d05070509041b150f11 62
    0x9101c055640b98200e1401d14014002d5040691030710701034200a4807211004000e850ba4510f440141c002e1000c101a4003001046281e5204030600703005040050540d18403106418049450b4007a141041e0110712500302c2e0031120b414082a032002e00f40701c000c00b42c0703c075542d415803991581e40090302c0141000201841580142d40c0e81400e140694060780d80000e00080180c1c2810890082c0b1441e40d400c4401010200a10090305003101c8071642c0541c0420003644455011172424001d0340714480400580c2c024480c1b616520a010f0708402c010b0944c030719500098410500201e40301a01d014003940c0000c4010301001c6072540d920b100070500541240e24000c02201049954aa0705104a0006094003050390a0000d007140400034003000300750000c9000c0300308903100744204a0384002400b0700c94032030743d40c003e0003805d1160074002c06000d8142e00c00c614240c580b1902d51285041e503044150b0214202143d824900c0f042110100380c162260510003c071101d00365094071a80316103805511070010030441 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 297440908 1250 297439658 297439673
    0x4080d020c03030103030809010504021018080303090309040f1505062101180f2904020d020a0906020f01020f030a020313120e010e090c0a201c03060e1b03090a 70
    0x7407008020025580360f50652a0042c102040030305201c015178182400c0c0700144c0e44026540500d02c60314104141d5581302d12404031400480c680c0080c202d40404400c0107001d040200080a00e401708039802c22150705400e04500c11241c4104040c2c482a5030650144002c1c10170000800d0307000c0701c0c135645100b1507010040c081070440d030036000a03403251201716980f43c4650b030600940c540c408a484050048888548000176030070030980c0c684600c109049181c14607a00c40b40d04071807000088450640d511000d42e64040c005082038498a801485081c03411155041d041c429034030100c0900240d240307582c5491640c8001b0350000381c803a0300d24940b02049080018590420600903940b29140d43c80c1c450300c0c3d440090310780442c41600307138002c48071041000342c240440390072a01e02804508040c61070300d940500380c0d10795650030700d0004064031441c0510140a42105d0a503103024565680500a040d15802c01540c2d00c0d0080e1925050003000001031b40c3d10346c01d0391026650180c010701c00c80c2e1502c0025283c8c0c16 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 297442158 1250 297440908 297440917
    0xe030a0f03050703030b06161205070b090a050c01210b060d0c02010f0605100909020c030c0d0509091509040f02120304061206090902060304121404080d03060501110c040504080d02 79
    0x30702290340010100c007015090b00400c2d10f00c500c00c407031032418828071039520511103a20a2000b0218641442030f002103500640544071020382050000010380b52078a01c06545130170390b110a840c2031040d254034540d203604c244401401c08048182d5512041c07803a220900140c0007a03101640d100034140040d601c580c07a07520500c06814800d5001092100c61990128125940d40e00410300405644401d8000240c004800d24210f4101040040c0e031a50b280d28140d00754020406c0140d80c0c2e004071142d400c44198080c016280f8107004450740c11541c1c4a407c0c81c01c580b104140140340d0099502d80018001c94031803030b400e0a18074005424032055400d0598400d0565010b41c0115003c00d0052031407140300d4207180300710409002403107020060160319400040090200603c0140318030f161030020f0304428880c82222107948142c1c8403080c0c596840b21403281e26140644030090001b07280803000130311980f0900209003600f40040c040c0800c0039040c8244070240c000200243e0b21a9001c0100d102c0d4003140380f0052 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 297443408 1250 297442158 297442163
    0xc11100e091503030906030c070605010b03070e0301061202010507020103060f090911030601030f20030105041202010e070303140c03090d0528080f0702120616180e04030e030a0f 78
    0x20218031601045101000502081d48903000522440e0580d00c0000494080300004c031011600e0340c0d1000c000780f0786071003004001001d0604140001625130607000c0614000c1d80f81c0e0310f4001c0300a18210916007250900c0c810341c0d0400803000201405540a44d004101060061401281080c0c464200c803805801917440b520b90150707281034841c144840817024402c2100120003905035035140d43c4641040030410100034110014140c40d4407040b000054990b144c003680a0024010b070b18203820312660213500d04050f90f000d5401c0a5850b181c1410203d020803e407940754075100148010ba0300ca916041d0405039210809200410101ea4035644030034004940328403030300003001c3d0600e55005514540118560750014000e052240c00c0019a00400355028690034040712901d4405c2030000032110340424000503007600070b0f0b40902521220401d800c121031442038541c0100b51008090207038202c056407180034001c4a1003004100020304c180810b03c4284001002c880380c1c40300548801498060f2130303004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 297444658 1250 297443408 297443417
    0x1050418210906020106030804091d0d0e010e030a030c12050d06080706140a050904150302042901090509060d0203011b0c0c0e01211b08070806060303090604060c1110 73
    0x1050741059000e6041005451144002d010306031561340ca11141b0b000324050020706076100c00c4a051800045154451081c001008842c030306a00140007400c85911504124006074203c0341c00351103070a000424210309a03150f510082d04861135141c21220001d100d1440040103000c001c1442e5441050103200044c1584202a2424501c0d1450141400040c2840c2c5103c0d210280010760300303c3d42103420fa40c46500141c07000b040040c81c40d468800010f1007904000d501510b081c0801150a14200d40c032a0846803400044a1404080b00191070000c454440ca580c01001c40001130b0050074200072200a03184003030004108174418045800b849201111080c0c002080f9010030130900c440c07552841d000300400700c1c54480c0340d4145820b0f403120b180590564003aa03030010b010081001008403030409203500100e02c0b01503540d00c8460040c1c4841d0780384a8078050748560400300ba51490007100f114048a00140214034040c80d01d01b00b564900410b800035a03903010404407198003919103000e000078101c0940d42c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 297445908 1250 297444658 297444713
    0x1e1306050c010b090f010e0604200a030f0605030a06020903030d0c1e0305010608180c06031e01050f06070f030e04110a081302011d040603020d060219050f0301050418 73
    0x6090860320f1034045540b00e0103000d000d0081345002078400324195140c40304015038a81e11900850003900144200d043c0309000300c5580320025210701d001d0202c0c1d441c03e507414032865100c9070120040e2607840c081d190f03040c0c02141c400e10000e1000e900609041c90302405690500003408104001c0f500510008030100b0407444c1c880040710317103004868440e47d602d4141040300b5414210018413185004041c1d80e00e0010214070403140d00800c10141404c02d100400140d603070b00c0d04030200030315418041c1d608508042c20f00e001241c030346048103a4002c60b400c00340ca900e04043c441c0c0c075115a4146020006d405004105001c050152582e02900b01e00c000c404038010b5848000e400010a4040000e00003100c000d17038200c1410050ba0b0210b203005007601c0a501c0f0f0820f0490400018001309200d0f03000030351003034491140c201048107680183c0012107002c0855000c2c041540c41c2581c845c0b03e0741100011110003000148000c0c90580c8c001d8107005110104001103030010b50f9403480b9400c0c16262883d003410400c5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 297447158 1250 297445908 297445927
    0x3060204120b012111120703030230190c1e0b0603010b01020d030506040b060408010501060806011b02010c080706140a2d0e0f10050105010206130302031e130605 71
    0x380180144211003524051024074000c048013200405030043c0304894882c2c12926554844542c4076401d00d0003c1694200c55480c5006561141840264070300c4800c01c500d0000314181005802c051000500c020341e240c8400c0c4000c00c0fa0b0034071021003071030611003400e0041c0d0105403c440e00391901c5100300c2d6507180302491030410174940c0300b0007044180f0980c104100803502d43d901141c90f03225802e1a082c04507140c1c41700d0b400070b4050044941040d4000c840410300183d00b620540000c1c0c121411510f46407140c3d246d4030011a1030129145840d41002a40d10022006511944203100c0c542d0203000e0307a904241d20f640d41c15068a00001041c0c00b800000c2c030a01002da00da5200300c41c20b0a9841d0420803c640b040c806982040324039100c1031803110340e00d4049500000040c801d480200d4034100941b9005071441d1440c000600081c0203181c010300c82c0c0000281030503031142004100ca03406030002e6040c1034400c20030703445108440c0500c4054050901c10404500321030448000900982c0d10760984800c0441e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 297448408 1250 297447158 297447173
    0xf0221071707020a0501110f070b0406020915030402190b0a0503040c0f03080d0509030412020915030a050d030b2e0201090219080105060d08161106120f07111b01090306020412 77
    0x80300b040c07500007008c2046c484100107090071140e1060380300740200c60f41c0e03841e4103044009001d0f01484942182c0701610540c04202600c00540c86030384210307086040d600280301c4588400d20580a030032098401040012003103801200650b038032034403d00b40c0703100d201d407030320107034403080360194400c4940020104000100403010b01425038051051001142860718104101190710720002c006800303196085d001c10420700f030a52803407000756000b400300e900d007001c0c1e4a0b140c0d6450758004c11910009181641c002002d1810809169407a0300381d00801c0e908044a550b0b01513440d0303002c032204047d503580e844001e0042c2c07a850030262090f142c2200c4403030340c0d614200d500b50948400030180d510411b83d0342c8034240007581c4130040d18020060b030454440c1412461804a0a903640c030b07440c507980a00d012419130a0362403551001c51060440e594181484c1d1291101940c026150380c90f04201078100662151121410b8601c8400000051604000c80da0f5691a900201d0b07005801c40c4d40c01d900c0c08000c58041c00b848 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 297449658 1250 297448408 297448421
    0x3061002011505010c0201020a0b01030c081603051e1509030c011a030a03180e01030c050a050d03081b090a08030d05010b12041502090603090705040f0221071707020a0501 75
    0x990009000c00340302c100311055040c1d4079000d101c2c1408a03140e038070700540e4401c000c0324040c039503c007001604550f10ba04141e042003419226800b4142314180c0105c8215142229840c1141d5110700144410519145c817400303000c4c00580c1e880e40b0f510402da04a0b1300c0356040d000c044d018842c080c01035961403032000480c4d400c0d02c0e240318240301c0500402080621039100003c207030490942501d00701c01c1d200c000c0c0504202d1607460394024460540c07400d001100b40b20000c0c24140031240100d41d03c0010a50701d00074401110403c60707002e004140803100080d44141c0e0100d40b00c9843c446000e60030310f412004030006042141d143c1100d0000d03031011072203c0b0313600e1480c030440e4003500c045a030460901c0c2007000c60460061005100500d10820040300304001b0440b501643d10301500185032540701d02d0000207035030f5980c0c00c45c07151a10450402046444140d61482111000f94120903805201455803c140d48a0f00b000344c1848200845c000c1200d041081c00210380e03003c1c40c42a4040c0580f51204e04042d42034604 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 297450908 1250 297449658 297449689
    0xb070309050f01060b0d020f120103300c0b0403200601080705031f0f0204050a09050405070e13030e1f09150914041d01021c0513080f160c0b0306 64
    0x513150781440400a00c5d002e44034160103c04016070f0707480c14481409040e00849104684c43c1d02e07441d0001c4100881c0b14a0841c80990188400e81d409880070050340c03900d80300103280b0340400c031480030303203c04030b025078000c81d601501030b04049080c2120040001281803d00c1420301554000000601c42080c0500041005010480c01803000d4240b0201c121010401c020000a04507a40c00c54000d490046805607802000d00505c03292010743c1c0c030301c485005000e08480449003070081c07403400714406243c60388090207900d510302d200120701115501079403040105036805a010a440507020544c91004003802c01d100029503441144902e4034000e000c0e10400b45583c0010f002c0c1140f030a124039045810791945545003141c01185070240300b00b0750305140344002c03107a015950001910301c3c64510184840b02c92200001010046596030010000c1d00403c000d5008100420800111520005180240000160329074020140001d2070355084007240156101008078000031081282d107203440f62b900540320741c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 297452158 1250 297450908 297450911
    0x30409271101110703050a210807020705041e0e030a0f050c06070f0507121814090a02031f082d0a0201050a0c0b0109050a062315070b070309050f01 65
    0x741c1d1456600c12401090358100442c8983c0a2032165040003980c000f5601314003510703018000b50400b401c404c0e0625802c05001c0c03254072650001c06209110343c078403440855001c0c118072402c1000b0000940b40d12a40280c9003130807810064607410461240c46400c816400085a0311070040c14007615407443da14000c42480828840d151101001088207644500c1740c0c03030091092220f407841a5028050110040d000d454100b00d1800640d4200610044889201751040302440d5124200c00b180f03240f00304110b40046044021401c01c140c01e0b000303542c001c94003522084519010610381450b03003442d0342c40503045070f004040240c0b151420b034540d17007201c0740d00d904260b25401650810795a151680c402c0241007020001d1032650891041152070304850340140390a059580d00c1000d0070240c2402d41d50070001d10311f80080011048045041050701113808010700301684041410400c22540203030054403560001c00c450720010325602d04441c0314070004c0d2400540501d1034106039243c815038120b04000e5a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 297453408 1250 297452158 297452231
    0x50603041a040309090c021b10090b090105091005070b07051602010e0f0d380106030c03061814091204050909030405030d0503161809020d0608030409 66
    0x245200d0050029841c032945500d14545032450101c94882c05640580c4520340f82130310702c0d0b1156a0201d540107801100040000009103400304004a00b103078211007101082100c403007005403500842c040c141000c01410320342d0400c100800072644402e214403292000482c00605c00c810002c541c2071090b082001460110304005402d103070a20b81340c2840300042e042c049141d00d401d0b4180c0d074442c0c402c12528005800750800300f03150f00c0c2085040e00b5070f040c16084000714410b50141154808018078001c0c00f4040103203516440c0100643c01000140c00c0c44040503282e0f0760205880094040e0404401c0c81444005140d21b00c800e1001c0c0000c201510880454111060074520303449480d05850544204940070001500d1b0100c01d03501e144180d9100c2034141c020100400700461b000b2001e0b501c038100003500c0840218007480211102456492400c3d00b84a8104081c4031008099001c4e24150716103e50029415880b82c846a00c0d50b0841d174042920340c0c1e21b420540c410858100e02000c6c030075448602d5215403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 297454658 1250 297453408 297453413
    0x31b0d05040609050928090c0e0906010e070504050607110f0102122203021e10080702070605030414011a030c04020f0904051b0a02100e0a0f0605180303010b090a05060304 75
    0x40b100c0900c982c510030303042500880d041c440104015650040444501840c46d20607020020261080020640302200d10150004000c02e40d500081d00c240806009007032540c0c28410940451030000d414181040030038040402c050311103000501d805030140303800100d40c04454003000014005069514115000a46c00c1d035400c58034082550141e0812901c40c0601050001c904100a071651b84080d5102c80030358000220303c03604506012007070b401a511041146410b010a0314a407400340c51440040e4803036501004034521950140d03170094070440e8419040c03600c064110b42034448001091405003898404275655107010040912040c0050384d065081031141c0910210794040e8a4049003e11b45500001d01a081000e04d00c00f410041c0e10404d948800d580c1034020f5480286154147c259803074940380b40180d502c0004c1c002066a88204460504081999500043d107405841d514070f402c19080d03800c94866050000d58003a143c45544035881c1c010710030802c2184480c6a115900514007001032001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 297455908 1250 297454658 297454667
    0x2090f0d031d010507061103010905010b030906010e1e090d020601050406031515051005271c030302130e040233070f0b0c13060201020313031b0203031b0d050406 71
    0x1180802e05022a1030503502600589103480741d104000c15641c03402d100c080341310018401841c1138900c070751000c1060340e07255070380800300340702c04e42c1c00344541c1c4d2207040100015500040015030004ca003a41a240c58040d150040389005419138a00c40e007070300883d0003500d07290303810066603005000c00c490038480c191464441c02d115400360002075011a03103582c0400e400350250184d0f88024000a0b114403910500300100520541101645051860003645544030104840b83c1d55038150a0041007480000c09512518180703401d501e400310181341d000c1c484481091403148440008080c9000590304d035142c00d1041190035003412456050480c0c50401000c85011842007122006132440f02c0c1503680c851906100318104a81c0b1001407209140b00100700320100542e0203007425086002e03a03c4d540c9511240e00381e080c0d0008071108034203240100740b200c02103403055011440446141031089420b81c40c540119007560b00103c424860f102d00c40d0003d000200c410001500034441e9860414105810000e0040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 297457158 1250 297455908 297455927
    0x906060a0501030e2104181b0e040b0604090204030303110a0c0b0408040806010f03020f0a0b03070c0609060c1106010906120627060b01090602061302060c0a050a030302090f0d03 78
    0x9042580e0303a00c1102803024100400c900054001c0d40170a00c0c06280c090b60046584240202c03641c242c1904000c3c0740d02e0840f4000c510303070300c0c0d0121052103030344088540480b0707c0508040607503030141d00c808498406403a80001440a030030300b400f015030f841d81581000350079900c0351031408031a19000c1287c035400c0340e4002d0004950b03e0340401c2407400c0742c0302d506041e01940501d411850341c44c043c0d140009100404102d10008030b070300c2500e5048024000b4000c0240c42c9140c1c0c0714080031940d080001540051058000c2a0340d01d115503070000e102c41c05a203841d411202012080e4011410042d960220039004114890042120302014400f242c140000554034030b450000040a454440003207101101607c020145500b10070510240c8113002070815a000d0304c6252481c5010a41d00e0f01c0200c0c49500c0131516512440d0306912504d01e0072819401d000307141e0301180910410307005a0350b203200000c1d0240508280d850096502588030800041000100292450343e10312a00a218080c03000035002100300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 297458408 1250 297457158 297457169
    0x5090c0a0309051c0807090603052403150408090a0e0103170310080d0e27010311040605030709050f0109020a0e0f01090b0d02070b0705090d0b0417071a0906060a 71
    0x21555014529100d882d110b020b0010740040e1881d1241603844c550702c002e04034031560071595060020b40d5102e0003036007154801e0301d00318614003240005001c08c6114030598001e10720003a0450f40c1c0005809110410001e082ea42181c245030000b88140c1c00385025070b8420040c14011740344485951440d0748074a940300c0a8840c50450040200005d00104101140d2400408802046e20381c840311000004203034804400c483c9200346410803c1c1c0c02c55140c1d41c41601100c40e03a1640e04090350b421915680d50341640d41211a600c00d40b1004082400d8070103000d40c0004000382c800101e0380f424002202911143c058001c001864814030480181a5200b10f0245070841b080d41d1050850900c10012151107006422a20405c130000603001841507007940188451801150f84e01899221a0030071140c0c4e01c1007564032507201402e1626030012803c8412a2500544120f618411400394280c004440c0c1d0001c41c0c3c266451701d05486c140303d0300c0d20400440744d4810b00303020140c6454508a00061300310003480c01907 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 297459658 1250 297458408 297458411
    0x80d05040608150d260309120f0c011d0f0c06090d0c0509150f04060b1917040f051006050a150306080f0c190e150607150606030605090c0a03 62
    0x3c9a03005000c0c4031050f43d03281000d880c040c600d13105030902101d00b22410f0214072500b00c01c134450249812002080d60300680c0c412002e0102c41003594030b40c56403500410080d900e03c800070032021090f54000d11517203881000c0c11411010001480065a0500304091500201a0404c14140343d11781c5e50641142d01150b02200d0f00030040d491420a060f25400a41126410044100c203210001d185440c03071071072100b02120811180c508460605c81502c0300c3d407045144000c400d0200c55003560031070b0300d40c440f50001d5181c54404000007841031028544165020317079208090404440501106000c00b080d119107400003484000d20780000304506015901c510161181c40e00740c0000b00d14402d410a000502503031040340c050b81000000a521401050310301c911031a1802d5002445142c4620100201ca4000300b2038521607568481c5025a10600b01500e40e000904201c444001980b4100c00700b00700b521075400240581c01c00310007904458050b0401807055040d0000c101c441e07840403003140c1c010701041c40c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 297460908 1250 297459658 297459661
    0x3022a0f06150603044d1311160b04021f0905060d0b0a090b0405070c0f020120100606120b0f040902150705010c0e040b03030316110102040915080d05040608 69
    0x4042540c498900d03d266410f445005520142c188a0f11b50000c0680603452460058601d5400402c62140269201604401d8140b522080b0800503806078003064008161207150880800c00c6801500d003000c0100c0c0d070902e070503050000350309001d14088900588071800000c144821880541044070724450307a4490040021200202d10300741e00500031942c0d024101e84c160f2515000e0607005041803000311030181e440c04001803052445280b45250140d040300140421507419001100d03121005030152185515105041003010020841400b0340d03c08808000b07182401d0a000a0041a2200c0280822410051000e5495941030154010b030030040b240010725842c00c0c404030700403c0421540044000001c101b17801400010741020364200d08943d680803100801c40204000c544642e0401030b0554418400140740d6003203441042d91804c21420002241d80c0e072011a03609a0784107030843c01032140c480c8001202c07410a4161503000c0c1011034040c0c680300e5114000180b903802540715403420040e8120 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 297462158 1250 297460908 297460913
    0x42918010e010f0f0b040c05030103030e031c0c0501050609060a0e041509080d0b0103060f180902030d0507140f060727120506060d0b0c090103022a0f0615060304 71
    0x50101d40381ca01040002c3c8441000c8083c000700402907100401c07810b5050810040709882d0900c03e0449041403504d860703007540d085440440c0c000041c2c800d040d030144250012100b036040070560201010819a85603100006140790840c2921009426207000780710351011301010b40c0c1d50340300c00000d0b1080340d462420780b9070303039070812604c1140e006a4003002c0ea840d00b0036207002d11160100420700104402420b010f07880904d0b0044044945c1842000d02030308000300e00b4032902d2541d00803516543c6050b40049065502500000d09040792585c509000c01c40000d01c85042040008400c0060040240641032207a2200000307501e40d0801448036041101821b09004140c074440342d81c003071b130000b821003010300f89441e00441c4c408882c611400b87c0381481000d0005120740f9000300c245c0c14043e807007200300c4e1083c0c0312003030659856000310381001d06050302401b1041740d0001e0200f0121050b42ca0902c09103000607805541c1e800c05442019103952a0051810020800002512116018800c2d183c2d036503a60740d50f0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 297463408 1250 297462158 297462161
    0x1c0b070509060d0c050301050a06020d020a0f0201030906060906050a050105160201052101090518010c14030601120513020f01020f03190c06020d050108010e030a09090c0e120604291801 81
    0x8064040b2140b1301075030350001d10f510102642c180e98056469960b01034565800360303a40c214442c481e400583c00502050006084a0383d1849000d01c103044c040380c40c140580d65882030320b607503401c014000c0341d591a003007109103000c4648070300600e028240146010908104117500a2400134060306010300080c070303644580c3c06642c01d114000300814101c109961070300140c4010344030a9902c844144000441c0410444042c820240000155104c1043c448118144125070750002040241802105903044600340700500aa6201c2e00040b081e0200d05006841042589100707641c0060442d80900b0728215081800802c69004480300e825001c0d001520103812a142d0640e00d100904641c00841c008049130710607000316043c1c41003800203104054448541503501d00401d5000b800041e400c3d0001c1102c1880f03907000000f25850b5280031003401c8501804150310004054010f80341d43c2c468010001400f44a0901e21060500c0100d501040200000000b03142d07100580300c40b0086489170b00908a0803401d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 297464658 1250 297463408 297463417
    0x306050603150118051501020c01030515150d1802010c150f0c020303240d030e0a0807060f08060901030b04060b0d38010b030106050f0f070b0103021c0b07050906 71
    0x302120191643e1213a51061340c0310b98244a0f00980e40c00c003001710700b00352440c00c1408020101a4002d280c02482ca40045001d41800340c0603c142c0809100c100d0007030340380d0840303181c4e03c8111581c819030745202c000503090490764a82c0c15040650116005500144c0c0d200c08140e12098000c111090541c4030b0280e0f4100503c5203100381c0814038500740030860455004405144582460a00c40d40c0800c585856070108a65182c1c0b2540d20050542010002902036041f59816202c0500500703107494413520214a8060141c1003100400c0c0d20303154208010743d03c0101e01e0752000080c1c4852120354559950b40703c40c580054070042030349032550350303000c2591111500d00812541020240000410303c03032111000e012000510400350144a03c0038140d5406c0c1000241200d2012124034030710703131812504882c03a40007452070002c1c2141c100000d500e5030041c8005442002e004850000d05945180704010740741900c0f0003492504007030000441c011640901143d036105403681480c41d61400c9000015400d4800c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 297465908 1250 297464658 297464683
    0xc08011a160c0905070207080c0d03090305160f0f240203221805060a03030f050408010e060f150a0501031d010504061d28020d0503032503020c070306050603 69
    0x40c1c0900078070500c10000200000c0f00c01c0c464040125444500d000c83c2c4070321030303402001680e610200035001582809812016094000d1400c40c10207502c03596641d00301090310f28a15001c80e007a18040c0a041402800080100b8254903840c2005103003a4000b081c1f07240100700024000c5e4040042d00c03009000303104454913101c1c0c00c8866050b204807411141a000d5480c06181a000c0f400c035816081003506e4462117028210080c4030106840c070b503a400311a01c68000c90a40c040203014030001a1451003401849047c06040002d00501d280c0120003519084d4001c1685800e0300174001e01a03041c0d02e0700785a05003510070078a00810074468504011090154030781d400541c540c81c12040205001280d4030104e2501c5031082c44420a150143d41c0c0c9540309605000d0f108114032140421080e40085102c01050a00c064401c1c4c5640041e501e0315400d43e00100d60842491501c0c032405801519422590048441103050850900a05a000315558800360100401e299038900110351699030030490450100c9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 297467158 1250 297465908 297465937
    0x170a020921060a0908040b0a020a08030f01080c0a150e011e0206010306050c0f120403020a1a180f03041e08061303030f060e0a0203060a051f02100c08011a 68
    0xc6051202600c1c14400249401d000d0140c600801ca2440050207000122904a60700d1400d05051044100d60b980c0005403580551003071100010020740c07508080c42c4680c10608000c083e0f0740c90700c02003a0800c400c800c5017500c00c9114880500c1840c40200028141d0340076894003005500c2e1031401600c3e800035040340c02035000a500d82c5074150341c8d4000ba0b0319040e05c0c80b0700000d000319114903500c04d030a80030f01e0b44902c0c44500c090202c006404890301000d68000c2c040c0c4111000f82d009078440d8a03a0707140081201c042c80b0301500400400415200410b810508500c005000040c401c1c1d1070a40c03a8040c074024040708000d20201d0714070000c0d00100b07640140409009540090521030075207268520008030480204e814a810000c913900d00d8420f0008076060515110000c1d41d6103000c020007980018910780e803244c4004404141d6440b00000c41c2d0700310414001c82c02a845c0410380283c64500c0c0303000940d034224140f104445440c0c1e030004001d4116083c280c50884c0315000d084016429024a85440c00c011 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 297468408 1250 297467158 297467179
    0x2706090212010c0207330c060609090b180316050f070b12010b0a0e0409060f06090f0b03010501030f03050f0712020105010f0503030c0606010e060d0608030a0e10170a0209 75
    0x404041d0720041400d05076408442406a0f145c0f24941c51480100c41e540000e004003200182d00d042101564110081c203187c40006000a540d601c1c040300d07901d410840c84039650b803c06a0400441d10314a036084440030402c0b43e180d40c800000655070b8402c0a004803903d5242211801c100312040004288480d40d081c00e8a182e103071101068100703a04400d90b0403002501140002829100b04800c4070302040c030035541c40e030903520920b00340801f9041c500c508803403080e991326049801c00c040f40700d00b1028015151011030908800e003004400c0d1750303894204c0c52082c1d240200400c001078044105140455140c14450f441d6050300d000307800d05005100001d0858460400351101c159810b62059041e16511513550b40f940d6150f0051603a40c2c0900c00d521241580304038049922036020301100513441c03200501d250714044504a403402603d0169004e242990710204a106541384c11010703540380b212041d81c4402c1032007034203200104669034828050036250110404a07203c4800e80e01120400c0320b0260170703060344 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 297469658 1250 297468408 297468439
    0x3070209041101050c0f16151205070903080a08091e0604060e03070804080705180c0a030e120d15090902010c06090809041d070603050c041707120c14030127060902 72
    0x1145202c0101900110980c0d0000c1803504040002c2080d88140b80e0f200302ca2440041030181c001e280180c02f0005100c040800040000d00307910041c41500a0f03595607110500703209079a14034207004820f04d81020700d140292594107200006541d030340b20b50004d00c0071824510030011542584039007800503202c11400500440c01c01c100240c200c08807001502e24a05c180c940e004501400c060984003288c0c81704c020002600403500c00d40100c1c40c900d101109541c100b000080700c02206a0182c10502c40458031403c4030441c2c80b40c0f002e40c410081290440c14000c1c500d003540000e044d0440c01d280144210356504019060000c0e8101766924082c01a004010340d80960104114081e03851705551040c1c800c840e40030600178824003a05002e401282265803d00303041000c3c0846000303c004420380c0611130031a00003400c00c0040034012401e8003070405039259a00700440459590390860f6564007036814490005c21481491809006181000c020b11144e442689482d80280c085018040c0d8440301c16100c4402 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 297470908 1250 297469658 297469663
    0x1080a110904080405091e0717060301141b040b040902121f06050a110304061110020a0903020108090a0b090f0706080108060105060703020f1903030b0303070209041101050c0f 77
    0x86160003108024a100500801c202280c2012500203240d03200900003013016060100003a60402c809410601307400d82c20079600b01409008981d40d034009012a544081280003000c0d1041c5c2046040d0028495070040f4100b00040310009415200d000508510301003502a85405031409400050319850b512a40c0342c001c01e000e50000c009540d40c100f40f94011a07050b86e2101d6106003c1e16a0303a07141904103280200c00d48003900071295031000c1c070405050441c05110144010005800c0503151050a4903500210500e00702e01c4411841c4c100f8410407501c80c1d003980040c069001c1300d60904e0500e0060380c3e00c4080c98108461640c004103500110340c140201e41101150411050501008941c21350b0f64491048408820a119000841c0c0210005104d2405c0c520f00170000d0034002c0c01140c0d0140c10385278004d0300c0c00d8a004681c040c0400620242404c048c1e040c05010b0307401c14103d004504180103600024000030004d0001400b0780c0700d101550066902503c142c0303240103041310a036010380010f441c0498 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 297472158 1250 297470908 297470923
    0x712020a080c010218010e0a090e010e0303010f03030e0328080705060a0b19030305040e04080408120304022d1002010e01020d09060b0301060b07030c0507050d200a1a1602090108 78
    0x8003e00c0340c015030405d80f07500c0707907166040c0c0041c010b01d91144203103054540e174001c0c01c0304080805a5500d4601d040160001000154000c02c0070061800c078580c90350070010046102c0044441c42908202c4d2a0240c141003007010386045075078180c45481c00c00305482d100b0828030a401c00180140203e508124507400968440140442c0035180c400d080041c604252200000301c0c0001004100f0501061184422001c0c2d59607019100e60711251806071200012031900c1040d402030182d12000008110031414500a0800701d1030303890017852941d4202d03220b98a074100541c0d480c54014001002c80040c618802d410400038601040001c40d47c1e07028800c0d1410241401010540301c46041440040941c1014492081140c6c940500181440ea05560444003030719168401e64140c4242c40c004101549e860b416000c42603c200c0d841003000201c14220000c158086002e11f00ca03904019040100b1686250f84142c07415030400119030311120a05000c04541454101030f4101c02e800d0f00105062038005140d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 297473408 1250 297472158 297472177
    0x60503070809240c0403050102040b040915061407030207240905030a020108061c020604090c03050f010b040506071b09090311071d07120c0e040e03040302060712020a080c0102 77
    0x348142ea82d0003850315561845458a500d40700b010300d903040c501c21084911541c028803c3c681a52400d65a0b0b2075282c260b0700103801000d035111000404026417a400d2042c00414a6010410b120407454004082e02d010250940707101c81020015094080620074091a0050328581c030040000c400450344181181d03203078003030103400314401403070204241c41c001881a03d082c1e4140d407009210f80d0b0340024443c0c0154500801d0308040209416900103030b0340c0f20301130409411407500c00100010384a0004082c2c2c0e001404240c901e541980050200382860400c850540d171042d07503030070396135201885c10b0b1210f81c14000000030b0040c007808002c02e0003162a0403d00000e030007940e1728142804021003041e01d840c000d2003030032072403050503403c0980c0310460060300743e201c5110300704070420304200300090301034940481619001070390309040500345252500c03540146914070001035041c00c1c00d503404102c4a101f0104040d110189010140100038070070032070341d00c1103540034403015101c21000c11030501030741100a09 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 297474658 1250 297473408 297473417
    0x103b0a06050105011106220f0606080d0311090d032a0b0109060b0414190305060f0118091a041704030f05100b061b1e0303060a210308150a06050307 65
    0xa01c0201c8000a2030f84c000d034203c0c1d9071447e0506000c0005843c40784942012200c0f507a001d0700355400b0421720320507980103000d40ea025101011800701c004040b60940714144011040c24420b0781041c3e203030a904482c00a0303060800c0040b0b1040c0c01314590440840c078601048003040305402c0c000300b160355841030341240c41c0500300b404104d0726210010018080c9001c2c0c001c040c000012020040e240403016000011815140c84c1c1015441c1d0310788604180c1e04031080c03040c21801030010040419113001c4204031680c034660410944101395100426014441c069000007075450012500340002460380c1020b6041025035660345580e6880c0852100c28004002e95290062140780c80c0d8024145c000d811030090020b00d00ba10b041c0c0710000c80e8041d100220580c401a00c00c1540d003060300000301071810442c00e00f0310000e640ba8a48802003202c0180386e5001901401040344005480314100c07801480840e6060a20614503902d5100400c1c10001d000405684401c0000000070074030b40040055002d01110b139503 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 297475908 1250 297474658 297474677
    0x2011d060d02270919020d1b1103030108100203180303010e0708010602060c0301092d150906031a090102090d060509061312120b0d0c0503103b0a0605010501 69
    0x70042107070303c1d1860441d420401e030310001403001204030f00100003200d07103410060400c5540c2d0301407411100c0c03d08140002c1c1084511182910350080041c2d220501340500030b40c917640c10240306540b10700300d5030700441030540c000c404a00d24942d2001e0100454078880100c80d00c07907039a0035203504005c1c0c080d911003002c12072080c0080f5005d440890b45a20440005070b2803480c5074640b10486000341b00050040504c0c2001000d007804900300c0c841045200d0103001d4000c20780c500d00410701c1d2000700300ba510176205c0071300c2c00004100068014036800c10310000070040070346030340e510040240a8462100c016502501009258041004a500c524040c04242e0200e80b003d40d110411851519151200500280c1001c80c0d4004940d2240e22582c000204c3e0b4140414200021030102d501d0a6210400301e41140c00c0709024410b40c1010451425040d49030602800900d450304007110144070403d6203805000c220350030220901c00c07241181000c40800703600301e03007000460707041001c010102070150720b00003081c488 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 297477158 1250 297475908 297475957
    0x20307090909030507140f1b10051201210602070602040f090b1f090b1c0b1e01030c0c0b04050a060606021506040903090312050a0206060a060c02011d060d02 69
    0x10401c042c03641c0c50740b2894503029042c0c0304d40b6100303411302c2c0365907501e84034030041d0f8014000144002814080640900304075410750700e0070046419040091201006828084404481404441c075411a551401441031001e014250014100c1c4603690141885d40000b90071000c10070f00798001c0040340e050b501c0304846262503104040986403008081640a08440000080e103e0300c0224003803c20784c1c80c00c001d6080d507500c801090050b00100b0101c040413050030b0784d0304551401405000c0749440308a941c01401d00c04151004031105007108128101a0755031220b00b5650f019a0000302c082d500071030712940c507180c0b500e04283e07140480081110801c1c02c01900080c02800010401400c2d0181500308000e0354441e02030000400084106501704000380c0340000200314420011400010a96950760b41d50b801004040d04c0e1038405040d04d070190303d41480030080c03d83d2040d400198a40d092070601c41013420500c0004260701908542c0350f12002c005004005200503a005024482c2c44c00c070008100c1040f00b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 297478408 1250 297477158 297477161
    0x406031107030f200106060509030c01030e07060503040302100e010905150601050927040b010f0602031c0b010210060b04080c24030703090b07361223010203070909 72
    0x20200a003c16914050003250a0159401201e407072040500310300e06030720b4046a5804c0d251070707900240202c0c00004560f85c0909081c00700031643e40086c20b052018601d03041c10140d41c0d020b503202d500308005000c4041020076100340311201d15144041010f01c5000440b54809000b00160340003102d1130700c01e031905410700c40f6034040d42c54440c00058561743d0400c0c440c0740c00e022954480c0c64400d0301d90044500c10141002e050000603000b580036038020a1a0740c101002c21400a50703542150080d58414001481056035810030b01206200e40803000c40c0c0d950071a030040c1d180c21103414002924a041900c0410410362040280040354150b400326603c0c1442c802c00d21226410080c2070303452040c07001c003e407119401e03020b0040d50400c056150008902155444e404410442070710940005003043c4d000810a85180304800c006058000300e8008920400407201140e200c0c038410700d040001c4a455410900600170810403603141c17000900b0741c4281101942d103000b5072049950300e01045100c040468401d086 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 297479658 1250 297478408 297478417
    0xf0206060112090c051503060a170307030e030a02031f0c0305091009020a21030e01080906070807051303060506030f030406050403080f1b010606021207022115010b04060311 76
    0x181c590890340750782c044842015201a007800d50b03c05401100000d1aa12010302000c1c40ca10008042d54490034008200200888c560f4041d907010003011459099444020040b1007a99501d0700b4001100782c580000f0a0605c000c502019502d0f008031152038840c605408480141203034400c20406c0b030781c01c3c003001c03d808868068510748040c3c4d10442d2a01c1c002001e0b80d0003130515600040c0080106035540d000b00c9640c0501c0852108445030b40c0c003c0e0410503400c0f403075840e6541400d080c010007515005680e00c5e503c141c0103201e801084032032404541040d0040d07040b62544000303000d003410f20702e4480c18050080e02041c0d8015000c2c4c442e4460a440e19240401a00d0603600250382e040d203007030302d90788540159800c401e080d401c00083c108025030802d035040b9007036200c040300c1d20000700f551072070002c0103800c02e00c0210350301081e508100003010041c0c0d04c3c2c0350f010768150540e01c5600e928034554090b0514280a50480f8104510200e0022912904400c0030b40201e0b0a60b5405105482c0000440d0760940074 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 297480908 1250 297479658 297479671
    0x18030e0906100c1209080d03020408100b0915040f11070507060504050105041a091c02040c0327060b0406061701060c030e040504141c08060901050d02130906050709060f0206 76
    0xc01940e40042d1400084d00b00c3c00d4894030340800955140c1d00304074189218599034034040fa0340040e08020740300c02805408030342745020404129920750000440e9050b1700007840100310648101440c0d95940e41c6601100e11105540f1b410003040c69101c1202c10700d42d00c01002680c075031294100c0040c3e40b0b8803400850782a123006959071400e05103020401c0550011140c00203844400a00c2084155241ca06014040c10b8062040c8141240f10380180412502c132806800d04150500021020f00c1941c00010041c0130244003081a50316050308040000300803001448c0d60107402c100000564643c0801292021001080c0000030340e640c1c5c2c441510700d803c5085008010850743c41c0448020b141c640d0145a0290180d500500c01150743d12500e800c00c090b1007035582070814151000035403194450071180d0300c088151011042541084005082e414010000a100304286000400c03100340d960042d00c0c0b0254031004c06d2020382068240604102c8042c0200700015028030500d480c81031000440074003415 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 297482014 1106 297480908 297480917
    0x40302010e3304030504050f030703060905070f0905070804020d08090a0f140d0507030209060a0308030408030402130c08040b13050316031b0510020d18030e090610 72
    0xb150001d03661030212160200301c002074104044806981080316544c400d60314280009140c0070558200504c010300340804a01048000100901520103030207030003050540792680c15084440486030f0708001402800400d016061441048070494092880d030703482c0000080110300251304c654411307104203100706010845c28205800c0c0116015048504a0b01c1c109113444290340d9001030302020344281d0004010035030715074480d154500203580c0403003166100c0c45d2500300001e954000b180c090380112400140c60a421200d4484c1003c60115a05c80f4038454540745c031840c03c1810000c000c000103000119001010980c108090022821280103454104440c1d103030040003c1c07141082005454000c041d444009500032810b52130140461000684569a20280e5005051076980c01240200481000002d0544c000912400030350140c414030050788560303080c8134142001110380c3d000507 = true := by decide +kernel

theorem cover : BRFrame.Cov 297302158 297482014 := by
  have h0 := BRFrame.cov_init 297302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 297302158 ≤ n) (h2 : n < 297482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
