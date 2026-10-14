-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1641
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:00:51.914859+00:00
-- url     : https://prove2.me/submissions/8fd68063-9cc7-424b-aad2-ac3cca48b2c1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 294964028 ≤ n < 295143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 294965278 1250 294964028 294964031
    0x90308070206070c060903060f02071a07031127060f04030b040f0f1a06100e010e0316030305041401020102130e1e131104060303080c070606030b0106050306130501030b0109 76
    0x41550002c2441441a0000075028039601c40002600c10fa2140e007a0003140c0c011102000b1201c211006041a4400d440c0050f03d5051028001011015101c1c6155000032542c18001107815441c0201c0c2c0d400d401030720681d8640c0b0781074604008024111505a80c24040445985c1d00d804404451300d021402140000b5217400c4c0340100140c104968100b002582540128454004078414a80710540d0f0052001142201e904200856142d040c408203519000e0603030b841d03400c6a0b1a6080044902e190303102c00c2c0c1ca92604c034070f000b040c00714200d58010b103024601955910340d07241c1c10100081c1c541e107070103c00181107a104020140d0600d00e00312900c800d4075280c0341c0ba05081e858001000c02000342e0810300204210100080c00700310003440303110f80070355441807022004e0f1040b0b580410048540b2032001801041c0d03c900058071a807040d0000303102446c49078000142c1d05850740c4035001c0c2248240c0103d03011030800814040f0906c1c01c01009005c0c6529840180910342c1140d84200b442c10040c8241840c0780e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 294966528 1250 294965278 294965287
    0xf0f13021c060b1b1f061809020f0f0609060d0b1810030303050903070c0f06030c2604030212030901061d0907050105092d09010510020a080d060509090601030b16090308 74
    0x43c4040c02128921045100c440b11800110002117004203a244645800410414490303503070089103000b0245840e400401b0040314000400500101c6440002d4680d0702c240d04004034080d56840c04003400c4c034407011010004441070b900082c4282540d0f05401d050b40c001c0500d0410508200b01019601074913410b150200d035a03250408031605e14040c18a00800e82e44114a011030070010718201082202ca0382c2d5020300c06648a90301c20344400c4144804030b40c1003040c20003042149608071201f550401c0c4284100c5500c601d41c46890401500b05031560340b07060351600010451145100d9046510201043c194150b81c24400f035000d41d20100e07449050705000001c20303900c8441d82e41840100000c1a03400700807400c01c8105a00198074000301c281d86200314040c0c80007144134100980c05004082d45a0003d040c868015181c810f0f8a0b00018045840613072110004a500c0d01d62440e0743c0c4c058105030004103003a505500d00107001c110000d00002183c0c0030303060240c2030f04da4414039002c11039402c42200307940c9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 294967778 1250 294966528 294966577
    0x81b0d0606080a0f06110c070902130308040e0108210912100e0102130902070c210204090305030402040c08100b0d060b0408060405010c02010c0e0f0f13021c060b 71
    0x9081d80e5070080c40d85004500b000c40500041400000a00d07104083c10000d010020031100400d0040c03034030482c0b06600114050082c08141e900401246510508480c14241c0e04c0da41c1c888541d1103500800c3c01c007500c4100400200d1410071074600408036011405114035210b1290070541d004801c0194800c0f6458842012414003e20070740c0d18907043d0a4040c0000d088003188035010303500c40c1070401a428950300d00051a981144207890000342d000440d010401d00c1c14142c890340c02c60b80700700d82250250104001c401652103105281c8214800d442d080d40301c0ca0140100300c00c079042c019240c01401000c008104280015149842c152072013440d0300c5840e121101140d000404240e000268a14030006000c01d49000015544d48030b944650700038007030165022022800e913004804044082030bc100303000c070700ca860910103070502201d0203450100501d6070500050842c0914041c5081526800500301801450170300c1c0c401421007040c00c092100c1450243e6070000c42c402c0c03040000c011044900d0031990b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 294969028 1250 294967778 294967781
    0x6090a0902160201020615010917240426040504020d1104083004140f10030c030b150904091e050705010329040c0201110d0213081b0d06 60
    0x50a8919030031034488555540700352022107995000e03800343c49510700042070200310440640351050107940725070030301c0d01d0a91540e2041c555500380c0c080c6801140740d900324001c41002010084200750b0f8201c00c0720700306401c00c200c00e0340e4003c058041001550003000c0d203a0306010304940448002741d40050340c0f0206521040c006003900300d00c0104040300010000342031800015540d403521500e07809001c2030081d24091110028406091101905c0b0501c01000501240100c82125030005000d421806c8140d20009207002e20390070310600070035510201030f0072031540b511075030103104029602400b4112401182020030b000324000c15208a444d40907020800003c0c4040c0b42c444031013200860f1070003185e0b03d040740d111a40341c0221400a80f8010303e40c0d4115811660b09003401034100520b24050b0850001d0102900b10840d8a50541d03494202440812450310020400d45603083ca00580b0360b0703401c0c018521080910703031140540754040c00907020f074410355000da11b030296000c842e1385011503503501d041e80 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 294970278 1250 294969028 294969049
    0x10c110307030611210708040210140a020d091a030a0c0504030807030206070e0103060e070c030207150903050f0f1906061d07020d2a060e071806050f06090609 70
    0x10003042c208105441c0c0380307014101500b0a0540d0040201d1021740300c03941c95454040c1191158000f520a07004a005801d10118a02c2980d00340e140c121885401601132040c40d80c4540f02000041c0e0120130803081c16648600c08030040c100410454120525a00541c4018000070301940f90407580d80078460f00850140f0700300c0e070046600c80c0d020741e1240e096080103505c43e08100c506901240c0300f000031242541c400d00c21042611071243c40102035484401c0c08564206003107008a0651042e002c022a001d040000355480340c40341030343c90004d42800c0d4078006003000002d10403001e81c0d6010f0b0750013500a0070082031040e00003000e0341448250440c00d06009014000e250301c00240b40580003041015801507540c0d440c802c0703145030202da901182c0c03c82d048070088450001c0c4c80c5102d00d124203014032440300c003800c1022540500c0f808601040b02404003800d1107055400320040f10101c1e50b40c81002c8909001d0a0001c1c481118081c000d100100c02140c0356218070038240c2e106110001e445842d80c0d45d18500030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 294971528 1250 294970278 294970283
    0x30d1d070e011d060607060b0f042405090903030f040305091003020924090607030e0312070c061d040209041b05030603070e16031d06070903030914010c11030703 71
    0x50320016030701c2491006501e42801055803466160b0700200d805020065120300600d0040d041501d050303003507203800d00100001c1c014664865481040c00340c043e5140d002718100101d0404001d214441900046072081c000b80e403159014202c80d0040041c140c00110940b503000ca013a0000220b030390b4542c581241c3e94414030360102c5d8024003ea410300c9a641e890740c081c0c06040001d4942c46ca2b541c2c01883c981d0400c1035401c204181048003048442100d080c80c02c060461070b0f100f0b0404043c01c20071800000e00b840c0000d9101181c00b4400700f6140c0c180400982c0b01030041c886810102e400104c90b102c000c0c441809500c2150040e6000220082a42c07900e6100e0811110050b084940000f0034010041890344182c80c003e100e0301c986000415201c24480c0d02500031901008440b4030460103207000d5000d4441c01e001c000d904020b0040c882003812082c481144210b1060307a03060001411f45c0340c080c12400f8141c01180701c4411810254800b80d810010782d1142c1900003c00008007000400000d240a610340c000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 294972778 1250 294971528 294971533
    0xc07060906060905070e1e0604120b070f080108060103030c0f0803090a2009011e03140a0317010e040204050910060906080c01170a021c02070305070c06020304050102030d1d 76
    0xd105026031a44040e094074454102030120781c840403401c0792103400351518254824120f0342c0000d407200540c02d42a00354140075240505251b5540022000d2a802d01c4c82034600c0c0b690f08041002c810b5118040d04619600340c10405815410318002e2503803001c0500004052240000c07500040c000301080303500740300c1c1c0e001811650700e2501803800358868480070000ca41801d07101c0070500600050441010700c0020282c000b540680c0380081c1c2c901190580017441c0380d183e0b100c40c0040b0114000001d11080d050300c1d40002c28050040e403070001d0048500c04c0018101c554080014030054840403621500550111404100741c0c0700c01c4c007402e08000645541c01030083c54250001801c21031034200341c0440d0b0ba04c4d4150307051290740b4801910174940420300c0c16451303c0700320000340410350b469010f0520b13880c50079100c81c0c0d1003030b04085440c100da01100c03050740411320205000301080a400c0e11038000e4411032014504040c60000081d5503400740029032501903807200f512400c00d280484401d44c1441d2035108 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 294974028 1250 294972778 294972791
    0x1207060323040f11120c01080a0917120c190f1707090906081b120a1a010e0a0905120705010b0a0f0e0f060604030b06031609050108100b0603040b0c0706 67
    0x60028031003410307842c100c4800021900b03c014a11744000d212014051020142202558180c011a20103000800620f82c00741e8031081c48012400303125040908408440d50141d44412100c8007040e0b130300c4014000080b44008001403a036444840d0a03141410a4a0074141c1d87d9145007001038510402400054000342440c1040100b130590241544045074040c5004009680e12840e225446081c030381000480b01002c40e040d038000341440300c07444a04000d40c60540f11001d0180c0c0d0b40c3d24204480c200b0445142c6504001031001c10641e186098010b803042200700b041459503580c0503111882c408070f64800c220081003160034007800390029243c42c140180000c052a07110f002d106400d200e9800f40ca00b0040740f031400690380302402d00c46107014620082100741414515514103c50800052007240c046c0a091000700380c091540507980054030070200c02140d10b6040640c1e80b07203030070094800c20801a06200740da1351076442d41d0701240d40203a0012000e078507540d180c1e40441407a20805400501c00c915045 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 294975278 1250 294974028 294974033
    0x504030e12010e0a032111070c06032306060705071d06100e0603070516030e04051609030f0201030905060c03061c02010215190905010218120706032304 67
    0xe02294a1408540d815400c0192000c950700321000e4403892401035104a401304042405003a04044802c0400f10300340c09980d01021034001e88220001e0740700b00140109041080108000303801e00609001e00c0c08114010901601ca00c01400c81a0007480d070040359408215980c0702c0c40e045a45098202e01180c80e01035440410300f00100b114041c00da00c1584a0000c10801d10b8048040c500b031190f1690f4900c0100796400c100b1006500291004083c04400c2084104907050f40c001c1052060094a50700110003068052009071500204001d0a80ca501d0350240c003555002500e8405884c1c0180042c240001c461005900a0004002c040c0140c481c0404110070641d24500461040030103551101e46100c40640301c2c050a000380c078000b405600031210540c0500d40c0c507544264442580d080c06500d0643c112020012240450300c151400c2e5000540c1090180215050881ca010f00b80d42c00b1580341400143c01c1c1d1200a140509002c140e160b102c0c0d800b4070001800c44000901031103045092509051 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 294976528 1250 294975278 294975287
    0x403030605100e04110307020a0602090103061a09030709020310441203040215070203010b360412050706060b0424020f061b07061401051509030a02041a04050403 71
    0x1e98413071040342042c8181c20308010301d40a4030300941440c1c000700211074480c0c0d40c0401a4021b0f120060401d56a05000526400a5114801c3c00c0c6007001c83c040d0384100c2d074001d0500f004516000003184034010002d100090720f0a541d04411074180f034040003644140481d8501070442041401c0354a0100303d455200017908031450040d08900030800c542c0c05040b11301d000c0c02140000c48010303501c0021002041e03141c14003200140400d038801030001130b03040150000901503540d00b08e00c2510b18296200003a9400310200752a40b54045950403031b41c02403609035280b458420350810382e0002c02002007229010030006801c103201170070b84a200304d134030740391201c07040f0f01b2048407403040b546024105203802000340d0000c280480a50740f148007420659460b4071000100040001503070080d4403042110001041440c4110400300e0405074030060154500340812a0ba0b08100296101d106020005403c581d41c0001d051610160b05490104103820300c201c0341c810b0040e500c907600c1c4e04681488208420560311 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 294977778 1250 294976528 294976547
    0x40308040b0901090f050a050409060906060b030702010c0c021302070c0b0301240f200a14060f0705040b0a030f09050a0507080610050f0d020d020a0305011b080c030a05040303060510 80
    0xc0e6100b003000350b511400c1d40c000210351311a49030042c0b03030034030140072a02703042d00400106800b0344c0002c0b07143c5c2c000341d41e00f0040380c000e94051078203100003006020110f1750a00801f00c0842e4185030201c5100d446400049030042040d0036009041c0d400100c001c00c01c030340a56558014900303900200d48941c1e58000c0c01c020340300000c400348511071042c2c90002505004070443c1080c42c98607030340c1c52031102254100b031007070301207010004085108230552200000c04007403c018802e0402c8000d4049802c10b6141c0016005014144005010051000b8403c0341c454100b5101e440c8114074010500c400b400b041c0000901b00100c01611501070202401c00384040002c4403000c0f98910403c40e80180c0d40c41e0800d46050030319003c0c081e0b125014941442c0d203440c002ca4441c009500003801c200c45598a0781c001900b8000e103a01c01c4589035103400c01034620100100c003034004081c80381848290782c0381829002401e0301c070007862407030202d660fa404501810f109601010140001900560600d00c030440060f100f100d2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 294979028 1250 294977778 294977797
    0x10050d15050a020f1b0705040204090207120903020625120804111912060209092a120720030408070503010e010b0306060d24140601020c031c0302040308040b 69
    0x8110214410811503c2240c1045510207120b5040442d0030010402c115130b40040461103201786000400e00741d8a030700c0100014071400c0760059881040386081040c0c0044800c0719400d1080c01e541c10005031f240c407011100220030090190150002d034440c46244200c110300080e12a8541e03035100c0000e00d400500f0035000f940036402220040c030340304041012400698008600405d140b40c0300300301640756a058002030030300c030780c0000d41001455808a4481141141c2e800f038043c0c010b40040309020848003d80306460940801140392045c4040072402025028201d401040540504403890903210308010351881a490b09030799549a0318246140d44110600841d0b200354031b0700322454040b480520802c40507420103009804560348030700c104078030f1017100c01007a11014211501c030380d020107481400c49010603080500140d4005412002520100020040e42c1550700000031014903583c001051801c0a03000d00304d0100c0030402030f0b000c6010b405650700040103001c002ca004201102d101c4054140c000c2c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 294980278 1250 294979028 294979031
    0x403121407050f0a03110c1c02030f1c18060c140405150a120903081618090b0f060408010b030f061605090604080a030c03030b100909020310050d15 65
    0x6948442884045005407054408502d0800c0310100030290792001d842c0e84000c030708001030009051801c88985500000c00300026030170180307041d544448900c20041411903144002e504080d035046614000d4803030700f041310010f1040b00390604410f69035504440b480013083c400b000c8840405143c8000034080c1d00c05140d01042c28160700201c4011690107840854100418401400355092010351242e446003030807104120035134001d2005079009014020b902d51003662001030340e14041d84250241010882c01c401000740d40e1914103c40e05c441840c1100362a500c040015010303036a080061000581c0785144e91300000041800a1604010751181482c40801e23003d961560102e680602e03140c4404070b41d594405200c4a11003100144940060044100301402840c074264840f540c2d107160030041003007203000549030403441c0101a80340c040c130350080a080c1c5981c01d402150150143c504c802501591441917408400207070a100080001c0c4002e1001400c000b40265042c248200000403150b80c1b8121a03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 294981528 1250 294980278 294980291
    0x3060e0903090d0c08011431020d1704030506100510170c0d09050a0c05010503070f0819050f1501090b07060f0f020406110f03120103020d020a170a020301110f0a0c0515040312 77
    0x5080f230886a00d4168078480070784030004500e608024080c4040c0b80c003540c0d94030032507488405000c020401800039600502c01442e41c0c2c40d181c0b204c845101e01c150030641c025030030602400310968002041050384120109440529500e898540304240a11362070510014107000500d410310101044c500c3d00b02d401001010421600e402c0151010f00c02030340c2020000c3e8200b180e44007c03d110f20040c03a0004c038109580e400d23041c401b202807810303140d055420a818541340014841ca0075501160200c0700704003030030014030070f03494503851282a01800c140500000e403140b54840412156500a04600700014000c540766522000001c091101c0180d451102d4403078101050000207001003652010f0381c00000c0001030740c0c215030034021708080c0c03000c080b40c002001e0100491401c80100c05165102c141000030b00885075180101401d540500542524003401003201942001c1150101c0d03400e6035850905c85c3c05000c092030502d141c00c00354100b02e842c50352041c0510040590141c6035035001030000d101403142 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 294982778 1250 294981528 294981571
    0x518070f0602074406070e0111070608070302180a0e0105090a02040803092e0e0307120804060e03030c030a0801031a060f1201021b0d03060e0903090d0c080114 70
    0x720310020400c68038082d0411850003014000540707a0340301c8480d19100c5120950324031a003880c19000f52091b001049070495200c01a507440042c403954074403030000410481d440c1802c0500400d0028110408168000802d4029648180e050108445024011920301550b9240c003103003000003801154031a80d481e1010a90b28406802514183c5281c403002e1850b01e0035802c10441d0300b041031841c6e100c1450040303000140101d0030380e0300a290040c13941c850b91000030140d4105414000140c02c00130b000c4181c0c254003c00b0880200540302602c03110b0800c0b1030701c041c1000020b031a500444c01c4e40d2440d84000a041e141a941c064402c0341213911400102c0c1f050024442d08144082045500d1500f10080c41c00c25940c500c1c04d06003098281c00007900042c600b11401980e190304041c0e03030751518601d6211600c0c0320243e0340e0522448004190180c00300c56142080c0c20a40e48910507400c0443c841c01c3c1d0a85440305205000d0580c400500c2400d0081080301034901e0400796030242201c1c0c0083e40400048410700 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 294984028 1250 294982778 294982799
    0x70305150415020904060504290102150f04030c080d0e010501060c031b08040504020a08010806090613030e0a15030b01030b011d0603130203060c07050106090b060702040518070f060207 81
    0x840e4004036403002c6020082c81e440094010501d025809511a0b40015041d1503520490400e5080e800100200c06224800004d580007074050755070440d40521317400101611b000a07510b822031204011041c03980c40e00d0500703c2d40070600d4080503001090002d03d00c0300022803075204aa5800004000b4000c3d44e90345c60055a00b401d900390080e010817132010000d80680d0401100041c6a0300c1271407001c0c145521000841c040b80c22040344a000715408a0040c020608100b2015601000c40c100801c4185007610150195041040e8001c040c4021804013462a81c3c0c1c003500d1002920031140c3c02d121011007010b008014106082403036012a2521401480303d521030300000f01d9180100901c3e0356103040e000280320403a44000d20b0307000741c0c01c1c1c81160380005941c184803240c001c0107110300081c2c07207400d207050882c212146c6606c02d5004070b2900386000c2c001d45465090750402601154006407964a402c03141500301100e60b10822507008202010810071030010609081d07460a0b4200c2700f40e95202c01c031361b60 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 294985278 1250 294984028 294984031
    0x10605030705030711010e0304090e07090218130f0207030903020f0d0b0610050c07030807030912030f030e0c180115091404090302150a09290613061707030515 70
    0xd00085003040080e080701d006404178000305451030300008800c400e00304083c1c19904141c120644068840c02c5004680c682040b4074409844100011403400860040c00071b41c841100940ea40136001241f58003541e98059800700e2222180720000f5584c0c0c40c500c1c50001e00d04040d50104a1085013200d0fa0020603040c011144c100480c4e1050341c9030002c1c2c0b10041008001c40702d00e1901c404200040000034070300c0c01c00784820f070001c6114004240e01c0b02900d20b0058214005600805840041a80040040303a17210b4090102c00c1102c0c140010409058a41541800348041269030448605010007098030074441d00c0604030741e1720310b14190403520569400c072030807030507882030140c45101c22801c1c402c80d25050b80108c0388144a0b0040300c9100c041603044012503071085039540c00c500e9445d10110203019502c84400d003802c1c80310065a8038600c0c0711420a104800c0030700164003505c2d00a268040d00c1100c0c0c1e00c9440508290300030010102c210384402d5580301c0fa18041143c107401100f01c81d00c00907a01c103194a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 294986528 1250 294985278 294985291
    0x8090105041101030e0f0f0606030f0a0c030605130209101802090a181b080403090b07020102030a0305100f0b19080402090103030c1109010611010c09060c02090408040b1c0501060503 80
    0x10303801e001e1400044004e032413040030b4240385d401002942c1258880c1088240d55042e4100007030205440c291040509102c00260302d5074280d003060034210005010f406101e41600c1d441400012907488a1a07800c4690100043c002c1d040003000e42032003401c8515009038000c07141d5070300c2c1c42020500380002040c00d80c080d8500564108840351000d002520000c122448000d50400d00080c005511140d415481e00c481121000440d05001c14402810307800041030020f01060007c85207004103503070000b0754a21480360200c0405607641e0226031612260400744000b8050000c14044070782d180c0c40e08161650051190214440c003590051140b90300408650340714540060815650ba0b01c2c54400762404121901c00329201c8402c4418400c0301c2e03071210300c01c9000e8901070380c8036000085041111801c40300d0740c5c40c5400c28024242d60402600e42d00a14115030079905171800d1034107807034620384040d20f400760fa00303c201d02c01c8020980c03082c4421481d1000c503001004440c10302013a4be82d083c003070b146032000b507424 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 294987778 1250 294986528 294986543
    0xa29060a050d20030a0f0c08061b0306030708010f0c030e010c09180212271203010501180f0611060106030b010507350406020c012c010c0b0103050d0809010504 70
    0x480b010038031015041da0030211503040225601103200000703042c401008411240440c070600380905100311a19524050600c51006190f203080803080a54100c8028010088070b0000200165190b1005c2c400c00c802000084028480c4104080c00384001d411004031110019103841c42003007004c4414010003c0031100d6172039107a1902d0502e0518003400d10001d8a001d00980c08011220600382e101141da44900d1042c52040e03460400041132400803403070440c5040c0b09900504d00e10021100810880b411185c09007441045ca008030384a8074010f0a4030307032200c0804c0d2144d03e00040c20301c1e00984078a0342034080c0000d85600741e1b280c1c4000e0381101c5031400402d0000e81c00b80a0b00000420035400f4038102406600300040818180d8035075941070280c41c803040391040c00403400304103141d0100103424616000b4200fa510043e095400305403400f1080d02111192620740304014000c1c0d002d000269442a0007040b12407040da1039092080e6030b11424620500000e02c48d00000e814400184601c45c06103522651 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 294989028 1250 294987778 294987799
    0x40b0604050d06150f080606011407110108060d06020d020a030b0328060204050d140c041116031407050f0c180a05062701030b011502060c0a020a29060a05 68
    0x5035000240240c0702440e0703004000d6000400c0c403514900b80c1c0401082e86c1001083c091400d80c0c00102141e0003201100d43c400000d000400001d4100045c40020b1042840c224031250340780c2000401451401c1e4014254502c002227034a6010764603001040c101ca907688040c800c1241c07007024542d41321501c0141400e1f54840241560803030750100741e11007000d401044050b04013503e0340006407520051400c21201b0340c0c026000c1b060303000001c1c0b05c80306148008460802034403012414001c114031448141244a6503031455100c1010301030800e503c030191081024a44998003407410399591040c05840544038401e02c6441801460500e00c001c1c099a50601106440d40302c014049001e028080d00441e8020b4210080c40c03002c80b60700c0c42c060442402e0a0140d64154518104480c0010068102d00351070100200f011003080c2d000100baa801c40621700755160742c0e50070004200e08051140c540100107680c4090000e013010807601c003442c034403800400d80c0c01494039400d0412900303c0c41c074450260014441d16 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 294990278 1250 294989028 294989033
    0x230103030f0c0203010212070c0201080108010c0504060c23060a0e010c09030f05070515250203061807030c090618062d0911070b0912031302120109030905040b0604050d 74
    0x200b014141c6101400240c05c20203440c0e8502c0c06220100e5451000800c2d45004600759a4040c0c055401002300c0b6000f000740d2094440300500521403401003505005501c0004c80801c422643d01700200c12007040c109207c1e0050b9400313103403120f001384c2e100010681840c0c40100080c0c1c06110381550008142c442020342840e540c4d0312110340d6004a42612140a5843c0001d86500e030100e4906a502007941003607642d0100c8070190b801c98103500d03480045000031210080040c2c500141d4180c200e482c9c0d080303122040000b80d21192404440c1d4000070484800d40b80002000d6840380c018406441200c10801c0c441d03040c1c00c10341c1040360624031a400018049d20800f8003402041001c0c1e2a490f0030741e11281c4841921100c000050701c00c0c1d01c800d2841d1a8000820340c0074400148042030b00603001c1c0340a0024810303060210926804054200c040c80031540d110581150344100515a4010788440240a41c000074140074055819512130b480c0100e09090b800016850000b088509a450003408441000c0054 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 294991528 1250 294990278 294990287
    0x30b07020d0221190809011808041e080a0b07032307080705041a0d050c03010e04170c150609010b2106040b0a120c05010309080a0c0203031c230103030f 67
    0x100c03c19018a0010400c60040c50004e1081201240303081c0c481d08801e05240e1152821264006000e00000b480d507404200007440c82c0084a041b50400990000310380c10050b2580c03029242507001490038800c0c0100701e4100001e10801a02c128541c1c0c90401070084601301e50034490040c80381e02015031095a00184401e40640f074034982141c2d0034038000e401c2c6925451413901c056401e03d648107510300e002c01e0b052000a55800380070ba00640c00d00300e03141507502d03146181b008210054402040b5468829030344d005844031209541c2c00040c0c4c41d04407140c44000244241400304151600c901418140b400031900018072012204d1400c018007811089001c000401c82a02c00d014200e1980076445203002065a641c42e400c0030098000105d514150280c1c91502903428006580003506042c24801e2450205540c1c070281e4070b010a844c00d10500c0c500e41d6200107030039440ba2030f0001c4d40c5031450200d40070140130b040d40181d040c55600c0e18401006807000b020418502001d01c40180012040e002121320315114 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 294992778 1250 294991528 294991573
    0xf01060e04050916030c150f120e010f1a1908030711030f0a0302030a0f08070c15140c0901110a1e050304050d0809010e010c2a050d0606030b07020d02 66
    0x1c420303202c44c08881120f003c001c580a9009403440e00440c1c0c014450031140c80b100c481460b882c2d040414152400040c080d040c0e010030a402c809040c0d6030400642404429045003c81f85640c2ea803c03c00d20404030105207205082e1480c0354064a4080119078000001001c4d100560781940011410070f001ca81c0c9174403140c15404509a014040d1440c04200c1a8040082c003032107500c01e0300a90703217991203260000c058448025801c1c081041c035009219403250400044568281c20030700b503034600d01140ca010341c0902a1056145c0c1350030203040c100b1241e1070403280944080d90007641ca9110110b0141c120964507040788074060640340d503507510b030444407d4114803440314920440603207041590760300c0018000c5813040c0c01900d40b40c2c130001e11076040d076a0010351000030b082e09003030030b1803074425a88594000c800c0071034840e1801e92452111f0003481d08150380e4130009180c0200781000c20f461034581880508940d2004a801e9414103002c00c5200f40045134000300002540d000f013080303629001c16903000c0c0f0034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 294994028 1250 294992778 294992791
    0x1514040b060705030a08220b1f0314070504060f050d0f060c0804060606020a0302100c050702120307050c150906031b0a0c0b0c07210203040803040e0f0f01060e0405 72
    0x180c4050088440c1c4400d005090024059000785441c2c900c60b5401800148004098113400c030021361040005001c0000c1950003541c000502a07903603a034000c00c8040140e1580445d0380c0c10301640400004020911400182d9410848203032030910741e80300c3c184801d0f0394480c0258980180c84c94018091410000341c13048501e030090311880d41d103004984410b82290900350b00c82d40020004010401400902c1c0180c100600280c80200141c003566107009485038480340d117440c5243e48a107a1a684140b0130026580e509400905400b0348592140c42d1079946d6200c15811941c0c1d0083e001d0303038000d078903007a10515003c60b804118103140c040400100a00c039440101360396181030407842800210890071002c4d04080c041522400340e8108242882a01d1620080661a0521003080740c10f0000b850700381405841e405861404802e0383c800001a42580585c0d081302d1410310000c0740005054403400c48180c041d031401158640b0320344451982d5501141e09014001c0481d040003090052401c0650080380e1085 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 294995278 1250 294994028 294994031
    0xe0405090a15020f0f2b0b0a0605030601020c040c030605130203040b0a06030201090e060a0b0316022e0518341a03040f08030709170a0201090e0405100204060f020c010201151404 78
    0x103011446c0d4005c0700700c07004940d6070750380e40c0d101c02c20494188031021002030705150034440d055140140000f95124443c400b11030181752241d18642e0303690b00039003200020300002002c01034410f18015101c1c3c000d4104031404d0b100755407982c3c04184003003000d204040940760103941d809000c038101801081840301c0640f0b03040c3c03c460400c0001810004d200d01950107a0140102000c1214003642d000349403281500328040c420300e03007500ac11403005c101044244100d071400000701d559615100070304c040019541c600103041c01070120010703904448007103011400c02c89150002d000ac00c0c242d142c80d848035050203040d409032216a82c103450440054080c551162003242c0050501049503551002d0360401c1c1e5500002c5280904140101c5807801d403c580c554940000810880c040b5800003800c00c0d40c10701c90910211031040c085400c2c864140038400f200300c0030035810b564440d51058005c2000003111602c10041c000d00350501c02540c810300503180040b6030303960b0500300301d07082c21094800c0c280c03406800c99006 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 294996528 1250 294995278 294995317
    0xf082508190f06060f08101512020a0302040e1f0b0f0c010905030408070b0f03270a050c120312190b04090c1406030f070f0e0405090a15020f0f 63
    0x4030194096410400202c46000c542a0303c2c000300038107041000d101c4002402100010000c001e03202800b030404079900046c41d100f40c400101d900b031328080040e500031542c284c00090400d405a0705900200112030000d81c1650740341d0b490140388000c00022414070039842101c07440810401d004a40030f402c801c413005c08181e2030048401a01c5003120f06ca0f0342c044030b090b0400f10b41007020350418003044000f010710f4042c4500e80180503407020440e1000a240d4002286080e802c121013525181009803503140d224106ca0708001c0d01e0030318aa4135507400d040b051144e0100100c1c1c201205000c810b8540c6610700c040006d03582c0d100c1c80e95000510351020340941c61143c4e40d0f00c074038440740d0301c500907072245501413040020b0710fa08200c90902441130380011907010b100104203201e046041140f4080c0e2080192404c42d80c000d04e0b80d08100c2e6078020200210f60701c90301b807100380300e08030030003041da2040c1074070591003107012041d140f515400342d0181480d800f820140512401c0c0c0385020242c010711a0018003080000710 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 294997778 1250 294996528 294996571
    0xe1303020c130b1009030302060901060807090507020717070f050117040212030d02070c0906050a0608010303050a050d09050f06060406080a110a030b01180f02090901030312060e070f082508 83
    0x199020310b8441000105d09010410525405100c5590420740c0c1d07800030f10000782411a07903a40c0380020712805902569a10000d12150300c20320400015205000c0e1400c0c024915070080c9644020b40e02440604488900340002da40d0b001e02140e00004241e5400d0142c0c3e6510b680030003402c030f42c1d017511f4655070380000c03c07100d24110210720081c4001441026020700c414144842d03041101c4040e080980501c020200074003070a5048001a030440b0391514007140e070752100d80421200340c0206031407041500d00341540781013008404154100c000450340304480d81e80e66884100001d136075051280401c2d0303801c009800004038501b104003031034107032000e807400032416540e5440d4000c0f410240d200102c0c500d0b082010310f0201c40d440c01804842c80e040101541040300c40d4000556a400603c002828044409010820350b101900404002c1805020403001803805400160028826003a20300008502e00c000452008074035070301109003548035100c5040d2580d504415603101c8070140c644504400d4184e1504503 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 294999028 1250 294997778 294997789
    0x70309080c1e060609180102070204020f07060b0d080f070602070c240c11040f090516050114041415070b090309010305011403101a06070c0e1303020c130b 68
    0x10415600c50040c042ca09601e440301540c0b5501c140e005585402240500805980f585480c1e600101d02e03400211020300003001160084c890203034001e42081c0080303089402410014040d08140c3e01648040c0040010002008640b158429008010803020b001e1280e51400d000b014180d00391051a00601d4440503494020500c0d01660004030100701c0c00719003c480c001d8aa98019040140e810001e540c112942d481c1e0141c0c01400ea4458042c660350000c00004c14a1600711b501300503002400d80705c000f152060034102050a0b0f014040c00700f00d140090410350303280c03d01200c086030042c0b4002d00c41c0d950080300300140c0c1ba071514022518440c0a00000020544040480c0e0091420400860f40c07006580005000d40c2e4050384500550b044160ee21542524041800100107603039410004a9204040403200001e1283d080182c0240300071401c1010000108980819160103c00c4506290b80d035440820080c400c0b00c00040040c0c10030240703201d8605082000031401192a1004101e440751480400d4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 295000278 1250 294999028 294999037
    0x305190905060109061211010f0c060e060601020d0e0d020d03090b12060405060906010c020f220e16031205030910050906042003210c030310140102010903120507030908 74
    0x210590050001000180d03402d1240740003d04988948086c00c2d4560380b1410b80300094409050705000c804c81c1d41d591020310840e035030350007650300c04810891500f5160049644010446485c0d016200e0746902900d17050280c0f90070b4440210041042500050650900c11080201c0d8011001d11001d848080303444407209028182d441c41d1005208400d00e04401080140d510140c446400303444044240103550742e0041c00041020b07015035910307550407001c2000c41c1d00100d90b074900b20241000540e8005e140710458202c94480d4040c2c500300c480d450341e00e049035805403005100003800c2000050f500b092141c05600138603846890300f800e980c400c001d404008801e80c1c0044a13401c074183c2008007080208844141c0e006400c400d080e40e00c031003401c0c2d41c401207551816401d2007000b40c03081c808000c02014600383c00711105002e19005803a00e81c14018518064044640141142c5844150619200754414852840d0064141c0c0d20101440c085501c42d40040401801a404040e12123400c0e0300800e0040c1d0050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 295001528 1250 295000278 295000283
    0x190b0a0302092b0b0601170403030e10050a0605030708010218010c060e0d0801090510081b0d0210020606012a110f150c01230402060a0c0b040503030103060c030203090d03051909 78
    0xc200001249030451307081da0010000c0c1d05004620307000c94421014214296030003580f6007000118030000000e040d2401d1114159042a0740c02d0004001905c200341d0040021600c0a81c2140c000b0341d117402c4c1300d0342030340101941c107800c031206040c0327045c1c00e50311915205420394016100026400440700340503003001510412107010548a01c010000401c880c810039601c6002820355440e00c03801c00400503111001c03103000314640e014164058090b80ea0301c0c60200c40c2242e0007030215010000c000b00c044e403500360480380700e80030030301e1609802c0030800b442000d0300c114455000002c030f06840d1a614203000050341e03402030b9084098010150070310b803a0000740101d05500004140d456802400142e13094500781410000e51501900300200c02103403201c0c44540041e4100c40381600c400c0302d075104844d0b22200307001c0501a0103050060100b03104000c8021410b99010328418410481c4400c030030f40903844140e9040c005a481030b003480d0301c0c040c0300341d00c000c0c0c016202032620380e400234169842c1c1d0240c40198009 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 295002778 1250 295001528 295001599
    0x40902210105061f0905040c03021201030b09010e0d0c0206210f060a050406050f0d0203030c0706050d050112020607030305090c060a1d01020a170310030b0a0b190b0a030209 76
    0xa02c0a140780c04c41e010781c0c00c11a541c01808108207002d100400807010381c42524003a40e102c1900368500e41c029019998058900340e00c8000ca903a6a0404c2e0722140070503a00301c1111b5180c0b000072a240100460040210790031f50700c52640341d01d510390038410980d219030702400c0c1d00140b00700e0200424240b10200c502034030b10241100045c2c1424002c01c02030700e619522492040b490203104210a4454a41011342080c045496a201d4081030002c64158410030300210054054001d02003905608600504803001b01c46104000b00d070380310b4401c0c12202c402480007070340c81941445900d00207442a0007403544841c11500f9180320b0140c135030209949410524546004c03841400701d0302c0703098002020002c0e4008007480200b030050015107401a004103000030b132980640c7c0010000c1d2400901403100d40040da4403180e0b10109241c00c524020003003000020702c0d803095003038030503000260315204c0403442030340c15100b50740c0c0c5800200c80041c0c0c02503100c6d50380203030890546105001a1500d20803051a0102c00d03409 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 295004028 1250 295002778 295002781
    0x151f06050f130e07140c1209040b150a0306080a0b0a0c09150e03060a0501060c03050c0304032f09060f060903010b03070602060118180b1f03080a030c05070809040902210105 76
    0x140039007001711440780b030744c540801444502e032111400075240051001c80000c15980d04460400300e070280501c01c10b0303182c0001c22041c3d05040102100c6c001c1001c120b2a80c0c0402c507640d115440d26890719094035000d05504200030105a1020841d4003401ca40041030900e1448690f82e140c1201014001d001a200846c2401007030282c5420148038156008004200c200595030400360040e0013428490f4018042001c0821840803c1d0010000c8401440e005100b24041c4551504207210401000402059000458050306607900b010811a80a010010071180b0b0031000034041c040190000078440d5415074807a8a003003000d40302801408058a05a07000d001c8560405441c2d424a884001d00d412a29251030a07200e500d4000403480707901c8070391184cd44811500ea0f42c0e608400c03510410200c10800390ba01c3d00c00000c000c003100041c44505460b45080c003c0711078190341500c060040c14800342500c1000c120f0311400d4581a40040c04951004000c1a022580b900f0343c541d034041c020000182d6a0764410 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 295005278 1250 295004028 295004041
    0x70c021908010e030c1c26060a080d020c0919020d0b01020114090d031505030303240a060903020609040207080313020f10200c040905151f06050f130e 66
    0x3440c200e50000c0f10040d0314044120000e182d035580401080050001e500c0101c1140d5480780c1c0190702c1e40c500000b06c1c46003d8101c3c60080ca00501d096030b403d4401d464681000800f8400072421421a0001e5005006c0010b0740c0024030040f940014a09420488182c80180f0308604510250108559000d4005001140e0320006030844800f0712042c9401510b10301000752900c00096206c60041444ca000301c2e02d900c80356402c1d0741c138006540281e0b40c18000801004015644c04080c404264000010007103202e4080b02403003d043c5080c001c500020710a10810b00250404900070004200040c2006142840300e0b2603c074581e400c1540c451035910b0302ca82d59401540341c100d036100160901180c04a58010003c00060302c07522840082480180d0054200c40c92488107110040754194050001d01140c3c800d46810f549800d284458007100042d11004920140510f10b0001d00200c90380c0c040b0841d041c1850000e6030140c1080300c901030040300030050051099217503400c04006028240d443c80c520b040c41d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 295006528 1250 295005278 295005281
    0x3190f0c0216300602070b0103050a02130b060a051804020f0c0c091303320d05010b0403030c1704051f0e0f0907030e0703020325080109020f0603070c02190801 70
    0x25070010b042c8410450388020b000c5021500001e22075034150f00300305880c0082c41c09501070301920b6030242201201c00000414003a0204502d101c6920841c1d1035481c0a1030081c0242c1120401d0581c0c0c0c4c0c11100c103100c500800f60180005001c0d00c45200c035071464003201e840000c1c0907030b4411107120030404008a5104d00c2142c04001c02c200114040744c00a1847c6040d21115510820829002e0f08204044000241c8000614141190700c0307440000c00005100c041402035490744150490105503103004c000244018100e4103450507a90701d0340d0b88180d648641d031aa049001d240d01482b119008041100107840d546082001c044022104c0001d600701d2346c100c81c0035100b095918240d901a0b04404443c1c4c10301e40d91203a0980e8040b120741800150b032948800300c0392411956420094040c07140e5071490160045460b08400c1d000303096a0261105611140c910b1f080c0e418605000750030542c040e0840b4480d1a000e00611384c1301c552486d1a45032016241c000880002c2c01440c0340060300451001440fa6100a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 295007778 1250 295006528 295006573
    0x15050c0d0804110402071b0b09011b0203060c1e030907061b0b0604020c0106080a30020706030f0902030d08060913080f0703020f030301030501060e0a060b03190f0c02 73
    0x80c1c00e106259203060f0700d0f9200b40c040702403040d03403049034001941c00801401442040050342049075400c070380c9440300400003959203d0058940440c40c003076500c4018403181c41c00000d0a643c050040d018580302e4a2100145400c0754002d189040c00201c0c130051a601c2d220f01640c400c0e03450364000d0503000d18009000e45072445c0c502c507903031005c20080940c0c00806d001440c0a0f070401000d40c2c0042e940c05115000e14010200c50308a254240038a5086800340440c00301000055010f460380102c145400000f20b0040c1045011841e0141c0c221107020459940658070142c400c0e0310425001c611084c0690000c0d041c045c1d55141140411500030920900303081810030150320a81804405401540c0354030303072048902441c95480d492000c0003035190101131080c004440491101c008690312940c40e890403c2c00780c1002d0107841401c082d00000100d05c01c91501a5000719010b101095186032101a140c0d1340c0c0c51401c14544803101c0d01e55150b103400400d54455010f1044840d4080d1a02c0700d03c2000c4101304641 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 295009028 1250 295007778 295007803
    0x9080a200a15020610090b0d03180504151d130b04020d08071506140f0d080f0304140c0f06040302010c03020f030c10060b0a090b0a230301030b10032003030415050c 72
    0xe00303c00d0f511f0503241e01c2ca8400500f03030141062494841000200c140e07103401900126005420322503001c0a40040c0c50b0f40f81c0070342d0365a08804010001a440c0814903040803580621548401c0140c2404134400c965a180c01038005000d030a03240300e0360703122040c05601002c070850b400c81c074400c81d00b4541c02d80c92240c03070040c0502c43c040c10406489a00080c640c1c00e4403601d07062050310400e140d2400c0140703c0c011564a01c0d036162455499103840d05200f1031107000c0e00071001190044140c1c03440140b403c007419003d0f101008000c0390415055030011a0041181c14040301507100d52946800211401c00140113106900c90081c101c080951031447e040d42c81c151b003c0c0030713040300c140251640d15030445005800c0e01c1050500603150040c5803812a1a40314502c1c3c03401092240302030b102c20340006040218143c9001d20031450750380e00c1d102c0124401002030311010301801003241d60f441100c0b03811040008a00b0340202201c4c01d00d600e401d806501c881c0080d02d981e0124000083c2d088043c10180940400d010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 295010278 1250 295009028 295009031
    0x301062607080c2101060c0506010801090f1707060905010c0f0905131808120406060b0309100203060102030903061303111c1803140d09080a200a1502061009 69
    0xc0040026182d40809840600c800070003085550111015810140508402c038082c000c580d40c2d10000504040121003043c3c843d07015200002ca4440720500031200030b40c1d0300c2003881c66918129154900d4165500f0101c20945200b00000c074041001c5020382d64005001c0d800015000000250241000080710791403c02d11860080c00c03c120781e40d030010f0711030702c00002d080803034003212055583c40c40040c841c070000c2c100d010126032150211103200f07080348203510900c0c003049821384800d6680c9039800116a03c5000d40c1c01018001c14820042c5c001c0c40d00007a041c011a420030b004407000130300b4240100c031280c58100104807194185503105052803100480840686019442c041d10050f41581c4403034148244002a032803070000758400f00d681d50065410208018841682c4803000ba21390004484800c0042e07094100441e866001065044000e5802114111103010402040ba0100d0140c0400c0364082c41da85000604030fa00140c42c0000104141d028110342d1030000b000c2200049a50030101016 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 295011528 1250 295010278 295010281
    0x10c030501140a1a13050612010806060a0b0d0c091d041104051608060613091e0b01170c120c030103050d03060501080c091f350f040807050303010626 66
    0xc92035068100000c502135003403e5651107490f12444640141d40d00858201800007041d00b54000e000c00c00c28180c4204c40143c801d01d440749820088480942d0107140032040040041542404066111240c1c103201800c3c6400d0099845600c08444520504840d072030007886010403082200c018002d0741c4105048a04112a080904500000101000f01082444920800304070345945800665140240b0251500758007915220010301500c0300c00107804100d940c0f640880c0000d80c1d903000f4030341c02240696441d40741b402216080204ca5a001d00220360484003001100320348800940c401c0d204010724400c003030b625403452410ba40360903201d20b16113041510300001401039a0388140310702c1d08103040c0c03203415840c0c4241c000000c0408184180c85000c150119111503540c44d00640c0600700402040040207008400014419041c010340201400802d814030010780c5541caa0300c6896003141c01607140038101501551502e01e154000e0300603001048941001288120300081508000d4421400f604480d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 295012778 1250 295011528 295011539
    0x150901060f0510110109030c050d0e15090f060d0c0f0e060f09030118030201050613020c1213030c0f05040e03070f02040b040e1f27060f020903010c030501140a 70
    0x3050550041a1040d02180010003405204010050411340300c3c1d4001c000c031030b0007458043c0c1070429100085809000d829114200c5038000e8103501c40c143c4001c2c0c84d9041d0310340d01c008032074030310780c065102c442c1d0100060003840003e485841c00750000d00c01d004000201300511000c05801d1542e112010010000500d24502c62078440500f5100300148007001c041e00c4c0c5002100090140c0100b40d49020611800c0d00a40140359054121500403101078038020190102c112841d016881a204208071540c41004044801440c0c0d80080c08a00581c06000110702c2e100ea64a5040030341c19030225034103001d00f171424091071405120300300036400a18000c5103403451a42e14131103801c52454029124a50340d0890349182e45071900848000000c120036140103103082c1141c903000701140780c80040c00c18074024840070314079800c0308004480007541310f007201a8023060341c03000050300940e402c29013003075001c0c00100c0c4107031003d010350101c40d6030703d4901140030b60411020b84401e1914a408510500340c04004010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 295014028 1250 295012778 295012799
    0x10204030b0606070c14040207080d06050a0603020f031807150f030c05120610030f0e07030516260304030b01080a02152d07020d05060406050f0103151d070815090106 73
    0x11580e26140c0c01200c440b00b0b000090007070127008000b41c9000d8001a640c20342000c190705c45800c0d501c080f12007850403611084200c040f03000b500c1030110410020004119200480062902d100a1080456054540701c000e007000100002e44c000e03001c1981601e101e803070706030507010302d0310802c005240141c101308440c11000108040504001e018404607404040440c1c03007500450540f854840b018072200070051038880c1d070f440280c40240c4450007a01501a54020400c0340c820440715101c248100714030a000c80c014948200744d600c1151844104800400180310020881c000c00c1c0c00c4024180810f079500506c4192b00705036810090a0701c040207552000c145402c080c01504e10341500244c1f15071195442c1401c00d00c640e006c00b941c429455101d020801000003801380c41544110701c10300c039503141c041400d600d08000380001440f68503110380c010300c00c1c06503074000b54490b0501200350482d0343c00c01c5086818685103030001c180d140c0110901f401c2441d04440c01b9904104560000c002c043c0c503100b040301 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 295015278 1250 295014028 295014053
    0x30506010e16120b0406060509090f040b010509151c1a010320030c0301060b0403140304030b07111e030a090f0509010501050901050d060e01051f080f1003080408010204030b060607 79
    0x40c840c03090f400103e00c1c440f99001d68903c1c14003030b100704402629030801600c50b80003000038602c108900f02c00180f5048840d100c1c01c0c0115485240021180d0802c41001401c00300100404004d20705014400c0c420f0390741c1708942002d5042018074003412200d03810865240780305484da02c018201c043d001080015000000710401c1c6010b4038614043e442118000781c10403054603c4079034076600380400818100203001c000c1c0700300c9210740d140004595440c600782e5240d000c0c0d84400380503040ca050001c1e2640b80103021081c40e01d4916400e03605903035081c0b0f0141121006803540741030f0b030b0345c0081148841135801007251400f500d4180c1503501a180741074001000c0c032205010b0035041100204000032941d0040060b503079004810002403281c242c80f4000058854002d11410303106c1c08445030102005030050b44086555030041d03403030750321076604c00000d8446c1c807001070f10206485034a064000701241f800d00240019000040025030b0351031650130440c480d0319000d0030040c450002005103400060a0f403082d40b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 295016528 1250 295015278 295015321
    0xe01050a0c022103040b0c0d090803090d020d02041e0c05090306010311210a110604051309021c0308250210110904020d15290318010213030506010e 65
    0x14001000d88100c0c20f42c90381c00001c078800c031511004c240460300740301110250101d451000101d4060429074481101c0c460014801c40c14a0b800821a090342402c000844038441170000c0d00c50f01216080364081000c403441d08031030710207a982c20441c0410030394643c060031824801c41d10b003490a00c01000b000946400041c0b100030002e244910404e030307040c0c40d04203803d414161f00b0400303004000d80030350b00c5607281d0240040403180124544400c045900e4544c050320f050750400303400160760001054a040050030b5001c401e03a408924681640420b2107140d0104224a2003039542d860541491070081304c803800b800ca0002c14201c248001c0c40009a40081e40c0e01880e11614004513940c140c04c3c00e150f0152090b0608160040d000150241319040c068108003480c7c02a2075003172001590318006004c0c0c5551945016480050000800502c0103921000d5038103e9a82d0503004500350b81c800d42c081c02ca0b400200c801d070140d840386000b001800340a0145500500d850b4000500d60b180c010343c9170300b8020015610 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 295017778 1250 295016528 295016539
    0x1091404020313050703033c0507050c060a050405041b050702130f0603080306030d02070b0f070614010909051207050c040515191e03020d03050a0203070c030c03030e01050a0c02 78
    0x50061400020714168003138002e0207448000d9102e040c001c004181d41204c1d4002d1041510013400a4000b14021840141d01c009a8500030400068102c45e958007140d03060b1468072510700700007140e65078100240000009912520366440c07501060105662503000f0049a00388004a000000d51304003007240c44290b17044844e1640281c0584100c40242030495040826610f010000300c20803103903034000e602500c000c13411200901c0c902c4201301d1307840c0254017640034194014400b810050440340081c18000740306680100349000c0c2020b4000f00c1c000d007603100032025900c40c40601c09118091003048544100000711701e2600710252503590ba9000d99000c0107010b44d50751000254601400400b04c0040c5000515000007a1018a00b01d19054a18040d180a00306000c071380041c0f94070164990b1003220780c040c202148000168905841c95000400303c4000d5000c100f007020001004841c003030014501c10b4602001c03103403c1d42002000e046c440304009042c00020084100a150005000c082040d4100c42 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 295019028 1250 295017778 295017781
    0xf18010e10110d05010303020d1e0e060306030109050312041704030308150a051305070909140105100207120311060f010b07060e030409020a1706010903030f0809030f040b09010e010914040203 84
    0x8218025100710315054a44600c3d04c4008400c040e800b19801007080c8141e51200708413a0520300a00d83d500300588168045400e8075400c000310308020000e194041c0008000041c811800d40b100c0381141d0201841140c00c4d0082000c000402142801c0c0303404004c02e40490030300307041c02c541d000380c00054003030055008541c940110034010755801c8041070240c00054444240d200c2d01800c420302915041c0c2c0c110000c6881c52601080000c0940310f011705500d034040c410341050f40707803605201220032914181011806044030210300c002076081130034034a41c072959a03030605041480d038072410a00040d0001c6001e80702203004018120680c404e03943d0721a04941c0000341d003044501418550b201d5603000b00718040c008074078050780700d4000c690450794000881003440140d0b20100115101c099070301005000c07403100145174540a01ca00c3e803261b4401c040d04c003201e103003000e58080c1503042e0300280e00c40118020001050350f00d550780400505032501d020300302420003a0520351090131a10f0700b04082e0f80500d60220 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 295020278 1250 295019028 295019051
    0xf010c02060f0a2a0305010b031501140403060507050c0d0201050c09191a09090604020903060f041416090e01062402070509010906060801150518060d050f18010e10 72
    0x44c00a10b10b000c041d26501c20342c081c07140540301500e004284a0b40803d20304800061003134204003c03603110700c140b039500d0144030503050019a41c11900e1050100814010f00000c80050754520501c0d001d248140c6039140c80d070041d0b80b11070385442c02d0030302d0540859040505100341d05c1040703002c2e5080b1501c100e54400c0858140d403580040581c1d2540301d0b0422001c01c1d005d00c104003410a005099008041d14004501c6d5600710078042644a003c00e0903401d030344030000003160243c2c42000d42ea00140701e003d6180f43e16020765401e5140120101414903401402d000402c2404c0c0710b840341544508684c0c000388040792a014007000300304055099500c0c244e141c0d100031803a4501c203011030710241100800d800050352f19001c42100901072406004007248000001040042602c14010800d0700b1548d54645010700141c055038020440300125500702e00c052120450001c8140200d074070410061800008501d044901c0500c6140e03441314a5160740d02d4500c00200b114008501c01080f03d00f00c001c08a1480004c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 295021528 1250 295020278 295020281
    0x905070b090103141014010201051605090a0b07060506040b04050f0712060b030a150602071a0d0b060c010e061303020a0818030f0f0c0609100804060b0d03020f0f010c02060f0a 77
    0x860f58044c1c043e440810488201803402c0b040c03003a10700303c034250000465801c0c01a402c07504245d9242e00884500c6c0890f0210500c01c1c0c0c010121018003400c103c1106584a81800d515005a60101e0707105444204000840c140f80c4102c00400c8000c880500940c104807929110402e400781031401042048861010341c01c2c1c10360081c00041c030000460340d6070b91401b51000e41c01080380040503842e60154490014049200003800020703219802403a081d115a410110411a441880804603003a100d840f80c1c0855580c3c0c0014180313840b087c80010900c4600008418185540100010351200d4200280400700ea400114047c1041c0d00400329603480300c0e0f80c60100d8900340d0342d80314168036100c3c01d81400c0115070701045810010701404100d40009c00341d40100a403a0140da40c4c010382000e04000800c04403440f907140ca80e04035006440008400da040000301d0058003980c00140d0141e0300c8107011907018501040a10600d0074904020861201c40340340c002d40340d400c0503003030a00d801c184501044148105 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 295022778 1250 295021528 295021541
    0xa0213181b0f0b1b030c0d0c020f090a1401060207060f030504020f030a050d02211c150b0c07050405070c1202030c010501031203050a0b0105160f02120f100905070b090103 75
    0x44860b1a80342d91190320005990109000d0012a0310f00003c0914029000050340d29164890000d060b000700105402c40d1801c05000d0305030b9010441d14207142c5c0030340b50005007901402c0c88940200304104084143d924120041c0c0c400c01c11540910009c002940d0f100000142e2100c051801003a82c2d1114000108801126004582c1c18000c0d1100c020400800091004a42c881c42c0c09451016070207005060000039000010700001e0010011055000c0d00e0841080c0b03003502e4440f0004140c0e00100541c00802815000359400390000180079960301010407401c4000c000488013440315241250300100001c0740550010504c8001088091078907000b8000d56805001c981d0080120b50781d02c0c00e01c1030b14640c03003a000e071000c41c2c68840450304807607003805040760a8106841d2113181c0011201240305051400c08196011420080400c1c010380d66030210760045542e140c0102100d00e404800d00d4181281d1101508087e0310b003450600001d0310206084080711428210191035403010360069028020 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 295024028 1250 295022778 295022789
    0x1120602040f060c020901060e0319031b05071422110c1006030606080309090126011802031218010e01030b0d061a040c02070b030612030c0a0213181b 66
    0x902c9200483c001358810080d05440703008036000541644d0b9018162041d02c42c045655030150841c00c0c0350351100e140150021101c500c02d141602c21040c012040700e6107104600021581c60700502c034100900c440005902001c00f8003101d00554104645039020005002d01d9201e2075076507291000318400d058480e080e02c15143e85001641d142009400c3302c0710092085010403205285881030105142c01c0000c1038481000c806001184035900f82030084107840d2580898814800856400140031070302030046d00c0614814014180c201e40c032501c1010300b00700756221800c0c2c0403101840490055115008500504002030a05110000c0c203140100c000e020560302541d0040d40d2045c1d100c0401003558040ca01c2040d40d070218050202d0150100000e903001c0040d2880164005101070000c030403040000c603005207004209800d0400941c02150a40d0022003c004403500310064903415404c02c80c0200354500490b02c0204030038040362400c040720f0281d405c00908200246408840000c0c070403001c0102424 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 295025278 1250 295024028 295024049
    0xe040902180c042603120604060f06261e07050f1206041406031510030204060810061d010b030406060905090a060b030303130f061e0203040218040b0112060204 70
    0x240c441801e0242d03502620031405004100c2950074a14041481441c0c240d40700c0d000030b103190000c126900c07201c440e0b014003402c2c1d01981e9288005071444022145d10028000d03520b440c5a08500c00e0240044042e200a091007481c1a841c200304801004604e008054a203c014000c0b15440b059001c40303940c05042e156800e000800038914058148503c00b040c800e000443d024481c41103086811243c1080070f0b2081034140d4031190b200004c4c00c03401d03410350358060040b0b1040c0180ca46e5030340001303081d10b001750b02140c0c0c6a04444841c9950916500441e0064101d6501c10030448484405848000740144079980c3e600b8030100c0031034208610340d04580014071070158188414200758500390f13142d080d2050119821440d02c0c1442c015402c001c01075a100361031540c07000040790a0703900d52000f2382969807400c841031662418200082601d010b0813000d0201004001038407807900d407051140b0411445904111400b130307002000005201014101c3c1941e02040c3c2c02141c1644078a031100190046802c0f00d860385 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 295026528 1250 295025278 295025281
    0xb1b0a06090b070c03080a0903110102030c0304020a0b03040503040b0f0c01150f1d06010e1302030907210c0b1b240606030c030402040518011503020102010e0106060e04090218 77
    0x20495801811201e4011942886980c0320810700f03803440da80444004020540c1003000030841d031300310707402008042d0007404d0044611102080301401c9a108882026100802005001c2541481e100d120060b000c240802855800c240d11030319564040c3d0f00c070701003142c076000881150510745041612510381c00c0a0080c44500071171310207801d441803c1e000c0c84100d001c0381e610000301e103611140c50024056042d81c89014a46641004680e01c86241c0b40443d00b10000b00c10b0711000c170b60b0901c002d41c4511142c030050a42141400c400711101c80072400c80c1a110328020003010003082c0d9078807620081307400c10701809030b803001000d0383c0303010f5085902c041c0c80300d40c0294a0760602c19525078044526403140840920801c0c0d8440e0704000341c0d400240c0710300a004d401400041e0040c20980c3c44603411000207484904103d2004d00403a00791046031501a0301c5141385e440810442d40c090054803000d2807900008d0001a01f8085d00a184000529225114a480d810410259190b1105d80303c1050141c042840f001d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 295027778 1250 295026528 295026533
    0xe1f0503030a0f0e0a030201140d1410050102010507030507020d03050907050303071112030412060b04020d020409020a08060618150408151f050a0b03090c090108011401090b01090b1b0a 81
    0x890342d80b00f491000304d040000c8a14030b518001d4201000e4075030584510100c41c281e0f91508006410503401180c04580e21070410005051488031240b041c800b074600c400e403160400c03000a00f074440180480f01498108000d004245801085070045c1810318500002c056032050b0b9001c4c60000d8a44c05650035001c00500c02c42070081d08038102c40081e500341e07101d205010b89010003136034901c182c2c42a20500d01250614100003444c42e00403e0b016040200090700309008d8440e110200e80c81541304010303072580040c810180320b402c02c0d6010b034055001c480240c200702c1811078410402c1d1340c0d0904e0724400c4680345216424450340e035046da0080c218402c100c4400c0b4500070000001c0a409035100d1101011030302140b60070415001d40e540135100e0161005051918003040343c411a04083c040714a6030040c020b01e051035131248044e803070081280200108000c540c40050200418042c0c0000c80401d041001c151401c1e44c20100340c50481e01c1496500d5a40c01d000740100381e0240000801904500071403804609 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 295029028 1250 295027778 295027787
    0x1a0901020c1201091e031709030f040e060f0a0510200303090604031803111e03060c0306130e070308070f0b0f100b1602060901140708180105040e1f0503030a 69
    0x9020303103d80c05910f03c0d4002e907005c104203680d280c42c0080004040c01c03034021006842410080d000880c02c0112401c043d04500d150030260010b401180c071103081c1130704100b034a203044011045250383c1603a0340f070744440c188400b0a112044a0800c0d105000508454180d00880041c2c40250f41c45810192522414001080d580f41c07102a20150000b542d44038006040c9a040351802c02166071042641d148984d880c818440380d10105070410300c4980c1d013070350409155101031008500c5041648452031741d074580b010800c40304400306910180d04c1d82c038022942e100f501c0006604010703a50000761141d195000340c64048041740d01e00e0001081c07031030940180300d000908802e5403405400f100b0030b0500d0300d60b140c55481c020f9005401c85000c2000c07080e024071001d410310f00028684500b040c50300036111380c1c00480c0200c0e143d00400045844800c0001c01003100300f4a0342c1d0800040c6c1c024031744245018981031080328a4100035102086004400409403d652a01020b0703900404018054035110048070348081d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 295030278 1250 295029028 295029041
    0x5040c0e010501020d230702090a0c14071a060f131b050306031c1115060a0605090a090e03130608040203060a05070f08150a0f03120302041a0901020c1201 68
    0x30300558489001003450741c000b084c0c81c141800140da44400c605c5120803c08040002c0182440341254100300c03060241c2c55000e01c940c032451803110b02091141c000a002820400481050503003a201440250002007540b10b56440c20425030801204d0b41d100c00001441c03c1e060500300f9527101c40c21050060720a00f03207400c1180040c00e1180d038600344882e410b00640d07052008171090381c0c1c103802140c0f900018610f040f0410001601918080c141c00460b00f000501c2c00b000c0418500c1c00f2050344042105525104a1302c0d0050242c902e4040e05100700800490226121401225110b64032800e40000c0c0075010170503100c291111034080304072560703100000751003548140c80c10f80c028020071340000c1c096a03441c0140c81c0900401e659a03076400c11007181c2201c42410141c0052201c84000c41801d81c4e030b035502c10040000d88022442e1617109851440c0410501c0f001c045034009050045c082080122080010041c40a0341e000b0b020340d40b8005400101d0400510415444c0d10400c0702d048098034030f40551290 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 295031528 1250 295030278 295030289
    0xf0106060f080c040e01210618140a122106030b1509061003020f0405031c120b010504090f09022d010203042607120f032a0201030507021005040c 64
    0x143e1126100455140301e14040d820640c0c14140c01080610607000081001d0404a844002268096541c081c140c4011030b0b044114503464a90690a000030080c03014240d5800000401482d203a81c2d0b40c0c582c800c05030380482000e0000950b4a051040d000702004880d07546000420814141c8a1030101d49aa60654182d018400a07800d080000e0510540c101c0c0100f4000740107005035441540124003a51014001020321001840005031646007041920030301c44500c0c103080d041c0700e2800750082c540c00601590040b4103040411030b0640f030b600441150151016080d005c41c0030390103010500080c01d51504020b40008a1090f0501c01c0340c03041e009407480d2040180c4081c03207454094012030760380c091030085011403801381d0400c00b5110000c400058051244400b41c420280d520140003120105080007a603004040c0c0404004166009100044a031a0380c0c0c030010403a1980d04080d002055903820080c1403594903004140b0b400e00030404030340f000205090500151601d890504500681881078 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 295032778 1250 295031528 295031537
    0x1020f0706090e090307031224080a03110a031b0f080c070317040503030d0506120d17010509190507030f020c0307120c0308040f02011430060a06050c0f0106060f 71
    0x30950104c004011141c0030781d0155203064486c1c611607d15801003101c0c488403a032928129409407c9124000f2002c0e0003070148801420004010381005010b00d04411f402e200d0f150042d003020720020760820505020100c210401e8202c00c0134a20b400303e00e4000404002d80071020115214220500001c0c007401078a11404800181070716800c04000d1901450240c0d5505070028031454010020640c41a03038803400003024440c1007507141030503504200482a215000500c40c4000c090542e194a550500520f000d8403039038030354508240060015000e485103055100e0b140c402065069109802c40d00b0032004401c0304560301d50030140b04036a00c1c0e104500898520407030500c0200510702441c540c1103001c1d016103a482c1140e0710741c3d45020041c01d8400d000ca06000320341c9d04141d03507104284064015030a82450b0b028141e079028401080700e910b00e000c0044c0c114003a0b02088442e440d08034103141201d601c0e003415174591710b054100d04e05103c04c0c140055002d6103085c5d800648a80c0c481007880b800301d41c6846 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 295034028 1250 295032778 295032781
    0x90b0f040b150315090c280512031605031b0706050406031a191d06310609090b0609070f230a17091b09130204050411040f021903050601020f0706090e 66
    0x4048800340381984201845030f0b8000c01c21160814020032701a540c0a04185c9243c0a0300c4881d03d00c002d5107003402614141d1000c0b880c90410031214144103d441d92000080030242d1400c02c0007006031089000c0e4004040d102c00d243d080318440303540c4404044030014030107090841184c0381180b007041148503c2c40021050310041210f007540040440c003075140903140341006c986150842084800302e182c8040b4000a010480d4800c0c40148201401380c284c0036000314848100341001051b0707031030240540d8400d0b6614014000e41507000008104222801c0c10840c2c41031403200c0f51510552202050300010790000900041003aa20091103051b07000c104c641d98803075131180381060307685100d10000020000301030982c8103010701d401d441195220088944501b00c564099000c2000d40d281034508940b03c910300c4803c05400e24250007110080b40b01c00400714107080101101c4010f0103c5101c5483c03d2566440c0401c4503640700380308030100c0c00f8020040303411841d65060001c11101140c80f850000844910 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 295035278 1250 295034028 295034059
    0x1030b091504051c11010606030923060406180c080d2606060d020d090f02040b0f090a05040f0f05030a080601050306060712021c0201090b0f040b150315090c 69
    0x1510b0240b500305004160903c441381e040c4480141d01c4414906000d66422806510302c000d0080da800b401983d6030214404055140011480380c14950044044182c0440c1c0e064062001a00c1e90b80702e0340128000c500007001c1955080e54040800e400b030003164040c0c4000c51120300008854000000c3c982e1074052551541c1064a4052903004e42d07241e95000c1000440e5161810801602c0c0d0f18a000400501c1c11441c00141000c030352801e002203401c00e03240f04444082d85058410185400c00999541700600e600c100003a001101c01009240c80c21f80d584049424000780400c0c2c14029940314116242c0700450f810f06540e02d1300040c1c03c0d0000030b005040082d10300c1d4811800c0c1c0380584405058142801500c0c0e803440010303441503014400710f126417004101d860306200d0513251868100c0c0c00028032070406050650100c400103150246a1107010184000218002a442e130301a0301d00003450320400f80c2038002810809007140f008511000300051055104020034161000d86045502005801c1900e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 295036528 1250 295035278 295035313
    0x3071103031e03040309090c120c0f020a020d0510110c060a0204050105030708310309050f0109030b2d091c0815030a05010c050405030615060d0b01051201030b09 71
    0x707401c0b0701e41c030407100340c140e00c40c403500b03801543e002440b074107210100e1500c0340c884401b200d01c0214000001082d40c90003a060321141d02c101031112480e03103410301c011391415401941c3d9052421000f4040d14140380f00e81e0502c24280081c40d074140c0014005d101e030701140310710030300d4a030001081802580035030400300da460b080c50b20841d82140c0c07040e1543c6046d40e07a40c5105585904005107071404109500017941c0030041c2611280152168203c4e212011507c0c0741401401d041480d08003600804202e80e00300e020b40c1c4c1191002342125402a0303d1086030390307050004152407605180c02c0c000b41c060800d44070449840000100d2159121008881c1c211070704d001070000400c6070351908004100300c6004274003906040c1640c03433855540642114021401c0f03580d0142102c2c2000b07a454001500801c2c00d000d9482d00b03001c0f080d00100c0c81c52450b031880a110300051031031321940040c5003c040e9140b56481d6564006d005a4038080021440101d0b2036a40703042013a03800c801192040901e0103800c103112200000e5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 295037778 1250 295036528 295036537
    0x240501020d0c081b010e1902030601031205040e0a020d1a130e120d0c020606030604120e13090f060b01110a0602030a0e0601030c0503120304051917040303020307110303 74
    0x1640102001812114160307030b015126901510070100c2004040341180c054045041c02118480c0001040c0641d840c00b0f90803c0300b42c454075403000403d044d8290160741c0003c1d820b41902e80140307840c600d482c005102a2401d1181e80d000d80c024504603c10490b0b01c12450380035213001040c201c01400190b04809105104400a540480e4031a8402001d00d221003c0c0d6400405c0c0c205015044a50054100e81051203d80150a4a07610300c0e0702c1e05c48802c0300c0b560501c01907822030000e4005142d141003035a07070311444030003004208040101c0300d030350403480f030355000700e0181008c540c00741c00c00000380c1c60308044087c0c40e0810400d4694504014031401994480c5814140003204600a403000580c6035840310082d60004d01410035098603000035038603002d403d2000500031417248401c1115249042c3c1414184032110610130500c10313041c41084041100801c0c0640554165405105c4c107c01c01d18145620000e00c401110484601280c08010950000002c0c40207d02034407144000140442c10580c0c2c9218 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 295039028 1250 295037778 295037789
    0x801110c0a170c070e011a030c160201260f07020c060f0904060e0108030a110a0b0105040915020309160f080c1507020301020d06031a010302030c2107080124 69
    0x1041907800460242d0841d6200d01c0c240c084400e140840349a4054980010f0ba041544540708800c010020342c0d078100d068400301d446007080700e41149015543ca4500380501482d00030b484442010200071a842a20b0700c1c58900402d01151004401e14040c15a607110110b404085062008000c250424000a0316512411000307140e01c3c034180038075600280e181c004e1076000790004e07100c01010070004c1d6901000ca02a0035501d0055031a0070700e00c0b80c01483c20324002c020b00710ba81c0100c00c1400115403101c00701030540d40b040d2400302c0d038a0198034094240043c25002c190b1520b2000c8180010400701088039049503900300b00518546481d0200c01404c0656482000c5da103501c4444603a220b0700302003a1072595902c20380d01450a1001e2900443d0a9034006044038640d44d6880d541401040034880440740000c020080c0010b1070b605550201c0e946884400c8854440c1d074100d03404007949060b440c0c5130b418044002e003e0355442551004528040d002201d1a140ca40b0899003114054007601c10404045a4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 295040278 1250 295039028 295039033
    0x10c0801080607030e0f0f1f09031e0210090308070201060e0112060b061611040f020c0606040203130c122102031206060c0a030c0212070308040308180d0c0801110c 72
    0xc4414500b1340092800004111050082115100308000180819040c000c2030328094501e0315030120007aa0f5103544440800e907164074207070303140c40400c2d40428500c0050410840e0318510300c94245080c0d1411410810100290b820120540101640008001d0155043e1b800a100a0380c54844000300c02d50240240000007145010100100b05e070781e007001c41003c00103044145000400721784041c0122140400b40d075450300c01702641065003404e10412007031001c0c08008604148a80804c03580700d140107446a0300c5141c010022038424480c1d2480f800c2801d5200a0414100c0d9a60398040c0d80044425010390300360100c0d010240303018040c10051218030442e42d0103076190000c1c030100c600c0041e02c060441a000b040512241c99000c004020078400e43d8002c2e25080032840071441040ba180711003c5d8401c041c1c0c0c003c8041040058144026034082e03135400b445443d1500c2403900a8014507a130300101c240d10403005181c42c42841614042c0034143ca045500078011100c80e41790100d40f40c400c1c03810b40200b56 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 295041528 1250 295040278 295040281
    0x1b140306040b0d0b0c070b070e101d0d0b04110301140115020703020603040614011505040e06150a09060e040c09060e0102070902031f05120307032a0609020102010c08010806 76
    0x1841c040d8410249004018603004010710540c03130301d0022520880b01048200d50000d042006d004071542e5043d4440302d513190036030301c401501000c640711505880901d024030094070604224450000c0102c1d00800003d459581d008180c0d08004605000030346060724101d281400910300b50406004450358010400c20404203646032083c89001c028070180d0020440c0078451000c0016030390f10340103500171401504041000380f03141c0f88100d030810041c4d0165a1440b01c2844043d10280c00600303681c00c695940005140b03a41d150b03004140380228107404050300501c001001c0302c19980045070781c800d80e44580e4402111040a800340400c5581100e9294040340b2415020420316104605811030220b040c410344a4a076070b1000c040050b43c000742e404204690115504808140605481800411003240e0105031240309100058072489260406000c124840700e94040c4040e8401c1000a52401c1c100a022050f1070303801c005009280740301040380154240960406020310a44200741a06c00c10790241065 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 295042778 1250 295041528 295041541
    0x51806010519020102120a1a010e090106140d09060c080708010f0b160c060e01020f01021c18170a0908010b1008180712020a06020d08040611070807061b1403 69
    0x40000b42c1030b03010110341d001c10091069000c200d0a5902400c6000d00102e485141c1811501c415583ca1040904103e5401c42d20503e031741d60f06603420304443d003d0824042e0702c280c1d40c101800a00c103050180c0115428040301e04100200c1d503218420400e00ca075540265a2607011003103071414400e101c2e80000c03550048060101c030340c1e008010f02600354043e20210f03100e900c607542c0054000301680144081042c001a4640558042c0500d00070401c004000b146041c8105940308544580d0120000300d03039548248080b0160b8040c0f24000c1043d4101c1001c0c054207244512940245d4400040400060003000c00060950b105010f00035000c00014000090f01e1004403007120707114001003a900c8000d0b80f211403103015030001d0222801070010324801d43d407184242d0050000a41c141e60080045511401070820340d117510440d080d0304181d1000740400c0408000c200c1c0340c0640030b03509001e01110f400080307031020020306500901c8007040d040c2a00070202c05c041802c7e15501f0b180200b0b03489003002000050803 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 295044028 1250 295042778 295042807
    0x61303050327061602300c040501083007150608070504023a0915111201031101020a1a09100c091202131103092806020307031b090518060105 62
    0x442c8808000c450701c410a11b0504884400030201d0341416800c5908070b10110b042c1802a00d0140040500904800700d064209811107241c4205140300c0c03240c003540281d994043d200c115a000343c2c01900c11750480b44a0301070340c0010300803841000b58601c141100042c01d410280203540b07884262141408540301070f070590340a0314080d1100b400401d0802446272000c880e2500c6224100e5003e442885248680002d56100700e41c0c0c0d00035807946040c424855000420110406941501c1d8080781c1c07403500600c810b0050740ba107000100c0081072820000b9400000d44d0f516112244503600301801c48d04115442c41403c8100c80700e10224400044615400788461190350044010740c0d44050082c0920f032a00d003407410111410840d03403400c211030000510200460800500b65030754001c00240c100c6030b0704124025114509510014006034002c80000e41036402540300c0d5001e40110307442d050b000144a500100000c0d00b0380a440c0c0f1a841208040040700c0300500e659210341c006846540c60a1101c003010034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 295045278 1250 295044028 295044049
    0xc070602030a0f0f0902010909090b0423010507031b0804031d0102100e01090218010806060409140a050f0111160609020a03050d0903061103090c061303050327061602 73
    0x91070036100c3c1c5841a840d01140708602c52207042c403800043c90000c5100040001842c0d0f40b054080a04011581c0b0105d1405d10055030091741c40740c1950580c0c00c026203442e9604164003202106546400708014100d0341640040d582031151100c030100b034080c103e90039101b464084e20094001200c4500c140508440c0c1003c4200112050040341c9002e80f50100341000c1c2d0b01d01e080c0120140c5d45030081d002c21800c0c02070100b10442c01300d0600441130341c140004c3c030340c0d5107000908480c0310310348450141d4144a010a10780e4416034184068405030703003150900c260b031802e2085c3c001c10250f1809514040b01070b401020b07601d98280740300c1490003510080c0c85500103003200f081d090345e00c161841400030003c3c03010440c80400f03510f06c3d10b805404e1840c1d800c20804440544440e804602801c100300100850301088500319034104465450f01c91011403c230b54000640d6400003000ca1100013117282d802e0800b050f000503219002c51096014882c41000c0c40502d00807110b030072201007400e640c4400185465908034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 295046528 1250 295045278 295045291
    0xc230d0c061b23241303030e0d09052121040f060207061205061809010e03070b0f06040c080a0c03110318010c0e0616060209060c0304060905090c07060203 68
    0x89403000c42600c07404448001c0b00c45200703120806038010850250180001c60480700e03400c2c2003060311010391110703c81d548130080c0384619000403101d482c002c00d4043c0c0e0100440c414980d04940c0da2014030070014080803590300441c0c4c40780d01d03144051408010000014402c048150002d0030409108000d03078400d107800070b000703403d161800b030101081c00c0040c2c0c607a0500502680c0c0c0185101d0b0701e06000503100061400c1c220724090308000402000d920b03288040400f00078076602d080d07503c3e660b00600c0c3e0700400c03185441c00f015010001c0c4100038032104040740e600072910722240c0030a54890b0800c00048400d0301e690080816600b20011b141c0c0f144039405008010f0a900300442c42c0401c41d00c501030a03074002c03120100d40c2c40c240d08010140020910842448000c6402c000c103520300daa0340010181d002d050701c060420300c0d280f0403030020086103030140c0b4074040020f0031594031982690495903c90304a80101c0001035144d8200240f070b454a03074001c80c05150707000b15091070280c058a900c00070b90f0005062 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 295047778 1250 295046528 295046567
    0x18070504020c030f0a090f050a06090501050306040f02160b090604032c0d03050d0e010b06030c0a0912060506090a0507050703030504020f0306070201060602010f110d180c230d0c06 79
    0x9a084c00740c0138000910b000c1440d81e0780d900c2d4640c00c10144040359444d5800640c010301d1030741818082d0542245c0e0500a644003400d00503200d5031481c001402070140c2d001001c50745400841e03110140050000c01040302803050649405590720f800c0c1603599000101c4010300011003290000302000d10041501603541246011408001c10403000300c1c3c0c06085102045000031800607221189420074802ca01740c401c0c20b00000e204180345000040e20034003000c2d121403411b0000107401d110039406a15090010031049100d0f041004803800e0210051404a0709580a1032405001407c1c0515910503944154001d84506040c1940307510210000d01e03008000b2a0442003e17214100c4a9404200321889005298004140a810800024213480d003041c08003001c682040301000c82440000d0503a904000303c000300180e100700481840215a541c190098031080c80f004010840d460030658400c202d504d40c8440034940c854443c14042d0582050a001c0c042d0100f010b014400d482c410b401c100c100d02c2c07062a8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 295049028 1250 295047778 295047787
    0xa150c2d080a4e0915050a0207050a02090606070b0a06140105040f180b131a0d1a07140a050c0c0109121101230c120c0d080c040f150818070504020c03 66
    0x91890459034200001d40e0240c1440c045c0040344a5540610742d130244000109509000d115546d2540e503c2e01c044000340f08414440018400b03480d8a415503071200c1c0c10541d850302c1030130440c83c0ca0f0000c213990702804105812280030500035500841c222400c980740011041c009910b043c1c25030b058600103154682c2e44ca44c540c0d250280c039640d042c1080c00d01c0000840002101800301c0300f952041041352217074a000c1c0d01e4200d07030100810150342865208442c00702c0340741086c0d99041e80c102c50f0a40b84a60b01203103101c005c10201025917008000c2c002320100368045400c812002d100555020b4082e01c0740f07001942c0b81c4205100040d00000d21006c03000411304000c00c3d610b52000318041d0000451030324113458600450800d07800c920400c507891000401c4010246131840e408051138072400920101410321aa420208480b400304a046a00500604d9000c0e003001d41c41d0a08182d041e8400c0c03006000041e58117021444140104d2612046411542c0081070740f10301d00380521022350000b42c02d1120a000900 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 295050278 1250 295049028 295049177
    0x504020a0e01091409010c0e04021c05010305031201080c0607021c0c0909020f040506090c0304030c08070326220f0209150a150c2d080a 60
    0xd0141d40a00501e40c0c1c04510004118030321406181e00070184807031681800510307000d0a4001c038200c01c01a2054401694030340020007078846030090580b048080b10301d00300000051080200c00742c0380c65040d00c070b03d00c165641da5030406c076501c034071000c0860381c006410006c560051500030080700e902d1901144140d26140151540307113902e079207644000c22440c2c51305210006c45c40e1010250b0a2514110790402c400e04110010032940b8038018018603803000000301083c2031502038802000103030351111030107a88408924004051850250024440c00b000c40451008420349513039081c8a8078004034165190400c2003e0300c007403070740e4100c4207954100207a01d803540561035048034144591b010540400c83e8a0103101807080300701c0c1720780c401080a025200001c4000341d004403900809a0000100c80510245441c0000700601c2d003c00780081000c104110000c012103000545a601400d4560700c1c403001c20344040c0803214031400c031110b0920502c0c0d00180020500240440d08500e44010288480402034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 295051528 1250 295050278 295050299
    0x1202280c0b0a05010501091d0a05060d0b01030809011b050a1502161a06030a0f0f060b04090309030302010e16090f0b031002031f1503110c01061410140406030504020a 73
    0x81d0b0301048042d80320700040c0308a5130032001281c010301d181c0458034030312281014103c64559000c0c1ca41681da9807a6408940e05540d01440032840c0ca070021014940e43d40c5d0f9150006082d80090b000354082850b0506d458030540503003600062641d003007c0a0042c0100e00c0e5210011541d807100780c0c42600340e003803100440101c102d8004014140c82000061440b0200780e10700c240e0500020200762099001c60010f00c00200c10b1048111a0b940c005007d9224407404d1410001400600c82c2e03044e081403401001600745607100b89400c0c100c9011360001c0081154680c03516884407003040400c101d4440000003002120019070068922040a41c800192280124002800c02c9100c0c0840070307580d5008130a0003541c0c1030103800c042584c00070402940d011460800301d01c014001d00ca40080c141551500340c0c0c5e078051800011135501e0003000008210351900d4400c50300700002007109690244280039001e5103928012103541e405a008024000e0402d890000202c001e440000d104a030070420300b940000780c90421 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 295052778 1250 295051528 295051531
    0xe0f060d1d120309120d0609090f0b06010206091207050f060405060a0c09050a0315090803090d09090e0a0209090f030304141605060d090f0503040b09011202280c0b 72
    0x24040d07828035800a03141440c210742c00d080c0d46940362080040c00210080040d1010170700d02441212502c40303c07651040e07002800c0c9948080c004508140d400000c00c146682c100818a115559500254440d580120b035195421107059505a2003400c0c00300d804031448020f041078905c2103080310300361004500540e040480c16038044a00c2c0c0e02007030030700c02c2291a50103001c04003865860a2190036280c540001c10221580c800071300b481100703989000101009400100c52140c0008940c2d90b0b908124000f15a03408403c1c4403200020812000450b030f00c1c1d464000e08610a54602c0144032585680c0c080042100001e000020300d0301c1030910402800e0018000f45214501030600003842d007540c1c40720f150511401c14400010444800300900c0b25940740029107211100111001441404519002041c00c03c070200180081c0700100e8000340181181d8001c180f25107003079869100c2001420b000006030b015000505070440304c4070f5420000c4e1000003202542c100311518060305010000e49904102d81c20 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 295054028 1250 295052778 295052801
    0x11403070510030b0123030103060519050115030f0b0d170c0f01020406080f0618061201060e06100801030f0201080a1803170c070507120203070e0c07020a14010e0f060d 74
    0x468a00800d000c0d03800000103c9800f660004d1a14070400b1402c06d980350b4401400300512269607040445c3e10900000f1003020a80520f52040056503120b01001800701383c00407100c00001c0c1040c1c1c1d096140001401282603011010301001c1d010001c55070f4800100e0400c0d10341d5013800e0000c0c000307118040410800c286108138502c00050750380f8140207000b40011f030001e0542280c0c0c0c22000900000346c6031540c0b490f902925042c03500701e150b00c0301030024504c00300c4040554040d41c00c01401203200841601c41c41c1c06240112610000200710b09801c2d12103807800d1202a000c0c501e240300440141d402050f5265004280c80000948000d00516440300000055800d40c000f400c200d88030f0b00b007030300c0e4010401d82145041c801c1d54101a410340c1c032150b903a083e034004d0b80d40b090314110703030b07582151020046900078005c5090241c056103480ea145104c82e0708034074000c0e40300c1d210b1510300060b04681245030715044401a59808181106901484603c0b94000540c60304014204580b00502c6400e2140c044c4905 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 295055278 1250 295054028 295054031
    0x708031611151e0301150c020a080a03120f0506011b1704090905010e0f070512071716050a060e01080411031b0316050a06081008010609020901020f0d0801140307051003 74
    0x14030100c1c1e03240c410f0000c41038800b8402d8200014000032002070f40180d085507191400880001071071010071890480303540054524800c3ca51090101600070300b030a214040350000030800b40c10740c21900801d8410699049005c01c00800320070140600d101d2a410304035019071005910400b1141c45521180d0281d404a039540e0381d114060710030002c0c2800780941c928299002420f545040281058a0300d910303114030b9204010104064107056024011400140b9042d520900d10181c0c0c0641c042d201c01c81c0c034240b4480c0c2c07070465902003040e04d00344000d0019110300e50380d540c201e050341a006494010020f40103680c80400c6c07480000e9655010402c410b00c4a031000340d8061512807180a042c500b5080c0104034075003100070b001c18082520b45404c0312040f100c807481c00c840a502d450403035596184d83c0340c2044030a0350074502c3c089840c02c000c0d001010703c000c082c0c1c01c40c0c1d04001066200d94540c3c1010b0361903400501950010840b1780009885085000303001000d503002941e440e0005042007419409007804a03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 295056528 1250 295055278 295055287
    0x170f101e0b03040f110a140409030309060f0c0f0207081216170a09050108190504150911090105030d0801140f030106081b091e040309080a03080f0702070803161115 72
    0x101748030f040800800415600380420303900f49021f520403a114101d5103406582d4400400c801d261286c0c000203001500030b00308100c4882c462110402a146c0b202448000c41c03216a00510b0661001546804440803980a0f040710721001c2801070181d4000c1011b0212a08803c0380c60011410321040840386070107650101c2d030348140c3e00c0740c081c0440301ea5621080c14400024104040380741300950300c441010950400082c15901c9251070b8400c0e000600c02c15012b01e1800311410b04010740035000248506044807102684e0b070f40d40042564440300503140320001402c0c4c030010850031121400c4c0040c003200c010684600002ca01e0003090031126254418440ca500c40c481201c070700c0d0520001e500c41c004060f140c009061808101d0380d04040ca40610503056942032000160031325114023650030181210304191041056a07050060840c401038411440000d075480200e0500c0d400016808120349000340558144000c1810541420018060950720f51880a2440e071083d0f6810500c2000070010103995501c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 295057778 1250 295056528 295056533
    0x5151302130b032a01050f041208120109060302090a02030c12040c0b0d0b1e03060c03250522080c01140d0e031c201b0607170f101e0b03040f 62
    0x131a20b02860602104202e6030310b50800c0401203e0560310034a82507216000185448885417084013032056107514058004109a800d503005281280c1c0212503080745911350700048012448181c03685540300000700302041c082c140456405601500401c6142d000315941c1421841c42d80c049030f03011120a03a244802c54862038008092003090340000011884a007810300840e5584001505c4440000004400a6030740fa15002d10300d101c00200c0d52144450100d1094040c2040d009120500749141c11140c80c101c182212501110465402e1802800c1c0c0c9000c400040d00d8049115143c8043d0b813504021640c00e01080d4003545100901140c001c56403041555401038032a68005c41c40042c450402e83c840c0c61800c21072145081b0118811000c990781c4c444451201c09150004400e0141c034061541040942608007071440c0e00340740c1c85c013001512580c0300d4004101d030305d400326140c10b03508045c10024130941b02d83c008120200b4004083c209c900035181c01c032035103954000b114202c40e06680003401408 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 295059028 1250 295057778 295057843
    0x91406040905120d0c03110906030106121b030209031027030e06040807081e06010e070c0f03050310090203040f0b0c120124020d0e01120b06070c0305151302130b03 72
    0x84a40100c0c681c7d410481941c0015265107c1031144004114401450355924242079120440c80484001d0195002200c00000303000394121405031442402180710a41058003240164000d040c051400c1c0c00d5465403070040c0350382070f10b08058160104140307040b08070380c41d44540c40208098284d9000a04034946040080c61410540646100780c1110021446001c0380000801505680b20003401514503569540c0468054503c004041c0c4a2040c140c6200e091541110045000f0f0809404400d880c540791801082640f10542d0002c00f00f042c031000060100c0c65404102e81c00840c11740c51107107800380a20104c1605903080e0420f0041c0615132a6451804c0c1d081880407a10303c0e00303400a82000e4007011400303003c010381c01110505200e5800507041e51480342c1ea10001c16548028417440c0c4515884c2080d1914a5280c0822541c0d03100310381c1e00441080d064824184030304405680302c0380e041d00e40e40c00d01c54110200e40b0f00801c03c603114807448581e07039014851074058070034003007141c498500c05c0420b030711 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 295060278 1250 295059028 295059041
    0xd06020301090e031620101d0a050102060112080408070308190f200f01140910060515070c050402040b090405100605040306110903030301060504030c091406040905120d0c03 76
    0x200540c0104914020310b0301410441c01d4007031b0040f4503203404842d03a0103c0016000b40c0c04e145a40b0880400e00040201e8019a40c806d644a600301a61040e0b100c05052140220b410b0040e180968801c200421041505840c401030240c03082c4075480c01c150703031150018500345c032540045074003860204501c0c4c500c4100c4c1704c1c020006111860181d03a80038820101810030104c071800d071040302d194900010a215001c000c178881110a040081054020801c40c8415822055a01080c5801032040040030380700f25014003015500700a0018020b4004401148615485540222801d0b0b44461000410755102d00c00b5100804041034800c3d55207204504020890720014403040c200b03131182c0406e1055992000a89003a00e9001400064507040d010344200340d8040c8481c41c0381d06102c0080049102e550200203401280e10a00180c09104e40715030068040c0d0380c8544101250b041d031440001c45900d0305e40c001c4400b6034024070517148000a10301c042105a8007048034049450b4913281401d070001e505200d500e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 295061528 1250 295060278 295060301
    0xc0f06020c04060b03070318050f070302010905091b0703090306050a270b0c0702040609060308130b0f070206163311070201050702183409090203090c0d0602030109 72
    0x100103c3c1c4c14841c2140c880d00014041c0d804140c0da41d825a00c021584640ca40c1200d508181101c0401000044150ba505c9950004070b000844601001407603040078401c1368010001d13004e00c00000d10500812290380d030400a016403c00200c0400000424118030603240212a49000400c1030300b4032525002c1c04800c2c1c19074031041c0c151441d4080000c100c4e02d000141d0003080c480149541c0b80c10718000600501140e400015209203070607000810400d2500040010b080091303080e0411030350750005000349003c1c40620390b503041010010300e4018078140c4000c0c948908080e00750190b214540c1c9a00314080b500c101c00041e1125000e145109000d0714026000e580c000d298414803001c5020350b1382a000f8040c0180090500602280200031940c803000180e6400c800700041c0600c13403a000a81d481400c01d0703d41002c8030120f202c4002454400300901e030390460300c4991205020a4030b41015140250b00c010301c0c10a01d401081500c17445c40d5520440649454020107016859506181d0030740219481c01044 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 295062778 1250 295061528 295061531
    0x60a150f081006060f08010501030f0906050a05010e07020313211e031103040f091d0604051614030606120705100309050c04020703090e0703020d0203090307031413210c0f06020c04 79
    0x10743c03a1700d81e0b015207083e056034401c0c030700443c10807865400b04001e4000307076a00901050030706082104c1240141d10560490780d9030a0410140d0f180c103582640c4905c42d89200030f0620400480911078510243c001c0340b00c0c40940e0b010036100580c02e4540390340902407120303094080014030300d03180241544201c0207040101e056010b50b242c5407400301c071070301d400c40c2c81c0c03140f450069101d01c03030194196032441088101030660707015075001d40340918101d5150701c1e0300781e0400106c0d0f074a0303c4003041d00c002203c8840d2034203001500070603250301d039401004004404002559414451414041202e444043d003d41c081003841d1800301c3e00c02c00340d00d081400c0004200986008600c18017101c00030a034440076031000c840884050348129101e03100110042d1080c8000c820f8039900004c244901010008001c00910b0301a558100b1044014000c8021030700c1340703003030541a4484c40d040500c943c002e15401c503852134405c030301d0f8201100c690f550f40200307407182c9502c4441590710412003003051503014452002e054a00f241c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 295064028 1250 295062778 295062797
    0x5040507020c0f0402070c0f09050906010608041b030c0b090306160e0d0602040522150302030d0f020c030d170f0412030c030b181b0903060a150f08100606 68
    0x402541d07005619407591040f039589011900070740355075044540e0750342c10580c1049125180e0b04e540b0030b140c00c28030070701e0038161800000410411020400c01c1c1a42d0f000c0c1e40e5041ca0f0345442d102c15628020804000414045440d4000700141320b95007030b24014030040c403001d5101c2003c58101424188018402c0b01c008248103920603e20368001819061480d0842c6c1442d109026420264002e00964100f2908aa904214181d41e4509100604280c0b14a40c2e4288112001102180c02d9038800e848020342541c44401c0100740b403800b55141c01064461803048962a11400340000d10b03108203101440049103030818841101c04c01e010301d1940c451307103d0903072904030305280d60360350f110b0310005d0441d44c10035a03101d03005500709100f43c1140c103482ca801030020070342d4518180300904050041c1c2e40070031a02c940c43e82c42000c030705440d0f042c0c514082c0020302424090340c0b0301c0c1000e00070b001552181c1801003192580460010300340307480c144c050601034006040f5400c400910740b045503250380016041c0001580c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 295065278 1250 295064028 295064041
    0x9071e0e06091e10090e1b091504060306050603061303020a06110912071401021b060306060f0a09030303051b07061d39130c020a140604050601050405 66
    0x1080d40e00544181d450306003d40d0b4030511802d00c0d40e090108850600402401c0c050304c02c803008200e01c25070f68240d4003004000340082203603a840c4e061001c010b000007641c590f10b0106161030300e44250702070106244800d0800b8507000280454040340c10407920140d842d000c0c0301040c101004040e87c0403009030f410b09581001610302030740c2c0b0fa090200060480e81ca0740c0c0020104085603040d506030b4680134008032000b40146c1c400f140c8034003c5004002500fa40085055010741c800684182451400051021004101070501407642d000400c403681001041043c0042007a11500800c518a101d558025116046150080a40d1005440c02e0f10015100d410009500060403c032441070703904c04400100079000d01c0714614480841c043c910f800340a105090015552900c8041040c000210903221110300d8902e0000c0080018002c130341c0c0c010050210001c0c4003419030303005010b050b0302d40c0101c070a03031031840c0d8654210504240360f01c0c10a030022424801007020030801e80d27025210803241030080f840c205 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 295066528 1250 295065278 295065299
    0x40e06040c0803090312090415060f11030310120804030203030f040806130b0609091c050c10050c0406111f0b09060915011805060403030806011b050d0302031e09071e 73
    0x940c0c0a0341b554001910340000d540b04d502805c01c0f01407510406e08245d6071580090300c0300ca80c907050710012510500c80802c1c02100401101e21628064042d18600350030700008186580304140102d840500c200400b00140c0d804101a100c80355181140c1a590760403c081c550501c1d41c0900102c0207150562081000219000c0e5601d501a03405c0d18510000d6071000c801170310781005480200c40c110002d40f071100c5c80c0d541c44402058100900340484030380c40380d01d84046044a00407120380018140601003030100c9482401801d0f18840b41100701e41180058034000350161005603080c48410b07a5529841d03070f60f401c0c0540d00c0e03940540e080300d000042b86007088603200340c02c401d400514100102c0001d004030380c40c0f840310204050b08014081303e4490343c403450094050f2006581c0980401c0064a02180790300ba200c5491801c180d200c8041c03c3c003103184480a501031740024205042d960401054003442100424549200700711a10062107580c0c903242c40e100e80140c0380f404400c3d40c0c6400c0201807186090f40c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 295067778 1250 295066528 295066543
    0x402011b05070308090316080c040b0d05060c1b060709090f050609010b090d0b04060f060b0a0203190302040510020607090501030e2a06070c050316260c040e06040c08030903 76
    0x800e080f185d0729100000000d062829816100c00041d144807004960801d0025140700b032071109444c1000321210b10010000c0b58900388000801d02d86c00352000480141422002e41829080e0740d6182045101d40050181021401c444800000380038a1041140c10040e00039040504c08540c020000340c05e085020a60107841400750011685000580000395154041e40103412130f003100e004d0201f420130b8036203c40238144c8200500d1409041440105d0142001d604440820703005030000d610302100b544e803040074217000090301c2042c10b900f07000000d1145c548910302d401d4020b640e800342c5003a00d030440c03001c0c158000a4000c01c1c101480d18800b15502040041c0040341c1c641e14840d40b000ea10303208009c04042d162405441a000400465401c1c104141810b0410564104401390b54117083c0260031045d4400c49440b80c0c0d2042d11000c1c84004a00d003aa6a1900f290b001c4072007903800751038003100854190342d000500c241c00c0d0362140042005020700000914042c0078200301652802c0c82d008000b03640e6118 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 295069028 1250 295067778 295067783
    0x80a060e090d110c0d0803010f050a32090405060f0a1a06030603030f040b070506071403040b040f0507080309331309090b0601020c010903120e01051b03030402011b050703 75
    0x101803818806983d0104000d07941814000c0584141c2e084a28106480c0e0700700b84610511109100800304140c50181c0c072a40a4400c0d0001050701400341c0e60301c050310740035112031240c000a8540040041500c4102da014400c3d130142000300020f050582e40040308107401408010f4061810707200065140c61403107015800f0300c084594075180e4030740c42c001908610402803011145d640c000750002d2908901000380c01041d01510a0301d215032b41728107041e0f9180d08038078018881d601e41040054002900f1210702070b08140074040340400080150303142c6261500c40d07000074865500210b10f02020745480051340e8076442d0780c1841300d8050319400243c50690320041c10007440b640c00200c3d826001c01801c055000040804803000c0c40000701c4d50038a80003141c01964441e005001e81140300c19994018601e02003225413042c020400f090805404682c0345040801103410883c0400c02ca03540f07a204000c10f001448c9c0b1352005541e89041504c0050304070f0703008036005c034100041c0003c1900403c0010036200304894 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 295070278 1250 295069028 295069037
    0x1905070f030c12050a0b10030513061a13021819060806121605010e040207170309160305010b01020607090e07030b040204081501030b1b0d02070c0510080a060e090d 72
    0x21036035100f40d590002c4070070301100f02c514010030051440c150f50014102141e007520b07052548110754038110147d0f40300320f918805181070b468800c40085c81c2644011080c818642d42d40800c1202c4600240c6030240036070400550540100c0c4010b0300f600305510b8a00502e80031107540a005550415174920a1081d109402c00e010202c0001150b1341c407220191180c4c152445d05441a0049a100e120807080103400340c540003880b000c000c00301d1402c051084a5500c0e42004545450201030016100c050f03000500303410040c0036548801000c04a10400b000141d0310900000c6070440041c8002440c1a00080c4240208034000604101820036503440b550010414a400f00c2e02e01d6000d0040350191144e50301c01103461150000d48841e58007520132040c145c0c0c1c4140040d40d2681c0b140c3c502036003c80580000603451120130480b2500c40c814503801071800a2003900c190004940d1000099040102d403650340300410352050411004038150322801d0042c2c4a00c806008181c102154025961040740c1000320500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 295071528 1250 295070278 295070291
    0x1404020f07030e0306090f061f030b0112030806010906020a060905100608030d0b0904081806040b07050c01090602120f07020d060204030803220b04081c050117071202010509150d090305031905070f03 87
    0x2275101800c0e20061904070400000030b5940b4010317400c52801401058002800c0640824815881800c44c81d0403030f410742d03004144040c0310b03480b02001000350b100b040b18103204e0050321404481482c010400140b6121000e1616401c0148040e0280c03035450075454420b035200010880041d689005468244e2080003501d805c00c0258000b0641511030f580100e0820f40010455004000c00068900d440d802d082e6550002c0c0d1f59540c00c10303a0340e0441c001200c100b40d03030103000c50788103142c800000e003600b00d000820070050000341c0c0d1544000ca80c0160000d5071024800000c1144400c0a02544084280001030104071002c05d91100c61000c0009003004009000000f420050580842e29500c3e28018501040150356590b4201040c811303045044d14105008903400000d01700074130815018901e0b01070b15502e250070b0440301002405401141e03468114042400501000c9201e80300d50034070180b288d00c690f5900d08101c14282d520411140d042280036003803608106c0b8407540040a00b208035141d05010500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 295072778 1250 295071528 295071571
    0x110603100b180d1101020d0e032e060e010608150d0215070203010c09050a050315180f0d03090209010b0315040506010210050f0615131404020f07030e0306090f06 71
    0x1245030020400758040b07010341c01c01c001c0c00035046134401c50740c809808491400c441c00c0c805030f5a081a0400650381504800c1150349410b541d10141070090480101216103200008200c008840203034200000c0c00e0141c00040c088290010f6185820040d156046d01c1c41841d0b01002420366903009600a01800c990201420380c040040c0699044507402002807003440c50684004194084038841c851240c903101c000014982404240105202900c2a00e50f003d40c0d103d8071009990160b181c804c0601c0d204188010404081c24011603540c0c5015503008119100c242c010000c4010042e00584041c0301c00f0014019806070568a090b90761406030b41c0032540da55500e0050b4100403480f030840d00c2e0340d4200340801640c00e4110540fa4860003040352500318807900c030b00701c2c030110380902d0a502c5120300c0c08000c1070040080c000902264030400030405840c0518080c4080c601ba00f10b14421400f0841ca042c858076549410f20007d42d10500040003084c00300100b480d200c0e80d0786005840030700d00380180c000101c003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 295074028 1250 295072778 295072807
    0x11011803061d01060504111b031c0213050406080303040215040b0c0a1202010212130c21030905041107030e0a030f050a06060e130305030a0e0712110603100b 69
    0x6503003148007000251002c9014a10a01c89218030a68075480d00c18082174529080c41041840031a21020314102504c403074a50718245130f80140d00d00c1c648014844800005c0c441540c0b003194101d0714001681380c0340c0340600c10490741181c3d04000e104a0a000081c00341e440004240c0703074131540446840740854503110040780a84140d4200542e0068001120352a00c1e4001500901203032180c03e09030319045200c07100702d00300d004a00c0c0a03409240791001140e51007248a8070710b16941d000d52041102165109144802030340d0044440b00c2c03441156115205140e009040c2100400d01520140006202c0c070495640c03504c41c2038030003410301c64910072840c01510790b0300d41c0700c01035580401080c6010403241003085d40d512050804480860030304801184904100b00400c2c0161103280c1a85006115654103440a4000811402d003590ba40c40009041c184100030050082c03150000324003058101e82480e000d020061107880d030080c0000c200340301040b40c002c2d01110884090789200c5450782c1d420486202e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 295075278 1250 295074028 295074077
    0x3050a0e0a03150e19050309011215120302190803060613050301060905100b07030504170a1b05030f010209100c02030a0b1e010e07170703150308180307031101 70
    0x10140000201031040498a5130300c10030914051004450924201d001e0760850207495050013051504180020001540590074100040500d004007080714020300d901508440310507440422854040b45003941419014031810484070190150b1a0350851540c640903d18032010f4045030090800117003049048510710707984005408010000c0c0309103650303a144040070702720586103c402841d40e035200140c251044411a60325584c1a11000e05141c176107000c49454101d140d020341080d00902c48241d000034000c0001c000d000c0795400407040c01e14141418140741c05901e280030b80b0144c0c41000241d4880d5100301b01c42a01c2031080c40e10801d006603a2000c40d04001c20f040000306005041424401da820081c540d5100301e41c400030118130325a0b45c07986010000007040e1203100c0818800200d4100305895036030001d511540d107003004904880d2414001e541030b1607a0b0700039254003201251025a24421000c0760310010005c40c002c115007825600c071280f00e00c2c02281414140814240e0301c8a1524a031075188 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 295076528 1250 295075278 295075283
    0x2061b0c060405010c080711060a0f090828020309030a020d02031c020a1b14010e060c15100e010f17010b06042603031308030405070509040311010b09010303050a0e0a03 74
    0x150410300b01442c103503010341070004000c00818015000104160b10a00740030101d400c4c5a0014103550303c502c80d4490080603154141c9000356100d85250000c41d00c05401080020410b05000b124024200c3c094200110502035030006c54204100c03d880b03582e0002a06035845804a2304686035002c0d900c0024a407030b541c42c03c803608850205428a101540110340c0d003200c5405000701c401203008001e44d20115458134003072a000d0f00c0c080c2c1025851541708118040c02c298000d0031003450301424458051410380e00f1452071008042d5102040803a45088404200070a04071000850a5042c5982c90419044d6405003020702d009200d12280d0111094000244e1007c0c007030210b41c1d0351900c5240c41c030000e54801b001c004903901d02a40020080200100300c0e88250b16040700d08840f01402da41e00c420f503500c09803043da0140306078280410039540741030005008900c0b07601c40780c580d1000d10515a00351745602100c50300c02d403c5a001040803903080000c885207803a640c60400d500e01045000500030103201e4101 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 295077778 1250 295076528 295076533
    0x50c03091522033c1101060b030114040e0307050316110a0f0501031a060a0309030210051e0a0c020c0111010e161805010510050306060f070c0509070f02061b0c 70
    0x1010b05154200092000c0c0344003444002c010024082900090307140c0455118108103020300c8070b03181151040a071101c01850180c0040b4216030b6840d0140342ca82c00a8000103401840018040c0c0c0501e030600c031707002c0102d41d0b0601942c1000c2e182d03203d035a128012700030848203103005050f004081090500380341160780d40c000c10148a16440d040010f440000d24050b041c00700e85403007000c1b4601121113468001095008141c14a440c2c4032000807006000301070740480940c0f003a0500142c68945a029040c81440d03046c11002c2c401c2c4010348404a80f00b4050840c0017080d147c510507401a640c00300c0c104104070000c1c00d000940e5a4080c44d518014850520001340500a04409802031100840c0c104201d80d52a01d0003400070401c041c035002219000c0c801c199200d8404c061610000d0b00400203564406001040c040c10300342c480ca1003804561213042c00311f034100b03482c04062103e4034240c4001c5d40c1040c0070f0300c3d010b4013003858a50040c0da92100940b08541c62901a00e82000c04001c4008030343e9054081d805 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 295079028 1250 295077778 295077841
    0x30627040f26070b06040e0a020f0604032015070314090a180507080a1a04050408190315151b06020408030c03130602060903033907020103050c030915 66
    0x100141541c200d500304031100c400e0714000c90384916141c00b410047d503030b6036400b034104144258204405c0c1003036801030580007401840000045500c484015529480a0b0408944518518100400c0d03200d28918812920b50078401c55012a9001080440c100380c079082c1640e88405460010f05441050390100000003040d0600e5808006540c0186014800c0c40d00c0d03c090503261451644196000c01c40c04540808940251480f68505904001d420a01a000452134807440c0141040d1201d000880d660209446448081100000b401c42c80021300030a842c03e0b9004240f8038008042a16050701421130203054101e60090080d40c1e81220002c05004040326502c8001d1000355483e50000110842c0365225007100143c054008140b15201c0c0e0083c070b0240d40f031941d591078000d0000c00141c0042a82d182c401041a08010b41d000449402c100000c00302900d80034913100040903103500814164030110140180140b2400024145c3e80416070b10740096002e690f0040908800c480900c001841c4c00c0c02c5d1107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 295080278 1250 295079028 295079093
    0x509011d0309011e050a0806040b090702070e010e070813050f061816061418030a0804170c030c01050a12090606031406040c030b150411030627040f 65
    0x4001c01c4040c1082e02c821140860b050444c4100d0000d400300180442d20400540350050700c104611540300000400004800e40c466001c102d405408442e0040540e20480c4103025003a88a90b0b442d004103034010044160307242c44039004002901c0a01204100c1412480c410708121051001045400e001400c40d101460b0400c08002c4081c5205100e4009000d6040c0403030002000400500940d84c058444400180701401028110b511a0034510341a4003216120007181d41d05004020905006d1542c50391900c1c207101a55003103c02c000754100c03103580450501502d9031404a144c4000c81000d003010f540340c040c04502a03c42c46074491900750003600d0100c540080020702d51108059900400d208030700c075580389180da692503006850141c070000f00200208001142809080d43c0030a12080e04265030003040081015102000500c06080c1400720070401d147c100382003a4100903030000348124041c0c22842062040308006003028200305009480b04003840b4008040208042e08121114910035165 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 295081528 1250 295080278 295080283
    0x130803180f0105160201020906121807060e0f0907080a021e040f060320030f0402060906070501050a0b010f1d031c030c0f05090f040c1407030215010f0b0a030509011d 73
    0x1c4480055440105054480c13291052007a90310b8018047d2143c0e150542039401c103414014010820010a44801c0c0103100c0d040d424421a8000c0a09407075060300103224400b002030202200741c001e801005603100700142103034440545a00900c131000016a941c1075400410f50210500044641c414800100094840e03c4540b0307000440d0040d6504100401c0e170501020034a5000110b1403690340000e001080e0b449590101c0580c020b40700a003842c0c64400b800f000710b403050f0080341c0166110795440d42000308941d035030b000e6208013050900c1c0c01d119a04507104054a0303250101520380030304628038081c11464034100441c030450121500d00c4524140c82181c001c02500c1074060310000504614100d60b0f403c2d00540541d0b580c8440113100455411040c82884002c0c03410444040030040800019003a201c8428014080f01e80a07a002d4202d990802154100501040e03010040303c0d44444010040b000144054030901842480c001c03506882d01c00303046024281d801091052140c041b065810b804000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 295082778 1250 295081528 295081531
    0x133212070b03010306050c0c0a03051c050c0d050a020a120b0f0a03120e04020906090108060a0306060906061b02030d0c0804050405010b090906010c0c1503020c15011805130803180f0105 81
    0xa00340c01c0c44151f549801d40e401394001d0041500142d808410040002409817020f4050001245c0e00070001623840c600c11700585070280c03000f1481c201d00148200082c4614001d040c0d02400303241055150001840b0000c2600a0750110b20394800e030703961440c800c15556600841d0040900a090138a030359180d040c6800100b031102e20081c0404d2000c000500e040c2858001c0e241b011000a0510f410301c51f904c401510403040040c082a0300040705207010001034654411113010708070b5040001000c60800101401c00310b48003a082850040002100e001a40c1c0040c1002e0001380600e40954005201d2507d010b160044c1c0e000079074407034280ba001080b5410018044c0c40d5a0004440c1081c00d0b850b0315005440c040c9810a0203009040d2401d1b040c020001c0100400d08040e0145c500185006540c001d80c500340360b44140c51003441e1601000402c0802c141c01c0680b400084045802c0101d800e040c0300c144c8481503030200c001d0000002200056000e01c0015480304062100800d0320f590103000d00034a4003c190 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 295084028 1250 295082778 295082783
    0x32d0106080a200c0627030d0222061805041503080a02070b0a030c090b130e09030f07060e010c091809030e0303070605061215180c03030f133212070b030103 69
    0x540c5551380b112071b158410b00451500e10f04040d41c42c000300a0641000707540161152888003041d150070750102c5049030712040041c0001e40c6d0302c0c0407524120a035400c001c1c01552215100381d040c00701c1ea011410410102400f1071760311550f4a81c0e5440c8642041e400d155499020104c40c40011402d0000150990400107450b03a15655580c0c0c9103440c0c10440354a030090300c84181c49100c4e40c0703806004800400180c40d03041036050301142c0c2480e0190b00c0c03840c041d82c081c540450f0450f0716807910b000e0740d00c403d01485018418600b04802214200241d0340801060340c1d941400340d070384a099400501d03004100107540340c04050f05890f901c0195081142c081c2c001514002d00660020402500100003c1a1001507034070b2489a101103407034410080d0b070402070703d2002607914041c4041016190742c1c20002419002c0c0359810468540c04421185060040c00b07501c10702100400d812583d003110302111044602d420740480b1448801d2041c008074040400d4100c00003002c0c81114400b00f101c02414003c0e6040360b2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 295085278 1250 295084028 295084051
    0x314010f050307060305090a0308040618030c0b06010c20060f04080a0507051906031104080703051c030902010f0305040f02150d05090c1507050f0102032d0106080a200c06 75
    0xd6031404205c040312401c03204045107030018440c000001e07104045c51130300903005050205c2e40410002e0800705060f5611012800b1504041002d410400b02d00740c82a801142420b101a80e0f42e05500c81d8407508600e5080c900c03420b407803884001130713031b40e2a54140c8107c83d03920340302961a035843c1c003403056075508a400d056402c0d100355080064545402d0001c0001c42c0501c1492400f0785141881c19000b03002400132052500c407041c4000308410a04220040046000714001c00da85141403a680800c100100391200406040250030710260340c0140c3d4401503540f00e440c0004041d03983d820100701d0740ea403d800080d07002120810300050b002c000d202401c03190700b81c40c10401c0036864015034155143c0f42101c0c801d81224035459070300c1107c060103015041ea10f004406a4080445a03041c1031300726801143d402e40356040e000040070ba0f803074050490300c8a20b19040921096035041210192034004000c0000c2c1420f07840f590032101300c604074003c0d828281841d00c0403640ba0800010310584440c2c0450fa03410111 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 295086528 1250 295085278 295085293
    0x1c110a0806030a080d09020d200a08160b0901110a200a08070905091c0201060e090f0705040b040f290d08070215040e070801031205090603010b0a0314010f0503 70
    0x614000c41c3c0c0b065074542c01280d6505d8540702e0540000600304110060f603000c07606040140100b90140402c0802003407a14102940914407000c101010b00345030080380307550f40300403070500c0c030407070045000401d440100d00340c030b0380b03c08250300103c5501104c0c00b80000c01780030b4031600904020110002c40c8405400c09021129003001c0d506100d0040c80b039203d40071496101c48002c109203201a0300a640041d888000c4d2441c1e00116910130480541103403102c00140e541d1441088448082e142080d0072428101c05006500720340445940d652000d070040c588a950790310320400c21981e50ba805401c24000044051002c504103a04164450b0240c03020142c5154218107100550f1a20350440c0e02803e9000c103450f4109203940d020b1142908192103103600300e0b60100300c0400c0310001519010b00c2051a6501c00030150304602e003445051030b801d444e50b010301c8800d0190112603038488055a040d150b000700c0f0240c94003da100110060000d6019150005245d24004182e0b0441403403c1c00686009500700e1703021 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 295087778 1250 295086528 295086541
    0x10608062419030c0c03120b01020c12060f0601170406110c0a030e03010f0e070909020a0b0706050402040b030f2112010b0301030c0503031819080304090e070f0f05061c110a08 77
    0x5618075500040006245040030050801f40341e0008000c18410f01c1224407104104000c80c0300c10b020600410035541c0040c0401114500781c01e162540700303a0a01c2c003801c840c07070008103500703040c2c40141c070080c0007079180da0740001760407090ba059070f0b09040c2203800c481c28034646080180c21750b01d002c00071074001d500b04005810403107060b00443c1040406100142030092800030050014030a0002c220303802a00f0b00800107600d01440040c006690007418000358904143c41040300300c0c0d50f552011806038010100d404071183c1c01040d6942054040906214241e42c0603203881154490350000344403042c07182c070002c01c6034410000074506a81c0314a0f1946107044d120410582c3e240aa8031090700000e140d9103040081d4200300a180105c06030100a8107100c60329910400d045130800d030880327041255a055401000d6608100f004c0c018600c2114009501d400c00f48070300a50000c9020b1140105000142100007a2002c0c090f1040c110a1803010800d2a0100e091801380d07a202c0324400d070019400c0d4003c01c10 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 295089028 1250 295087778 295087787
    0x8130501090b0a0608010b30010204092d0603021e0f0d060504030f05030108060a1a040504032307020306060603040309150906200606100e03030304061b08010608062419030c 76
    0x500c901d800858032403503e8001c3d0031000070708d00618101c080c0c0d5024031000880904a0040489420591241c20b0030030b900280c0c60700640881c41c04424a6500b45202000075031144c01031554040d9006002a0501c500384000c510411446140241c00107541d100305024401d0a40c4141d0141e4820742d603503862120b0f4280100d0b01ca0000b806514074540103140031800101003940040114058215030000c8200420700250450f40120703002e9011401c50f0001d0492490700203181c1060035050103486042100e00e40220760303100b40043c80640a050000b011406142c001c04800e00181101c401b03541e503500028030020170010031485403502180803141d006034084030894002204a18910013044150780f48000c02030280107504800042c020011560403094030140000c40c400c42c050340c4049003050600500c1c01c80c003032011020404018801006100b031590020300725800c004100c4402c0d010341000c440c400c41d500d00211070740300104400114002e00c3d601070790036100c400f002a10100040801c0c10010741c2d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 295090278 1250 295089028 295089049
    0x1c0c0516061b08070f03090201120507020106060e2706120d020102091009081c180905160203030f0406092909010e0705240c030f0403050607030c08130501090b0a0608010b 75
    0x2007a050084000518807d52101d01003500525142025584203810602201d409440c4e81340140d440d40c4003446501e0f008541c289041c0419070b181c1e00781400e0385400038070500c02207003602c2d0700e2002031001c01d140d41daa101c9544844c02c181416101d5400e101c01d0040e0007948440318242c02040f0003000340d00b400d40034428150403110810f000c1c240925141040600c0c0301c90b60200b01040c49601c40b446a600d82d00d030300904000d01030103500005e841c24501503860003101140304034021513104008010300a0102e030400d941150740081e000c18030300c2a03440c150b0305074030400705031003d02c0c2404405c021580b8041c07501a170291f074001c030082112662001e241c50300c03280b4a00a054125540603102c025441941595602c20142c00900b10b0511400c1d2003240d04542c4a0240c00c101454086024000d000e814007820f50052420b0504000265000201400144000304103a00035080f0401c4001440029005001c40c0b6a1002c180b00f65444c10b14204000ac00f42ca0003510302c1503203003c4030074000342410100d51 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 295091528 1250 295090278 295090291
    0x40e01090b09130305070f062409061d070525031107050603060f010203090a12020306090d02100207020d020d03260f18070b070b0106030e031c0c0516061b08 69
    0x4580407055101a200d960002004941f6441c80c003950002040040c45403c844641054007403525629400c4240e0050005400c02c103000b45c81c0090800100e1010300304140b07001c029030a80200355946880c107950601808034040d4900340782c03600f85d22804071800d40c500602c900c00c0e2078114040484c80101607494a1134040c003500140d041010421074503001c003842c0b120101c144100d900d00642c42010410307072000ca50203203400411258820003185410301100d540700c03401c0c0004115840c2107000096a0b0203c1150060015500203094800d540310381c000c202c3e000ea0003401c50900b604a9250003800d000b05129140480380340c1c003503501480c0c006e40362868000c1e20501c003203040a0702ca0380c10440c040c000c0c0d20586000751044000007c8c030075801c0c0020345980c074010f086910640d0b140c000040e05458145036401002d42013002500c00002000703450b08840c1903001e80001d80d10300225030070358180c460201c111000001d0308820348200304040d0001c64540110601060807507403030000654001d0801d4a10 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 295092778 1250 295091528 295091551
    0x9120c0d02011d1c05011404120e130e0708120414060d060e01060c150c17070e0301110409060e0403080a020c030d0507200d020307060209030102090303040e01090b09 73
    0x1800550701c02c1840c03c1180c4404010946001040710000d2075001505000ca01900e529a0340d00b07060000a10903220a0707403c03213104141c54500b41d5141a01c231004d10f03181c0340501860700024112a1588131744881910a110000c03c0349030f80c3c0901d0395940f4502072040040314401c645e401d0000b0781d09401581c003201c03018410fa54200740880d08000068201c01c10b8503903c00c2c0d4038000060403015000c9024002d0000c0d031202c0010380706500300300e80c1080d0072020100e12039080200300749000d507100401c2040f602c90007100f00c06544070700000b11100480380050310303450360030803401642021040c0001c1c012510f0072a4200207443d5900300c159495031049078080c0c04140c0c107000090505540341c00a00580082000740d0b0303d000c8010b00400210b50003030b104080000c005003036400e640e02c600c8015500d0110303498000c02d464503001c1c100070342d070344a185030040107160042441d4107552403d40585484410050a03280c03150348407260340700026824450b000416003030600010841c10180341d041e0003018112007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 295094028 1250 295092778 295092799
    0x6020318040b150f210f0402040b0424051f08061002010905071d061e060a09180203090613030e040207080d090c0510020f030921010e0309120c 63
    0x100801020301044140d004032410294504070511600280040c1804ca9007403500c801214415004002c618800e08040b040e01c4000e1091380b40310700120759030250b81101c008c990a550700c800f0501a010803200c00c10304852500180303a00100b00300c0c110b0f082d00d805850b480c010441d02810360000300400400700d0003103440d44012030524181380b036940c07065200a0001141c0342d80c543e0786a61500349039034030071203190b01c00750003002d4089800c90b003041d040107045a03040100c43c40c0030010084083d00503016441604001184010a030140035803900a149800070900e030b03507000c4034002002c0d502c08c0b00c68004901950001964a4076201240c140c0030b0b40654803010400f9015051100a520825096503284030134801024032945501480440c40d1003100002550b9140c00207108800c2d20704d4001c20300b550040e0f0810014074900000362031481c6800c85410200a0002c120107103101c03c810441c6040e54281080c0010040d0000000d01041809071003204a43d8210521540c43d80340041d14254003011a12 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 295095278 1250 295094028 295094077
    0x10311070b07260112060e0109020a06051e1b010b0d0807060504030908010e1005011a0706150803030901020901090f0e0f06040e0d020a050111030c190309080301060315060203 77
    0x41c0070300b03512101410f40312485035800c2c81e810f803000402d81c00aa02c0c4141000c07903004000b0240035014080c54140001d100040030703680051040c80480c003c0d5010440049011503103010207040c41c0311003022a4940d07660b500c1030f9103034a900081c00c1520307600203503080c0400310b03200e82010b9614185017500030022600781300c81a0380d85d0001c0e10700030340240c080050000000c0f500003420b01c42d00a2201c403000c0284814121212500245c0d40b0503807128522803201101002028844000c071800c03160b209000040c1d200d54074011359543e50454105007428803012042040340101540200301101c400d0300c4a401003030341c60740c0100007950680103403614041400301181c950103001500307a030041001800410007010110100703240a02807403020006a00944100043c041c0078820756140b000d02d03500041c03652610001c1c941c4184114051400c01c040f00c0e00745015442d102e94450751010f9070040c401c0351380e540e60f030781d00501502d041d6030007401609070500300050716400001141c09140c04080911a20141c00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 295096528 1250 295095278 295095287
    0x15040602030702010f06081507091206020c12030c0d1a0112020a03060503100c030615020309010c0507030f121209051015030804030602031009090203070e150d11010311070b07 77
    0x2610b500e0540d0340320920046080350902941019000400041c6801001d85045a00c29503000e0501400e000301a80c06100d00c42c0c001e00c1090312940c200c20003580d211380d01d5128a140c0300145104007407030f2201000b0300c441d040100c0010900d58030701c050144000078a2144000e244800001e4941c086424449048110740080d0083e00c250b031043e0800141407030340c40740400e040c1076040d098212115954261440500d41610400010701a003d480d0641d605607000081c1d034130b10541a021741844481c0c5c1d108000c01c901000000302943e480840c0c22103906c0c45150600081c1c14035883c003004101e210703e807949083d016221f9400c405812000500c01c488100058400514040180315540e002c0d0710350100100382c44000410081d441359100590740d1500305444001c01e0b015400003100103091540c0ca20240c0d85c001001001d94200450b02403d03500d95140010b440d034100100d1a80210654506030280700311411610764170700b803e032000d002d880d810344000b52541c03082c103a000b0003046000c0c0c0401c0300303940308 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 295097778 1250 295096528 295096531
    0x304030305150301060e102102120304150e010e1903061d0f0a0302060108070b0307050904180605061003060b04211506150305011415210a0e1504060203 67
    0xc20484039500501000402c0c00d40d9501d401181303051001300140400b004000b5070000040000c4168003182c801e524441000c92a10600081e10a10b214005c0c0c0c0c440090138001c5038010004005084cdc038125090740c01414210340c020540d800704002404645030340c1000d0001b528024500007842c9481815075603030364001c0800712081005070a051600c5110240108540ca40d0150228010602803500e0328000745800c0c0140c22581180d08540f004000701402c542c1940d8102d0044c2c18800c0d12483c440e00414024001c52030442ea004600c04041c8043c0030007580040c1c016002030b59003272117080b07038058154195100b80c429101e540b50100070070080c0d481300e120300c0c40822020b180841c08495840d2501c0c1011025000c0c01540107035200020040c440a03c8280103d00625040c180010342c90710080c0c1c41200c40b983c0c210303801040d12114600c0414007500840d0300380120407010700c10201c503c1c1402c00da01d0360201d921030016803038501c25140c000400624407034000cd82904140e91036881e561560080d400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 295099028 1250 295097778 295097791
    0x20a2001020405030d120c021c08040f0f0f06051b07152d0b041a0d02130f020c010f02070b01030f1a0a0209010206060108060a170703051b0a0b0c030304030305 70
    0x600388004990343d035080c024920003404c19600d0842506c02040010201d4008000038006c2d9407005491100c0e503000c03500c200210800d203080080490340c2d241040c0e1900707004054000c0045004201c85000c06c40e1040100b00300d81d005000401042d0b039280c961100d00d104039492198204024407031203001a181041d460983c0240000208869141c00c4e10440b150500c1e4003c4811179500a14190004000c1e01c0360416a84084a06021440c80411034500064000f4206e030301841049411005548440c902d6180c0c1045c0c81c4000c108007009600c00000a4000d0a80d0601c80e50038030010301c08540c0d00740240d800054103e500c00759030741d1071a81c4625008101c1342c0122100810841c080c004012103044040c403411500d5809a910050803000a04082001381807030f040c4244542402000d071504220f2000b0345403480d1a4204034124005450b14194059000420034440c0718030800c288422030a00e0007031020181ca415110380e440b030484001c11700640000001c607071700c10b000081c0400c1c4a0b070040382e001300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 295100278 1250 295099028 295099031
    0x308032a07050a03140418020901030e0a05010b0a0609150e1c0b0f0f090619020d02040807080706020f0c010813120e09010506070b0c090f0306090a0213020a2001 71
    0x503180d04440103160400c08040c0e845800c07440c880303418180c01030b68401d014188942c1007072402e410180000500b07402e81d100d010301d59038082117030048c0d03034002c0d8440084411000c0403a00c0c103540700d2070124060510140158003031100c201c400100f4a018140c100151340b42c10001c03480f00400440304540e680840541941e115105449200b01801069410b583ca9030160314810428a400c2e9042c40d400c1d64080d1051540d9080c54040040c05000800c9481c0c001107170010b0800025005100355000e805145410301c4e816100140014181c02c3c0050040c04450715001030703e10039aa240b100b603827903200120004205030040a40440c1319840f44107410741c840d0682c002407085050359124071100c0300407041d01401007100ca41e02d0f400d0030714007455114010003003103c01d0703890100c0d51ba6509401c480c000d05010103106000c24982035a03234606240c01c0c203155020f0101e030361030315003100f01c2650f510040405900800d0300030704445c2e0000d1139000300c4501040944810202442c2c242031035003000500d080400c0f295 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 295101528 1250 295100278 295100341
    0x60d0509150a050109060b0702130e070519170c1c1502030103050d020c0604080a0807020f060a08151009140a081c020c09040b07050c0f0d0503090c0a030803 69
    0x1030004050320760203000e003a500041c5540c14902e079030b070407111250400f2800080500c421001a51951012507005840c803c0202c0c04c14417202e18149031140c05c0e04401c5d44007400240404403446400584800c4031080741d82a1014801400c1c03140c0c882c5004080c007600311100c041c03000c034000d2074200c2200c1c4042c8582510124408100a4801241c0003a08111203d40020385292021581046085c0002c0e104441803490145040c074030a075912008000100028400700e00c0c0d509540d68481d0b440c043c9070b005801a0342d91000881e00500402e4212421108414041000c40003070801009007038040c1560b8890044403420480030701500d888012103540d00809900c070206031001c0510103c00c1e80030030461612030070054035030081d05110342c14002e1030152548c0400c0201240071090a55000752581c1021aa2044410021801c000c41c04084028900c602003140310100e0388440114031030181c04066841000c00078041111061480c440509000c2003400455402c00b440b07040052440303c1c0041c102501e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 295102778 1250 295101528 295101553
    0xf030512040303020d0c11030d0e0a0606030803070807050906090f12151608100b0a021002040605030106080603010c09060e040204080615040501170325020418060b0609060d0509 78
    0x4060121802c0300003030f8020841d88043c00c03080c0a041d40c404120304200109540310340000740d617405541c1454104c90744034544002c009000780040390110760000c0060150f5078582c102048180d0090394580c0c0003485640000d107047e885042980d54403080208018a800c3c2c121007006503010040007001d0f071020714070108144c400e4082002032528084062100200c1c0b409800c04858060710320344c44000c0c0700300401000f0706a2100c000c200290380318040c155449010426007240b9040440602c41e881c03030b01c0020b000c00c0c1c0c00e030804050360403500160b0b40c500d941e03075480e400d060036604401092030110b02d18402c03d10210303001b500c240e2821071000e04010b00b45550345039003501d0254207491401d00070224031039034429414a40a03050241102c402b400c0342d004840f280496691059014074162503104a5201000e40d400c0c21035031a0310b1790020001c0c444080c0c0074115000080c0700d1001110f41c2c3c0d25081c041a02805c0400540342802c400516440c00e0100180824001d0440102030b0001801814010307981e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 295104028 1250 295102778 295102807
    0x30a0512191d0c01390b01030302100c0504030803062b03090e07030b0a03082107120605010311120907170607020106120209060607060f0606031e050705070f0305 71
    0x1c0d01001d0482c82c10740c0003044140035082c02e041d0109241000440d400060411700507040c142455001001d00e841c0c00001880507140c142140e0000406c1d4040c1900004185640020700503000151014104054034003c8420350725071081e4880100214410f00001d0341c05d1401d00c0700c0b40d0742120b40b0440c5901160700082072042545044508402048202d1028800c05415400c03056101d0400e00b0b0420410541c180080c01e100d40d184401008010000b40900a9404540141e2130071500d10a464401c0c3c00c0603680a480c4200d00c1d0500141246050000a03c40d8480c0c001c0103045c0c44030544440c5032000101400581c440e0040040300319100308440000d01421090706901d00d201c0c070030060711701d500301124028207480a41d4400760307901c80390021030000b680c0d40070180c2c4c0c0c220408445c11a40c07030f07100e85842d40160160700c002c030a00d146003400c0001c0c0c1c650181c10480e0990402c40d02419858242c00c0d95a040700d1007a1000720004100303001040000c4c40d0761000e0111036002c4c5c2000740c02d00001c011042c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 295105278 1250 295104028 295104041
    0xa080a050c01200f0d02071b140d0c0b0d1404030c0c080309130f1404030206011a0c07090209060706050a0f1a0d0308060103150803041403030a051219 66
    0x50019500007841c20190100b032042030340100b2110543c078402540d06541d4403842c041c048071000450000030b910b840d038020340e50480300025840070301011080110054020744103140d104082d0040000d2250381054a4034844040505502c81c2d4400221410210103c10f680c000c400303a18619030b500c1102c00e003800c3c4080c0c52203104501c255904442c0c02c0c1c0d41d280020002000317600440c140d900501884004c1c1d50340302c002c02405410450300141900c1c100144001074a000d2040d950141c21903c1800213056003c00c91905842c440d43c9080d81403070000041c400184100d0403100c80903005000c007030050451640007030009150040210307040a04984601c0100c8409403410f0481c40d5580e140e0b0030910000740190740b8401094100001013a440c00c1c08103140b1403584000504200a100016505078042e03480324503000c0310382d11080344094445103119039941c094003801004100340900c096141c503000044481c0103800380e0b145824180d00b00b11485544001a04c1780c0b000f00d0318615040703d120480d10501 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 295106528 1250 295105278 295105297
    0x7230d0507091a03010e060f0d030206060316050f100c1e0312020406050306042d0b040b0a0503032d0d020a080702160e041403160b07080f0f090a08 65
    0x154504041d4000340c070518043c0d0050b03503a28002c02940300d1600781682560704449139142041c0300750b510300001030035810240010981c412030031010385081c544d00040e40b6120344010b9084841030300041c204040841480d100301684009020310406c040c2c10541808901d0490606101c007603104150b4548075009440700f080a03030000000c220800703050340215203d0380880121800c62916007411401091444001c04a60145032192143d07805201007104000440714100c509800c00c125407401035010340442e0710b80c244a24140000d05845c1d103440100801124802030055151004da00b0952081109084044020724814489007080600c40b10041c0f43c0c034030740c5e201d0050f5111840d40001e0301c0c11102804410440d4403541c0681900012107200130240c4019240308072460f034907881c1001000c2001543e81e03402d808080b400080302512300780034003a014840c02104403542e880c401d04450781801110302520028010340400d0180720f4800c04241c10442c84810707103885070304c01d44901c40c843d800140304 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 295107778 1250 295106528 295106531
    0x3240402070501093509091807080c090c0a0206010302011103040f06080f15132007030905030709090819021c05040f0608090c04050c04090504061d030703020607230d 73
    0x602c510051080344081605c0203101c4076004044029440da190341c000c50031044d00a00d072000c082220040003003102d00c264240d0108a0703071259215401c207502d620000703050794020009400410065000344095a26881255006120907840c50300112035030000c0482c06641d500003040089001d40040303d24001500707154440c03c505040480c0c1d66840d0190080880003d01c44005e240d44042da51300c8406000c0b032000e600003265560101c030103c480d41e440e482107400c602000207440010541c004001c0d1003141c200b2015117013015511794441d0161454808000e11031041001801c034625181d06180c403100c0054411101081c4050b142121600c042845007008034002203410405100403c0d5460302924280c507000885090031304500c1d50720421610749501c901d459131700245401c140002510000c01075400e05000500741818408010408e485140301c2140c90111244802080003044548082d815801000e0030b41c3d0b00c210885000d004600403091504800c4400501007559502500440d500c4000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 295109028 1250 295107778 295107803
    0x10506010e040509071a0f220e1026030307030f0c022b020c0d060f0b01090518060103182109050a03060e0c0d0b07090b0324040207050109 61
    0x90050034000380200d20407401c3c80108503210002042c1c0e90103c0e0383d40301d456001030b8a8011400e525010b8031540c1c0320608404a0001040036143d02214001803100342c1011039640c0380d070a032404001d0126004034200c048440708000581d41c0250100562140d00c812107c01d80480d40194215802a030356240000d4542c0c80813a42da43e602d115103901d002e0075000070401c090f030088102c403030400a51a240c070400c015001c0855010700920080e4a510801840030356401a80d29150740102004c0441061231481d10441e43c0e01355000700307104001c1c2c4400800c00103080e4041c102c4074000300c0006100b68100b40e200c0b45285201c10b43d0415401165204400514403030000d0160180f203032101d0320400c0c00f0441156810440e6482e010b4214055035042000400c4600c02600c40e2481c243d4200100c0d40c00041e014a02030501c03030424480b902880c1d269580003020350369504040d40034003055581412540348107000740c0c41c110f417140c40c070702e10100007410240c01d0200c07980300c440c00c440001c00159a000070149 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 295110278 1250 295109028 295109041
    0x110a0b0f03070203121518062d090f09100203010605040308070c0e0709050f04060308191e0f030c0306080d0f1407111305090703030e1908011d01180201080403200105 73
    0x78087c18400311406c0310022a850118000303203039224030038101110041000c5a035024462801c003246014400541011020b060543e1005289807080303a6204803402004003888502e01d01c0c0c001c0368100e42580e0f031818280703811f6840d04c0c032503644200340841d41000d51850000c1c03030180f01c080ca42d2007050207407909030b025071414046c46003203515409020302c40d031b1900c8070130b000003070f400c2d8103881100300041c008600440e404141502c1d921042c003400b04a4410201c0d41083ca558400040030203400355aa09000d180403044056050b00c0081c041c2c8086900f182c81c1c984030182c072403000e07461450b071689071500214044080350308459010342020f03100710098090024a60828215034048a000c890003001036181401b002d5842d4078250000808000c00010f4417a55030790383c01a00390a000030649211f68681e90f0f250340710300074400a035982e040c11040b00100404590706206010f0751410030640d094203481154011036203498000e004805014600040d546402041c0071840481100c00340005031508204 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 295111528 1250 295110278 295110289
    0x100e030d0608070f0b03040c0902040b0702100807270504060b1810080a020913150e07020d050d0c0c17070b10050d060902042304110a0b0f030702031215 67
    0xa0b00800700ba50b0101d0030030450800404c629404444c0000300c825261707213440c42c0002c54110341b0b038031041403107002083c08641e05038280020324840c0d01c202d401c0709098107410f1055035401011109030b030101d00b001001c103402c0c042040d010343c80b01e10740141302d00105444030009022a820b507000008400c80c00725100410442c2d09080350f240702003c0340c0c54180d0083c1043c008100701001001107142e0f680100b4100300f00d0b12a8114516210720440301071101c1c0c02040605a2080032a03c2855544120b40000ca44514000b1485042030740441c0e8800380703041900d0920b503015029a20003601080520228540071600720b000d802100d900510307940d9a140e080e42040404054040c1c40d1000300901442d08201c242d44001c580c07040720b1f078490800f150030407e41c0006002003424a0420540c03562200b0b441c0e000c604040043c6114911502401040503c90000d00c55114924020056940e0042260000c02c09856000c0d56100d482841200e240c4690404031921081040d0764600002c541100314043c40d2505 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 295112778 1250 295111528 295111541
    0x215010806010b1e1c090b0c04051809070e070f08060303040b07030f02012406030e010b0f011d041a091819021c0c031a060102070b0903100e030d 64
    0xda500500540d41400103440b01ca1013210702401a054207101442e07280031404d01600d6411074a84003841d6038403441012030000d00000c2e1021076003401c0d44c200082d14203280500756015039078040c01190041c141003850000300100501740e070103148149003001601c0441c0e0b2445030700c41c00d45503441c44808141c0c0d84000e0110000500841d1190300140010b000550041c816a040c040d0580b81184040c04441c80680c0103203140c1c01d60044000c02120841009c0e040000d0725130445401e82d4003001015030594903203003243d0a058840c0e0b800038146a112a06600c190000d80c1d8000b640d041c00000c0c41c02100009003100c904100940f030f14601c042d2070407440d04d4180f40807540165450340c1350480348003030102c05031102103c11031043c82d01c001844030429134803514001d0308840c4041034500b103607954504003510300f43c1c80c0c1d1004641402c41c00d85080c80c0d030104401d400c0c0c041c050680041880c94107248081ca100c1d044441100d03098800c640e4404031518036405a0401c001c0384401455554424881c240141d641c0c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 295114028 1250 295112778 295112789
    0x209040807210c1722061103130e07110316020108013c030f060b030d1707080712051005010e010906020303060d0201050708030c0a180e060111030d0c021501 69
    0x210741c0c2d4200d841c9410140c8030304039a40c400d82800065410f0b04140d40180600040044c0f10a20301c035407030850303051001014058600300c0c1c5500c01903403500c014496a80c0300d12001c0164140215000304242c003500c44515400c540b041c00c2603000b00c5403402803c1c1c51500261000009004169290425560000d4540d0b014018240d46100c040f210710540342031740c840c49010103401d480c2100c0c88a1004d1540ca040d000696440004261940e6540c100315000d4403416412901c680170f0300c0c0314000d015010780380c60140c591060300201c16950b00c8904c182c580580007001c183c1408915081581b00302c6103485a10703c640e640c8ca16195103142030100040401d10440281418000c28000501129800105495000d24119031011314030030740d8070048800b0701400d44010301d200d0b00881401503002d0030f203001d0102c080c0c4c25030f110100140c001494081d5001c1600c26800a20b005038042002540b20340036262000900c0000c803480c1c5801a08010200e4060252410058000705603684143c041074075090700400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 295115278 1250 295114028 295114073
    0xc040302010c140c0307060804050708010c0f05070213091202010c030c2a0b040302060702060a14040f2a081209031c0c050601060f0f140301051203070209040807 71
    0x50640d4000782c800340340d00d040600040040201050650810008145851001340030344003030941c3d5660141404005030307401c960500401502044000051140388074400b0140c1e034070580100003e0051781d43e6800a681682c114200391280074a10b4894010301c10030a1080720402c00c01c40200000900311290300001100305424a010a080550320000900380c031101c0d071040c0210310341c20000c411006182c0340001040a95850104414140c011450301c1c85a0f24030303020303500c1580c0c1d02d169420031070354003003d0204042c1202c00414003151000306d401e0b150303520910800c11080c0070300c800700718042e00c8482c0c0c070000d00c42502028482500140314600844a000511f5810000080000398403190051020742007410444002e4130003070711547e90940d1240e00b100907103505584412000300030140c0c0c002d10a000c250208061420716201d010040d402c1204030380c0f2281180d0131300c410001c50345400640c02503184420b02441c0b01584c0c0300b880840c01140304020300c554505561500e58286021000c1802d60003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 295116528 1250 295115278 295115287
    0xa0819023c04090c0302040e0c120708070207090b03010902031006080c0402030903030a0216080c0106060e0909060c160b01140405010e0c19050423012703020d1410050f0c 75
    0x24901c140944041c0d0340340c0140030412089054048001b8000e5500002d600310800c0305010f081540c03d0024075824000050402035a525801d0a503413035402510b5640c0140e01c1f4040030000010254045c55182d0001070012880802540010b40707060741c1c10002784030b07059403040100a00308080051040200040d2003c2d8258501a00616120700000700502040d0b50005140d40c454007a020007887d80e0740e40a440c05450394500d00550b802071200e4010640800c1c60810342140324540416224441c0640750300421150742e424110b46125002599a4554040111840400a501d440a4501802d050104080c91020580030481a1901a4041e103044400f40c0d00f40110f1802283c101d44c0c41c60340b00950b00104000c142c004440c50712031a40038511010070b0000042d04001d03401041d041143c4241c3e1016000540c039403040c0c41013000d0384030310040010701d50410030050500c0744040745170f103000d0009100100c0801c1c20050410002c0f840482445688008001c41b90709071002c0540c00810103500e0f242003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 295117778 1250 295116528 295116637
    0x210206090a031205090a0804030c1517130c08030a05030610050c07030b04020109050405010b030f0609070e1507120207030302070f0303050a110a020301061403060f0c0a081902 77
    0x98032101040b01000761315880050500142081074071003080d0320000440d0384036540d0500364102d03021409a1550348601c03c00e0b0030742d0203200740d00d0101c104507842c42d8004542c949020030b458089070800110f0310340c1c0c13031075500003000682480a0055070f0300a4440b903559190240801180c0076074445a501800710501c00200f40c2d4400069003001d4aa000c0500c1495885074001680d40c40405e61110354030500b014000f00d084680100030b980540101240ba20417500e512003000708080d400c40321180005ca40e1038212403070f032030409403504107041c818045031302d0900142c5618008410303c1e25a1300c00360744041d40401c01c0581c104502c1004001000d5039901e62415641e0090241c440c01a10340c040000c083c45e05810041d0074401f00305d0b640c1c1c0c010001c10542d035031207580441e4420003400d80c501c04c1c0101d2000818900080080901c20500492180c0c074203003a140c01035448481c05840c92003090703609484000300c040280300030480c143c0b0000144ca40b24840c003609400301881d80e141030465007400c2841c50340c0c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 295119028 1250 295117778 295117787
    0xf070303020d210609140f061c031704050a020a15050313050c0d060506151305060f0706060e040b0c0a1d040209060301030803040c060c0b07080a09210206090a03 71
    0x940e640189000300c0030080006500c031201150002c4a040c0c0f0b4541240003801646a6100e141c042ca50444102c001c1c0d55509100c000b821740485d0015000079280c1d1565407000148011541490700c40c2c28501d41210710942a040000c800322000c60f4158006003a80066182911140000b0003a502c800464007a60b914010400e001c0038201d02c9000c1c0600d80c241c1e04114003404841c800d644041c20503900700016090041c040d11050710304a01914002a18038138049028044a01c14584610741040c864500303814801254800c4280c1e215115080c082440046d43c14041d1100802e20754840c03440034202030620071340d200070160a10410762410460a0340682d0071441000c1070700c8841100e14400d924000c0800e02a101b41c0340d2082e0300c1030001001200f04038204d07010f503018600404845030000c0c2c803950266a0a024500050070520508002401075845040103a502000c0083c0118441741141d4808805400340c48008015402c000b10041c2441e5040110036800a9803400801040e035031510081d1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 295120278 1250 295119028 295119043
    0x11e050904051908090915010e0604121b15020601090c080402010e09040303110f1b0105090604060b0301021303051b0108011d0c0c07060c0b3103020a12050c0f07030302 74
    0x200c0e0800d0f101c96414040c002c0251501900f0181c20300c08140791404000405062440e403040c085415407503040380b5806e144081e00c060322403442c800c414526981e129a0b10442c0c2c41481401d9006c1c2c84000407662008040c0e8690b800c5006400a100729414400f04009448a0301c1009d030401c901c18080201603a07104a080170060001e82e403c144541b16400c04601414a02e0804030283e20f000a264114040c00d03001000e804c1201c001c61201d0402880c650380c01c0e02c005841c000c035076a1050b40400c2c0418500d61190301e01080040005261036282c1401142c01d62040c1e0007580c0c0e5401c002c131410300d200d81c01c000381615102c2c2482c000c0429810940b400c03588005080000d40c400084000091400911504a4416510070000c5131207841d42d4003802403080701d002d2811075070b0041c050082406495041c6d08100c04c6094059420900320040040111050440c0c505508610800d08280003080819542c0d10b21003d4035510507070f07101010b0704100c0c0780c501f200306024401d900102041021039404209103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 295121528 1250 295120278 295120303
    0x6010302030901090503161401150506030a061512140105031209060409060b1902120301050d03031407030209030c01020f0307060c0c080408100b030c030706050307030f05011e05090405 81
    0x507125151120480d0042c08440380007030581c40006501500780036410007101e4114401c100d0028282454441ca50030385180304821200705000c003030103215a140100103154411003800c0c001a10341da580048588114200e9006000325101d000307400f600107100d001d0080110b16039031406401e545820042580e0301c101100712140b880d004a1100b40710b07500e00c021540104594002800b060b510381100c1c00c0c80368060380710104018045c0e40074044050001c20301c1040141e130100f20900b03613880d000500c00288100350044080569582c0d0643d40954540c5600b030013841c0c155401a00ca50f00201890300e040d08100945040d980007064a0404100010031103552070b50140001c9140c40803240203940016100e00000c1c5032400106001c1345400c000214503401403816101880110606800d05444d034200c0d610850701504020300500c00340e8028001990000d146203800541301e8003481e048011540d00f0780088200b8482c1d050f0990001c2c0c848540710014001c220350035805402e09035a40c44c1c0c2c510005100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 295122778 1250 295121528 295121531
    0x15180b0c09060d0f060501030e0706091202130e0601061803021509030c090c131523040b18030d05041211030a200301110306030d110a06090c0f120803060103 69
    0x1446a030b4442c0d40660300c2020080c0401d210301084120003401030a8280100c1c0c1c0000e1500e610720f95071520000e42401140c03820b032684c06100742031800c2d0314040614420b003660440d001040e00004d0308298403801301210f4207007000e0641941070441c001d20448030320443e81102409604c0c01e001603500c0d103601c8003030585030b810116030352303a0403202003030030460b5102c4a240c1c4007912804000200e40300304000d08102419004261040d600c0f0b1b00002c808607602a0040006030080300d40e1000e503110801d03000248025800140d0074541d60341320f03098140c0e200d013920903264076614200214606003005200074052403400c00a060900f00161403003140080c400190140b001e440c42d0717080d00d8406116400030700c0c4e0820269640b0040340c10042e43d01494249400c0e02030b6103040783c03080f000d403100d10549008480c001c02034010360500300d400300c1c0c1c00d0200000d1000c0310b010300380403640010220300c0f8a200c0d40d88240b4001c408039180080ca141600d085501c85c001c3c1c940e100706400c0000c2c1c09501100e602c000c09080 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 295124028 1250 295122778 295122787
    0x3110c04051509041401090309140d0803060603060d0b0c040603060812031906030204060f17060423010e060f090f03040b0a08070c060f0608073003020f0a15180b0c 72
    0x1401c5c14141d440301400103480d441c204038041895031000415044d0303501117594003402020070080c4201e11043c824007400442060001c13841910301207000b507811035001040909254000d031240c42982c2c0c410744a08060780000142040b4050700f60181c00014101d040107440002a407401da64100d00c0300401d4040c0c01c1d001e100043c0d202400c03550200c400346401900c20426035846150380c041c60703800343c0200b04052550480740302d448a0005040c9115551003400d14220b03550314006051b5032002c1055800c15552503010710082c2810030000d4034414a42690191224100700c0096414507154000301d05081c0c00c01c22003402400500340490304d000d60245045503036651600811a80e00c9441540100080d05200380d00442c41c0c5a500726609840314641501d603003554800080c1480c0e80d034501102007410325160908400a5403240b08848980240107035490034214801aa007003090420045422100011600c0c081100310f20440c4c150040401c41175484803c5529450140b0030020082d40b0407280c00a03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 295125278 1250 295124028 295124033
    0x609072d030b1c030c0213020c100b04090510020309070b0f120105100e0105070c090507111002090d0b0702010b0d0506091b01051207090506041d0c03040c1208130303110c0405150904 80
    0x40780900040391340464272004403c80d4240c9581001414a0005007004401a20bc0c40c0511480b4031441e400700003424140144111400650030080202480c5d0194540000b86004140300130854906501102d5550702e584220640040f075043e0449401206d4182005840c140c2020300070550020908050f81c8070506844d0024002c101a041301d00803e0402003440041c50f040143e4510351034684065545c0b1b1200385100f00200e01502c44602d07400520160105c0201d03120058a940012562002248000355040490505040540211000d900c4070341008000c1c0000d02045c40414020ba40302001c4500c0c7c2c0000030180c2c011040081102d0303d03070002190010340500c03602001043c1c00740483d900d03a65101c04c07403070075045d8505c001803c031202c14001500021200040768403580d40112608009401c0c1407050800e03140c500f0702203802510030000d120904482c03001b4078002b035110750f48100e01002c1da00ba100d8200761081160502517810305c004e00a030f00c070700d1a490001040054400c1707200da64460 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 295126528 1250 295125278 295125289
    0x1a0405060d020c0a0f0b07020706020c01090612020c15040c0501090501050f09030c13020c060c0a3002070609141b120a06060617100e0609072d030b1c030c02 69
    0x504003510b0034a100c040211207441d00c7e02c99041c1e6000c2d5081c080c0d8402d01039031554402002d1600061004a00b07104a60090f10441c2002940750001418040020407040c43c10381284000d004101000c020441006181d091001c060003007882c102c0240d030316080020b00103000c0d096032035800580220f500f5026403002c100203000d50600400340340308100056441c3e030003984462034481c210300810b40040c0070f08100781c0c11105103a1048d55240400b81144100422005101d00100e001c0c0e00e005040002c03200e4140090200c844c040d582c0003c002c0c0c3d82c0c0ca0080300d080300c18404201140c0144507190080c6d00044041c031080e182c01e88000e8588524003900314101034419200404491030002c010900c80c0c2d020108030381000c019416440c0585a4201c14032400225210f101e981039500000103516080070300c0841d8002d00c081c10404159140c2c1e241280f171920110a07401c492480d84204082141c1d418014280240d5040c0c0340081c600c03c440c6807054011200c0c40000e0180401c0d6204c820464441 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 295127778 1250 295126528 295126543
    0x901180f050403051b07031109071b0812130f080f0706050a0911121b0d06020a030906060f05030a14030f0d050105010f0305090303160e060703020102041a0405060d020c 74
    0x21400030007552419150140480c0c0003108070550a4005101d8903509140010b505415203400c142540100c0300c0c20010841e000d00000c001000f0444540325600700c0b211420002c2004900c92010140c403403051442d02585807000400844d0100040d80e05240414000d039030019046402010790390356040d00442126142c420580300800304c1c0d10b00010441c0340b102c0b5a0120540910800401341c40420b01d1081111408220344030854941103450800328412031100a040000340192448142c0001031715208126084884542c0100340ca40041104201c03181c03040c03a01a01303c28012845041c100004241d0b9804a070400030208100450a83c40d5404c0c10000d480c494403d2408007550b840107080028013400083c8541c9000c030f45c0c02c0d10040d002d130b4028010144140481c500460650350341c02c0c01010040d1454081c44144110711a50103160b07214080202000d502030780026030741c1d5203000314070020803414800070000c05c035091005100300d50781d100448001d00c0300d0303200260f283c685030001c2c103040555 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 295129028 1250 295127778 295127801
    0x20c360c07121b2303040b0f09041103010305030c07050312040b0c1501230108060105030403030b150d1a0d030806010f05090a150f020d0f0f120e0a050706030605090118 74
    0x1040c0d400301080000c465865464a02038880e091307081c900080c1e0181d0390b4001e60284004000c0180803604402c260f400251442140040012614005a15114005a0080e0030540f1140c0000a000502c183c0070000b40c070080c50241c00030404550200040003040c02a0701442c8401034002a9100c40a04100845099038000342c40d07551072541d50b0071100181c600c06a0600391012111000f228456004189040c820030341a101c892855490f81d400310018450021a543c1c03007080a0412541c44228401074482d07413843c56000120f45100d080c86054182010b01640c2c401e42d0301e04902400298010425604a4820309120800e078900600c282c90030301070021915086106008002402148001c200407101159140c0b42d201002205040380c0301d91006c4c046201041360340d00043c51643c882c0740010034015030340c82c1640a6500c00403011043d21020700c0d400307680703510500001c8203001013400880c000302100d0400700301a6142402040d1207150510030408070141c0305038840c03200350f15a044444a0311 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 295130278 1250 295129028 295129067
    0xc1a04171e0106050901141210061a0712110a1b0e01120507061101020d0e060105190303080610050f030f01090612080f0a020c360c0712 60
    0x421805605545440d04034100450070701d80100c42150200620501c025180082c1c54800d450b03081001b16008201116005500200d442002000c100024018400d40c0030b01c0b8170021603000d16000c1416032005000d0500c08900208000207400162060007900c0510000d00b40140301c012f032155000c0c02e0400d2080081e00e26401003040c018440c101911a10540d28021a0008c0c140d807034003444024407022480c0109141e1002c4c00910010780200c0004503c6103860001524000f2149040001d5070300c2600390a5041e84100010f1056281c05102d8044088103d607050f00b84c0f62441e01c00400c07844001d0021342c02050194001c107034861088089510308102241496502d080001d60f8007d01c04e402d06c1003041051a0010202d001015045400440781d00071201c01d051560b0810164942d40c00721002500790301c140102d0102c1919800c1321005248100007501324a40202e0352441c403032868208428000f81d00010400000c5a91a41a140b01a4110101c10070075081000c00740c0c2c4a40411076583d4298 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 295131528 1250 295130278 295130309
    0x6151002150613063f03020c0d02060f070c031205030c03071112040303020607080a06081b041503200105131203180b0a1806230403061806050907030c1a04 68
    0x40280d00401015501404504203a02545c0c05201500c0801d00300140140c000c0c150040041ca08104000642400102490300d40071400103004020f9010800850345aa800c403002c2092012544122a0500c9070f41001c03859032501c040040c81c6840000c081e41c050094004404421070000c002409003c6040c02080d0380c0e0729140c2c18065500d00049611701c00284895000402c42c2440d401140d08807010100144804081241a5043c03809034a2900341c102d907851000c100740c50403901d0540e000f94022074105054116042d5088042008040b181e03060000030414503c1e080d042500d400c007180c3c47d140783c840f501c824900d02201c040d00013070f2061810525040021600080318401048501c10a0f00d074500c1c4000c0310202d10326017206c03d115004c08079001c91169810603202c191300320100b013008007482380f4068803a9900d404480091110003404010020740004001e46445000d401c90140d00040620528540d564881d608060041ca050585480c10140301c40c04060107603009440348a8462401 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 295132778 1250 295131528 295131569
    0x60503120403020301202a01060306090b0a05060310050901231f08031e16050a200901050402090307120807060c0f02060601200615100215061306 64
    0x5a04a030106900c01d505c2c02802d0807501c02d90040d4039250140540c3d20f6400e10407187d2490700f41000e21790f12000c40507074080805566503002e10442000d11f214684c005440100c034105180e81c401d00a0800c01d01620380418400f4646e80026407034907034070076604046030558560b44880c1c05801c100100004440c01300008110071504c00e50b015100b154500c152030021990b0658161030a00e0300c1c490100d4640040192540c0f092407140d0385040041401c001c10700d0900d4050440202d98a019000d0b10941c1103002d8120410640700444040d030b6021000d83c1c50085003480000754400c1042c410540304035070008501d03016490034014040140b041d40c1c10110030b2005410582c1b820360003100c08407922840e202c0200100d0b40651018141c9580a43c002c0c241591200d00542c0c00c600411240303000e0405a510140c00303c0420041144185803c03070708280c94501c800180800c09980080c0c0d982903401050703001c00d1540481c02c005900c91070498040100d90707130b5841c0d00c000500c8640c001c4a613002040669514 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 295134028 1250 295132778 295132813
    0x360209061603023f09090403090801050604020a05030a0b040b1806041805072c01060507030e01090b0d09020a0509010605130608070e2707020c120d0819060503 70
    0x307024000d80030b445440d090300102c0b5450280c0e42528040806082c454100d044c1340303401c0c0d42098500400c106600d09008100042d0900100311005c800081100300c007400010003e0045541000040e5811342c02c10081003805410f81c040200034051060307807418810780e40c0c5c0d9240c001c1c0e10659030242070300e400014490307108948002c2c100c80c214040e1b410315880100c039480989101440581100107030900e1420f01d0403080d011130340a441062445050090040400c6d405695103008001680304c02d5542e013820304c0d003e00b0081c04c4c20b1245041c4001640c0802c9558079100886899140303c42d80045c64103001d100044084d0082d8000c65040200b43c8004142941c01c007008104234a00c041410b84025074801c03003120f00039000c0b2544c40c000b912068100b213884c2400c4030710381d410200c8013a0340b098a4040550245e0799040484030180107902900010840381884040d8080a410040140c48003212440303000d001250003520354180e2507181103100d402420780d903000d940035180c010f0656040480034003d00c0c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 295135278 1250 295134028 295134067
    0x3050901030b0a0623160b090a022d03010c020c2709010207170310060804031101090308060a061d010f0c0602030c07120c050c01050a17010909030936020906 69
    0x2c09440300e001060b400d4161700081d10902d454840741d12609130107580d0743c0241608042d10075441403181c100c070040160795003200e18245003107110042090035240b10700c0c248800d8459204038041c0c0d24085054103607650100341c1d61090b080548001100c4000b02e01000001030000070b13120710001c04201031040110043d0004c0c1082d90040440f0b0f100c10001030f103d50a40e20080c2d54101e450035100608010700350103619465801802801c02e4041c45103003005030390039903480ca002100042d001301e0401c00d02d4a0b065041201400c0980741810001c2c41d84007002400e800400005810700030014080e102c0f05101e40310090386036074000015522400d207403d44d80309a4010790710840c3e01400f06440100c0d01c0c0d124003596141140c000d80180143c2045200540301580b100d803419003007110540c42d64441c100f40c0b00c1c0b020f00912002400264111550074001c1101c00b00d60015100f8000c0d003400c8400003a1001d10381c00c1c1d170305041900030300d080000c404854000d200b074900c10f0f50000400304044140b1826942d064 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 295136528 1250 295135278 295135307
    0x1140708040e06030f1605040506010e060d0504050111120c0903160807091d0a0f170a0c02040b0a0602070306050c040f0314070501020105011206020d0207300512010303050901030b0a06 81
    0xd400d051042401c0c207031500071b840309410744e4580c1034108020b80d25050700141e40150f410704180c60300480c0308010800030351000c802030300c0094454003070004120f000d01ca1050795080800c81d56003801041c40303221100d0a400380941100e0800410282c410748c0d410b114450348008924681500301c1e0b80c4010150300c03607505218004007186401006103603182040e924000300717500365000c0c054068907aa5103002001210b070b002e8400201042d8a0a1501c1e8081c0081240641c5511010441d1a01d0310400c020356a000803058015090220704012098001840c242500e5002e00089065540c84d50b850806020301e80c000020501c441e0380010a000d0070011119400402c20700340c4056585440042e0b080c0d50081c480d00225200c9154040c021610703950180c1500c0341000800f52524103161200c0411090030501120014124052184015900e031500c021804c10783c02e01d14104210918200b82c408814032020b4140900020003c002da0f209a1040580d88802408004115140c8500500380803941018 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 295137778 1250 295136528 295136533
    0x1b0708060c03070e010807020c15090f0414061512040f03030c0809031801020703050304090501170604021309061b03021908450c0a050105130501140708040e0603 71
    0x480c24544846007220f00c50070403034079140d0f44018810011198400d0040c035a004502407121510303816691f101c0d80040e01300e215501c19444410440820441076002000c103840f807490110342e00c07a1000030104103540000c044811605403452101c00000710310840144c000c5110b0240304110800ca402c000041000740240c0e01003003121203c05d0b040d580042c054440c0d007a41c2e401031000c107140300d810300c001c901d24a00600c1956440c55496481600d190499042006030355120001407051144140b1000e6248100100521080c20960082280240303042c0801c010151036001c1981882460b03008070070040045002c580c10100d800c1d100400075040382291040c1e0500400301c0c013510906c20b8111a0240484440d8104413281941e20340103004d0140865145a8040b034819684e2600301041481001e5812405466801c9442c030400c0815a56900850306118082c800701c0464554603d2034400d5410070700f4143c1c2c4d00e03803e000e00024280120000280304840016010807182c40f400d88003806880140c04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 295139028 1250 295137778 295137781
    0x5010524040203370e0706110a080a08040f14010b0a0f0303170403031508010204031e03080612010b04090f0b010807031212020d09060903080105041a040b061b070806 73
    0x40100742d20042d100d440009400e05840c06280c19a800840b0740c0420900d1015000e400313848821042d17414816880000e504001c1c000c01400360050420760409050700301810300914290380b650301320700828490b4401c000b034200014080045c00014450015000030b0f201240304c60501e51140604180c1c1c0406001b40e040c05800603c05503241c1094042d00d43c55201d840e0850883c0990030305c1c1810081003a01019100c5552401c3c0e884181001000344c10184005644d503404c60400040186600ca5103601c2c400c51407442c580402d41c001d01c510707080754044030080f41c00524080198054020207402c290300901c2d000080040103480100b1500880c4607400b4100680e98480d0031689680487c0b00141c19003010304241303006188140070500b00d942c241c600041c1800000c007922012602008030885001d035803031401c03209268010a101c0e00405040728240b1100d4800401a001c1e6600e603110309004a488404104a40e80c80c101610b500d40320f4009083e441c5460705e40e040307555a4071482150303603d0250741e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 295140278 1250 295139028 295139101
    0x507030b0910030b0a09020a06051b15011701091b1a0708031f0f0308070506130213021c020d0b0109140307060806030a06090602180409020d060506010c050105 70
    0x404042c0300701e06544403450700d80e1a54441c400748a00040900c01910382d40c805042c0142c0c0d410071040f010300a182e68017911030402416415184114442c94221a80710060424456210707a0000d810344010410f0710305100714103c003044c003504c801c140082c5007103050480e64104d5140843c422040301c1d080e460300e9450b07440b9010901d01a11071002c0c041c1810b002000000c40c400d106811091202c12036400c0c0c5142141d480ac11300380112a01c0d0030031640140006101c2080c04800c00c0281d0704809811180044d500711a4006801510f865607501c50458010400d45035560783e008014081d443d0b20b010940d56078024604c150020455802624045003048002080850041508403001900603005102141c14100c040d43c0051000341110341c075200c0c2ca10a80c000a840d0300841003418858100540c48211144051946409030140d01c2e000d40d04d8007030b1004c056514190135042c0c441d00314270b00103100d48a1350012a20386110f0071014000303600b41400d000c0d8400301d00d088410b00d07451140750321094840c4d22 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 295141528 1250 295140278 295140289
    0x209040c0806030d0c0819050a030507030b0307030b09031c1d071d04020a0302120d02120f0f0307090302030d08090d0318060b12010903031d0307050d03050702100f0507030b 76
    0x20760b11140c25078821810200b4850003034800b1130400340142e040c0b60400541c095001d03d180202c03119100000d40101c2d1000200b0b80601440ba04032459040611102000c0b1011a5881c220392002512810808000c542d10344424000c03645040072003403903006c220151120704005400c2041d00350203c021054a104082000401c80e8020b44401c1700c1c007842515410150a01042c00190007641c1c0200032580000042c0da030b01d4002d55000403014054102c00d8010f6001a0410000c040c0c1c0074201001041504805140309040320700d006040101d07903840f61207a238812100c07401c2c00d0300000e40500c1160a40c5011a40120040f4442c030354440c03c880c25043c81110031801d552000c1410000c120240305c5030390008945411410300c0e141c010f440001308100407c0300c1030960b00c0b200b0061f00031036580d910030403646810000d00038221042000951502513550789660b59810140003240c2003507a0740003c02d078620f00c28483c6466428004805204210035405801c004040543d1400c0210340f80c03007070307440076410032 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 295142778 1250 295141528 295141531
    0x206160f0c080901140711090106050f070f11121c030b150307020c041a01030e0303250903150203180706080105010c06090209011d0703052203030914010209040c08 72
    0x155998411807406554401c00190003000c002c0d8180b20811401c40b140d02c103200c0280500d240241d20032280031f1401e07424000915810b0300180104a0100b2003145d44564802c101d484243c1d001422807081036403810070385000d0003100d201690091016502c441a010001211400c081d9090381d80d081071070041e00c0603022182414000b40d00940c1201c0103039074110000c40a16406107050040e00c000810400010341228140c1481c81c0001c070300040310401d6568140b14041030000080003d610b50304044070030740c4002000d0340340c07100c50009500010216901c50071000340111751000e050028112402c4050010350807c071580d444c40070ba05c1c01d41704440c045c0003403044100c03003454035400a164244401102c1414400300705032845900c034264000180c840300308550003040660b884032114211011000700740c1801800d0031007014100010700c40010301d000341000d4803444401612900e42d41619003078010746450300002d44140348110a046074000107400400f8114000c65041041c00401101a50441c90 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 295143884 1106 295142778 295142807
    0x30207110d080a09271e0203040c060e06030415020c070815011a040806010e061c0f020118030812060d0804030309031b03030507240c020616 62
    0x50203002d00c0b0180c170402c400d000d240b4402c580c0005400c0da48022200352580c2ea510300507007414400032802241c0d5102c00f025505c900e05418041c03414940d03031007031001003481e11a4000c0185800d408580c4900e50241c402074039107041500d102d0094004182605891150410125680b0010000b4040502d9000c010611940c100301d21030100da4004030900b42c1c2c021003808140101680850308605540b4942150301c403590703a0f40b00103401c04480443d8000e401016002c068244040c2c2043c0607400e6000703803075490074614042c0c2c01e82e00180391484040e000303080600200d500701031007100301500070b040186101c804075100e40b00d5002c1d5600c02d52045010402c08001001000007980c05d028180e420040100c03500c619540303010300303548a960401807031484400044000c0b28088504920321044030902000b0b91132401101946d1103c00303460300c40d030843c6d5403003400c0d175060b20038611011300c141c = true := by decide +kernel

theorem cover : BRFrame.Cov 294964028 295143884 := by
  have h0 := BRFrame.cov_init 294964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 294964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 294964028 ≤ n) (h2 : n < 295143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
