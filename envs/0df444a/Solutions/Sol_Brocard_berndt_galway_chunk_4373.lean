-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4373
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:24:49.969464+00:00
-- url     : https://prove2.me/submissions/301a5fb2-8147-4fa9-923b-c4d07a058473

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 786330935 ≤ n < 786510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 786332185 1250 786330935 786330959
    0xa050d0c0905100612050c1c09050c03010c020601150513140a14240f0f04060f0815010804030201060b0c010c03110c0c090a0209041404020f0415270c09 67
    0x2081c40d003e5080c50480ca0540c00038080c0d10801c581d4400d0360b0b40c03080440c40c08034643c0e04941e41d21540381c201346580001005000010f06929108540c00d124000507801c69040600400700e00c400680c0240c0b840d82c2c030b0310074481e10b0440d0080c001020002d08008a42c0000c2025181101410580b8080d5103440e214034184051030515800c80303c0d6103400400e060a032179496601c08082d20720716401c003004000d294080802e00e0300403040101080d10b80030a010440c6803100000d48211140355441041c04c142c07000c0151609031066520b6900203025029036891540901111a040f0384a407000084107a43d80b80c0c00e04030b5030042d50029203565158a40e5101c2d503076050003543ca0b000e03a401030030b602d0046030f000c4082e81c1d12404040c1c6400b400300c0340d0000d04840b03c140e050b1403a60401410030f2081e882c2003102c0e00d14110b002c46080f48030b0300e044a442d28890600b44502d00340e000026900f04942800c20b03042e00c0c0d501c10031220100194171654800080d9200300d004000135aa9503403143c12190341410451102 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 786333435 1250 786332185 786332191
    0x303050a0c02060405030a050906090a0e07020d0c0809010507241b020313060c051f050604050a050403141309060b0309060c030c03150607121205071b110a050d0c0905 73
    0x2c541c043c500b4000815000701c01ca0750002020300300700d84c0c2c0c0c00542000c540315000d10209294440d03001180040c5214030441100d1280003260700350b0341d120620303000c1a80c801154080181070300a042c00a800e455004800400c041401200e03401c0084a101004e0075420900c039001c1c00b021a140e610354411000c0d034001e013005050443c009941010300e00c403424000100c003442244100a50501c541040c00418014000e403180101034080f8110119000603016200a5815038000c0d460720000a41301401d07841100c0c080e551560364046040c825040c1481c481d04103080b044401c40e105800015070240501c5000000c10404010645902d41000d40c90308107180200181011035040080000318041d000480381e1100c010706d40c0c9140d10760300034081406805000c0005104000004001d1443c0381c00a41400c50240c0d8034405121642d030307c400c121404503d44655503000303282c8081b0000005c0c1c0801c901c175042c03d0050b002e50784882c1d5510004a1104a003d0180c0d184016001c3c140400041400303035541c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 786334685 1250 786333435 786333437
    0xf0f0d05010b1c050c0907270501081e04020d1106180f06030906010b0c070905190c09060c02010e18131a010f03151b050d1a06070b10080303040303050a0c 68
    0x741020f4070392241074407030f803401100070300c1174032601c00003090a4080c40c40030301172100104040b044501d09610300600c0310014000c59010404c00b1001a03000a58a480c0150303a200c180b6014000340c50b19800d0004403607540c03504452400795260014065100c41c0b01400380c4090250080800c0304c0000c0c1403000c81081302980742c4c0140400c00401c0900980000e034035044503084030125559158807144030b801c202082e0013070210281041c003401860008851044441c1c0c5003024104084c00c0a60025104109207110701000308400c01610000756001f101c612411810140104800320441c0400c411940c4040720f40c0501040710000410510070a048082d804d080030080480300d650400da500920710a140c400104802d6055650b2014421a904091520361503054100400001c0041c0038046801c0b005a14045a01e089840000d00d100840d804c80c10310009880703186001340c10703110f40505050081c664442088008000107020f1320030002188624001e070740014203800c082d811501a500f074400600 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 786335935 1250 786334685 786334729
    0xc040b060c0613060b060403030906021c02250905041b080c030c0402090d0203010914100b06190203210a0606050909270304030501090b010608090307020f0f0d05010b 73
    0xc41c18040002e03a864120003142c1c07911008500915061001d0160f900015400c000003103800010150010304a10503030b481d036001d6503044101500c40312000e6181e0804240141e2001356400705604041103101512595a41c5000c0c41945800c8200182c8005513001c440b6180003101c80c444512180480034041d02200011702454802040002e0340e401017612101d118907070008003a02603a840201190103942e02030028800c1901d2070401c1c255113a10251034020301d01a07001291284c0040c3e200e100325000c40149294108050000d85001c82111814040c00354841004151582240c400004400c00898020750a0b0391070004000c2c0250b8000340d12502c10300409005000c007595528aa00d0b43c00401c064012120840801406100300303a07201d1038000900002401206201d01900034111543c010042000340e0390740e80704111a42c12048860860032741007444020010300d401d40000606250050044aa107004903000502002d22400100d03101c0e0354a001c86e10440c00d2800010407a000015035a0b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 786337185 1250 786335935 786335947
    0x120406020a080a0905090f010303140a021b0406180e150403051b030409023702100203040303110f0a02010501090c0e0d050109061401080609070f090209130c020c040b06 74
    0x1956407040700c44010241180494214012071141e101e0744001c1000030020065400c01a0140710410b000303000680001d03901c0381600c1843c2c401c0b0002c031013501c0c1c1e29500605410300a0704005580f02510b000080d40161074200005020500c4880328100760710803c0f0014003c1e09a40540f41703041411135441020024910030031002c81e41017401d8a86551129075082c01002000c078070203096100d590400b03052280300ac9001c2030ba50744094148081900a220300105e124181c00f00c980e010800d520111005a01c9990300546400c2a9006143c015200b420701107141c52800d101d0b40c10b560449012103020381404140c0081c0c9550902840d401000c03103c008000e81c2c1110040208000e240500950054003803900840812009501601040d50060400c200c44190903101c0c0c01114001e20462603140b0850010965031900850010110340c5d540d00d01e005030620700b05805000e500400402584196810149294144540918080200e4036400307000403180700300401003119a0500411301078035042c008 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 786338435 1250 786337185 786337187
    0x3020d0806030a1a180f0c0a050a05031e0c04320115030c0507080706020304020a0806070c02010e03011e150906030f0b10120c0e06030105040f1403072102120406 71
    0x800320341d413190380c07040d503281d8500502451911018145036964451010020038a05d0007252041710394004854055032a5526803c121000400d8000e40742e042e00400c0800108101e41c018850ba082c0c0740c001540c040c182440001000ca810269107803050210400b841a00c05005602c081144541c5400c40400d650500c420307000341c4074000e07400700e0a0559402d40c07851060300030400e8620040d40285031994841d1180380c0740010790810b690490007610b40d4a004108080c01107041e501c1407805550303680e40005903800440d140d000ca621216055507031444a00d200c0c20100640f000d00c0788446001084d040c1c51801070400d003920030350029851ba85042820300c0044c0c8038009402c04030307400110241190b103c4504c1d10751030a841e60302002ea80c8880a88982c10803040c580c42c80c0490b210b540c07940905540b00320601d4247c2e07030111001031103404440007071b600054840c4070b031001605044048908200c859a1081000b141d4603015144981d005461202d00c0c50381004400282c2c5000003066091500e8220 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 786339685 1250 786338435 786338453
    0x302011d0115142e0f0206071202070606090f1401060903080904051e04051513241b030e070b120f0c090604060e090a02090612090f0a03020d0806030a 66
    0x2080911600343c00078214560b200c00d041c402c04044070110a807007203812410024142c081d03001e040c3c0800c0b0603480e94800c1d640086a420310440d079a45841641030810305000e4001e5010050031601c02c0c6d520b0b0000704224000b445081c84809038040006510340941c4010102040141c0c006002c000c101103051002611800584000003404da4010466480e050741d81e81c003140c0001002c102c40c904440410051004c00503100319106400803601069840d1a0b0411070b20901510000e00300c0381511203402c01285620b0884a01c4058409001a04460080c1030018102c0e402c4036502c0029142c0c84401380120041c840c0d40000c2c4401d8081518090b0400700d524940c1e134bc003c0417111420300303000006141d540c035001140c4110b20000d1000e07a9898645001502500604074100e02a240e0b80c070020385480150310848210040092519041c080040300c0c0100762440108800344500400d003111a680200f08100c0c040d4134402d80141501c0880428000e040a100401c0240703e548040d0200c1c0110740144 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 786340935 1250 786339685 786339689
    0xf06031e0f0506211e0f0d02030a030f0b010c030c17040f0e0c03040f020904030c12110606030610090e031201030f120e0a140d02130204051915050a1206030302011d0115 74
    0x44149030400403054500707007001c071006c0c810030307944c02040d07074402c034450307001c0010500110a40c504118000b90680b0040480303031132203081408945618600c0300800c0c0a40c0b2144c40e078501c200b10a10301030b1098040d0811030740140e0f111b9030030084120700034080c0075503029209500041d41c0054905514145d200c00004940c2401c029004d402240301040c10b0510503d41490b82c04e03007082c0010b8a0340401c100050001d0105480c1301305501030b80d2302140081c41c01180d454015807008000300d101c50b040180000040031105200c3c03000e44410010314401e04c02d0440e1b00ca000710f001d03c90181d1050040c2c2054001c0404810950f0b0802c81070b00040802990b50b098400300b82d40c0040045084685044003248290413102c0e8065880b8008915064000c2c00300d800030300589000344c03000a66142134144138840b414490240c3e021020b081d1715150a150b00c40d1002e4001641d00d850310100900c0101c0440c4111160358000b42c4c0183d45032564001c690015019210f141c00101d002004610362400200c035041d6034038 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 786342185 1250 786340935 786340963
    0x20306010608060a0801060b1305220203190e030910020a0b1b040e040b010306110702130e0304050a1203031109090411061b010e06010b03010f06031e0f050621 70
    0x302c0041249511070100d0100a440d500c00204000c5031980b0183c03043c0e0308003004103140041c0980e004941801c041c02c1c0d2000381b1001c00e940c1403641e442e50008401a40000381001c011054880f8a866200113500900604400b035030041c2d59200008003d0008030308242c002c01d425940040411400201c03c015510b0b4030201013040006a120301842c030b801c144c03142e0382c454100c07015018140002d01c00700712640d5048a20984003000845c1c0c08510005041c06888000b039400389041c00940100070850704489411180c0300f040d0f030b14140d01d5000080c0c075120180c00c011349c00c0e0881002e21003055014450a805004000800c5050414080000310049030040c80100b0703080c5030003010880ca0300c8a10903251200903071040c0a401c030401c03c0c0520b00808401c080900d2601c100710001074108100c500300e0741614400e00c40e4814039820910b091380940039101a0b0038030040f1390103241d00c0d01d462502c60001c1c0d4414420000c07406080007401c101c0d002c80403154850041c64090480c03444c1e0140020008500d00d01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 786343435 1250 786342185 786342197
    0xf12200118260312241302090a0512123a05060603060a03060e0a080d140105150318070f0b09030f072103110102070c0515090d03081f0b0a0306120203060106 69
    0x7000e00505c158a081c00040707a003100c0c1000b02a0181803c0383c024004405090710310701610381e40d520400c404181032290441a0ba0015004030885012480082403804043e50700d0003803001c0740603001d141c3c4c40c9054803941c528400409659a480d060b0307008946d007005040f00c107076007141418000925581c045100041c02d01d40d9500310340b88180c40910076046c1543d00b0203006620340d0301c085125005005c5e0104500600d0105000204403854007481c00da20544d840c2044a042d50f4519003611806c1c1088428000c42c0d1144980008240700030042c1700002d4890305203c507859903c40d10070301d894030a401d84610043c2c1c11100c1e09000300522404c0f20341d0300c002640004d403201c002c6420141c030b60019104004540354000904a01402142c80300c034006c03500c05441c00d034451000100180c196019070058070f940402050321850110f4807a00e440c0e3341001d00c0d001d88030128241908000e2943c00c007035114010300b08003c03032484c01d410b401d441000b00601c2588000c10080300c140d8002502c1f22814015a000d00c80 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 786344685 1250 786343435 786343471
    0xd021c0512072f0f070f05061b1f0b060306010c110415090605030d08090d1d0310090b090703080d020c01020408030f03010f12200118260312 62
    0x441181d05040e1101501c4850100c0e205914050f00c10035101007001c2c4451040c51200019050b0002e0720a0484503512010506203080008104159010381151060210b10540614802a042c850100007503c2a0010303017400300d02101d0384064560749d00681784140010300c200149a40c103c6e0307040f210584c1c0a0385c25441d0185000c0010300400e5030b03840c00081050b40c0c290104141000e5881a4244c0707808408540a40e248000c00b15084d8804071004206a00855242d0100c3c601031035101004c62400c0f00421081e2901c8804a80b6012285034541181c5444100281c00e10803020f0240e5003103241a005040228110348400b00244202921540d00c5507000a01d1541d1810a5040e00e01401424044c1c9980300407404481c0e03102d0b0020f01a0311580d5004110008843c03041544103224581c0c414035a8503040c00c2c1403144800070003000c01d200d047c0300360108000c031440301504031003014000382d640c032980030b8891111910341c454040600c89181e6004100b00e0035401060030280e5031210030a050303058114 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 786345935 1250 786344685 786344687
    0x60105072a03060f052a07061415040b060a1d0a090203250c0c060507331a010e2103040906060f0305010501140d060302120d021c051207 60
    0x6048005840c981040341d00301008006068106140b5441c4c01c01d000e00c610f4484200708030005e17030f8960050403030140081c180484000c5800c0600700c403030300840000800300740061540340d420744125402805845089003603c240d00d417912551040f40380540b2aa802c0c00074188002d880000c0308440c120f520b600e1000c0c0d01c085651202004c1000e4540e0f000c0c01d40d12410800b50020019450b0040700030802c41011140720413510440085503c69044840466510b180403401c2c2c0342544000740a8480c11034049013802900d0703007148075410902c0350a00d5560030400c42c8680c4000c407014101d14103c80c054034a90454030780c2c0d2001c9064800c120803240114071031903403101c910040c02e030512003001502003c580001c0245035548040d0842d0b1598a1f424581282020110129407003402824041000010b2a0a4860403080a04084010302d940080c5041d1690005082d43c0300555038009250b20006041c407095034180115407040c43c0e10170070541d02481000001d4100d0050004c54a009814040014212 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 786347185 1250 786345935 786345983
    0x41401260a0207060207140607090e060d031d0a03050303100f03050a0311100504030f14070b0f15040204030c03020a0803070c1503180f05060912030402060d02071a090d0806010507 79
    0x250792090201f2000d0304c00700c004944405080b12902d002c0380300702c000020301c1100b40c203650384280c4c801040004800c00b195810703034074400c000d0300f5401200003082801105885042c00000914050b4008685030300d441c00d171004d10802d06400100817404004001c1000500020b06610043d51508022012512140420349412520010100780900b4030040c401419000f03c4070000107122591007080c0a8001200008140708102e4010710180013900003611144c1d4106503947c001c800c20a858800c050900001416608a0b4109440c00c4141c914104110b00e04034050400070a000c801030340c2045100c0d00d03090300e0b00f003840c49035000d0207800c11014148944241c3c8009801c491b00c000707080c9001034505043c1801000ca01c1e080f28141f1030354010030004d0130005007030305502d0790380030f200740c6140c2d00c560078052030b178014820300b030603240e024030182c00000e8030104a820690342c0810398848a10342103025030f251500d8907003440d09014a250034401c142c1d82c0041292680346c0c0000b400c0d03c921a503004241d0381 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 786348435 1250 786347185 786347197
    0x110a030507170109170c01050f04031205100503010f020405031006050303030a110f040602030901031113060e0a0b0a020a030e090601080601230a0e0310110a080714041401260a02070602 81
    0x40790302030440d010444021010380180181b52008000c241c0e541030140e02103400c207480c0640071800c003080c0c2c440040019041113074007032040c0840c403040d80c0da61f90209003582e842c00fa4040e1200d8000c2014061403c0800a000b544200000240005c601d0400071940320b100c003806101c0b105884844c09042c0e55011412100d414903119202e0b07a40707a50341c0707200948a4000e40100360001e0300f4601001c1e0700c51056800c0c0c40060481126584140f480c0000c1034600c034100c11040c41d0000660600065039000e6200645881f1455402030000e5410600d00140b0607030300c02c540c0034411360621040c0140d69a018130f40950059084c00e21800c414004018072040005141c1d000481a00c009036034214258010100c51b0349400550486200d04007040034001681c030300d00a070b1140a08180b08096502d446181c919420001d1420030344c0c0c0402c0c0784042e0451592050b000008901d000303901c01101035030b11800003034440310361401c084021061400c403004540f80103010280999008240101802250b45c100c0b28 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 786349685 1250 786348435 786348443
    0xb130b0703120c030e101e15081e0616020109020d05010213050a050303070204180515100617010b180418050c010807050a0f1b0f110a030507170109 65
    0x2444036403a1400400c01c44510314580811030406643c028118028000c03c2c540d0724130300e005007041c1042c0980c40001058080584642e103842454104041140b522602d0341070351071400445880d07806c0c507a9083c5094115044400800604a0320b071001d00b2001c81c10503040013100710b40c0c3c0300e08126024128090003801b140650300841007100c0c0800c10005500400c40e114141d0352a0b80c907541d40d0401c00900d060607205607600b5410401a60b40149080c1e44084403180050032001c00380700c2a0348403645451000f800c201c405203140303c00d01207042c85401030340f40207024501c0c3c00c0c15508030221115628044c18070032110002800302d14419510911740c840e94041d00c0c0035100300454600700404a19034564008207071158001c2120907246540300d410300d144101d142e074071103a2030001d080b4400c65170120440300d4402000752044414906209850b070340c1000302d00078240c0d000401000c2c00e110301800da204018600c02c3c4070011082000039008074038401140c503081d44a4000910160400f8003520071044014 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 786350935 1250 786349685 786349687
    0x10c18060c080405120708120c0a020609150705010207051009200310020a05030604060608162609030304020f01030b0a050904050102300106090311042310030201080f040308010b130b 80
    0x1070217a070000303204411200c0c03140444149171584806800e0304d11a4540261054204009030340160030680000c0c00d510380c015260700b018255a01c414000b81c0c00c01c03002281d099400064110500074100300446500c940c00c0c80401c001229940c0304000031040011844020381400164019aa414000f1240102244005554546041000500592040710294411498260040740b2a44a4400e103442100c412000d261184c032041c01c00e0f01c10400001d40c0c0120888142590500c1d03110b0307800d00a0103002c208004603101c2c24144100542e0109141c0c600c3d0400d0301d0241008825520000c000d011541300f69500411500c4a040c5203019200d100c5070b00361070f50301100401c04416a402e048500b056030400b9911256602c450041781c0800f5588030160100582141d4041c40d480d150b1322034521807040c0084800666440e40745444100030450b1009404410751200700b0540d42c00806059000703000d40b49aa11510706680c3c098851541030280b4013002c1e0011404800c3c3c40c140218080107455421007407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 786352185 1250 786350935 786350959
    0x1d01020301090915020703050a11030408011401030b06030c0907031128140909012304050703060504060608010b0307030b0307030c03120e0409030e0411070f0f05010c18060c080405 79
    0x182c01410300c180088070003090010490504084c07a10036550007942c15902c25181c01e031003941c225518042c07100760407c1030000300800210342030240705412408080e40c6400700b2542c50b5040c0031081c0c586c020003a601036081481e1038101c2d0ba54010b050380d4801241e041c0000d4440c04107641c00014003e0f41d09001d1101000000340381ca100c92503079200c012003001d903a512010f04c040b00110201e0b0060700c40c0b20fa04803e440380144964003012107015800250000403039891100c00c00040c0a071031080d504070300440d94941c400e0055041c140510b80c064200c2c1d04014906514200c3c0c00e81140c44014600420503a55480c84801c07540e0500105004641040310100346503120b00b484465204005e01d508045034840c8900e5003a0f003014020184c100d07030140c841d0700c0c00d08004d0080c0000360203c2841010012001c225550015003000942084140070b60007040a4088a00d0030b2421034840007020004e1010b0f80128524214942e80c403503050329254a0041201e16103494032401e10b0049030010703940000f902143c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 786353435 1250 786352185 786352199
    0xc070332270111120d0906050a06030516050102030d0902150307020309190803220b0d1e050f0a02070305160803070906090602031e041a0309060c03011202041d01020301 74
    0x30791103038160180311460712285500055030850b002040800c107940007103103609041c1d103c08000d0101d0110019011898041e5656079400b00da404a565040c0c0558440c0c0500600404001e00d00184002034076180910b41810000b0b90b40340103200304804a140c94406038021502d401d020480a40d040d032101c80d0b140d04000001a449803c1403929a004d079013810a600070708605d0290500c2181d400d0b0000d03614004a4118036403104141007141d07030b050055802c0010391901c90318001c20344000d0301440021400f152901688042ca2090412a24a07003410280f100c02112005082d0b003180f1840c0c40142d03613401c41d140a03240c50003842e43c100c0300342c2d02503000d1009003c1d2a000a5100d40c81568442c10465101c01c0d040d5011489030055400592003840101c00601d039094001110f07681601c6c040741480d55503400e400ca40c046035449620303070340c00c04414031603000003c003c10303074000010b05007890075503050030b031f00004150100b0740c042d20451f10798068004060754403c20021039031204000303540d250303183d00c0c2c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 786354685 1250 786353435 786353467
    0x3070c170712200306090a2a291b010e0703080d0b0103060503160810050103030c1101170901062603040e0c0f0c0c04050c070332 57
    0x204000d515454200124003010340800d440c02a615400b080c1ca002c0490380d1100034520b160381040400094040d0240c10513940c0401003144101045030040c15181042d280c00342c46289030700407151200b44280c003d841007001444124060700c80580300d059034414490078081000c41d2140c20303000c00c082e0000b1303c410441c0c803180041d80c0c040044002400305068840490382d468180d417001030040070050200641c05031858000c002c0418052402141c469240d0700020708182c80c150410b0402580345e00b04001640051180c080203401c0642c04000319851074034054015400003d005010500b22240794609038020214074080c6d440b880e619082615044c180540203100324014200b00486002104140020b115400d000c1e44d00340802460515244c40c1d144410701801900d40024040d040c005901e4214010300a010600c002070000c00c016601501480201d03413024010a01c10101003080e00d0100b60090280107020440f045a000c1c002c40d1049130980c81c001c0210248070140c0002a52000004509 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 786355935 1250 786354685 786354689
    0x9030d021812030319020d02040b120f09060705090d2111061f090b0406030206031f0f03082b4b020703020a0b090604030806040509030f03060d020303070c 68
    0x2581c03980d4a2009100b074a9070381d000450304404502c42d40700c6a20324008031034003c0e240c04a05402c003d41041d071030b0001c0c44450340004441c484c0300c0c1580d00c104505d12400d66000783d00300301e43c440a400b0314140f01c44001c00368454030312200d0245034002d484008006003145510100034103c601181708002d660700041402c12030320101421481410040740b220041180300324442d2645403107100d102c4c3d1612440f02c0c007801109030001d51180c2d44c1c403400030140e00d0340c100452003155407000c1c0719580c1028041c0c1c03048030482c58001568000041500340002038050040b104058410311110007914904881c44540c0c0c00c0d403007200202607050208501e41d100a0704600e5110038141c480440c1ba01c504800f00030000307207035880d5100d14201c0ca68003410554290350300821100b40a4415210388100c96141d01c074030401c040c0e4809540350310080c100014194812078107500408101c4042c405030801303101080d80c80c0070700301d03048101440010100f00b00d40d4132414040102c80c2c4c0502542e0301e40798103090030300b5444018 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 786357185 1250 786355935 786355939
    0x1407020f10020d090b1314040917210105010c110f1306080105060f10050c0114040b06040c0c051e0c030a03030c0f0903030c11010e130204060e0103050115050309030d0218 75
    0x10b000041241c101000c1a02c100452040d2641c43c1246000b4030400031f08a80404607810607a02c50061001c43e580040f0401545d5480314059925190b9444030030000c0342449804003100c80e08001801160ba101d010030000c160020481e500d540e503460b000966002a0031240c1c2d6020044500b240c1600c0d03059040340b0100c0d409a402088245c3d9110b050081041c0595076443d402101034808482e800c2c043d10241c1030652040300002001041d02045804694065800b6240455040c017008980e280900844100e940c040c909100070a5080d03903850345da8848000003080d0101c20800030b0302c072003000300012403100070010229480c83c10281000340042c1032041c001000244641d4480017134074011406401240d6051340c4240c04440c40d51039800080343c0c0200aa41000791700c1140701d0700e40c0d55001e5103903001401880d0042e500c2e4917205001d440602c1c0040c54034189810a0010131101c0360400314280007082e103040966481d0f41e0b1030042c600707611414400041c228030200340400d258034003e071400150501 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 786358435 1250 786357185 786357197
    0x2030d0e010e0d020c0a05031609020c030c070306090204050a0b0a170f10050106023d1e0b0112090b13020301090f0f1506141912030c1a06011407020f10020d 69
    0x101c1060684032784161b0107400a4000c4a2002c000d01e81099000b09039014008013600c0c03d2188421209080c0281e942c02a5405c0b925000c6000942c5020310030036400c421a4002040500102404a145d40c42144140b414039020402000380c182c2080c0545041c0c0b132001c4064621202c00d0030160b000402080c001d200040c030511000003100d05000300584803007540764183c4280c0c552219199aa08843c0400c40282d0545648100c8a10f40c00a2000c100f5601807030f00116403080e00e0702c0010110034004200c2d0030800d04180b448000304041c0c0000742d03080101081468002410360000c45e0143c40281002030185052070800000e000010101000c02d610841c1120030b007c208038103500a0b00e000d40681c00c545141002e42558518041c075449070301d4201d00700042c004580d00c200080240c800200160080b5050114040c100708200712a00085444501c1103043ca043c080c3c002070942c519500543c000d0600094810190359031000e0054038000c000b000c40601c42c1000000a440360f220b20031401c0410300b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 786359685 1250 786358435 786358439
    0x1c06050a0c14031603090b010e0a11190809010b0a15030b0f130902011107060f0201271b050d0804080609010b09070c0f0b01062007050102030d0e010e0d020c0a 70
    0x442102c00c007900084608074203046440e0080d114024401c051501400d1542c0d484541000402c0b128500e8020440c80e051000c4500d442c8a00c3c105845290000f640181401c0110100d180e0a04065244000b010f2a00c080e450f81d40022650040c0700154441d64411044100000c65407018008204c100006540500c119807040b028424015101c03c211540001c090600c0d000c521a0381d485400c40500500d400c280c101d02c080b920030308140c1d4a401c00400264094401420660240140c4007401d500000448030341d189081c04400845000c0b0703000b007401c0034031801c1c41080083c03c103960001d0a0018000f028403142450000742c140d11a200e100c5081c052000050780c1a00c061140713250041000d070010700c03203a54010040712208039040d81147e9012000702500c021a00720030300c56010302040d803201c203100e4a0981310791014449007102500c03143e01c803250603c400d9074080706450b804882c203400480c00c0003660000300d0160102044140d0307184a081c082100c0164000f400307000d400b00503110a80700e90307 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 786360935 1250 786359685 786359687
    0x9021305011208090f0915210319050c16060f03050402090606031b04080705090129300a051f0e04020111060702030c24060d021c06050a0c 61
    0x903001d109000400341d50701c007020045000d00c0010980b206008142000000180b000103030b0900c0705403205021203030282c1288909051206114140a41e241501004a8641100345503207114488140300961100410301c41420f01a1054a1702d4041c5582601c041c2c07134603103000151140080c8121000150b22800c01b001680c041d104144c0121340140c1503506581d15841405800c1c0e20241452241c60007002c039070602000c601c00030b08003500301e00007c3c0c81c03014504800c00200d0741c01a0012003030340743c11041110041c0c044401556a18842d1100951555004200460701c82100d0380070352074842600120a2820000c0c2e0b14440c80f070301900c04100b042d911503e40c9184000068100364088404c51384042c448010302c1460594490f105141c120841d401414140d0305010056801102691001c0703440101e819060008040c1142c4000c25490303c50301c00705041c0f030001c01c0900b075540150141c01e034500030354a42001c004480902c20003014600d54452a094005101c122110102c142c60501d03950701007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 786362185 1250 786360935 786360941
    0x30e04020438041706070e010206071d1e01030507022406061e040305010b01020303060d08030601020f03031302010315030804030b09100606200a03140703120f090213 73
    0x60b800c006420301c48005585035903121500c0d801860300509194010424403900c40704000c00241c0380300e035045007142c0c4c410000603160800140082007400138002d1030341c49590340004c0003a80001e030b929000c910381e05d1028081c1c42c086d92285603142c01c40300400200540749483d40710000c1e41e8000b80d07020802035490b5203049850b00c211076444181044040e00007210b01e132002c01403d80141c1d00402e40f078648003603500b40d860300001c50803400c0d4240e000420f040003441401c1c8030743d801810080c00a1441c600c1c205002a00031100c80500400c0000c0220102d00c560f4400c001c3c50206403141c0b011260703281130500b040306250404100483c0000c1c1413a02c40030703850b5903030054001125444074205082c14210b030b403103a601500003000cfc03055078400c204503503600c3c6026010301001043c1545580750180d580e01c0b140500e520301441043d10ba5801000c0341d034002588401c20008010b541444546c072181640f801712214a0343e01d0348001045d08004030b01c1a15a450744c840a00584201c0f4902c40c0c01d14501c0d082e1003a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 786363435 1250 786362185 786362189
    0xa08090607211a0607062004030b0105040507031506081927022205010f050f1011010204030507080f06010608150f040e06130c14030307140109020a03030507030e040204 74
    0x6800700340d21204242c68164021002907284080405000309a14010603495008424161061600d9000f02102880c080007240c1141041868061a040c15034603561038014062003183d000d25603ca0005002e244240e0000ba41104407101b8155182c4d912140201041402d8420458128880c1d4000e40c3c0c0700510311488114414200c00f030b0b2500c800e000c0c102510010b01341c5059070440159480c0c41442142e485c01100900c0482000084950420341c282c940b002031034011500030759550101d200141d03901c6504414400051900c944070107170001c1224060701480e44014070a114142e00407500709030101f518a005400c040031035070241e80e2840100c0c1d01100955000113800107440429a0a082880c128aa41c1e007000c0c00100381e030841141542d260060885001494404281980e400c012154103284010004188011310921070940029100d01c5031310001041c0c100ca000d5249407202083d00913180c0035400810001519940e81400382503a030203c6811000155032801030b0003103280610035101 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 786364685 1250 786363435 786363467
    0x50a0b0f0315130b28050904050a0f1a0a0b131109060721020705102607031a0906010212091203040e0a1b08070309050c040507170c09060306090406060b0a08090607 72
    0x140e01c0d142c1702c203200547c207018005880a0190281403008280055904074442c2d2144003200d00700003c0d29901104484040c04400d000c50601880c101280c1e01d2074800c25003280419800142088880702d041d800b4400c1c3c010407a080180031030240d003480080c194000c62030401925030812040341c05400c9032150410300400c3d80c00b184040e00b407050617200e50a04540e4450b01c1e80340303124400100201c2c1c2d001d001c0c1160721f480040d03213692031034140d107440300201401d003074007601c0a41180c00d0090021751943c41102c52480a664042090407141d561a16403028015501c4140ca98598031600d1441020404540c5100400d040c0704044500400c884c0e20890038503000d5890321391546644400b100a0800403d0680b828403400006407080d40c3c5912401e03002e2800d544030408040900c83d0760924110000b004042d051074107018651094072280c00302c0e9030002d001c82e4405c400d41e541d0329106000700426004003076010800300d8280c038540d8010a08030b000700d035201c00320391750f50f51041c1044400d201503440d141d07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 786365935 1250 786364685 786364759
    0xb04050105090c0c010902040207060e0c04050c040b07020f0d1a13020f130b03060f06011416020103020702030708060f1b19081512030a09050a0b0f0315130b 69
    0x3c0650400e440500000c401d43d0340003061000b021340008059801207501a600385564130034030355406804000350410a01d05031030074000361801c89600049070250744144501c907180000d2400465540c100d21081c10324008260740300c0d1a07950304000700c020300c50302d054480c850742170008180f288501099108403140d0003403c1d4100c007030302e220922076074800700201140741545402040c40a90f40c203002052245100745040c40c0c5030b280180005200c3c17009403407003031054602084410b41241c0d5000f0b0b42104c0c0d64080c200965592440d00c00319103001c0e042d50005280b4000c3d402844400d047c0000d02038000d600c1e50001001818102d0400c400c1ca00c0740c0c411130490460205032400001380121000b5030312211021441061520b100040381c1d880c514200c00c000382d504002103007800d444d0001d4030136000c1d0000351540380c4158140803420300e6500c603092400b000c4010100000340407805c103010103400030340701134813100e02d100b41d01e8011809000c1e00309000c6c0c42112000c0e542d140c603d034115040c0e2203441143c0301d14 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 786367185 1250 786365935 786365941
    0x17061b0408031804091e060b0123070201053f090c010819061409010609050607060908130b07060501050427050f0f0717031309050709031203060303030b0405010509 72
    0x280c803080032500480313a005070310b801c0070f40042988260a5004d146942c41c60001001343e51a20000721103451040c5814080401c121a808548040e068032204500c0e49445a031108540010794003802124584482040e00d181c040d9034078014000c489000c07202c0041d001c00c80305000041c07004128821078181c00f943d8807034021010310798865040280c02c10104602e500042c1a894020015203049400000c0c098402c07611042181c1000038040f0300501581c030f0a00001c6041400085140c072034003c0c05030000c2d8032503000000740282c2c0021202e4001c044108140c40c680e070707140440c84c070340c10074402a90442c0ca03040000807a41024042c1000760000b440c2910f4410a071041c0141c22110010070580740ca102d01011823074a0304040007248d02030b07a0540000d04644c2c1c40c180400340b005e61584c0e1880c0c446d81060250b00001c031404200ca0046d40c501c943d000c1440d9550003421600d500342a031010b04401d0400c3d26880764240c1643c0001c0a0700e0103550280040e000036824881921800e22a8030341180d209800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 786368435 1250 786367185 786367207
    0x503210a021c090201030603020a06260115080c2106040c0806030d03200406051209070302091602190303051006020a2a031502210702100c050417061b040803 69
    0xc24001c0f81d205040000e900c81c3c494010481110b600e4104902090300d64a460718552100c82140c036640c02a40313a5071900b581410306540d41c42e080e6003c51420311800101268004c8001070685088185495030020074030760b200fa20900002e07003a6405405203190985400105100f0302660740701d00805801451843d040c40307000c80041082e040c003c0700101d03000c0020781d42840c8800060005282d21b03075130107484501d8494143c41e09000603003440840d900c00e40007000180c460100325540700092501c120707040c654010040e030421490318044403409182035440400c054040e1f0050380641d03c0c051452196070340f6117400307030f98a89142d031010b000f903480340b0b628400410071138606001202e6180348202e0003030754079540c840030b10755491001c05481e0b4000c50700702035000d0750000e18100d80b100b400301e07501c040c1000d00c4043c0d2214038010340e0500351a21180e4601d01680924100c4000b024684c003000c0b4401c91200d034254407180b05485402030f111a02d1510800c000220066806072034039803015510f00041504 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 786369685 1250 786368435 786368441
    0x3160807050f12063c0a05100c03120b01020a080307020309031608150c0d0f0b03030f0d11030907060809190302010203040512042603070503210a021c 66
    0x48404100038040007010344003804040a00003e01510500b407079681031400400c00034001400802004549031080d411480c04003490200035107100501020712030889030042038114019800c4580c0011070f800124040030390040c044040180a5511070100c00307400c0f40248280c0b10316103160b80c016030000d08404080b0300d0610046801c8a81401200e14014451002c6414040d00d241410000070340b2100800003a401400320283c1c3c0e414004204c5c040f40350802002c80c0e80c4c0a192440221182c3e00da11084900c01c85501559040c14001c3c100c9456445012740300f40d85030300c0154240103090610148105281043d01683c0c014030030340340030702079a0341410b03c21508040d0080841b545485044403618070303840300f46440b144842c065400580d0f0391615040092600038000c100c0150b04204002c1086219440d078503405488902840422101d6440340c042865800b030f02c000071f01180000a4001d41c1400c0610950300410118200d0807150b9a03820120030072402a5115100800304d6122800400300050b8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 786370935 1250 786369685 786369691
    0x5090f0a080a1a01060e2b030915030c0c291801060b0906090904170d0606030e1b040207030e120717011802010c030c0c2607030f0204090c0e0903031803031608 70
    0x1f448055007610880402555000200c0a0b40815011401071141d090b440c9803403503145a031030802384040c10682400400500d41c0344009040c207400c1403090116984100500301550b40c0c4508520440d0400c011482080101b00075104055845c0090028584000c102560b418001c010000341c00c242d02a8180308507100c005008861445124a80f400710482c91030180617062a031141c00184e00d030038036274081c0031a0444144051150f02294003540b4940800003148e115110649000d620fa60705440c00344d5034200460182036200b0741f100265401e41d40c0000c0c0c481d086030103084480c10200445800ca03800c0341e9600031700b01c881500b11a01180594042d450710b0a41c2440380c6800031106005495541c003184698200100900c542291074003054254030305174008200312005050903e1460b92400d0032040d82c88030090045443d92020010300400000b264002d08452aa03920f05140c800c0704113441e0360040381d50040d40d0781912904182910001300f030740d11800b29510401c518a41801b01603a0b104001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 786372185 1250 786370935 786370969
    0x114040209031002032d16140408190c0e10050f011209111e03151506040602010506031e1509030d06030b161e05090f0a080a1a01060e 59
    0x2140c4400300903c180f000b9442060240e00c0e0061a8044a041611062a020029031012001010720150352141d0420094441c00c50420400141c40e98207040b9680c007456000310058040c44504002104191405042407442401400724079600d03400040320400d4140c60306021100360010034000c60400c28901d8000c40d07014100030340e915850840c00802d68a840b0011200b0255034098003001d030815200c4801c044030880040e005445241001c80d42d039120494141c80042101008942c228543d03079200303c042c000140034075940384d40f12030f0081c2c080e100945005019100391941a40d4141c60030841e26070442c41800076000c10102d203140341c0b0b800c1a006d030010324140010003400c600c440c01c80c8a428000e500c100d0040d0392503d0a68a580700c2d540c00e203046141840810240600030041c40500201d44584038141a500d5031142c50116000454500b45980c001c0c21400d404190f0340000504001c00b14424020f04600c038040038017481c4044828030481c004104d406070108143c0c60184000d00c00c01d100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 786373435 1250 786372185 786372193
    0x3070f050c0a020907031d010c05070605040c03050f03041502070b07060e121b011b08010e0405071d0a1a030309010e041503080406020f0105101511010f0501060f08011404020903 78
    0x1003070300003840c4103000b45c3d0a4800300e40c0c5c2e0800d6401e100020a5880806100c050007002060b460031806041d510070440000d108a60f98000141041003030000d8802441d00501120407031004014100d43c2d80c0e00500895001180081e00340c280d1910001d040c9040d608040360796818204030303596180c06490010000860350040300003802d02c158070040034200d000107101c113518828805222147c04c551100c04103c0d02d210b810100d030340b10300b600160058115549446040c00ca81da403424641d00741400e540000410360000c20740f0702da0781c0b07105002d518001c1c400204d04000d08040d400d00420150140c41c807058054000303209008031507004a00f030f0b064504012b0808681c0ea0010fa00d80b4064070350301d800c02c440e02400442c091110076810000d42d00803038051002007105060502e540100d0f00114070030390700742614000341048190704c115001084c0c81c00000003070100c007003108048400741001b40200c00010b040c5c4201c80c5201d600c030302080c40c100e0310070b100001c404001840511019602c55540b00d501882 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 786374685 1250 786373435 786373453
    0x60509030903010f231003140a0b1501090e060d080a020a02060f070309170613080d02030f060f0a0605030c07031e0c030311030408030708150a030507090c0503070f050c 74
    0x50a00a0350b40d41080300000040c00801c605170504140d15295114203080c0b100803c01c0703081d91481107001d080c0c98204035001d00780f9600c101c1c10761809d521540b00500310000c00051010714804107000e4510741c003003601c4010035180c46105d92050f0117001c540290703001454402030400300d00040c0041a55403104d02c10f64003850708035000318440d80c5c00440940700f0341c000040d464003490307403040302100680580d0f0f003540d21264a4400f0565651405040c41d134184814000c032a0420904104441c004d0000900c29500c03031070441c1c0030410f078040c02c4800701c2c0100f0607800c0001c070074940708400b1000d5070003540326a421341d15881408425a000350008030103105980000f001d05403039660303400116031000d90340c00c6250402c0f8500202603418010380c00384120010b00500c80080c1c100c8058990001440ca016001a03465540c0e540300740c6600358049030031020244001c000d024011600b0000c0c0e41a2660500c00c9000300f50084505100443c1e0980010300ca1088040100d403140005000031300501c0300b114565a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 786375935 1250 786374685 786374689
    0x30f0e120312090106120c1401030b0d0506060f0906010c2a081c02031303060519061409101406070602040306060905090d03062702040b030103030507020a08190605090309 75
    0x6400380e401c0c0d1902c8042d410800040310340901a1002070074454031140d96000c501d544009442150340220804190040f407aa240d41c4d110b540b010f030000c0750041403002c7d8000c0078280303a61920170580c1c44c94060050001c0350700c101d04190038a03e006900680d510300c080c071400d4032160042611103072161181303030314020308a40411417111108007030004500500140c09904596100038420301c00c81d402550002d001307004400700c080d401c031011aa0818401b00e495039030b07052503201003080e03e40548451407420601041440c013217000101842001c0e6a007a04030345402901c912144928812007902c3c00388460030010741d041c024040c100e014031071600541010745a035192004d8940301e4000c1c0385000c0e40c4904102d07011004001e40c803000d040508040024070b0a020500c46902100c8400c040561401400c001c41e0320303401d50441c2c00178548023041c0b503160f503143d02e002451607024100c144d1003002110700211f080c000c0031500d041403c0340a524903150134100e41e61400900030080400b901e5002c1032105070361603 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 786377185 1250 786375935 786375937
    0x316032a0b070803071823030a020a09061406040e01092a02010c09060315140a03061a120d0207090c0c020d120915210b10030b0a0e04030f0e1203 64
    0x2d070301ca0500345440346030800c0000c154190410300d00c09000500d2070200300030032804d5070807442400c402c20680d80102c04840421300d81480039000a4102c110441e0000b68002c06078010829201400e4060b942e50086108020050059018202c401038002c001048a02e01a500c03015a0300a0401c200312035140729150045048904445040036075159a1400c1e00305a100110001418903414108482c030040700e4031924400f5140240c4652545500001e06107548440c1e0700001140d102074244100d13035100b0840003101068070403040c00743c110035110750020800820918070344005980100320052030f10481001402c012a610001c0c4014840c080001d600e17405c0980309424000c0501800300400c052000b01b2000c000c0d800309440d001c10741906a2850340c0310500c071075208403540d0136400c804550000e82e0010400340c40d500f5405001b0399000c02480d80c240d0000e95030420101c0c2d212940c213035150440002404215001000500140d19210300140140a0001c8040d0081c007002c01851051403940d240d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 786378435 1250 786377185 786377197
    0xc0c09060501170c1204030e1005091504030b040305030402010509040c03050708090d0c030809100c08150312030123040f090c0801060803040b0a02030f0403110316032a0b 75
    0x95551220014012940c01140c0c50a0046060007901c2241c0340039100380d20b6900954034014541807400e0007040034148503407451580000d00404480d10a046148040c0c03190740100702c2c0c1c07400740c0a00038a101c941003440060750100c80e003000304900584e50340e07581264168030082c0100d060210610104180761203038420f000010810f40c0f80010181001e08014140500c020210000c41e8424020304000c02da11803c40302d410b6034503040c000466182d04c03196500f48000302041d078100f075241c00590024103a20840c03c50180188245400304c0e2030054044c5910f485040840c0041c1d09020030040001110101c1c4e40c40c031100c0a800100002d24801c0c0005080d25903491100c4241515000900c060124400f00c840051100c030000304400b51801c1d00c41c1c1e0300d81c0140c0c81241400c040100d20800598000d1044828620050801c50b941700c0e10307483c141c5180310104500900902c43e2094a403a401840c10b020b40c05c0d26000106030118818042c0e40782044003409042c6421645490f0000a5541c1d1410191070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 786379685 1250 786378435 786378449
    0xb120604171308030d020c150412050a03140901050615070c05010e0f0a09050601090504020909070e03030714150705131401090906030c1a0f031f12140f0a021e010c0c 73
    0x7c1e036800307400d007050301d40040d89140f86800c045010602000440708540481c444200c0e041c520707115115650250010b01c80c0c04011180466a03004100c45c41c0410340c0200d1007480704031680c04285e541c1528001940c02001c40c000c1490040300c60600141d07008503080d0b266403400400085250b038403080421000c1120b0740c03011540940310010700c41d241d80c0080074140600405e0351308506000b0508000f074514140a06400144014101416905e071003d00c12288101d4202c0106061170207000b102555600c1c5850b5000c044c542403d0128004a01c1141260490704540550307040d135030304000c1c1920310034110b240502c0c10b0106404001a8095860240b400214024000d8001e81071802d1001c0b06058074420110700504000c10500e0030507500f02064039082005c0c01b12a144804140d00d4140182009402c48880300080620200c2001303490017141405013054002c0d51580c1d1118408540d5170304407088020350201c400e8403c0a41c07028462100c0c0781100d41450011580070712903d410b5031660b01608102 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 786380935 1250 786379685 786379687
    0x13120206010f060f21110c030405090708091b01121404120306051e0607080d3e070c051c0b0903040e0c0702010903050f010b120604171308030d02 64
    0x301c0202c2402800600560804c4040c0700c541810051440c0030656280d6911600032000c01d100c0c2d1419403060982a05988070302d65940c280000c0269603402c1480354900c52940080000d40c20361140e041e4a00580301e44005224007915407045180020b02d040c50141048007081c0d01c03111044541c05003446c0310b0f0101e4903550a505250400d510402026600340c07050504040003000306841c1c103038401d64140003580242005000607000105184605400508500c4000c500542009000d5001c050000f03021030019405640c5001d000114020084800484821070707040001c00e100c07003000500e84241304071f40c1d40e1400d03502c80000070301c807004103010326512090945580041000b00009039400c00c03d0400214142490203100c81c0340c0c2e0b680101095240b01020450404590154001c0c0025540c440282d40450b955a20140d0003001c00c0c40c0e442c2d2003007021440c05158000d0100d8801d0150b074016214896072012a6804110340c2d00070660b40360202400c000018803041c0900180000b690740c1c0b031001d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 786382185 1250 786380935 786380939
    0x6030403120b0901090b0f12031209120d061404050f06120a0c0807030b07051806070302101e1a033003091b121f0603080c03040303032405091312020601 67
    0x10010307420b540001f580c050035424500141b0ba501c000103a0b080b0f801002d021220b0390ba03840c0c5485091100c0c0680c3d44100c9140405d02d082c40100070b8000b40142e403006464045241c0745281003106994043d40c09680614078200403c8013410118042c0d1603d40d441c03c100c07850390109684003c404132090784848215005400107200704116681c855800010514000e428110011415012812401c015a1254400040d40e0041500a2069100e1103a01a1040000203180088a5892130070403505561242c5400d004101d0717025820401e010031358010740181600008010006040c81d15282c41d400c611103123545507816800c001c2e0045100e02d0000024003601541d14a20f005080d0740400c04c580704610b4038803030014140c00002e9540e030010310750780550107030484100090020009604003500504000414000f044400402001282c1c0302c1e81c0c041140c008c4552149402c0180c0000341106074400e600c00300301e5071404a1a03d41c00c4032a0754005418801c0690302c100c40f40c02c260003070b200581c01407001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 786383435 1250 786382185 786382189
    0x3060b070f02090c07050d05132d050402040b12041b090209100c02010c150e01090501140f13060e01020d09050c0103050702030a022121040605070e06030403120b0901090b 75
    0x100e500100083e032485d04014095481584503100f841100701040380110301c8191210031646088000c210160a0541c8032944485482e5241600090707014800c48040000416090138800c5030116200e0500305401c10043c084a0444000094030543c7c00078883d0144060f80521244101c0081c04034000060362450305a051202c3da500140c458002c2c800e00c40c0700300c40541d81089409aa00d98854000300c0600d22407030040c0014500d2030de000b83c0d250310704400002040015030004c000c80011244d100c90503910300a102a10726811210030300c1848003518904002a0780341c00035029002100000750411800c140e801007120f072075500942d07159111180741149542c01d88070301c80e042040c0307201852821040706000f80d5501c080700c001c14540c660031545072000c440c10300c2c00e407010f07280c810103042812510420844503010043d46c007901e1061820002c81c010305e0050103913001012018200c10300315961031302d05441404100803441c0c50f56407075500f6041c680c0d071180b10f840d01801141c0800991420701c007007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 786384685 1250 786383435 786383449
    0x20d060c120f0b0a150309120f02060a020301300f060f0b010806011d030715090602060709030f0308041104050f071101020309062706042f1f03060b070f02 68
    0x42d411000500d407400301ca6082e11104489000d60b01010440b0003241000c5000303c0040c031000401802100c1118140904c0caa031001d4007000ca82d07000c0c3e08035422600e960b29060201c1c40284500e900f91100700c0b220015100824030030303c0b8175841c02101400c20b4591504c40c0c0703806009080c0100e50080d901c43d00340743d40c0b100c10f09c908902101c0a181425681c41d1035000600755010114910983c402d01e10502d00c4155030800101c1c1c017410390002c1c82031040501c03000c040c040718070780d0184c4005401054005131000e442400580300b01c03508204890f0420400351002ea8600f40060020380d5001c40724100415940c4441c0141c0303010762a1010000003030b180074040103200c0c00610103500003990042040c000b1520300040e003c0c1e0080740003542e040c500d004041d400450606110503000c45406800304000601003030845400380c101e030100d200f0051a8880103484542009100d800d644a90942480010199569550314030115113040008500b0344070380c502d04581d04801011594102d40c00445011410204 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 786385935 1250 786384685 786384701
    0x806040218040f0233092e12060801090c180c0905090601020f06250c0b150f0301020f21010b0a120902040e060402030d02030a090e04020d060c12 64
    0x116903124145683c8001440d441050083e10400071400c07a80742d800103c00c0400c0c410314014420070104000b202c001d48554000300b03d6648200748943d00c00f410603146064109802c1c3e5a01200c03202103041c0c20b01601c0d840f074070704c410700d440950711000403449101c24410580000c1c01001201003c83c0740000760605c4101c0b40040d5030040e81000c280c0341c5156000000101070b510101c4211242c0e40d54040100c2c0740c66080340241c0f00c41c0c4520300070300042190404800880e44207101e114003503403014030030503035080b041c07000e008241001c1d0700b00203038480d4100d0350350b52802c6600900c0c2581203c6c44600086c01d80e080702544500213000021210344465000d02c4040300035071407004800b9150300d846500c0708140219503802051091040800c04140a6070b4404d50b5160341c02130041080705e40c03048807181d580c4002c0350100c1c040c1c4a80c100c2d14843d180000b00342d805c40180c4d41c0c0c8805402d811b1001c5000f511101a0049070030040000c29000000c5150148046401c51580c0c1c3d2805002a440010305a030b40349 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 786387185 1250 786385935 786385969
    0x305160812180423100909020108040b09150a06080609010506010c0b1009060b0403052b03090201020a0b0a140c0a05030105060f270102010c0201060f0509040c030c08060402 76
    0x40806404403150400603241d5001c0d000d0030b4144080c1c11100801c0141240d41a0a10880c1015601000c12440d1505440c00b41c100301003112800c42d21101d00c6011035980850281c041565440050001906021801e034000e01c00c0c02500d0190000700328040100c6400d440e05440f844c2c58400503c00f81004200720f541c040740c0324000380141d0502d20b0028021411901003e440b1114440c00a40800361283e1304038001c04600c141040741558a50300c240d181e0b009070104885038094540c1114503c10491030401d0304a04200c010f614940b00e0180540c0108980541241507001d0b00d02980e02181c14020818403601c41c403800801c48040404c001c1c0c0001d071000b00640004441801440006035111007680c0c1960000d49603507a41d0400380001410501504846405400c40c401092401600020504d00d00c800203070001e1000d5074a2030016800c0c1c81080c010150803800e0781e0700c00c004a10706008801c0d0041c0c040c601000b03050343c49880f00802c0c204207410036541540310900303002c111304090300005c85100034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 786388435 1250 786387185 786387193
    0xc141309031d041e0518030c07050a080d0819060308030c0301080c0a08030d0c09240305010504020c0619020f040909031202180904030302090301240f030c03030810090603051608 78
    0x210b9110510200c0b400019402400d45d104001480002c0700034071300c9503008506084a850f03606044005907070311303c3e9001d0f0700c0c0115001000007030844000200c14080010545410903e07689608200d20252200d50b1070f02091610781c42d0000208144000442c0102180030303002e6543c0d070620310b40d5454550550600d501803030800104124840703005c41070b182405c9548a000c1281c038000403049800c051607410511144180e041816901134015041d1020101141c80c2801203031f903100200700890041c42303082230b5140c02c10b80c0050603880041c4030100900348010001404c0000502401a0f00c0d08150002c4600030b5a50203040140b6421a0703000614420380001985001218600d40b83c030000c00340f10301d0b0700440e030000208040500940542d01c0000b0080c000300b100d0009400d55202e13545400040014080902c1c2003c0b90104000351080152900300c2961101c140ca1503500f02c514910081c581d080b010180e10340850324000c140a404001d42c0120000c00c01c20200e10b07a50000c56120790b00c4010b190384 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 786389685 1250 786388435 786388451
    0xf0c0406020d0503090703150203041103030906090f04060902030f0a0f0209011d0a080115290f0f0d020403030801151e0c0c090e010c021204030c141309031d04 70
    0x81d00040004049140703150094580c0c8030007000502e060120340005200301e07000350341625240e0440c0d015521550244101e401307100c4401d0185038032813113403040a5030071640410644015041c4800110200e0002034800900d9664446601c0126081902c08407021020b041c01d0010f0302c45503004281d0031984800007189071041c1e6000191092402484505031091900c07610103590b500c0500202c020306912000380410749070040350551003000c501442c030070300e45102405501c0000c1810304004142d4100c00c500d241141d881700041e05d50f04012101c040074031040003440305075003180c000740c0011446038850450300d50504a10040e10401414014104403055075905404520030303150402ea094282402e40380200d0b02d0410002854841c3c0003005045c3c180058590701e07400541c00500d103000c060742600c0240f0740f4500c50311802c6c801c921020b0500c3c40c04440c1881104102d5590b20045a80280000781d15801e016082064130311600c4194007050b528a0745001c00751071807640f1341c00100102c0c3c0410807d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 786390935 1250 786389685 786389687
    0x201090c0602281505070e190f03140307051c030b040e0c09090c040207111807050a0f1e030f0e0c0a0b09191401020114060d0f050102130e0f0c0406 65
    0x1241110201104640d031282100380844c50700da4884404500e80c0c184014038018a010f00b003240c00c1c00000b0b0040681024085803408254804c20540e846c9103295500c55240d030b22105e03402a079501c030f41d846a0004001d0780c0e00182041001c9104c250700c4500c1c2c6550000905800350464441903642c90280c1d0a00440c80c400100100e084081200100d0700c4001c03d03254294a6480e00966045480d001031000a1a83c140902c0804c021803103401228283c880c10b5040302c54540000040d1101004150240000bd070124025144a0810a01d03403500c1d00001407803441c600c0c400d883d0405a080070a0340d803020403100320668041c00590b050b40b00c0041540c2e80c50100820700f410340c544140010303418003291080341c5542e41030741160665402c1030740040c030301d40b5a240c1485007114004854095841e0201d020203c40b030303220120303100d0034004000d40700d265910344402c90300d240358210843e4255420003091480104180020300504110105e600d918a070003045248801c074060001810640d040c00204203607 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 786392185 1250 786390935 786390973
    0x150f0e0c04051c06180807020f06070203070e1302091611070b04180b090106050d0b0904030c0201080402040f06080d03060b0c070303050711130c0e010c0c260d0201090c0602 76
    0x41c00b1240410540c0c00ca00d040010040006520000203840006100300c207201045007d4007005000311002d200305d03491481000054400c0d000001d425801c589801c101c10307c0f0300c0c41007940c024201b80c0700c48400481da03800501604800c071a03001c00101c000598500c900c0c0d2080d400d5a1028071200100b040608012000000d03014030301c68a80c2500c0400ca2004e4429095000074800c0d91014101101e40d50316440d000d0095001041c014080501e0441102d05900e040380980713000e2900354a644c03c031203119400444024500034826a0456100c8085608080c550701c18040101080405000a161260030080640d60030707a000e0103c4280c03c0c0710402e41ca160104a10044030b92500302140c1c0c5051074600b240101d144c106942c0d50249212411a4542a0315088095003a480796030720020390881700015035103004049009890100862028030801111002c5032101800c0c200303842480b0700203808142c1c40c0c40030004c030800050351aaa5400c04020710b5050070300c0601600e0010b0107100703800401c05004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 786393435 1250 786392185 786392209
    0x1c05100b0f18040c03090302101503080901020a020315070f050f09060304050a12020607030e0d090603050a091b030209071403042d0b0f0c0a080402090703150f0e0c0405 74
    0x15050000076140804910b04500b00d101e05000350040c00100da205070042d00401d40818140d001d402500b55a03804c800d501e106040410002500d4a0f40450464a4440d6550800d015060562044610140140e90308015003c1d05000f90100101ca030310b0000d20041c1001c41c1081e032002400341c24008800f40c000c080054400102c425503c4603240e40da1414800d18040040c00003516034070046c0004088664046440c0b8442c901c15207050050510400e100703507540c00450720480004075510b10a1118910a8001a4114200c600c01003880582d949942c00d40000886000004c150301282c20400c50612800b0503901c00810300307001c418100880508a26132000070700080c81d149040c02c1d103459040c9500c1c040701d076034280070070941d08114191400c04800e20043d80d440050740d5180d8001901c1e5140507003102c2d00e0700025920503c15403500d80c03d000e205e0070090010010315884180ca03202c114000c3e01a40f0081100c003074620000c1d49840c04840d03082902506100550704100428800fa469211620709 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 786394685 1250 786393435 786393457
    0x10201020c0c0f030a0f031101150305030d09170c070509100e0f0a02070c0e06030c031209040515090f0f0a05160f0201110a02030403020111030a08010e07050705031c05100b 76
    0x4801d40c0c0510020b800c11600b03d4000f0900140b01800c0346c05d050f0b20511190820021100803c0401581a00304491003490b2000a0041d401003002e503404a903940c00c00769006104100080040d0340801c0070400e07640280b50200560b03401031a041100e490061000b90300113400b0081c542440d404c0c6601e010090030002c1c00c4040000301c0300085940c25900b541201c0d40b00b40c110700b00d404e1007604e40000100da40e00c20b49115110f8403d02c030141002e031401103003c0c40503c48200c201c5250000240c1480081c00004000341e18500111502040f1611003803940c6110703a180903490320451070301d08900c001020020303222030b2501d4036080030040030b80f0760000300345250b00c50b50410a11006040508034090220140040404e40000c10101d8038150008007900c1540d100b62542d103181514001c0e0b807503480c0280b454090010307661000400902d2203c0c01c01c40d8002d05a4a0814600055519120702d181d01c0311566049070103003a07410b0780f91051248160360b00407140d8180b918202b4a404c0452006008080d1010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 786395935 1250 786394685 786394699
    0x1109030c0603061c05150f010512060f01060f0e10050702120f191401060305060a1103060a1512020721030e120a020a0c0b130503030a050d1802040510080c010201020c0c 74
    0x50900800300041c0040c1c0f5412131446d5a1803031301b0a0714004c166820b210306401040000c041c50007441c2d0200d200751007020000407400e41a880c081040310600d17030000c0d0000c10b01440c48c070342c02400c1e19940f40901c10400103444550340c1d02032510500907801c90f031000404060b0002066400018070104e4180c0f4107000d80300611340314130401e041000c4507480700e9004954540c6041c10000c03c1107000307c1d07400c3c8201f042c0e000402c05050388403019443c901c000c807000355000c1c10b84001880000c80c1c0411044120072149440c60900400b50800412a0b05c4400c081d18103c00e40651a47c090304a030050a0001c061440e080c07208440003048240da4040b2026103510400012078501c0080d4800c00030302075555042402035a820390344001004095201480d400c11141c4000070100d200e040010446190240558406181c00703810b110400c0148620003607151007190718000440540d80e54000c69000d4040d159084689134030342000c480c581962125a41e05690040c405489a014003240a0303411010a072a80 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 786397185 1250 786395935 786395989
    0x1905030f0706080112140a0506041b0324020f0c1b0a0803072d0303051518041403280210060605070b060a0b0a0215071704031805041109030c060306 65
    0x11b0502c0185078081000901c1640e0101c8248840001d640d8003c6010b00000500c01480c4a1112325916240c00041e220b004460116140d00d10702c01020b43c0c042203021001803d1038018108004107030711600380d101036580811180d580c105003074401d420703801004441680300c90f0319201c01d440e02c034000d100014180c6008181c220310810741c05002a4441c036100800b0070414411440c0240080c042920960300b004507840d0300829905008100904131030001030002c42035512655888a018040b0080710050301052104038080e180c43c68600e045020000e50f01210140c04900081c42e0400700800500f40909210041040640100441d00b083d13401402040c02c039950350300400e482000640c41302c3c190400005944159641c04100061690103040742085941c0311a40704461401a407022000e140c1d14681c08100003c0c06403142110340c000482721003a00700d40d5503000404423550503040c40075032000022003142e90700c8c040c032542e941082d04460490843c2000400f00b011080501000c440100085d203003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 786398435 1250 786397185 786397193
    0x31e02010f0507030213051905090703090215090907020c0604060c020a030b15120f031b0118140705120c01050309031c090b0c191d1905030f0706080112 67
    0x210810040074104140460300744044020001e60081100c0450160742003800320302840c242c1140c02c15812001c68000740c05051100300801c90702c000c4c1c000030070302d0764801c500b50041e142ca4100203c14000c035070101d900c0702d007000280100081c00034180800c40d004520390003050750b1104151019035403140340446420b0520303c0411102d01e05500040c020115003010042c0391001c100c4a0603004000342c801d081a80160003400342e84d40f0404031a950550400c2c404450030180c001c4280d40102c0038070001003181c00140650394402c0a04c03039403c0d00c0c040e4110b0804c0b07200c000d08001d010002c1c0f0007a0313003e40c249440d01c0361301031b1111045003000341005030000c00300340d00e0740c1e0820130b43d505180b000088185580031070080c00c000300000e1004652507103003d400150b0a0f0040401d680d00689050011564068a42d40032244210b080711084090940421581010f88075424500307a82480d46a041d8462800c0100700361130f003580400c644482e03900884c403e100296005141c2d50456840070030350818101c41e850 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 786399685 1250 786398435 786398441
    0xc1f091404061d0402040c08090309040906141e150a0315060f1d0a0c0e0d03030618091103070302132c06191107080903010f050103050d090e04031e0201 67
    0x80004015490701d556030841c43c40c10a403240c0624402c5400308000c1c000c601060b100310404070345018040e0818004841542015081502410b102d000c0010f0040d0080f4180e080201064544030402c41c1c0c41c03081003540c060045061500522600341d0003201070208000a40c0d0381415000013851318900d004138400882c03c40c1c00400107400c0880300b0308201c6071582d164500c0c0c00511360400c50500b00080c00701c0c510342417900c00d8085c0000140d9410004194860600ca040c000b03010048041650f600d80000d4031024010f20400d0307501d494600072900701004e0030402c0d070085209980920070f03081040108016a0b03250f901500145541601186512505128070601c1a9424940d96640242c001c048401080403c03864401e40c0c0744544d8010340d1080049580031070345240c282e82d0102400708107590201e07489034090824208014004240d89454403030210913503000b070b401110b90758005104000c0c829003100c0110003070703c4000e00c82280ca140c00d03113002703208044580e117180c107400383e0044c0380307100503c00c1d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 786400935 1250 786399685 786399689
    0x807080405030a030f02011406130b13050a0b04051005010c02012007060507060f050103081e0d1104150f080f0405100504080a0e0f03100c090906080c1f09140406 71
    0x40540300c0070300090402030001c85d081945032005510701040e1031408008906031500600340600404083e4040d00140380c000c1c400842e120358003220384002c24111102038005e03244515044800460820040300a000541d14058880c0201c0c0070301160901069070b000c5141201a0740910740101022150440b00e80118071512200515000301000400c4e542d810100034006244240400c001c2040540c210108903072080c040249030740c104002c042204270407401c1000340c455466030620710f481c030b034034403040e08680282d40381c481001c00101e000c0103104110446200313001c1d00f90920b2100c1502c1500e004143c0a001003901c1c85112104001c5400d01400700824900d00c2c90102e0200902d05082c2000700ca55040003c1500001d00100610034460808541201c217403030020b001420b004404046203405440041c0c0d02d0703010442180000151500140103c00040c04488060852445804c0c10311410310410640780100d10101c90b00c040c501c0380d00072210340c1100e2041c100303800001348000004001d06415 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 786402185 1250 786400935 786400939
    0x9070507080f07120905041404081b060a06030506100311090c040e15040606140f0d0915020705072106052e05090702150a0f0f0c05340807080405 64
    0x2c01c6010030400312200741404c2d24010f0f00c0d44d0321482d1307403042000240c034803440c00052250010808500002c41c168060300c030f01c0b40304040c2c035a070300c4039201c048910300401103d404810503201c0c00d08005200050200d590401c03400540c02d00c805045441d01d804404610b0720060040c50002e00150392100004140c9000e002401c448000d2803c05505500f480d810308445180b15a01d4440c000544a006001200f400710701074007010b0030000b000004003501e80083c12f030512030648a03c130703000000ea55200e5040690030341210060f2074804601b003403481c01200e0b8004031400c1c02070500181c6580e541810300d292050f441800032500c0d03a264010740c5000c1da1007103074030040c9070b6007840b10881090040351000c4c19190240d544501581d500203080307170b80301800c1c0c0351041c03520342500119090001c0d03a00110005150303020082201c1104883c104101d50a51000900107030000c40c01c0c07a814000f02e40c104918410110b041c44c0494026128042c95040209008002c0c0c03500296000c20444420156801844c0c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 786403435 1250 786402185 786402187
    0x20714150706090c080105060f0402070c080f0f0706030209180403032c06091203010e07170103080a0f09080613020409050a050d02151015031d0d0f0203040509070507080f 75
    0x94034020010700141d0f00100d6160381401004100e1070014030403d482184001c1c580f05403841400107010080d0b00884050b00c00d10006a4042580e80e0100f01124002001350000c24150410810060401ca20f0760031000130035004002030665984c41d8001c000480d02601d5400105849614007980103040003c50040b8500c1c10035160301e00120b403034a4401d0180924400d5507101da856842c02c50b05d4110450365030352140020f2005000002160300410350043d06030038409680760742c4200300074040314242d004a401c1030000641718841c591140d201ea03400e2410781400144a81002c3e802900c0d40d00080108070840810000201036644030f400080320250010155841038a00e0b05003192118040328810000d8801d040d1000404140b054902e80701e08481c0345034850341e5003025804220046000700f84010180c65900c8550b8800a8205010074000d014004119000e07a00d80c001e8045010070101e14190340090000300455120300041591200c007518115903511641d1a1140c814010809800380d0220 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 786404685 1250 786403435 786403447
    0xc030a06020408010c05070206120702070911030a0e0f0703061a04090602030603061f060f27050108070203070c3302070e0c0f09040b0307150509130b0102071415 71
    0x400c41d4020b0055543c1c4000901026122076020748840c4600c1d00000d4000108006030a580007400d00d601d07401c030207288141e9840c9603603201c400042c0c0b00e4040040c002e002002040c058170700854880d18041035001343c0078000c032101b11b640c102d40713aa42510016002da038540710002090800d0040c80415448001c204210940107420044000c3d00700b142c0060292041c40d0101c0c01181c566004030019105411075003004a007811400c50f10344412814071018000d0304035006040d04852040200740b0700303800d20300100d0341d41751200050a11401030600c00a41d0130408c001c101164500300703050107407800f600e00c00c42c00c40c108001d80161031603120340c0501000c81d86007204240f07660108200017140c40705e80b13000010ba01d48041582003441040c4100d07001e01c00c01c11032800c03142042c1c0c000001c071400080540d40501d58520816000d010806052400284005800350312840c0000d214119504d500c1010400d03101c184c030020350f44c1d5547d03016041c807022411210609039074890300001003000c2100019a1194 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 786405935 1250 786404685 786404693
    0x603102c120a0203042610020706060e04150606050c1b0607080319240519030204021b060a020403050a0b04061e02071101110619231806060904020603090c030a 70
    0x10f0001d004910728020880c1910101840312506c400d4411000005800c4250030121500000e40c8070040c01c40f407580e2140b40000714031b800354061505c65401a003944140e69a07082141e0122400c07500540103104042c090705900a600158a4030915010110302254110303070b00000d2081d0143c28002440e0300b400100308484500000c0d42c2485400e10303040c00707101040c414031030840c400440220105014011540810aa10f001540c1030ba10003001c2640104068480d0042800d03a030008400101094100900f482c05440800019603c080600c20440c285801c5999107500d0b01140c01c030280c009105000800c003404010341c00314030800311740249071a85101c24400341c0c01a41050b0400d4600308048581984254010341810003280c0c045005481c1556540c114030507100d0800000c1e421240c2e55000008000500c840b2044080c61440f0084c0303a1440c165000a42c03203003031040e900c2c929400007418400d990300c130070703501981282d81126070544a5076030581d40c40c6800f00b4070f8072040e4540304102080c0140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 786407185 1250 786405935 786405937
    0x180f050903040e0c0a0f03050a0f0903020d1229010512070305041a280207050f030405120d080133080f150a1a0702030d080603102c120a0203 62
    0x481d906284443c02d0b44d5100700c0c0d01094002c520002010403600001007448621a40c8140d605c2541d0081c000b941e4000c00524004070f0b00f05407401c8015034001c0c0240a42145c0002c07036500150100c800a0100d41e803842c2c151100c0010354858182005d89850f0200c65607801041910b001100b0a10b60003014901007000402912060720300f030f20b286440c8204919084100401503105161003520751ba12081007645008042e0040b5600e80c030b84940c24450400014400d0005080342000207000315165802c02003002042800491107091aa0042c0c1103100321a8014040c5411100381d90b480c41005994039100d0403c81e410b08003580c00700c601c8041300c1640980c112030348601500460005000380e030f840c038000c20345002e516000306078002d4100da0100141402c403400035031100080741304070f41403a60950200340f41c10840c605e108045005182041080d00b020810518814002c084c1804042c40c004241a0b50190010b1100404503415841c000d0726801042082c0d0781c45880040151b450354001002901d03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 786408435 1250 786407185 786407189
    0xc12090c0e10050a050d05031e0409060906090b0604030c06050708090a150e060a0c2907020604060f02040f0902090316060302130504050c0f03040309051c050f0d09180f05090304 78
    0x820304c1c002c90041032606100399500c0da2140d01100451030080c0340851881500c00c2d40c1e89008452504010100d4290002d0099a0040c000241c1c0443c81c9030500000c0d0341a110b681030841d026560074032040003c88c6255845104582444c240103030b880d851401c0c400034034803803042c44030340069541070000341400b80c28410380c041078400e540d20740d010341039081005458403d10707030441c0001e409009040c02051619030308032011768490080c010000540540b218401b0811126640560004030400041c00203e000c1c80c5902c0304124821490a03047c0801010304000742c0c01032460865010401400c261401c024035040c4900743c40e030b0300804d6655600010060740c060381e51242e25403c1480c0004041c142401b40b540170350715400b909800d0038208100141030f0b810042080c0e003003007981c120000700c81c0c030b55034202450960b80444042c0a2403031814071070302e0010400034850300c0790300010071040d0312640404600262030990748401100d401d005a00380203004507020039000c1c1e03403034081413045c1c4c00000401401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 786409685 1250 786408435 786408439
    0x2030f06040b22020630250e090414070801050106020318010509090906061513050d031709031b0c031c030b0301050a02030114120a0803040317091f0c12090c0e1005 72
    0x40038020100485005416120030260545168284000340031f40c4407906510310340ca24041e5041800c0100003107a82005031400d59140c000c0150300240f40005008003c05070210030000c2c0020b525001000755244524107010048002c010307005a040ea21580854a604000601000d01400e2000500b4bc42d0001585d80522034001004101d0f080b62041050310704078a0340400d2004018035000034400a000d000e07104074100400d07110f101e0011081040024083d03005900115101c0041c6410403488001060803030a01c0d501c100c08004840d90005000c9645881c244040e14800f450654180c1c0502400a03e10794194200303020000707207205030b070b0180d4100c1321700d445504180000c81d414480442c24400381d898031904680c002c4030106030940c000f144c03c03504c030f460b000c20b006001c0c410205152000fa40c0140c03140d089840080c41a20404120b401581041e9500308000200703484050710141c1c5010074004491744651581c02400034090112004086840b4508058644684030f0b26031186103000e014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 786410935 1250 786409685 786409747
    0x90b090f010b010503010b070804120b090d050c06070e03070906080c100306030825080403081207030b0a1205070506190f08010e060906030709021602030f06040b220206 74
    0x3034020360050040d280d0707403032040c1c44051540e401c045103003038698003508060b40c003a40200701c00542842d41c8030400c4452401a00c4284d91401c05c0000f80341041e01c218004400c201007800240b5566501040317094001d8800c2c1001071500c0e041d180481d0070f0100780d6111a0071245020300008400c0404101d0711401e910442d400c0403440780a5100740d04840301c82c0000303041200b05104d541d03601c80000003000706a4640a03018024507880ba0389070361840e172054004940380320000c152602d42c001450059508210541028825092000c0105080e03604510804200e55058001784061001c140050406000060042070b52a0001c660030303468104c4a8446600148110380303451032540c845c6400c141664030380c0000300b407903490b00c40c1001031070080900740a0f0f25000700c1d01d0001e0201c04920080459140140d2612000d042900415040c4491903151001c1600490104000180031040f040c0c3e100200c0084021031001c14220120661010840290001300000325500c41d1014802c415207003201400e00340e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 786412185 1250 786410935 786410953
    0xf010e06010b19111504120e030d08220203070e0601020601150c020409030210050f01150c050c01051605030d0f0e010207020d0803060607020402120105030105130b0112020a0801090b09 81
    0x90501c074419082ca4000c4600e04911515109220b6003103c0e520700e00000031240d1641484030340341000c00058a0480f50500751f0384c1c030f020f4100d400c540c10708102ea0040300a03046000420308007500304580100f00410b26052034800082001c000d0503151001e5801404681d20192581a1048004020f940c0240075229240000404c904402034a44002080d5170701e41c0c00c14a06903007400007500070310400700d0039030040180c1200041c103203108a500c1020b030818087c41c654507084012a248449070892010081e840c0c1d81c03a40810400a500030406201b071800a5072415844600f80792412202e0f40281140000554a03d080c03043c2c5c0c1041c2c079100101001045041072041c0d905d4201c1c420031000a4000d809010f0002c0420006006545d12802c054505883c00f45030390700040403640074120b10200700b0788000045c401401c0c00d10a260b809038080c0b500707803d5100d482d102c0d00e4030384a05214615101481c00c1440c0300715100c441c0d001c80140490070007030100074460710340f01694a504545c01e10340d41c4105121 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 786413435 1250 786412185 786412199
    0xe060d0c0e1b070c030210031d07031403040806130501090b0408180108070c060519060f150f1b0302072417060121061505120703020315120c030f010e0601 68
    0x12a01019489081c2d000d104c1c0c41c40e4288409080c6c1074044406240e0b44810f2000c03224401c1c0c0c40844410802005880b2003030843c50700c3c5010b5440c1c443c02c41c070030344c0c020f1206001c4940c0000c1c0207a085006602402c84200705841c081b400f60551107002029a0380402c1808100400e910180c407100141c140b55036143d815080c01100c03200303801c450b100300203000b001320700c80418150342c481a088a054100c159101084054807416941c07241d11280d14520045420801101d10800c1700d080c0102902c1c00c060b505100c2100201940c0303040c113000040d00b0741284a1002c05000700b003a00020480380411103845c031200300d054002d01c40c5082c20344022078090445644171421075030307021b80300d014141c40d0001001150140c3c07409003420910706021040d5941800302c0d021130b4180084010010039030318155150324198003180101c1c001780c1020149401402449103020101124400d5403d080d85c0ca141081e1086403460714183c0024422034040c05207170f48510107180103400810f02c40300d12804403142d0380d90ba044 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 786414685 1250 786413435 786413437
    0x10207210909110d05150418150e0c011103070c09060905060103090b0a0c110601084204060f1a100c050d0309020a09050a02310e060d0c0e1b 62
    0x1411412001c01014030801c1c4d540e48003d802807460480c0c4c00c180c04007100030030210b0f04144d01060542e10340180c1c0c2170030000800707100381903c01010030038003441200102035030f52181d00b100d0241c144034a000611054100400c03d540076203802c04d40c81200c295482032284000d10b414000c0203074507400d00d4002811540640640390400303030300c03901600d229501c2240000c01030209034240c10810900c84481c24004800f0402c2da400b81a541c4081e001c80394240c0c000800c81c01940710403038990290804460040090000c6444500503101c40c0d22156030b9030351074248010f00442007403042080c13030f107640070303100b090a080c43e4110060140d500b031400065696041d541d0703400d49480148603603c04055421800c3c803a4103c01072035840601018011900e50046030b054800c03c41d8030b0701c5c9240d404150709804014020000180700700d803109000001002100ca85080e081d180a20000001d0000108800b0388800c00f0a043d241e402c9283d500c242074951440e252410001c3e82c8600e800f1400d41d24890071540603074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 786415935 1250 786414685 786414701
    0x1180608090f0346031e0609020909010e100b18100201090c050d1e02010302090306070c0303050f010b071b120507030b060a080615061c05091606090512010207210909 73
    0x1580c070403081e440500086006d010f03101c2000c0c03500c55a07034103044404501c6010b01c00162610100150b2901c422000380700c0e82001c16401880b61141c1c090621405004001240d0180d5440341020b075665001d007618074001c00340c0c2e0015250080c03200c00b92007121036410341c44100580c1c4210210041c072681c0f0070400000a082c1100070b044450300c0b03160409456038404045d0307047d5106042c05401c00481000090401c14126075003c0031681c09101c0408240d803500c29203500201d07502e02ca040e0343d4100030001040307001c0c078900244032041c01201e0042c80181906c80100034090186050154070702c0380340854641c00940b004441c0d25541c20086070f12807422505040039182007000031700180d9540c80a0000711103078280300305c1c1c2092041141c82600c4080101c2c00d00700c54010781010405061100c069458800851680100400c040d441409030680c810a144101c5504841801e4119459a10540280b245050041014004a85440a1011041801160741e10580710b030410155103181000584030b5078 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 786417185 1250 786415935 786416047
    0x6070e0a0612150e09070e0415020711061626190905090c180411190203040b040807061e050306220c091401180608090f03 54
    0x41041c00740a100b001d103000c8655810300041036500c03042e0741d020160803490b048150300744c0d4100c08224408004200e0030004000d1030004030202d25154a8030f507104000c40030000003003a000502c02c020700020207842e84500ba00200f440c0d548445000c00c1100d03011480b40308465940741c41c0c0016403506005603698045400800b07160b0f242c14081006c400404040d14564400c1c001812030103e4141c81c1c0f5903000344a8846811000d641c2e4800f03c241c00340340342d420005a8800d60030302580b07140346075842c002d40b04907a03a42030807840c1b4900d110001b0f80c298000c0c1d401206a00a0224002900000000b005811038000c0c1e242c941e1024440f41d100d560441d040ca07401804a842040071403002c0c08c0c40c110b51481c51290030000103444080011236010303035400b03454000c0018803410042c000302c86040d00c400700501d001d0810910750b28000c1604010030215100b40c105000d040400a48909000c1c820300180450343c1d002d1f1b0380c0d40c0e01010641000010684901e00900d01d503c41111504069891151201010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 786418435 1250 786417185 786417199
    0x8031804061d190e010c03050622020c0c0904120e0105030108070b030a020d0e070e060a03150506010507080703030603110a0308030610050c010e010203061503040206070311010207020a061106070e 86
    0x145544035042000003501414041640c00214401c001c4184102204d40b82c130000007044001040c40004c081d50000340c503151081504c89104070403002c8142c0614003284034100702586039417100781c044c1e0401c40f202e00032980050b00c4e40b0030001001032404840d8000d8840c0c1c3c8503054409452001101c00f40824040c2103004d501010061144d4601c20000d1a03200c0803d044c0940f40403480703031551060f9180e2454400c00d5a105030802d00260b0350101c1e980d94040c006491104043d841c3d038984030f498004291300144000c1d40c03040032501e9a40301d8002c8075009508407034040d503200d6140c070b0018018075851000355210580c80ca600880342c42c100070104100c98100c00200d003140caa0004105100d103031840c4240500504200c0c2a844100030b01480044200320400180c0f83c0c038001091009601c00404010050b01d82041004016075038a803e80344440d4152516243c01d225008120b80240b046001c003030f5124170005000504650f10140d4251400f0072401030340c0b000d440d441401da4096150070722040e40310036 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 786419685 1250 786418435 786418469
    0x90a060b031f09120323100b07120305090606060d1802030708010b01020c031c0c06021204060c030e060709051207170d0f05040501080703050a090c0803180406 70
    0x104941080011040c0241500c0060005120140e00c031160441000d00c0551540d4145042c0b03c2c1d006144130b03600007542428081c00d602048800da000000300c82281440b0303804404140c00c07400408550303000c2c03c4108060b41d0303240c611307003891141d08180ba8402e0001030b09040000d2154400410700318042c1c034014045d142082491000c1c00d001e001c01220000c51800c010101401507901004440020111071000103034071312004000908080301854001d00944c0a2805201150101390784003248016616003010100301030b1400401a201c0c2c0304845003200101c83c01d000030301065510103010034400d910200310501c004440c207078440008071100360210305200301c10070160810804480344000c0280554200684410004240745e05800c00c0001560000c010a0700040d00080e00c1a02961181001410300b481c14000030040e41000340300c4820952564085074100c2d51941080080b03680c008801d120300342e150b40103203550303800001072000f507000c4d150001400360915114202c103440c0c0c03140c4240c210345 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 786420935 1250 786419685 786419693
    0xb070b0402040e01021207050a020d020303060619120207030e13090b0c0f0f0c0d0f02030c0718020f0a0e0f0a060210020730080a0e031e0c01021605100203090a 70
    0x7050100c4450f0083d5020418000c0c140c40a6882074401c20752502c8a43d00c0e011102e0000349081ca01d01c0c41401954020001d104190341c030582962006032842101e404400b4a1000840f4a2b000c0c9921010f121400450b0030350400d80c000f81401401681500c0840500d445448400142c0700c2c1500040e1015813000d0220f444d0311740c402c0040c01c102151800e010715081980300410380700d6001045440742c0d034014503080c40360207510101c004416440d92000b23504000740f201c3c4041d15404075120340751020480c1e109180d01000c0c0780c0c05491494030442c120b19203071811410050040d60008030030340c1c03064000312484005031401801d40819110a580108000034008200d00e000b50701020301a00d5132210440240d4000c4481c0c84000c1e031141c01000359a04610a401014140b944042c018407482d03420141c20004052001094560301240071215289100746d04503203855522544038003400a5000040071485084200744440303525105004840c49a8515071560b003c81c0030599510010390003d4400346c0c041 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 786422185 1250 786420935 786420941
    0x6190b190f21110d0603051516111212090d0f0f030b0f0d05241b130312050403020f060408030f1c0516110d02070b1e040303050c070b070b040204 64
    0x2180c42e0140004041d05003000051441c0c00c102c0ca442e1080307854220078020002c00b4031402d14844d940001001d11410540d05040460040c0c0b1585804c004181c90080d07202c120400036224042c45205034142c0e03650a9003000c42040030f04643c0142d5521400362524100b512411000781104003d54038001030b4002c501c3d00b01c020303000100e18240e2003403065100d280d0742d50300e12204100880c86800140040300882005100407820300c000003c0e03010980040040d5490003001e072040341c0082c0c035180355403228050fa4100c06c0f800c481d04098840070201c1c500ea880740e9000750081050341c1c000c075801e9503514130580404c02240320b28041c80003150030900140d06003881c00c0024001400342000003180d0052884400c0044413411515942108001483c20107410b4221900c1d00750f008442018040c045410040650703100120b204240300d0420024051b08508884403000c0d11000e654804550b59507076904005150b5000340031562050300601a000544c4981c40c81101c181c0c0b079020b8980e508a030394a401700802 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 786423435 1250 786422185 786422237
    0x403120806090c1b01020a0201020301060210020403020d110d230c24030c0c060406021b191101020f060f0103020907080f060d0602040306020a090e010b0403020303090906190b190f 79
    0x440458000c030079001300f080c000b07014403c17040d82c001038580d854984001c0c6010700070815101090702c1007000b8005611101100042c06401a614001c1c5181c050042013594041070030190803243c0c040029442400c4100420b800d00e6220401c9808020340041002b0500095415828421901c0030101881500031809180e00001d0210054101142c03403140c141071000481d42100c0a5034005414030a080d203103e201d800205064009050480074455000c0701c5514101c030160035850407018820340e6a100b0031100c12010090003c1e51030700d080041d407a40501c02d00780012407050340c0507000501058030402140f44170712400c402019140c0c0362041413206a54245a0560b2000c3d000c00011012070118001009040a13555519001501e004401800840180c000c5076504004010400240e40c0002c02d50380c40240032103460610f5103860307001460468180036040d0381d00c4413107840051507890183c060901c1e6140c51642c02034003002e50108456020103c3c0f03903c0041008a51b401090800303400f00840d03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 786424685 1250 786423435 786423457
    0x8060f0a05060304062f030f06060c01090503030a0c030b1c05120a050d0e0c012307060606260106090e07021005161101020a0c0210090902030c0403120806090c 70
    0x10950700c4101242240c1e0007280e0643d00707070381c0312004d002c5900d541500d901003005008500081c10350300390008466610000d8110703107402e50500003041d407a41d00c8008440c03c0c0546c0c48000c005210891821b180c03240c00072103000c1c002c030380781a580702d01d458000d0050069101c0002d01501c0e40d1041c0f10600e000c1e80840c0c00c0d040d5114810700782030144403007000380202000119a240e01b5110780344000390005030341d00307446040607036080031650318880d903001103000441e458401c07103070304210350441c82c3d1042a002c1c580028000341d0824400107211034120451420000702d90f07409905854500141010603e02813040000046612004102c4410019401030304400e2034410340d00c85143c0ca81410056440a46401c640000c0d00c50340c0442c1c958211000ca110701000074025420100328000c048c049580300c5c50040e0141d02c400040c00b013164800c02c411809052a01c8003151242001c100a41d805d03003007404101c90045400b100300080a0140034018818000146425006d944a030b00d284083c0d080049405 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 786425935 1250 786424685 786424699
    0xa080d020c3a080c0f071505062812020616030203031830040e0a090209060f030a08210a1a1903030810180603020f01020d08060f 57
    0x500440c41072151a0903441101400c442140b005041041012072201c0740609100c000012003584a8101c071800380d000250000541d1594400001d45400c2e10031301a000340320320030580d80500102e00d107034810350080c501582c41482c890844501c42018010262100c48140e0002e1410840b030070543c0c1c20500c40b5803002e8140d03400e20000006150ba0300141010880242e0004000c100c4640b43c620841c03000205040001d01c00c01d1601007416001c41c5e01d4440e510301d038611304004021070503c0721003120001c02005601203031918107001c0d10402864200b6080b442441b003840480c403075180070000348042400c0280940481400383e86c556085501c0980e201110f0012070036010300b0034600c0305242c1e119040103440820340100500841205903140b44680340300d080164000303907410084038048016a1307030600380011305865000190001301780b0360b8400c0300280481d0707005074200030300ea40111080343e01c01d42e4070f1204011104016a29002003091303860010b8505400100b0f2442c0c0690003020710840036185c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 786427185 1250 786425935 786425947
    0x6191b0c08070201050c010f05011a091f0519350601120605030123010602061314011e14060102071223030304050604030f020303060108040615080321010906080a080d02 74
    0x1150958505424860b8123030ba0b200010847c45e611910860f0f401d602101c00310f4900010400000e41c881040ba020800f04464056001174050180c0c0813a40d500c10b0404404140d121115001414903040400300c4224403004186103100183d00401d08600f40b02060100d00d490340c629004440c030f0007211007081c1c00d1585030000024940c40038464401d0000b8158500320074004010b461070000901a4050000c56110780208003004841001101c41103911110003052844400c051b14050100e06191201d01e0b01c1440e660200a12550702917101103580700300d47c412944d01c01c07006980ba5060751040500007004070110100085400c1500d104000800105c04c2040000d02023040c6150812201100c00ea070120341804141a007007000b118004081d80700851461038a00b00080040341d002d000248481e840c2c10303d0001c510003894042c0301a10743c50003140e40307448403803040d59404001e2a004003c03030200b400c00491070040c4c42c00340805a0b008000104884411f40c1e0340c030a2540d00c01400303403d609509000c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 786428435 1250 786427185 786427207
    0x31e0e0f010903062301151b051015090c03060f0b0c0304031208010f0b041a03060f150a030e01090c0506090a0e0a09120807020c0114090306191b0c0807020105 70
    0x90580c001032214417528000010100400102c0d41a0429042c0100340d4142c40c1183e9440104041d2050091501c009420b200c2d2400f0303458488681140b4000504202c1e90b00511800c50102c0012107420900c203024031010b008044e0120364413409080000e01c02d584050210020140007021012400f03401c903850706550f41c996100000546140d078000641c040c00411561901704541d001401c072008506291615050b4000721200d0145010070107107101000080032030b03039003502d482c583c82c4000e4034912111004103007164503070f80040e1020011910b00383c1c0090404c14141700c0d40d280b440c0c1c0515420640b80c00c00007000360581141500c40d910080442010450a9401e41c41d60700800a10502141c2c030801840c142c0240c4603034004541c00c01042c40304125540d43e0000d00d50408480038240040d40120040501c0c4141c4512117050790103100c0c0b1802d2083c1240c4040c03400180c5254103e0030402003040204800da200e005c0003007000003031942c800c2100460440b40060030001c1c41410000e14181a01207 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 786429685 1250 786428435 786428441
    0xc080a051c02030405011b050a1409040f090606080a050a06110f0a0f0e100806041a0415030b0f091203060a12051f0e0304061110090b04031e0e0f01090306 68
    0x281d02204a80100520007007003402d0003204040280032080c000f0403010300f030008000d406500c0129042003000224851107801c1c1404481c09000c001e003061003640020310b407610190043d8403003280d001d417900340c00281c41100407034849200c0b17911a0251486188580351752000e40000010104450010400102e40c41402001424440c0c0d01d03850b8240d0f05800c00001410074a5100c034803902449907450031a42166020940c19448401110b000410075103080013451100200110300ba00030340703070030303051502d604100080c003045074442c46000c04556241480d00c1d54402c401c0e00c280d00a9840f0b0000e4604105098020b103a0100014040d0b095455075500e500960701440f2200744c9041c0c0245840c10b00e081642020144100ca080307500340584802e540b44070703540f440f0f60310a680030070030480c24070708c00c1d40818481000040d500c3e140a00012585080ca48204107058504a010903403a0f00c09144c0302584400c01e00e40c0501a417500302a2a20282c103000055206003030f01410400160300110009002d48 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 786430935 1250 786429685 786429727
    0x60e12010b12060a05091f09050a020402040f170d050a0c330c020c2110020c060f0106020c030a0609030c02090108161a0403120908030309060f070f0c080a05 69
    0x50062880c4d0918640410880740f014006000f1074000b0344401c0e07500350303030803402510241e0b10141c0060000c0d01400e00d903042c681c840780001d5021740001000901d8905003100c59041c0e5642d070314550406203e04074281d41c1d54000700d101201241d03007481080b141c64058a02d0800702401000d81c280c0f50045d04c60450b0000841d5985006580705030000400d10074410b1190054484841c001400600702000c000b031441c18586a04606481900122510603407050081c0b00400900c9070044d5192040d142e021502e900b01191a2130b05140c01000014003140300003a00000200c010300038002c00030081c0c8806001d081820030641c14000c200301c80c10016110710744402c0c000c160340d1014005100d000ca200c00303108409648190000300c450607001909039a01c0e81100c085070b91013108200000d28020050b15201001da010103124080801003003241e00000c035085208003c03814503d0300942e17402205445001960030241e0020380f5124801c070004440c1c10040007442034a082c0682000c1c030901a48440c01c82130 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 786432185 1250 786430935 786430969
    0x120b030c1503130c15030c0c0302060a020a1202030a0c170103080726030a05010806060a1a0901140406020106050306010605190c030e04020a020c1c17160209010803130906060e12010b 80
    0x50510100f170568103201e071400e03240c1546014a411545924000d54039940505042c140f190f0029482080600075940b10f514044403680a5460b03141c0420601c005180b00807510f400318000c01011140e80d403907030203039a058940c448003c0e07003400b40580759058041c00c0d2010301d001030f80c1c02030007203503103000d41d01c000d144503c500440102d081d6050580c0c3c282040005440540551100c3c60103200b070228910b80003124143d0601c41d1030b194566100121020000e62406440c14800002d0200d40d26a040d0051401d480c1c068088503160b99844408071094462142d43c0c00e07114060f4001210400c1c80f600c0440312a50203450611f010b40d540c0b0000408a03400a0213110244e0301c201c149070034030f0500c01c03200e4180d50000c6e8411101c07400b00c4e44510701d0b2040b01400d10340f5544c0380045c0311902c10541c004824942d5402514201d05580c503121100e030707680c1c010f401c8960000e401e0100011046250b0080b00182e0f20b03243d840d03100c90681c6000784000611603000044944d521410440b400741c64211600301c82c5904 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 786433435 1250 786432185 786432209
    0xa09050d11040b04111c09080a0809010e061009020307210f06050d03200a060213060216061428080105090f1e0403020f0d120b030c1503130c 62
    0xc11001c12048038103c501103401142410b003110906070030101621507142440b14201c03c4403064200c018001d1074502c00042045202007040c43d1000c0e40140e48510400d042e40c020450900340325502c0f95107820464100c11040d102010600c8660800e402940d0404501e0400840d000941483c0e03043d01c00700d101c914074209a07546150003c40c5110b0246400404054440d100c1004250300c00800011130140b907078841050000202070440d000708608501aa04190b0441d110882110302c0c5500a0080c490800103124115a00d00c1d40c822444400341101c2d40c0d900e81101421035004130b501c09402c0030450360804050a064811740c50844038803d454551300f0b40e6210380d00e6040008202c518540138040650115401080182141140d1403000c8180c0521640000d1540c03903180883c40c10895082c407040f14080c1c0000c0980c2c81d03403c030a02a00480165600b8414600c00a00381590390000300e01c0c240d8040365220982c1c0c4400ca44600650300000703100020b0281c0da005880e00252100d19500ca1004014 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 786434685 1250 786433435 786433463
    0x80c1005040f090225030f0306060f0c1214040806010f0f0f05150c0f160515041502120a0e09010906140f03010f06030f0203070e011203050a09050d 65
    0x5012110401004114204242080d0400c2003081c0c03001ca150060300310255001801d005005d01124a00112181c0449450502100d601e00184a9030018104a02080c00c02c14081090341c080c03003824060346e4040e40c4140d5107009036142d4130300342e4000d070170181c0500c50745403207800c05e64404100802c060300c0286c008141551500402e84c09881080d03002440e6031084000501c0816a0400f071101203031412640c0303109039103810018170003078401c5800360080c62003005007a900002d80400c4c49003001c1c4001c03600b801d940d03541c0d0041c480381181428081840b928204401d01c0302c1e1354025000dd100c22098411248108a440c0c40110742c0e80c0203800000105a4000c1540f0040c03070302000550152110903014800c0c03602d0036940c224000a00d4403107a01c11502007506c002c003034400b584504e0100c19170349070510507242d490504c50a0300400f094107902a0083c18800315603029015003440c100c680e11802251900a1510200c40700d8100207030031001c000d000100001c4694504e031500d1200f501070000072010030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 786435935 1250 786434685 786434689
    0x709080c19180218011b0b060310050a090213020c030703031e02070c0806010503010c05090103090f20090f071e18170d031b050c150f16021207200307080c 68
    0x140000c4005d041000c0090742c1400800180903e800f400d6004012411380c0d1550070000c1e041021940110030190703d0002084006491030b04004a80b070f0090300d0101c040c4245a402c0400c0e449400b0080e00c1c298030030080240024441d5114082200480a29402c8801480b03003120591303000d03000944006c0500e00e820301400c03000f030241a005110840080040d4480180e01034424010350740c00c5411305549e0400c200c240101c0c3c4421840d09a8442ea2071135600384164485000703004410765142c000e207043e0000520401007480640d0060300540c83d03018001030381941410321640300e0840e0800b002007241034003c061440400b044003410320b407000741c01da250705a14168540440d0102082c00c140c1004485c43e401c02d5004e4529031500d40030301c0c00d1552078880030100351030603401303800e11041c08280004100b2440003021031540107c031410004a0446425a4100c0c0c2d10b10700c0c5e16070618190020000240001d4291402802244a03140050b480300503c5000a003444210350103505941c0014070188168 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 786437185 1250 786435935 786435967
    0x50604360210032412060203090102070c060206070318020603010326030f04030f18091a03250509090601060e1201090b010602061e0408090a0323060709080c191802 72
    0x401c00c400c0202071045c1c5810310181118000c0c00f405807030103500001140d0075100c290110303800503800411036a00f45e50360b83d0009546160454980b80020300d000c030a050f4551425850100071500100300504590075a1100b4000c0805d8076a0000804038145080c000d288102024512655100340900d50514160601910b60b00130141c8030410004103500240007004000d41e040107a0b1814080001d5160046030b25030f10040301c402c00c1642c1841400c3d00e50400c1104031090021591045000030a0a9030721003e0010440b01a1061b0f501c0e600100c3c01448640c1c840c44071040000c0e0024905402c4106c0c000d03e803800c4480b600400d4622060980040c00100e40420099800906c0f503420b403c00d65021804240e8000ea01400081c030712140012021001c2e5984050000a03503000800002c0d059119902408501240c40744503c0da800b0300c03000928010b00440200048841d51405007920145050401902491054144510113205840420f60064000c031301103a54000680050703031041c4100000d808 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 786438435 1250 786437185 786437231
    0x20a09050f01080f07110f0c270c0310030b01030f050c010206060f3a03030b040b06030604020903011b110c1005090d05010212130605060436021003 65
    0x1d060550820403080e41d11121840c2d120654200c1000141c480c1e160858003007038224803640003031003071000b0f10804203c007281071b00c03486130112118103406015500a1042200e030a9031182c27285403103c006000a6943c100039544054105640a803c1c1d403a07075140390b9070190a81042d142600c82c6a00141008002c0000c1c91004500740018501407425000103800b07050a510b915000e40b5144200c0d42070030915402c0c0c02503000c0c0840070560209450f003105625000344540030740c00603003082c01c483c4030790074144900d24800030301038101c0f85903035211400c0c00040d51104031000d41544d6079408800689407502c900c21004115503880024075a02c20107058070b04005030115910841164001b24242c0e90800121000c840e0f068034107d64a080703d0070300500a000d4510b810703580000c60410032600303000e050180000c031489103900300034949915003440110323516800100407906214211340b04100d1080010046541d0451090342c4040c0113a0108030b40070f00a91245001c2521600800302c5408003900d1400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 786439685 1250 786438435 786438439
    0x12030504092a0e1c0b0712050c0322020907030c0908011401090c0215040b1008010c0807120b1e1c08070b0601140a020607021002040b072d0501020a0905 67
    0x4000752507014140d071002c2c540881c4140f1001a02c1a481d036110000000e010000c082e040070031130200c1d828114000402141ea8000292182075040f480c3c4546204642c010a0400409030840d59203d07400c1c2900b050301050442c4130303000ba00d8076400513503030794111510488242e03401080c0e400c0308030700c064090f6a0503008041e080c0d04098070103c09844021482381140d600280100d03c4081000702a401c1c813a0041300080c01030404401c01003445030401c206401991400c513890070047c4da9030b001070308840c0c0c0d08220714001607540e03012800c1248148414074034000354a40000302c181020000406288411301020390785a55069200300f50302d080004d402c0402e8207803080323140318003c43eaa0501c1c00e200ea80802043c1c0d00c10180401c2c91030344510818201c4d102c416015035503a41510340040d5980804036403820051107020000340e1917820368000e440855402d003c80398145000d6982d42107107182c102c3c00201c00c2c10600c2041b603c4030310030880d03080512070241000581d00c0c030f21007000074600b040d0381d00094 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 786440935 1250 786439685 786439721
    0x3110f0a2c0607080a09080d050903120408060f27010b1f0207030615030818130c090b030a020f0f0d1107021507030c050105070e0102070e010f030b0702071203050409 73
    0x40d5440d25a02e0884028541c0000740320b135615001c0d4025600c5100b5904040018448c941010440d10341090040035082000c0382154007000a030141400d007031240380a01c942581280010420002c4018070664115411441220803604017000e400c01055541c0b81641c56a0744030240e82076641030410408110b03c4101c0c100c124403803501c802c043e507100000d2000800860752a0000050300175214103500203154007040a40c0e95100d04030414650350103402040f4469410b0a00284030310300b181c03042200c5404940c9400100c11b103001307414000c0e500000c2100f09019020000403116480620040c001d107004044c0c1551502c1d00c4a0b0b00c54200e420291107034032214400c2100c280940e0700e040d00e8003408425054141d81d9060507240c01c85585681c8c840040003582490240410b094201e1040210004c0aa0071141d82540e0742e06207400c1135100b0f102e24980b000c0602070500201310500341c000c0d40030b402801112480c0b55980c401035506240880700742c00080e4003003000c2c025207481d4040d610079040701c8400d803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 786442185 1250 786440935 786441017
    0x6051e16090510030902180a050f0103020906100509041b02101116261903050114010e0102070b030408070b06060910050c01061e060206130503030703110f0a 69
    0x60440456402403610440906020503041413194105e180c0860b03014054046001e0101703844010290142d0750200d5242c00c1c9000502900c004044103412250010040d00568a48a00b4484582c0c5250300781e07020400d04001a204584079400780e1024099500c0c920222160501d40007410240002a815451030420052600010805c820f5440310a00b0807200c40344441d0030b14180050381c0002210320440b600001c4404844009000501003000415802d40c40f80700550000301c00320b440900684180d52824403d20301507500c1a00107502d00d42060044412182d15201c113949a40c00c1107504681007100002c4c140c003001000c500568102d20252000d034203000da0400090a4041d0300110001001008210200e681074250089001400310300a0f104014400c400c14005500b81c501035000940325003070100f2014104c0340d1300c640340544c00902940c119110241c00300c01520b131001050850318020700c1040036001e070b084001d08080b8401d890341e24200300000d0300080d00018580d0300b98900c075005101 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 786443435 1250 786442185 786442187
    0x10061407030f050306120d0210060914010902030c04030c090218040903170424021308030406140c030d0e0c01020c01020628060b04171002031311040906051e16 70
    0x1908100d03500b0750400c2900c3e41d41c2c01010400540140c03031144250f204442c4441c440c1c03500030400c81d815400f00b00090250076115a0300c0c030162041e82490581c0496050010065000298099504070541c10080b915190349c9480f591401042030704200d181c103600054000542c280074241754410305d03040e02c051180c0c40c0d013a20301500c121200c1481c03000e071801100014080140e00c01c1000900001002e400d40048030100031000250002450b07a000c0130400c48004c81d84036400415141120040d603140b103a00c080700c5043d50069002460700c040148420311111000b14014043c01d00ca0782c0844005103020311b40d603800241f8000f18542070b24103540154043c082503c00d180e50590f04190203540d581172402c80703644841e00400f01c40c0d0200c2c242d030401080c045044a80d0315511000800002c048a405003241c6584008910041c0c0380ca40c141c020b40345000001844640b400804904001c0c0009081c0b0803d4231220140c9504890182c0d140d808040022181856001e900c1e800800306240d400c0b041c085000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 786444685 1250 786443435 786443447
    0x1503180601051f02010603020312090301271202100603030c050c042a0e13050106120e1005091504060203010906090203060a17030c0102040b040603111806090f091006140703 76
    0x140c0380d0011082e60f0841d01c8058000d40050004640c0607084a4004410042c8050641c1040c180e603480f079403e0610380b13840b20381041040b030801c1020030790f103d01440d1b890741c440b6224080c001e801000c1d4040c0740750159544141c0c1c81203000545c06a1180d140c803071018542607003000c010f80e00052040345010758516954903040c0e051340980c100d032003201700901d0304450141c50b0b4071105134801e41c0c000f4040d52030407000d1000d41c010034100c0f00c40e92151264800c4030303100c1d002910120350304189503901044602ca1000c40c40c2d08130300d82000e1910103480e0400503105018580c200111402c1d9240c0350008010850101640300e180b004220611085040d030a00a0004814503100d00c40c0580901c804490080f441c10140101e070724428451008658480c0c4e10940c54100c1e800c944a14030100e031a1101e62852440e02d0b2040301c00110000888001524615040102d981c101c000d1254111201c040500030949440b9003543c060380058140ca60390b14904400148168401c5e8011510807005201420000c0e800030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 786445935 1250 786444685 786444709
    0xc0c0b04030305180105090309010f0c210909020d0b011e05040b070c080d02070906050909030d050c0417060108120f3001150801051509011409150318060105 69
    0xc60b011405454641c0b4622a201520410000f80c0d441d2100780854003034004001c25649600381c03a0402140c203041c1094601c2141a0406041a5000c410503c0451101c2c58a03e15401c1103082c41030070305866241602c200e0300004095240c60782e0302d03841d007143da41c1c10003c83c444420300c0950705881d4564045000700240202e100e0202d8030080402c48000300b01d0560701d080301400c0313050101c07881c1c01c0072254001e54442091140d24240c4d03140440114550502c12180c1d8841c11002d07004524100c155140e10b0028603009240480c046000d10001c2041d400d0708440c00542260000101003d5061000d2603082c02822109000440820051801c1010750b40d0140e8403070b5401000704580e0b403000d4080412540708d000d21f10030310541d28131002041140303007501c00c01600642c0b9030700c0c00c260b070303803504103206400488119021043e00d0500003451658425450500315204113002c507030901c2c01480c00721b03c001d8214000780c03083d81c40c04020045134104a4000a400da40d4460050a8552400c40404c0043c2862 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 786447185 1250 786445935 786445937
    0xc2e05241914180126030d050c0d112104020a0522050f15010c151d06072c06041205030c0d0314011401031d030405011b02100c03021203010807090c0c0b0403 69
    0xc80c00a035105100f8001d4900b00800550240509d180600000f000c55008401d000d072100d15004d00c402c1c10f4180c4a09690074024a4001041c00c0d03034078980c501040e0302004104903031182e0300200c085016241c914459214413014001b161000300d442a5000c141c540050080d84202d0741e0f801000400b000e51940001d1500d000e080a042c0e80184d81400074010f0441011b15039002e050801c0150043e2145a000c240810f00500b943d6047c1c8401c882281c1c10140d080401180b0540802d4403001c689856118011040d002000c81c1e01d41580c810040b14112900e00058490350000701e41c841d00c2c0d12051041521b18400c0785010400782d5900300d506001c0032418010103111480d00d0803250034030f9009038400340c141c01d03443c4c2d500c1c0c0c0060810900c003a80e0340d01c54040c241c000b61541e00c4603001290301082003441d041d4010424201c0382003041c42110b0a052182c025001c6101d220071021200342040004e6029103000400f82c000c150810300c140040d90b6141e61028100b140c80400e50022820b1000c49540242d49 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 786448435 1250 786447185 786447239
    0x20d14220302070906060c1101030b01080402040b010c0f15060602161e03020d1203060611031801180e0106091502030306040e030c2e052419141801 65
    0x450400b00d281210581000500b00e2500002083c8260402d22042c0e050f40310340c1c03425490001040c01101500d2005141602041c40800803030010702d020342080c1d601701c1e070600d032000f9010100d84411002001c0e28070143c0c1ca5002110501140750141c2c052070018001d01d000a00e0b40c08040030364802004490320506840c039001c20310b00700003044003000501c001d58004000c090400014200307584504030307500b0040e0220703207003140000700640203d04c0a0400e2401038003031400c01d6501700c141b11220000c81d081c181045001001e800034801000c800d10050005010f00201c60341c1051f801800c1041c1c5038001c1c1180c801060503102d03511394000101ea40c810400d5402090b40c49018000c40d01d940903501100c0202c1c0103070319040c0070301c05411503901854240c034040f0041104e4502c820008890059a0215001140b01000e29400411354065009448064048506040740c001d01a040d4405d581004071a1100302004a0380d515180c4506210010507800d40a265490049480070030400780301040070402d8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 786449685 1250 786448435 786448501
    0x221030406090c0b0d0f06080d111005040b09010501081923030c01141005030c0d1703070f110d0206060d0305040911090a080609120c011d01020d14 65
    0x80c9a000716007003d511214a100d42c64454110010700d03000481c000711303198589000c1c901010b003140200c43c00c81703030741d034000d842c0c4082e850804582103c1c0d030034405000c80c400d4032000820b1651710300c00d09201e0b50092a0b20a2a42002401c3d00c0c25180b040e401240d01c0c0d40300314545002c4484100c038026960303030f00410318071a92071007500e8607400300c212419903070050001003400d0f11003a0701900075252618032100040700d01d940e424409001c1c090703240295501503215400101070350905080700c00700540a03514000c0b4010a48860721080d0380f04541078000180114041310103182c00c43c030700c8405a00306402902c02d600c0040c100a680d150300521441c0b0503020520103205040c02102120050540b8a40c10b011202d46810410200da21078030009010750301d60800003620a60226404c5d00030f5400c1d070058006005440f00c102c220b608010009107180d542d49030404a203616071284003150040800000d81c441000d06041011210041c0300c501d00c02c41c103801003001c280e40754070f5030300301400d00c1d01c3d0000c10201c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 786450935 1250 786449685 786449693
    0x3020a140117060f090a15080312040b07050c0102210f041104053103020705031c0f0e10081803040b161e030e130b0631140307050102210304 62
    0x14039000c082540102840007401b260001980041c0b00614400601e00140d039581c1d20820364030b100701c00b190b14814601c030700490300090900541c10340081c02850320b1814060b1090764a1708a034001044041c080303480c04020075842e08020140395000c51101c00c04006032400d900c0b84100d91150394a03403442503a65100203080300c140c06100c6c03e260f84140c2e04103910101e00d1854548401080380e8180d0141c42008030000741e92074000ba40c21000500044813600902100383d00340c40d84009922814203000c5800082111034948030051140c1c80206d61b101121420541d07510180c900d100d51342406c080d0010401402000050780880f4801c6210b0300c4007441220450030510180015608600300710041b9500020501d41d0000c00802134101c200e4400c2110117411072994101c40c0300000b52608860240583c860703802080005080768a143d6041025000c901ca01c417059001041e000513404003482000c2c15504d0800b0071100740601001c6c00145441d00000004002c01a6000352102082c0c400100280c104 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 786452185 1250 786450935 786450949
    0xe0f0102031303050312090a0c090e0c0907080703050c0f072607140606030114011205070f0902270d080d0608060a0507031a0f0d0305040b040f03020a14011706 70
    0x15100c0c2c0c40d0000142c0c50703262454995010b040c08031400e114807004528207810104650f034665601420004600713113131101c600301801b0049425010350160041c050401d85171811464450305196031018164682520064200c1c4c2015055684d00c00080c4980d5211010240c100c40d246500421101c600701c2c140c01011000041341c1a01403920b107004504002008803a08400030000011700c196020f44d0745480170716088481c052041480142c0c20801004400388a1404100090190098030b581d6030b103e20021818219503800003e000f68002190f44001180ca900013140d20b03032924142102844845c0020050141c007940501501030004006da80d401c4141e001100500c5990180d038210301c1c2079400301c4014202180c00340c012a081030307002403404007828841c011060b402045600b013416100d041c4804004200400c8003840b80801000c18501c210707002400060080303c0c4104661402e520620a14400507130009045003442141d41485a0300071a08086a40440c2c1040d4102d0303440340006000c03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 786453435 1250 786452185 786452197
    0x1c0c0b0f0705190b0f1b030702030c010c09140603040b012d0b1209030304020108010e0709030b090a0210090b09060a1b03030e0c01050f0904020d06030506010f030507060c030e0f010203 81
    0xc203200790080c01c0f180010b0b20844440060003401c00c180325035140322002c1c074444000c0765402c550481c2d02680185a500c0342001e50f421000502c1207904101120307a8042c00c40d4041c0703540e2008646000300070409424108004160030320702384e6582e811401c1980c2c5550320141c06019100041c20320020a100324a00c1000190450030906040070b0166601c0b6440d0960b07512000c65603409007182c0c00064182607000003100d003c0da606948020441c0e103002502c19a8602c060180401c1203040e000000c01b04111015080c0120041340207010342d000c0c680f040205024800444c01d00303001441c241000f0011046040c0c41c8414005e41c1e01d640c0c0c5814804c0f0856046450050500451032100d0304101895815032212181655640c21640103081c46030045d500340c0910301c0c2801000b4000c010410040c2441d4002d4050305514a03404201d4a4503550740c14241002600322505215407010700f0400d03c0010083e0304d008000a04010f207070343c0d0840e02c005040d003002c0c00c03100f40601c0c200300203070348264820012124 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 786454685 1250 786453435 786453443
    0x20a0b07050a0807050412020114270405071b0b04051005010b070303061a0a110106030203030a05121e06010818010c020304080f0c090414070b07111c0c0b0f07 70
    0x296034509084090320580050200314001000070000840260052003128150b5419600f4407600303170305c1030b80110350b00350801e4900358050300e0900c04c40d00088075100300307007040064a07105451a001c981051004440c802441a01082060903900310503078402e90841c1c1c05d9a800600c9070815a90302c3c00c00324a04185070030303212041840c00e00002506120300010303009081c800d0b942800346560b59409003019a9100c243d40194080400c0050031150084500308902c560300c10011800e65a00c0d00000d0464203c0800900400e01c00920010780504109000e980f00d501d80c00d04a0046140261050860b40000c003068184058100800c058101040800d5484a0303100e00900640e030b4102002500c80e001440b07955a0b40c4a85510100c2c05140840c035100c1002d8003030259100c0d9615512650b02c0380e02c0901c004800d40c0038586c0d0201e110317140d00d8002c141190050001c04240c640140500c49030948800c0c0e1420f0078040440204c2c00203108801540840790940c0c0820340314100c0b803d03561300900c05c0d940010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 786455935 1250 786454685 786454703
    0x5070f030c0b090d1b03090906080d12090510020a0314010807060201290f010c0f06090210081603020904110d1d07151407021305060307060309020d0f03020a 69
    0x41010760201e84076a44900c80c0b0b0124960b629034845243d90f40a400070b540011601c85413030140703c080c0c0082d0405100707000385400b003003075035031103800c01b0440b2443e810403c200d4200480c2404100d4004000e03289170003426000304454001a02c03020313181c01600c0000101290002a6a2040b03031094000b0819891407148021095a40300c21060755000140708000c0503509025840ca070079240340043c00464042004903c0c20048000c040002c000c09a4800505108140200c0400301b940c52401c0e40c1c00ca8820b050009600340180100000603080c103400724100724082080005000c14064420741c00c0d0307030a00300035880d003224200190182110604008052801080940b12303401c080d00192005a12030341d0745280091200c1d0780c03546404460140201030301d005554004868421049500400346900109050102c0341d400030314009aa101507a610a0721074045c00258501803154000601080c14104000c000941c00b1808031504000007808022400d8214001d05001b48034000f1155440318201c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 786457185 1250 786455935 786455963
    0x5190c020f010e0a03021c020703080307050711120a020405040501020d181b0608010b2b0e0601090c0905060d0e03161109010f031b03060f06090f0b1f0507 68
    0xd41d15405540684442d60a19000d03041003000450180c2196405501501d055480d01100b09455442c40c844401148252800080401c00400c0503600500720b0b0f940fa20744e00c20346d81c00c01b00c441741402614984140001046440240700c0001e4440310598141c9011035030f81d5807802c041d40280601307903051b0b90142c00c20b8070707100780d038000d01c600122103d200c0c0c603a0306605841804280d190782114022240452000d0006110003040340740a03014801d1146442c0001e20707645038640c2c400d8100b071200c0404943e140e10000c0c00c2c00c0c0b0f080c40460701600d800d020402040405c0d58004011440c80c0c49541d006860016680318004031582103807c000800c14101c030341e0b92069480100c900d11a501040d01c02c04010414100c191610f204864100c52912401412050071511407841c00e108044040c020210318000010009055024880405802c2e0400080107441e001440e0705583d4241080ca681d01d24103d405421507450540760040e01460028184c044c0400c0c9a00b0346e42c0e8801c1042c0030b00040580304503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 786458435 1250 786457185 786457187
    0x70513060f090504020907080406020c161d0705090d030216030804170c090403120905120417060c07030c081b010f0b1801030b1e09030301080c0307061205190c 70
    0x104a4030581e607030000c0140d60b103a58000f29101a0340007540303c0c40e042d0103d10401d12441e00d103034009000742801440c05610804a92600c0c002d0641a1400e061183c0d0820850601c5ea21050b1640e45107000381a203890040b02c001c0503803150220480c445d407015107007030381410b108102059246000c4410003c1c115100e040280a41d04a8818222104124001403004610201c0c820b81080005050401e030781d01c5d42d84d0300f928003144c202c0c1c207030480d25960301c801c601080c420080b44d10741c1d000030600c072a034907410600c0c01164800040340c034500d01c0d400001030110b4405d00108882c2001e0301880d044640e00312a01d0603124500c82c013846400c1c441196015a0340d0a20107520605a4001d0b2050800c200400c40045c46404991100c200c000f0250711001000450201c1c2c41281c0d100034690a80c084054000503501504c1c90251003a04260b44040014080700c030342085505421007084000382400e52402000911032030f40d0070400c81800307441d140031600d0b403564002e11860080032040103000c1801c141c80 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 786459685 1250 786458435 786458441
    0x60f0c1201080115053c041a09011401170406021e0a03050106030c1d060f0d0e0106060e101b0f032705060921010c0c0c0509012105070513 61
    0x8144e294414240200050610300308844041c50f075407000107040c02c500c40407032401c1410309625000d030b141013000452050300d43c0c1b28841c0c00c120b0200c0242c2894103900d0b40062001c2200140c00650303001e88031206101450303802078060210b04910009868581c1d5072442d20f070010303005100707090750303402001401030800c0d04400c405000141400e0b9010001a0b07a6080c085060340d40110b280c1000c52040509014242039909518030740203809401c4500c0d211107002450007035401707485640300300342c0c0d12286414100421300401d4010009460030a022811200000d151700e2800c0701250b0034880c0c1801c0710014041c24000400e15203070070014403907a0200c0380c00e01034020440101102d81ca003180c04050300d00d01301c04000010035513070044c0080742402194024401c207a11400401c10300001200d0803009002c2c42401001e0051a00303941d50170f40d200d00c034031703102141c0c50958000520888a801c0140030349110b02440d881c0c024080603400700e80c0c40782c03424014204011034005c00d4002c040140140d1560310190 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 786460935 1250 786459685 786459701
    0x50d02120f031908130822060c15020c0d080a1b091e2102031504050a0c0605030f06101e0e010909090209150a0b04060c1101050705060f0c12010801 65
    0x10302002c1c0900140034100d03100201282d440405c2c003a00e65442c0007081507240500001c02484448030006103030400382c00c0c0742c89000d41c0030384009450b4500c081d040040e101d25038043c5071207400302036007072420420380b1307903142e85a0030608002c205032070000a000380000c0d0050700c845064122a02102246034400a20800e0140680c0b04000d03101d240aa801120b629035150032540803000072070365a5412a540380240c841c0410076641445220b00344240041c0f00090a03000da88588010302d1105101e161401440c0f0180e4000300501c6400c0c000c000d46082182481a03000c44116180700c0c0c0130901d000d0030b9071120600390740c80c0081420a45c01080391034001003d10f0000a007600d40c12107440c0e0717445003807003907412441c402034015000c040407803007001c4400781c11003550701c2c0188565026178552101542c1c0350010323444803000402110398142400ba44007922100c42c4000c2c60001e19041494031115030b90b0030040e01c820031a40c01000058540c0c1d69200c10b0341c07010040c42d004040996500c08405010703007191 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 786462185 1250 786460935 786460957
    0x90f0803160e0108090a1b0e011203020106080303131101090e150f0a0b070b091f0b0f090906060904060b060c0705120102040f06050913020703031a03011104050d02120f03 75
    0x30080482d580a888198480da110500804800006544100060300016031342c80c4801c06030b03034022405040030941a406817401805c11100c0ca943c1d804d0080c207483d40c81d8080b0f015600701308107020917034800b010201e4009070400e0b0719414100355600100ca9544240c2c0c407200030307200f41b41c091149508550a5100c502c4408484c60b1001c034102e0410081d420354203220351801030b44200170100008007200a00e550080ba41403d845151207418040c114283d41003801044641d52441801e407646403061b0008260070055407006000c0c030342154490390f5a000a0b00142c814400b0b24006000c1003640d4101002c07440740601019204d50300300c9140e955465941c001c01e4402e1395201c2100d912250144203641c103d076084459101041d182c1641698194000c10382c0d50782000703a1810044907607000340014110760303110b903800066100301e05500511110120814501c03c3e41050010803a160000c8251000d94004580c0d0031001c8040f440055968140c0c06800142d602440070301d1921003d010000d0441d03aa68 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 786463435 1250 786462185 786462197
    0x302150a15140d0b1302060301030c061b0812040f200102010e03181002030409050c0a23030c0d0e0f010207120e0319080c010f0c030e160603090f080316 67
    0xd0300c42d0400080000d44086400107440040e40c00450382485402c1d40009500603803128142c1150042005548260000d030f402004002040083c0c80d44040403070680042c141110310b040d00207a680340d03080d1040103c0e030304001c0a1900031600f48034104100f036040541c40302d05655808103c000c894881500720710308a0265280c0030b001c1c44602030200460302070a0729460510941403004041050003501c110342741003144018040800d49004512800d4060b01050640c0c0d41c07600684000100b40550700f84007040443c0254040a00c43c0c82c09509994100c42c0310000203440300100018030b00104582400000544580d0b03030342d48000c520641c010080c850007040030488000070440f00303445da600c0124005406078894115800402c0542d000120b07040c0c800c10015183c9206000001d00751109101c00c1c091640d565034001a8007909403043c14040000c01000d4203050008624a051000c2c240c800e4a081c542c94925240c1080811500119196440f66400b610307400c142d9904500c4009060035507004c505 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 786464685 1250 786463435 786463439
    0x40618061d070b04090e0a29060609031e01020f0f090a050a0308030402040b010c0f030305010e330406030c093603030b01051605150c12070c0302150a15 67
    0x201c0410ba600550f07070110b4030145000d05c0c00c0303140402041d0181404449000f006810b10008034040003601d2108008403862000b600343d8281c140c07050501418603480381c04200705000c0152000f150828440f0400030354950b806e580c8080c158007900c66444401082d24002445041c000c0c61000902065903094070400c030364603242d50920044031103c0c00058081d403410710010b001440c1076000080c02c25810701d818009090341d65035007420245c80c00d03021000b20362548018030840300641045688850f0804458682c3c440000e81590041c00c0c11400c00b00740142810104030301d4449400c11001154090010085280c1d04c140010042005540c0b50b9014407600124401c10740650380014030850618460a00a0907295426001005e03000046814400280300d106002a41000382e800101d0144004d013444854181c454a4440d000400c2140d00c03180c20310602d0800d40030001d049901400c24100151a007829040c140c0c03408110415920b0000c40301d0041000020164024840c0031074070340a102d2602c0d03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 786465935 1250 786464685 786464741
    0xc0d0c0611070308010311060c030d05060312040b09030606030d050d090f080c1c03090b011e0e13061b02070302060f04320f10050702040e01020d320f04061806 70
    0x22003034170081812741d4414000b0a400d1151a807016410401c0101181e18650124500903a16005580110300f0039102040d40e5040f424184101540a00e04400bc1c00071400d5a03080035005000741c108103851036584c2c1d06440104401c94500d4500a90441485901c808001d0b0b019a0342d51414866070182d0b40c2e06d03200c2002d010740203004452200c0d6122160804176030070320b04500c040c2064406100f8514640000005461464800080c01605000301d00c001050342420400300342c40350340304c80d101c9490420108041c02c2c0e0b80403641000b580d078110b034481e5696a0360b95803881c40d801503822118001090807140e58000d44c90300040401c540101d1070101c14418560b04204090b010845c4582d002004d16a01ca50160703c61801000407602c0280001207415040e50550b003260002090075131203035954100c80d102445602d1010044041c40a1b0301507014501c03240f003418070100500781808880f240790116040020642007168200e15814855071554031900b403410250081c0203613543c107007507001c54108682c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 786467185 1250 786465935 786465937
    0x303040c0617011d090a02130f06060e06030105060f0d0c0f121a01080a0e0a0c0303201009060b0418060c020d020a14031207090315020c0d0c061107030801031106 71
    0x1c2d824814010300410054a071000e013403000901d144000d020300c604040050b50b568011211014410b05d0006858941d56003120450b2401e4205406001c2440325007a16560f0703101c11241503e40680307000e84c99804846069801e4094516054007031402c00c403114032559030000020300319001581e81c80c1d100325a088404411904d4030a1824a21010f141c800b102c1940540702494000f50108400101640c0711600307541050851142110f89031400c410070818140e010544080b665071002e1814000030039000003540c2c40416000e1601c15503140e1030104280841c580c403031050007030050b00c1407183c13007010044a542039003001c40484801c0c0c50880c0714600d50380300040d9456801d995800411102206132902c2c08220300e2480183c20702e1104015001c0312060114289018402c01d0322810b90b00b5041d40381c45910700707440d02081805d035841030000034070301d8100280031280074026080c030283d00400c50508401802c070702d541400a80c1130000e032140401d83e00c0000581240d015141d1006032001c034404001d45 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 786468435 1250 786467185 786467189
    0x9020a05040902060d0c02032101090f06060203070f080d0f02281706030709020a0816140d0203060d0501020a0c05100504050c01050d020909042d0309090b120303040c061701 76
    0x3c503509100300c01c0c0803d41c46d48a10148129401103c2c180380e8201c0420211044e4030000c3d0b81d044175240010811010f880c014034403045880303072040c0005420004000d6803405206409040020001000418404800c0c1103442203a08000d0078880303811028688006580044419032002500c802e000813071211400300019605d010703036290410426449841c1210803000b40c46254540200640040d00c00c000d03100a1002080b66250490f4034900703040d89845401101055006001c1c1d5800d03142c80044843d012203011908600c00161203844420110fa00f00140e41e4004203e5840000d524020315002802c03640c02600c81c0b000c46420300307040104e000640d91300b5903004105078443c2591480c1c40d03008401404203442c1c04500142801114000504560303800e8070180d0b1801c034541c6803003a0ba105201e4501c00e50100b0700800098180f465038004000c800584a04416140e43c0d0003481c0b00d42e07440b5002c03441d4105c0b05008aa40720704150400545080300e9100700c501180700ca001c1c05c20542500f90490741 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 786469685 1250 786468435 786468439
    0x1603050d0f1130150103181202070801110912030d06090f0b15040608060303071a04020414090604060c0903060603060f0e0a0f030518030a061b0219020f031e0109020a05040902 77
    0x24440c0c4502005484e1440390700f035444d0500d9143d441d0b81d1120045d02c081a40c6503801342c2d42412403803001c0c010283c03d15446400c1a10141d0406407492500031002085403e0000142d4082c4c01c06140b1618076810b502802c2503c00c0924108100012000800d41009a01d0f201c07508041084100d244104040c400c00c40f03d481c5030f500f5080c031041000c0ca02131036106034007031000780a40c0c0c504425980c03900c4454045215610844440c42e003448158207103803003070030425140145588000e04107141c1060342d8040c0200b0040c1030300c1c1c580a81c2107945104446120040d81c0c4044107000c925224070700900a080303505001c520f0b403407800d4450044132200180401007e6080302c1c8290000c1c1140d2021500c0d0b5000e00d694001070700f00700c0e079803200b82d8071b04016039028a8024000041c2070b0884080500300880648030080442d0b224100b403140d4202550f1140313000f164100c824002c2d54004202090500c1540c0b0b0701d685c80704010b110361b66421a030641000c0e251a00c200c9030704000300c0e146c1080100b15080810701075 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 786470935 1250 786469685 786469777
    0xb040612050c04021b070e09010c0305010311100915020307050f070f1a0909070c02040e011505040e0c090118050f1e0703200d0b061603050d0f11 64
    0x1020f81001d5000700484c0c800741402c0381060a02c030b08160f160020640c01441c2d2404120201302c2c2200f000c1c886d0001e5181d40389824402c552454031072200205022401502c034030a0b0340350858506008800210041c40b810140702103c0c4042c07000030752a41c1010f8000d55507030240d0074040800700000f00b807601c1034803484440c64584030709010380d00b1a01c055800c5901d48046082108082c07070307035460703d4041c49204903079990304005002d0b2051000303990354024810b406078140050301621807042c010640a0301da041d14001902401ca400c510703e018580084190071002110010440b841031443c0c000480e8075010061107a5100e24204031102c04003102c0000c082d8404080308001450824407098009800d45000b05486545854005e00f40c0141d540500012000190800040ca401e00031560039207012030303807a41850742e180b580c50380000043e8030044c108000001e010007012030b80d500a90310038031005400c020a21a810300c807181d5a00c40e000494006410b01460380c240c13004c0e503203100c3d40b070901441d0390 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 786472185 1250 786470935 786470953
    0x1815020613170a0c020303040b0a1814150904090f05070b0a05181315051801051c02150c0106030308061e10030f181a04030509010f210b04061205 64
    0xa00042d0064610f250411402c40c4600000d65400c04c0940050840c081005d82e45240c0624090070312610001010b80400c08008100700c02e000b00300d00d05004080c01d403000540f020728082020346a201c1c00c8140355010380f8064104083c0000c82c1c0c1d5000b9410300c00d0044501ca640c03103076660030442c090011010001031041002c01b58003030404080110802024240790159001800e400c1d09803041c502c800c41144bc4d81e40004c101a00c2c202c040440c8071101c0350306841495040c68041251001141102c051803008140c0c6401152142451550000d004200c803d48032100c141105010385050300c4150000b401c2c01000c94414a001c0070b40030419402c2d91320b004400c000e01000e2103215142c0d84e100c1414540c1d1541c02e956241c20034007925038030506900303041e005402c842c0f42400940c00755109200d400b81c844000c02002a4016080f5207482009081000b456400d03180c2c2107421003102e40710548481e1005440034115400c0b03400c800711030901101c042c03200507110f843d42c182c10814a08080d0081d480300201d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 786473435 1250 786472185 786472223
    0x6041410050d0c03080d050901060911180a0503031809071b060f0b12070f0e06010912061d0c040605060c0a061a0d0f120504030c05010305071815020613 67
    0xb0341a2000d1003401c03110481c50356a15034944a4010035031000030b0a8440d010408511401c1c805d190141c10108001c01140b682c3d4802203030380c2c0c02441c11082200304140080c400a40d1400305003401400002c04482c4d940d0011101c10903100001c04006005400240105204500400700d840c81203c2507042400692a90f49980c0041c083d50126840c004e9950009003000da115940b8410045500d01d0042031843d142074040c60f0f54208981c4240156031014043c025503030b80c04906002120350a00e5041c014105506212000708145000b8100400e12441000301281e03021440e4420380d101141c080040d5030740c84007804513520501a100200390440410180058001c1d8400401071421080c4e00401202c000c000c074905a503440d030256004404401d401081080300c3c0482050035106241042c14249540e882030341083c054001c05052580341c00021304075510682c1e000c0e4100300745603518040280d44002c424818003150a002006010b07880008a026054005001810780d001600c0d404203020010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 786474685 1250 786473435 786473449
    0x5030705090109031209030c0e010510140906040303030b091006210e03070303051b0a0203072013020a030b030c0a0509090f010e1b120a02010311040e010308030604141005 75
    0x5072190501110820200104949a07200d0a50002944510308401d0650a100c8001c0480c0d80c45074040b1441840148000e0301c035030101210b503140c1d5090a55554140645000c100d002d10304046400c0480030038000141035040d040540490010303100b042442e1030b221640b024810080c0106008140c0e52041c4201c00304800c4500344034420403003c00200703102d030104074074110761106900307500082e203a1041c08900e0740051241441c11481c84101031404003a100003944034000c5040140900004500003032003d45c0c018000703800d06a00824850811907042800c0002f9042103009a000030b2501c040070210342030001d2031020803800204052880c900c0d0200300406010b000b083d070300b003d000c1c192205060b0902402218984035484001c0d001e820103030190440521285280c2d9446211000c49604501d140850300d04d082540a00e0046507080010a002d43d041c4100d500560b15005920000410700c0a41c1003d540120003c8a00748040c14100c3e03012050749800362094103003140e181c4010030051a00701 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 786475935 1250 786474685 786474697
    0x101a0d022101020d0f05090f1c050315061306030b0301150306020c01110d0b04114905090d08010b0d090f0f0b060a0801020a0215060d0501182105030705 67
    0x41e0000d0303e8156566180b03003d0783c00c80ca090500a5403560244250140f050241102d00382c0082c00074690300840790f1041c000070000000e480c092040c008081881c0b14903105680c04400001f80c402582d41c1e040c62801200040d040c8642c0d0002441d01c4000d249030301d01802212003403041c41750035640c11410354131a80025400804658402d40d0b03642c40d450300d5568040060124171815010005440b00c800040c4810f940c0300c008500200001080302051542c004d02c040c20840c802d5403a50910424980c003801500300c1490b03181000c0c1e82130581d40201c607100c1c0b5003105104445541c166400341c4e030601400c1e109403000780280307548540e003440603000500070b65210800c0f5078043c0034841d40c3c9101c2c44c1c031007403060b2046c50810741e80c0e41d4514040000e00e0a1090441000b404020300851a02c00100d100079112034060400c9442c40340c00c0e070701007510b43c0e42d90150850903d40001c020040000f1405117a5540151380c02c00720398850100d0410540401000a0000100200c0d220189140d55203401101c1541c414 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 786477185 1250 786475935 786475999
    0xb070203070b0301181802220b01020a0b042306013c051003020d050a02030403030b0925020c030f152508220308090114090703170705101a0d02 63
    0x440107800540e6440c04200c1d000c0e070b81290302d040003800010123142564900f10010f815980107014201c0091103000d2080e40c400d0300305c0b01014003281c1a4406401e031012201030300000d442142c001040601e2203040345d006c10000b1010301184654001b808107807401032003004500e180fa4040c410000390800340a032900001e4185001480c0444a180c6802103038000c0c3c2d4034001b1030780c0c00300030401010327010710410a52110848011070245440420014101e94484200403001003441d02050201d0007000701c1d40c2c8070840101170b2000c0e9401d0328600c95440509035550f0200c1c0c020100803400380d0307a038201c4488501d5002d0750b0107100b4403a1403500381c600340d0018004204400c40d0386294220b00400703c011105041c4a507903080c0c0c55041c050100343c2901e017000c075031240235140039080c01010078002883d0000c5a5020f103155450b80e690900c042c040d40100e10002e4180e00500300c1b03404a5440d103a00124100e1020310648003200d08a0003480303190462a58000c0d0000d07a400011440f03010009018040002c02d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 786478435 1250 786477185 786477221
    0x1180b2e0927030207030b0109090f06180f06090204060e010e041e0203030a0f120b1c0f020a0e0601120c050d0504150603060b15070b0c0304050304030c0b070203070b030118 76
    0x440442c00b0042c40184800e5006030081d1009108200326140030a004200541050080c0007683d118850000d541c0500200102c3e0f840384005010800d00c410700c48419009981c0c0903038110181806405400f04082c120b01c205e1415401040f42d04e4511000d40c11790b01141801c03010381e991540c41c0280c990083c4015200040070600110069900b000200840400d96440420b11240c221024064201c40e1021803070361401c102a096158450100e5004011703001000101c400413a81400c44170075160030340c040e4108103514004181452082d80090049034283c0c0e901041c0d8461280020458407801e4240c00007076810480c00c02c02c100745030030458009021700320020b24003803003040d00030072034606900840364542c0300d6103518094903160b00c0130011303070020244061074071550742d84030098004000c000b15042d030404001301782481001c0041e00c018640c004520007400d62076800c041c0a907001800224440d00c40d40101041f140d4041081c1c0303040f00d0744000c0d044501101c0c0c1359503101411b6102e509001c4441 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 786479685 1250 786478435 786478481
    0xc0f0304020307150c06050c0c0a02010c08040b040e010f06080610030525171509061003061a03010311010306230102280317151201180b2e09 62
    0x3071040f01c44d40340714603903807074200e80e4501700d02c1c004058072030047c8081c0c0c107643c0c24002040d105202050b1040001e509207001c99150800f407500c036655004d00e030480504c44001003000301740c0d680314142007416070345039284000d5025a611021502a54100d503d01d0700041a51060310400f070003508020307040680c1c0040d00e03042c42e80312000d01d41e2010203182850009182031800f07040031589090510742203000c1000c241490355028011400740c2c48080c0c0042c2c020746008103c041d07803501c243c1c080302c064903100701c140e40041c0d00080e1019540d00203000c20384160407084034020056004e8411681141c41c003040010004481590b08000301064400300c0d4154006e1012401995400403403108100c0e4903566142d14220303903420020700c05c0107070120107403080c1403110030300400c101c02d0400141a4082101c4201d009801c0c0440b5034050280f5901d101070300591400e000301040440f114061082102003408600f41c10214000c4026402d000d452802c4001414400d224002c0380340c111034610b6840403c02c0110030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 786480935 1250 786479685 786479699
    0x1b13020a03020d05091e03090d0b09070305010f050103030e0f0307170a0204020310141801270c0807121e020705010b120705011403061f03061e030501050604050c0f0304020307 77
    0xc1d10807225640f01b50072809043e036445104402040c2102c000c14000c605014054000c6941c251503004007900041c018400144008800c0000748091540180207100b44141b03030100802030a000e0100f100415810b00034601642001140e00300d00c408006c005001240c50700303816016540840c1d03d2003c090141c40240310150700d440c0011809107641101c00c00c51395161003002d02195024003285403107410007580f840c40d503045034107074141500c401114114174005541c0358204907440c6014210507242c20104694961a0001e100c107102e02d010361070701e042c42180d40750054210790071444820b49810610f40345000c0306000f6400703030032094803510000801074003003000981110116807078181980d114074020310503542e0000d008172092003010391003411824540001795808a4054209410141c110f040c0f2017102d11a821281c02400301c0d000461200c81c010005018082090206450039800c01000c144217080901c00c0c68821011041d40341c0c108030032800807141030390001e48184c2e403601c220f900104020b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 786482185 1250 786480935 786480941
    0xf031b020a0b0c1b0318060a051b0a14011a0406150c020d051227010f0f0210060603150b0717031312030905060601090b09040c200c01021b13020a03020d 67
    0x40707205034004503160204d480007400070400901901f80103000520203081c10a40150a0700c5199160894401304060072061141c034003942001e0203000012501000c440c9040194031018540380800b904030290399110043c001035410600c81c01c0c451a0070300e02640ca00354800d4203018811840200000301304001500c503a03140070700d80003501410f41e40c0041e0b12001c1409510b40c0002c080408803a074484480c9190000e00b40c1c454500003c2d003031000c64203441c00d045209112280f1b1001c0f60b150300304181910351a0050003403581e921004450045140c020500c801010705880030641c4c440078040d64906854502003ca030005400d41c68244010030940002074900d00040461a90690f00000c0f12800b9003800f5190000250107a81485420b0b0804c4c800040140c04444500c4007d50f00400d500c84080c8088500f1014014107818403089034041071201d40000c240411a110260b00303d503c1c00040392026050f50000301141c5078000b0b0340c3d01c010001080c0700d4019103841c60080c240141050320180c3c1200917 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 786483435 1250 786482185 786482227
    0x10b092808100e03030705030a0e010c03061712040b0c12030a0f0605180609090a02041407020f030f03070c060b0409111f080f100f060f031b020a0b0c 66
    0x14500180e03001c0c040100100000c6000e00b00c001c505100e841c1081007030940768032002e014002048000070001d1150725140d0410002ca8054000804c891902060001c00802e200d0242003030b10743e441503040701d10b250001061800c846010316424a013525140058040e507002e00d031403806a00654020410703a0391904091442603032981030105101071098214021a41d04d5000688500e40d000c0c14081040d001d110081d42c00311054400d80010b8858800c035600e007901800740290f005040401081540075944010f0340070f020aa0205c50b941e088044055880e4022640011070005052000604075842000c406540b41d00807540001c42006100c041025140e188800791100c1d00e4000c00d0400b1800d15040c0c05020b246049a903c1464885034001000a6400b40400310301051000c00706040400c40b404001c01001c2d103d15501d07855076602005070000765400303082d0300860b01c0e06210005480311050740b1102d482456010b000801900e0b80e0b12280108090840700800a06104820240344038100d98030b6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 786484685 1250 786483435 786483499
    0x50402010c080a081603020a210e0a030e0f09010e0417130b1c0507090915090c021b011713060e060a0b0a0b0f03040f030219060207051b09010b09 64
    0x40074940000004c8140c03901880c5071782018070410500480c0380d0300540000305d01e581c41d5101c81d92017581e40710800203005a04070900803805180001c81c200341d0490341c0004002070541d07203001240070b004100207010500340b29110168000b140001c0014080005580e001d2021842d01410140003d1680c1403034000c5400040c8480000120500e811801d10800641268180f0341805a4504401c00800000d95403049800035502c503510b00c100c8859070310b2004090100010100018010340d04000d64981421000322000d2400c1c48405000c0d522a112448190030174a03030400650300d87c0d9080420082d0300300310550700a5500e524402e05803405102a0f070203202d51302d03008285803820208101025100343e01010701c445c810440c0151225189041d0303644603405c01d16089012015042c240d051900c5605008020440d40c1290f030104880f0341e028000b0180210210740c080c00382d080c10101c3d440381c40000a544601020010400300301648010094103e01500c408003d1a8081100810188840142e0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 786485935 1250 786484685 786484697
    0xf200a26010302011209050712170a05040509090703080306130212180d081510140f040f12051c0e0d0c06081023040b1206071b02010909050402010c080a 67
    0x10941da4444170510050400000400c00c0c0c0216654095882c1c84030302c106441c00325810307280e00a000427013041080c8030030305913101a41c0d24400705008101e60b006c0d0144500c2942c0c004040f51858a001031401c0139290300c08045441c58403200200301c000c0101d00036003507d00c0c2e020001030440005a0300c401303005003484072000c90790010b9030302411300f8203000c084540c08001050301007015444407070744002480c0310b0541e188101b003001440e003100d510340c4404107000d850100280c19074000f204034004200b04c615071140c00c07450780d49400341c40000b865948400b504c00d03846165a980213540c45003610310b03070308114188402184501001f061448072114400c1c2c0f20080004400c201458000c248294003030007050851503c2d90401d01860070b0303448181c80b0071200880820340d582064580c0e5001da048100000d04154000050010550352001b00300c4140000408100800514400301d44400303241c0c1e41d050f128580714500349240302009010040050341046a0392110a0100340c11000811400d43c01d03650360 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 786487185 1250 786485935 786485939
    0x41b120c0611030c0601031103010905150601030f0903051b010b03011e05010503060103030c0b040503040504050109021908071d030109080c03070318050a0312030f020406050901030f200a2601 84
    0xd042440d40e0341220b0080e400400a42d07620031000705a031815a40e00c110403515540051010900600b00d441c0002c209100c0c02c0040c42426410b6944240b148209a9051207031101101c800c006580d0354141c000d000c55000e001d440c0748a40020b107800d50b160b15503000044c0500c846030000b0b007901e4408049000042d00310701380000b89515400780d540901410360081c00e9a52560707034000e2010011120241c01c4501d0840800d0400c00c050040301c0080000810510007540c441c100c0f000290301030441d610340315010703402080440d030240c0c01c214802c41840e1580d151003034240428031199407040e65190b1740365580320f20410008071044080c0464112a278010342e120181445c01a1500e21801e14079500d80b68092003c0100b0764070410344d64181ea80c06400980c00c601c03000d50681c0540aa1146000b00500100d00819070652280140a000000b43d8042c00840280000e1381c040f500952801c40e915888043c0030864035a10500400150145107408028048202030b2212406021301c00f44020300b09401c01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 786488435 1250 786487185 786487187
    0x41103061504060f050114070f061406031011030c1804060b09150c06060d0618150c140a0f090b0c1e0d0923090c04050108090312041b120c06 62
    0x543c10103081e0114191a4007810400042c0032030b1891000b5842442d000200c0d2020020803110200c1c007a03901c65070600090740c040c00c0c018203031502104c1070350103403140030081c1000510342d0007121426a1450074076440c54030f41016030b00c55540501d06048200c80e40f201c81310433540b03880c8180e80c000c20401d0ba0160b11004c42908002144003400d00b611080c0c80c0912200c040350f800800c05640200d800c5036002c069081c00d01e00b00c0301400c00c0d2a03803c954101c807104048188131791040d0b00c60b00800c2c920020802240003103415907181c41184601c14a00c4014482242d10134010601c103060a04a4208600c900782e407110408038560100c80e440210742c10503e40012140025055019200714a0004e030820900710040181200918881c014194802c480c0d03c45c0c0558494003480c4114038050a049041d24019620b004103a10922515002038403034400100d601001106603a4a040c3e0030115200a4540d82c84030049003405d4401941d604800320000115845c01c6d84408120500c1081031290320351a0a44c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 786489685 1250 786488435 786488441
    0x20702090c0919080703050705120309061c0903031e0603051e12030727050d061512030c12170106050306031c0201050405010501060e03070504020c0a060e07080f0d080708041103061504 81
    0x110090056801c0d41c20929001404400d4508064059035640c0c0c0703813b4480c0381c0601b41c01002184500c05071500d00c0b4502450780c9a080307803041c06010110f614039044144120411591603220141030340e0010384129006204110300200000c00600440e00003d00708024544280e1090741d10744081000000250101c079440f825600100440d200c0d40780a1900d48800300d4410741d0b401f44001c05240d40c8400c030382c1e40303441d200908102034060a00301940b44a00380c40e0180189107529010796080304a1046010f15034032038a502d42c1052010740d1464041d07442c101040da1984c0014000c2541401100350298106441c0315210840c00419030020039541014181103003101d40c1030702700108104010382d540c0140e4800258400840c1c4040da0016034410078405142d040050102d00103003502e051641596030031400007100c5040e560220180c41070306900c0c200d45a07881caa005810004540c805000458480c06203800c40c1c0d105008800c4100802039900000c0d00301081243d003100b824a40f0042e0b44010f0030544 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 786490935 1250 786489685 786489689
    0x2016030c091a04020702011e030207050f1c0818101a0f03030901050c03040302090a060f062a020315040c210c0504090f140102030712020702090c09190807030507 71
    0x20410040d110030410111210030b80c1480703050003203400040300700459100303914501e0f00c01402c01c00301c20400b10041008019610091095915124503401100f4040021885883c6403c0080800c145c03124454000e90700d05200900d03040c0395212419540c0504082804800526414a14005181e084441c00ca02041c0c800d43c440a0150144c544030420649000040301d4403180b090800c0354a0311300519800c0c1c81e512413500700a401120041c01d10075464030b6070300040191441c42c041c0c149400e03151b080031610884185150004040840a508196850740784180300b000e001405a07030000c08000e18180014809403401c8444146150003045681d000344c4000b10500b4241c0d41201030242c0ca41c070307120307800003150059912461b80c50400c201080700298a140031590b0120342a8400210002918001d4000b00c4461000c00c1e00c1010030703100d4444910032038040c150b00522883c4281c580d8200c400140d0007400050f84c01020050b10003c00c90411030050008002d03100042c840c407821460014145204c50b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 786492185 1250 786490935 786490949
    0x4051e06100519090e030c0f16030f03111912020703080d181b030201090b0408100c0210020424051e0d0204090c080f01081603032016030c 61
    0x80024800104818800d00e402c542c411544401207900d050441c441807001030307000840592406426503144000031000d06001c01c0b114050740d01e03850185100070f4444c1180c80c5c1110b103521640c1e80c140001810341d200000c24500030300d4a0707d101032824650902c2d00e80c0450010484190700c203019010044420708150301c01c01548003402c8400c5c80c1d42d6500d4014041c404c84a0030307168947c0b54880c1c8804117054035114947d0008006902c46a01a10061a2182c503004c264005498130030040b544490400c1101d00715103641000b01140e885100c8000001c01c0400d04170306c21070290032309103982d00c03500b40054400740002808034141c1400c1c07a018008440d1340002400300340f08080c060352419042585065480f460b03c0550f03035a60b025003274038a030000c0c4616000404003d25003148140403d43c0034484500c90035501031820340130f9807910700c250f41d265107240f43c1680c441c604d1001800000c1c405d020b0b0035000c500d580300d0001c10aa980007a40e00340800d43d80c40412040e420300c410801d001200807500024000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 786493435 1250 786492185 786492193
    0x140a080a150b09060304110312030f0c03070c0b130c15020c040b0307031e0b040605150102070302060d110f0d0b030d03050f0105091e0c03010807090204051c080c0604051e 75
    0x94000b12161030300400030424426200400010140404020081c582040040685410344004059442150002d46503040c03521804400588110700b044200d81c051490358541500382c14050707aa030a13071900002c1c007291220301c3c1900c85c040059940440380300500707600c2002d843e452610081c024034246009003854071482c2080250f1040d52008651502900e401c0303a18083d02c190410100c0038405502e00c4c0c001c007400b0030f0300100024016a588200d000c0d650328807824040c40e4001004903681c00717442c080a0b511403410490300b1100c2c8100d60182c841c0c0c155100b081801c012803000007400c1c940000d00307850521a151041c8c54064a002d00c80035020032601c0c02c00b008681003541d070320518502c05000d010300030550340e00400c85211840100e01c060402034919400d403171414143d01031080d0020710540c8500d10500707801142c560502d0090300c0c1513441c0a403401050940303070700c0d041c85c0350610914143d40d0004100701c4601101d109101d81886035000e040280300c2c5140d440d02d501520282d48200d1070321030f00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 786494685 1250 786493435 786493439
    0xd0c030506090609100e0403050403020a0506091005160203030c030414150316030207020d030e130c020606090403050f0d02071e0503070210091e03021002060105091303140a080a15 79
    0x1d0380600194100c10140c4c0c0c0c0b0460f03039503016481025020b10381c0107083d010780040204020194014001d00a1340c1c0b090307984200b02c99070750062000c28004c015199610024031010341c542c5034400c80160180c1d05580303c1890030400290082425984440c480c000d16410010b02407200070b2403007003400d8a02c40103032803080400450140c0702800340006029140c0881e8400b8141151903c2074065441c40d0350010250507014100c1d1801800302c0700e10f0341000b801004006104a480f0300d041c4507480e54049260043d200c0baa0320300b01084a2980018821800d000c0700b03010501131080314401401070783d8a250001a07540f51030b410070076001100c0c212201c6003c95040300030300005402005480714294103503140031110301078240503110b20b6519040034a2105a0190f0721010028480041048138029164110034412010f007c80c0c0720074090280d2500a0030a00228681d658009180f42031f070b9020740760514400859400300071841d8001d0401c0c1c0b001030f41e0325081c411082d240f4444c241d0040060042d03052414 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 786495935 1250 786494685 786494689
    0x3192603040f06090203030904020301090e2104120f0f03050a021c1b020f2d0f0f0108100819060f09030206073915110f0a12060b0d0c030506 62
    0x250002c01c028070305925401d0315400c64800300280d4a01c9000204107645035a126449103006064000c5051ba491250040c24800b03500d89400ca0911a00d00c0f2110714649400d11600300f4160400100403a0a000180d0104001c83c603800b18404029101c2c0e61400d0351022020340081c580201082151015400b074048401001c1d0805029894540c2c41c200c4089496850700003da0b4040f039074905280c00c041c0c031021099003131640948650f01c1c4c1600c0c41c11090000c0040e81440794140c001800d0030b41102d03d014800b5405c0d805051840d511000446501c0d4941c3e8660b54458200a074a00c0300922480502d4982070400650b801409400320034184100441c00540e14001c1d5904000f80c0310006000c2e80c2c4100194070341e48080d0105c0d0f070f40000c0e910360f0040c0c01088110603c14a0943d425105042c0b0b4903000c0d200725605019101c43c2c14000780e00d55092841c40c1c1030388003481c0d205006200900103861621441c0c3e61090042d00d0081100300c2c428ad80390f000441c8490255940101003804043c03800d000c2000d65 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 786497185 1250 786495935 786495953
    0x90c0a0906080a0b0a08060603121206010813080c160b07030207060305090712080304021503010e0c090f1c03030f022b06030f0c0807050a03080d0b0319260304 70
    0x311424505000203442c3d41d40014010621401202d4101c45400d00118402e400000c11600540003a4211580001862840011130140b031900405440140380440d180d90300c00e242d01034001c000114101c42c44102d036a9008019071000c5a002c4050700507100b007440c0340c0a84040200100016000149001d0041c1d400039204c401d82d0080000b4036a60f0004102d181204000d840080c02042516004110050800d100240c200711400c80c41101c81d101000301243c0c101068030b040b50740d4002c0300d42940c2c031002c108200c03e070089190716400c48482d0f4040350250f0350fa6085142c041c0d050841c1e01102c00410b060041c1650744042003141e016004000c010324a107410820000440c80c0510410081940503901e0005020158006089180003540d401d05000301e0f014078400325001c030740c203c1e0011680c44d020311820384003a1001812040003130200700d0f881181038000315000040242503404005501c00050801d40d0300d100b0659044d05180c12441d005440d08000f2801e14640303500841c25450f25030384030350702d0b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 786498435 1250 786497185 786497189
    0x3170601120e1608010e10090203030a030c050d020f0706050718061412010602070f092007020a030b093f1c0606110118033c0302030105090c0a09 64
    0x4035549100292111a05210001101c5080d80d0801d03d01590f905420340030788000290541c0500481c0d5115400d08240d2058050320350340a0040e500304103020106074010001c803842803060020410030407010845070b100508081d00c0c401d0303400e51180d1080c02e0036022184000d0006040c01550010f80900d894803039800030485450b40f40489d166a011580c0c0303039080c041c04607003905007001f181c00850b15503004079100060b1601c0001410341c9981e610300d5141030b0f503c1064603881c41418a88014aa03001c1140105038047c006001120100d03525071340d8595051b0300300c0b64a14240c0102d0f001c8a02d203000b10955a0702d4401c0200d0b050f1404480c00c1c441d0750310400d0412030f4070002200140f010347c401c0d900800600c0c0c1d100310450412485648180140221100c2c915100481d40303004000c00807078407c020000052a01a510018400042c8401440039241c902d00100300401d80300852008160301d4809042c845030a91b0056140e52400041c094800301c05415400c0b00c034800c0c000403c3c2280d22016a80c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 786499685 1250 786498435 786498467
    0x6091104050f282f0301030b0c071a1006170c090d020112061509170a060c030b090c0c070501050a020d0513082a0d0f020904020a1d010303170601 64
    0xc40042080100034081c0700c0d0802d001010350400c4459280b41e030b89014100c40c005184007200c18080e030b1344030700300c40203110900009000c2d8481b0000302e805408000054804244120201c00c40c1c442402ea64019071042151480d9010013403003000c3c001941d101400c0c14850340600500aa41d0915245c42c2c2c0660041941e82806100d41c0007817070065a20410300210100f84045c810040e880c0c6546900c8600070307450f03c0c0700d4007040b0399083c006206c161074610902a54900c0c006844491403d94541000d4803d02034035104040d11082c2d42d09099a607600f0f403038082c10b07812a080d80d03501406401c0798101030701e56010a0500c902803001150107500414119900b41092914540d540c5059001000e06000e540000a2506c0f50340d241c5458000b0101043c01f842100c41e0b081503d400c0268204030700840041001464096650017503001814034028080d0410320060103409403a0700c40d0000780e1401003440c0d031000b040290900400500d5040001e03450078058031760740c0004502d000c10001e4460351020f89062 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 786500935 1250 786499685 786499711
    0x305090603070e06030109091a2203110f030c0f0c13090c231809070608180607020d031103010f03201e0307080307050706080703020d02040306091104050f 68
    0x369039911907030803d0380c40c0e080140465140d5031904170700801459040c87c200c030a603011280c1085c40443c1031003a5440750440301c44a103500d10001040f80c03103c41544a088051002520500c0c203011400d220031000c911000c0300841d00e4071540406d40d460201002c240c0d05050304158a0b00c01d140c0c41e100c0c1502c0030b080c540000851091524a0400a070b80304030741c4408006c3e45001d40d9800c3d1045c6025030501ca0442c04c65507403114007135243c010038071260b05441c10300c020b50080d5001c200321f500460314154400691030700d41d05d103039205201260502008440c1c2c0c500582113003070003080140d0144504542c903050387d0042800e40d030509002a440451301d00000d80300303909140000b400c02e014450210082c181c0038044c680e90301c02c03005030940f018050340c1e51907109000307400300130640030000400d581481d5006402130034040d19011b1300b5a20050090320301000c164082150900c4582e035400100000c522075040001c6114550078402201d400c001d95080c400e0341000280308604d00310100e05030b003080a000810b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 786502185 1250 786500935 786500941
    0x61807080c0c0615180f190e0f0f0d03050114010318050d09050a051206040b070207030816060c050a090b160b0a050109180f061a060d0506030c01020a0305090603 71
    0x11600c1e8024042003108a21401080010ba84121842c590700c034441522070010380e6442c200300d1515032038200c460418805400c1300203908015a00d1030000d004040a60002d0300010030001241010030300310b402e29490f03000c0d82140b0284c130300820120065042c1440d041206504256105d0306495101081174105034450340042c4c010004072401100507a1f102c0120b6000710000a000f50580c80345218251065400301d8000445040c195020082282e58602400191380d8603915580a0755000e00160b046101ea0880480000c2c280d6009210340441000344045a1080345040816200c1496105040040c24050701601075040030500c01526040c1034507985842d142c5540e49412030080c40090900d04811003070042441c60b40d400309050b6105410140800301c00000c43e00301c2240b24140050410603401a01c1c40030803816441841c0701e8240701c4041000302c0b40c2000003519070f080800130b155841d6603401803003d1450b08116030a070307041e028000380c1407506003a1005407542c0a1503004da80110000000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 786503435 1250 786502185 786502201
    0x4140727181116050c010f09030b04060612080903011a130f330801020f030c09030a020d11120d210902031501140f060a20010204150806180708 63
    0x201c000b020415200e0640c031140c200c0a0400e03640c2d02200141c2d600d0141600720210f95204d664030044c3c5412079242d804000b45540c3e607140001034014004e40301e142e603a010210b80400e461105014060203000c10644503d80300040500b110300f56181882d010504111802c15511410200c52643c0703106070000441050078480c00e005003074890406560091085400281c01c118081d06020f50b40b0159100313641e02c0c1e12881ca107400c0703101c4d0f00f8002040000500004000204a000404818101038181c0f00c2c500c1c001c0d40030480c00c1000e072108652514405407421000c0c1003009080d4020146500140140d11900001800010800341c58001104c110b40000c14101210b8101002c2d490b0301404458041d0381350405464902c00038040e4048258051007000b64603c0c021119041140b00140203501d0050103207010b8901d2610541200c00c641814555a03c0c0b0810030320207000140000320311421848482103000304280710040c60b10f84550608140c80600d000e140c81d000c2d0303006056052200d0645c9035009 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 786504685 1250 786503435 786503441
    0x41109041a06190b091f0906020f070f230402030c04080d0801051f0315120b090705061c090c0e07030b180f091009150b010c0224090414072718 63
    0x50319211880c46e0341040641300e074810b03a0390b001c4030242e84c203a400150f50b00c0700c40c64540b501889111050115000284040d6640030700c0600f007555002c140e501c68008513400701c1e040e0b8108641c040110440820704100034481030180300340001642c5040c0301c0c95810040060140d071440e8881003d8845000d02c2482e43d580641d001a050710b403044161a0503503960820b0145100b1080c03400c690b44010180880ca10038030005a08054601c0204803d00b070992030580320b280d80c030806200c0c0c401d1035201d4500e070001ca030859041703034050030b040c0d00d0324038582c0360151015099a2424452a0180b20954100155070b80e100340d00d40e0b00400e100328521016103a00354402c0c544802c1602c03641030b0070325010000e02001755102401d07044107040001403040541c00700041d40c0c8060703002d0003c0d410840d41c180c04070202c0308010183c04540c02003180681821504030108040b110f24884000310440b0304018001c4040e0401c1d1040001c520540c4a42030021802486403210700a9129000a0908140d981c00d00450560 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 786505935 1250 786504685 786504709
    0xc0e06030723060412062f2a01090c051509040c230301030c0f0617091911040f11040303030b040209120c1005041508041109041a06190b09 61
    0x140604d072929200d2680d01c3c2c181400e10400c5900e14944001c102181813900110242d05e900302c0650280d030a101d100d01c40056020b5041580007545014400c01d40c2540062018403031050480000745a0340e07540f508441c07403ea07941001d0702c02c0941c40c003070810b14042c0c401120420075081d240840c144132007080c140e41c00800050115202d8400351001842c400e080c401840c1228003e40303141c007a141c0c1d1503409590b903a10300c2c001c281c005105600030807008864007400300c0e0444041000c862030350240c0b048440b01d001890200300c4200400386c41d034030ce95180ca80580d0340313002da00ca03808120b0040c0c2d0700c60b00001d51145200c001c00340340d15108080000d6481d80e040c0c65080e000030b070020740200200c4403066164616400c640b48038030102d0241e980384a01c02c0054405945210387c5012007501c01308015160548014021207002c400342c501b162040d200c50100701e0041c1e208600d401e00d03804080980010b00b5400421141c040c400c1c9040d103440c5285001503640488104405d126900d114000114105100b00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 786507185 1250 786505935 786505939
    0x20f070605010b070c0b040e04030f021e0a0308060a05031c120504060f05070e060307140405060a020304170312010605031f0303050a260621010f090c0e06030723 71
    0x80000541500460f0051036220b00c1000030805181c0c8030340120045009500a0511362071000002400190181100f0305850340d543c0111820101c040c42070b100400341028640199800c0000464109074000f520a40c02010448000c03039214242004a942e514502150304260f810143c883d02e5624001c940b260445070761020140907510301401c0100103000440501c9503094600341c0010b016a22030080c0020780500101410f1441e1580c8a0445001400e000c4405a045040000140ca581d420f1700401c000c90103a0081d50700e56160252403500740c44112a21401604200001550040340f00300e1141500d0b11401c100c1d031640c64031807100c5d56484894840005401040313a020081c5900407014100c141c000e0f6541003042d09110111444000e0054441003584140323034003250007498074040214822012030030790380c4040c4040040a0944602c520313a64400360340e689009003803110a883d02009000d8200040f0701030700f0034402003951040c191003090440c20300001050040c60011600009010300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 786508435 1250 786507185 786507191
    0xf0912030201140115081602070b120403140f0d0f06051801140a050f06250b061c080a08090c030307060b0f10050a111006030b0a0e030c0709020f0706 66
    0x24039001e4000c03c4848510f2002004000000585140d01e034030020000348103a844001c2c54480c3c00008861810f450001c1003075000d50607000c02c1a1101c000a480d400305a43c0102d8a14209820301a00103200400a20302800c0c1c02c2096820195150003202e050b00d118042c000b8a0703045c3c4c0703c40a0020300c1d10350406075214603040700580c100e0304a65400c5050390692821003942c61002801c10001c032420740302d0380c0d0300040040c003566407500e0b040000e009446030b07a183e03603052440b4000d0800ba0030741c10501c003144c2c201c4032103050000e03e040c01c41108900062140210303c40d5000ea40b1040081d0107120000c50800001c9000a414100d0a2000a401303c602500326074903990f203858184003401d00e44690b40c0c00b40042060000d00d51800a5140304000c038641c44503458220140c0d03080300d04c9400c503d40c818040c4030b541e160b0f00e04c003001886400300840c09410f466103039061040c41c8006072200140070400d103900038801407003411408921442110031041006a441c41c031202d1400740c1b03002d840d40292007149 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 786509685 1250 786508435 786508469
    0x70204062409090c12020d020f07050303100518040b0907030b0108030409050604110f0f040e180114010f050f0310110309070608012105030c06010b180109080a030f09 73
    0x54402418403001c2001d40300c0c1c00b80aa203490180080b60075200b043d100144800c507402c02e0003441c95000305004584107101520300b0710349021003901ca41c4400b0003155203600010801401c03920752a032020142c2030480d041390500d0f508640d141040c400c060b1020781100903540119400c3c8030100300200c0155445078602039250b81d518046a1650031074427601400c01e088c40c000989902d01b84c4101d5480b405030a802c130781803c1c0d01107056240c42c1c002c44034061030000b00700f0020650203510820641b003075110b12303a100c0c3c03404408501a405e580d6541c81d500c0003602500e0041c04110b00001410054440a940102e102050000064a0b003484c04505030030ba00c0c80d00c5000080340d45290011480f4600702d41c2102d56070b960300c980c1100d4a0302c0901c03c030040300d0302c0e92840c03103946100c0c1300111401500501c200c0e800e042500b211542400702c203a01030311032000700203030003c40740c000310002c454030312400d00381011898070b04030b411501c0e4525131800600f000301ca02d4114108a0050b06a1000b80c4000000c0c1c04482c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 786510791 1106 786509685 786509729
    0x628062303180307060e010b010306050103200c2a0316080c04050408040503030a0207140f03030409230415110427180803041202010e060c07020406 65
    0x20004000c81d00124071103001c6c419505402030000112503044000140840d40c40e640194149400c14841400402000c54016581e8007031514281e0b40305202c0c041355040c8018520100a0100e00e45031002c0f001c00c900b8100c4401c81c20035400c42e01d41600050300c0032800c800030310824415038455105d0a05c1810a6000603800a1040c03810030700b0300d41c4a500081c2140c200421000059106400421100c6940901a01c0d11041a02c0b00382001e4003407130210380c503840b8038016480c00b0341d201c0c07101c2e500d0b0480c1901a10400960703281e28040d20b04180c680140e42880c9440d801e0711541c1400750b00740c400c01c021011138080354603907011404155a012040c7c802158900f1040d5509955030300c0c820f189401081c0540405440f422805640746002e1800c3d00000004114800440e0b01d040f0841d592007000041d0243c012100c0d443c21919400244001005090703550421040742001078a0b52001c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 786330935 786510791 := by
  have h0 := BRFrame.cov_init 786330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 786330935 ≤ n) (h2 : n < 786510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
