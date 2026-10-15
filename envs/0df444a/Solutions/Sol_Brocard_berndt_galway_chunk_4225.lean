-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4225
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:55:35.246265+00:00
-- url     : https://prove2.me/submissions/541c9556-90c1-4a8e-b9f7-427d54938618

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 759712230 ≤ n < 759892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 759713480 1250 759712230 759712237
    0x102307140613030212030609150117131b05032515051908040b0c0a0e03161805010e0610021f1a040e03070b060a1a0910051603050906040506 62
    0x20b1400c060240c2c400741a03040100d0101c003004034001901d5400d00501258601c2c100a05000203070403e10307603104061f417080242c21000107810035106c099040c945c080d0500e80c07448030030a581d40e80c544103240d85502c480310105002c03240018010490a41c207458150301904c00d8800054825040c0315000032600140340c489001d074481940c60b60fa9900c85420407109a0201000350f40030404031b0008c100008607200341558000000ca040c96407244926441200c1d820420803c068140c0110348520384191110340000d01902e40382a0030f0b212040e16860f48100b103940900c605a10050110003091441c20080e04603015101c1c0e510644030108580d500754522102c00f07102c2c10340d003503641d00210048000001090200010100ca090004000680400c2e5490080070806406c200840010a08694840c4500401011003000390200c0901c4221076004907005454068040c40a800d04910002e104000b12400341d10f007107525021030107164900315900d400428009403c02402c000225203595050b018 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 759714730 1250 759713480 759713491
    0xe100b2110080307080d240302010302181908010e0d1704080d0c18080a0308010b0a0c0b04060b0f012a02130e011e151202040b06181023071406 63
    0x1d0546c0d442000c41c0d403108071076910600402400014403412565030041c4d0302c1c801165024640562100c075900b46040b1440c105c5102140d000104c13601040100d41300e01200800c03030751443d0080004170343d04500c0e13584480f00c1201d0100020042040103501000400445070032601800102d4203203107131031a803c000c45114104038008911600e881443c0403140f0342281000c0d03c0341202030310381201035542c0a0060031041c0240c4c40001d10114030007001d144281c0c1406880e07070700b0100441440c1802d0900b20010314044076a00d000c0d6042031000d41c49540550318000030035003d00102c181c2441990f401d103840d840d003188203c1c1d1080706000344c911803500034013410003031610f5000009424001c022012071003004c003540c0080c4050030b00090302040340342818507504446070590241c50190252002078001d140d1000f115078842d0022624a6019106034400c030714a160950728901c40d01c1240d030301030f41c141d001007280440e000b0ba042d901d0031406544001410145201d090000070645050a8070360500904484 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 759715980 1250 759714730 759714743
    0x302010509060916061101090c030c030314030609040f060e06070f170405060105010c050a050105070f080619050409030e040c022401050306060105090d05070e100b2110080307 77
    0x2800a265410b01505400c500680001c01816080e265903c50305109442442e043c400300a00c500406c41d001e4118601b4190301800402c80c00b40c60389040c20041d9001d00040e00001c2c620071400705c409041c0003c40b40038071001021802940c0d40e41c2d503505112005000210780581e141c00f030125102c5001c001a500948858071281d200c00d2500d400140810900702082c64214480c1c3c080c00007295004c00d03000d06460007840d00e8400285030b810411300e400c140440c01800d561828040002060b4440704185442d0066956014542c4980741086401ca88500d0441140703410803d081080786001e91210720311610a007440364603550800002000c45070f0361750526000da00300344d407800d2003d82c43c1c84008940700c43c0c00079220f60a50501c40440c0eaa4030000b48481d050140c0040c508071155500c150340591240c1c04022181c03026151b0004042c80034082d220141011200703000803070103194050680300c013860031001e4140040c00b4401c40444101c40542040b4001d00e508102090060003400282000c500541c0c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 759717230 1250 759715980 759715991
    0x1090605010906051c0f020d0314070819300b040e0c03010c080702060615040e24060f0f070206042d0501030603050c10020c19150507150f18030201 65
    0x828449000c0c18141140794119180503000c00042c03002141481c6c9503016204000280c0c1c0f02d140c2a9030350a05072403820425140400c9403c10092510003d244140310301e00d61510702c40380000c05031502a8007040d0150010540c1022032690b00340c0c0704c0d07808016488480c01003075040581d004582150b141d208903200313a400c1854030701644d060900480e0820390b5145048e41c40c501e0040c800a40300c1c40c01400c800e204840c0d002d00c001c0a100454143d5000d0300444030b94a1300742c14207c40d42092900080488186615000b01004042c0b8069003680c03204000084600c0c80c2209074410707501250f00c080c80407a88060180f1003c00c1d00b5403948841e50f941c803114008408014010900c0c01c41d05a01644005d0400d8101102480054004591001100c0c2d041e10130351260307803108105a0a0441242e00b05410140c2030b8440c8000ba110042120100c0b85025424050b0b170040490807220741c03040360b00180085140440300c19101641e54030210342c044a0120000c0c0c1050700b0090309842c0c052050082d00140e4540 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 759718480 1250 759717230 759717239
    0x30f1412101d0406050a1d060717090d0302070515040503070311031812100e25060504051002120f03180706020d050c010b03030c030c0d0c050304120501090605010906 73
    0xd400720005420645401c4101c0c01256502d20040c0100403c0101392548038408201c54040c0d41d007105070320b40e161088880100008400e804e540345821a100d500042c18600084444866a80f00a0103040700c00064600b0f840010410350296002030703401c03105442841c1d5407064007003050100c2401207200700041d550b105054200184a102c000c403043c806078100300300c80c050048000c00a25035444060b1442d818040362400c000e800c16a103000717491a441c2c20081c04583d44000401d103d1114640c001c0703180100c2c0e0500b0301214044401c3e024100105a0410050000e0b02c0c0c022140c00d00821b561045850300e440c4481501c02ca5001400162000703031001c402d00942c150305440c2512820341040003010040d291480c02075540080c08015014080e0020b425081b2020a40100c102c3d0f40d405011640c0d51000308041c0ca45c1caa105050080c0c443c00b031b0205403c134403807143d820308802c10b03007000085007846d080984d0240c4580890808844941d60380c50690002030007405014001c00b440306000403081c3ca030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 759719730 1250 759718480 759718501
    0x519020607140c07350606030d08010518091204080a02040606030b09044d100e01081012060605030c060405011d010207080604080c070b0a0c030f1412 66
    0x240c0320703620310300e051184a84545000a01340c040301c400e03902d91800c51220500750742c51107004009000041030214221407010100041d124040d810075000c4a0a180e285101110741041c00e000e0281c2c40b03402c050054001c0d03100042d41c26003010811055a0703010501001005070765001d68410851600000c802806514262040301e00030303c4141030078808080f040c8002022282c00810051050311040d00e00c6560b55035040001004082e02e044c6141d54400490401148900804550b40240c004840040060620310405010401e0b59113030341c203040c03007404015100741030014881c081e52256207500250b131100b4070740c07142000c2c0d01403000055040d041c4030516080101c205603850142008020070051a60301141801140d0300c134103114030b0f2080d81140100c2c03d08003030381d11100e41440350314140b105024180e0001c04c00c41641d401190040381d0359481032555030007012260000300e00c000c203400f0040b074025201d0b000c02107207038501805842c21071348080c0680e821003040b01c00a40503c20800c00907804 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 759720980 1250 759719730 759719747
    0x12041410030e0606040c09090c02101a03061801140106080618010821130f150903080f0a0c080a3c050c010b151213020105190519020607 60
    0x40514060210352507528065030364020240544e0b000383d56607400104154414400e0902404140509100c1c40900500003581c80b00c01c025501d8541c1c1c6000311080742805210842c01c000740d00500038100725560344000ba18222402a485c49465494112440000c0d0710048824080d140a40700d050303030b500b441400d00c0b04002000450031101d09110740144000c0340d00089040940c1c0741503a5000118010b60248074150185101990600007030340c0020030640100071082c2c003030398809001d1601803600b510301181e080790544005000040104510101d080c1034800903e4841c2c0a8200050701204959480798254806100500029980f41c119082c40305100024849504e035210035a244406008181504c90f440c0d01e0600d0611200095840300d427542034100b49508100142b0100e100000505209411740c1300865514450180d900000c0d01144203104450401d070b0181e540d1030402104c10080604860742c61040b42c18400700344015200380100c2d040c1c4005001c801d82c083c114a061151010f4070710340 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 759722230 1250 759720980 759721009
    0xc0406110c010206010b0c030c0114061302040b0909040501090212011b0201050115080405100c0918140c090a0b030c0a020c0307031203110706140402010f1107090e120414 75
    0x41200702109116a030000c0d40c14199075a01444030340e2403000c21000303031540c41340340350928aa5081403120007000d0f5100c56982d110702c40540b9084180c440b8040480128400ca014441031110240120079031824a8000143d01c24402d2000140e8081250000340203030b1000045490607a44500282c0c102e01400000c2e40302c085002c0c00244559410104100078407008684c8420070012124000340a2000030086000c6054125108122003500b0810003042141c250054401c42a40b41c0b8007101c0064a61140804480752002000020b4560150040b900d5010800560384078421500201d0b811050800640c01001c0744088a9942d41c0294400307401c0a00894483d48a900300035020404070701c00d000c6081c03100e100d5140c009502c450180c40003105006804010300b040e03203800d103220f01104280002c1030045000741c0b02c003a032054040c10304030b59488112500801a4008801c10450030110340c00191101002c1c030203075110014040340c400134030382040c0e100302903204c000d00052110f1705010485c0c501c4c80 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 759723480 1250 759722230 759722233
    0x503181c03050301030f0317071e0e09041101110111040e01050906151612120605030f0d03090809060c070303080108030304030c030c051006090c02010609020c0703080a030605090c040611 82
    0x20301140d01c0142c0180014480945801c0040300080209449880710680075140d03500035100e82c3c2041c580003406190101c1c41c10107418022689a00705074040c640d032005900000381811006c1c1d455513507060040406001550600c240101840304810080c0202550760980303110041c0c94524103a41c40d02d0521060303100d42d002d0702c0a4024829992100c8404040d0b100900c00480e80e02c0c3d40e442c6418240000303000d8060300e00c011540d06182690743c040c500c10b004c03041720542800441c0e00d8100700340d2220800007a40315a40e002c0d1364000079041c000d401120a1601400c0c5582c2071010400120313001c1c0d40104070016050304070f040240205600000c05501510900c07008501b186060b13078010f420b00c49001d0002e0300384614901900c08104e402c10100ca940200700409121136555180344d40b0180c201022540c0c059401c100d0b000c40c45038000c0c402d8071600c00d05440180321040c6591100841940002c036103070101078488101054030303145c0c10503090290000700070950391a45849001041444800e41d00b051380d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 759724730 1250 759723480 759723529
    0xd0f02180f0904020d02010c0c1a0c0c09010b2a01051503060c04061403092406030d050c03031f09060b0403120804050c360103030e0312030a02070c03050318 69
    0x545c4407140019030075582030a043c119840f01d411f055042540a900c0a83c0c694002401d040c0c4c405070803005004002103c42c1114140c0c0c00c5030007040304000302402140c00401d401e010003401c0c00c5c0003c10507402d90040117522403500c2e140c002101d081d58400c913114040079111040c82d18040c1405c11040d0390008040288170705040c1410307402402480c89200c4001c886e20044041100964144032041544520b03101d1030241e4007180c0844507051314101e0b1024842e000c2d40d640b1342c80d034030b000c0e0b070848810440e050051403540d0380c1d00f91102e4100517000150180342c0684180400e285008d0311400c0054000444500d0b182c07461450030024001d01500680c081084a50500000910005120103070707080c11111818491100c1d002d01c40410351140e0b0b00c18150000380c0d582e02e250018811a541601c2c0a584c900e0007228000c8e0a056441103210f41305500a542040002c06a0307c040d80a04100c80c440e6800c888056503a8a0711807840d00b00e0810296424200d516045a40c60092800e41c0300810b10400000c1c03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 759725980 1250 759724730 759724733
    0x605180103261602060409090605040506090a0f061812030204081605010e13020f04030f05070509040b07030b010e130516020d05040603050a0204150807080a200d0f02180f0904 77
    0x50740c01155090030707900503214034900465179010190341c0580000082000a1400d906000c805130406840940e403074080e41e008100d400c030000c203500e510250030000003400380c2d06c02d5850400030041c0b070354212226482c2d210f4010019a10a0f11220400c805940240c0c5aa00380b01100d805d0504e01001307510441d410400800061341c014036140c150000442e09019408115000d500180c4144182c80b015a840003502008118480c1e031040302d00c9000b6003c42d94619212000d01682940c240c2c0d016082940b00f00004410521035008495003101c11b14200341078203510b00c00b18040300095100c4421007034030340d404c0041d03c91121040070082d12042c40201300c03040c40100301410134851030240d0320400d40c03142e002400302045130f01142c1c0108a081d034104003c58102c40c006219802c1592003400003134004001c101b61805600994116040544115288591401c1294550390200d0300c00c10781b20703807070306400d1294404c544007a2800610b4080100c448850740740170009440039211005200d42e140405100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 759727230 1250 759725980 759726053
    0x5010f05090a021b120406110c15070c0806100e280b0f060a05030717060f060711030d030e07091e0c0512070c0b090a030f050d0605180103 61
    0x290042c800020050751044000402181c00c510307400b03005203910400c09120300e24200c3c50001c1044414580e1522a00242d4011168a607000031805540c00102c2a01d026407895680e001800351502ca6404204c0140e51007880c03604240d000c03500c0010035440c1807400c11081190b01703211640240742d800f841201003226408400c030005402d8440f0324240c1c0d030303580c2c50095494400d920601008010401030321490343c00e1005209501c104c4460000851300d42134030b044292903030350040c040c0d00c008000b87d000405400c00c0c0092600201000d86800c141281389400a0b1000e10402c40ca110b05540c0105606224442ca18500085035010b15611468a5a41080381c01c40f80c200080c8454210000f041d40540010225403c0c001c00d00b0031102c425501c010f0060703090700103100403445403042a90307005a40e0b81c801c085481c0d101c61007010b0302203001030785071b110b132248100003d2035404229a07001602540301c401007801080c40000c808440d1892200500a003c601e0f6010420070200c0031043c0c0d42024100d6220 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 759728480 1250 759727230 759727249
    0xe070201090314090d05030d05090d021207111c0515070507050a02102003030708070e0d0201081b0d0b04110a14070f080307080412031a0d05100501030b040605010f05 73
    0xc043d28404102c90120f0390318008002100354208081307a40341d2164000540013000700307941e030364110300c91810001c0d403050020403800101e072440c041c0c890070240a5101c0c89049080311500c203900aa9000700448900c0c1404404411130b40900d0080030310001c0346502c01500c420140c11078042c001c0c01c2c0619000201c00080030845035030f040d508450b44054500085d200a40380502500603002c42c0c558400340404004040d5205804580c2ca501c8980ca6107401601c042005825054020310f0344802c02015500410b091508000d00150082d42244807070610702a6821030b401c21051070351644100562031809010741240120003d24070381c6030190254010342200c1000e6507042c84040042052024003500c6260320014942001380e05a43e07240c1644020a001e804980072191000c99044114082e40700c0c3c400c034044100d482041400501c045010056800c12050003103400c8d115041540c003043e512405a140210300c140902d18480c10185041d105403074058206607a880800c141c2040b50342c0d20f8a440 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 759729730 1250 759728480 759728507
    0x2070b1606020903100c1701061b11150c07050102070f050a1502120301030c181104050103110c0a0807020112140a0b0d02180601200307061509090308010e0702010903 73
    0x40c3e88101003008242000d18140a105140e0710340403091203203981140d140441c01c1720724207040c503a503a02c69900f500c0c01c1c2c140900070303d1aa440c41c1c07000b500182c1d641810480c0e800c0002d0601481d0410882280d20640c0300d024102c00a0700015003c001950701082184064a10114004022402c14001c0b50105045100340c034000326141c60f00c0c1150600910841aa4100b036100c2c290740d03580c40c1d0401c00d440002c03621034030820440c51744030a100c0090314412480d405059440b11480d041c5440d00450190900059045192790708001d100c01001d0100081c541451154001503200c411500002d080c04013400d4452081c01c0c18401606d04106505403450390080507080c0014419485202083d480402410001d400c8880e03010340140d190090692148100801d903940700f0b46e07040c504405e6a407481c0340c03030300c1c4052030303106010440028000341c0040e0b1130741c2e416855903400941d85c1c210140c160b40c200030341900460b030054010b0000c00451002c2070703403028050000340f001040c0f650f00104000140010f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 759730980 1250 759729730 759729743
    0x3060f0b0403260d02190f030b030a12050408101401050303070b011e0914041e02010c260a030603050d050715090827040507110d111504030c020102070b16 68
    0x12140c020041c660f058403161030501c03004546031070300001210740e03001071001c2c114040342e00103c400809501c603002c0e401010201a010f05001c6c0c0582d034079602d1010301c01d4100010b00100b4030010072140740401180c85c01c290f0041000c12816a4030b030502038440011781203140250020003800001c40ca807035442c241120f00e503480303500040403c0f000b11201c0481a8204d82030341c1c2d080c0111003903019407200b100341c00345005040f015075004c1000090304920000c90320084c0071407031948070080030440c0c1c100080c0ca044da11880007605a9110505603105620020300c06011070350342d810920600c5401c01c800c1000011904100e40350081076110510001d203080542482c40303407030341e40c807104200a150955001c0c91071340c4200001104440311038014800d807003c12034080d51900000a003510320810b5855808262440505040d000f80e21040b501d503021219244041e204102e1618000740d210074000344250300a41c0c5121104085100081c1480e004e0b9010f0744030440c00380a08291151100d4045100700c2e400803 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 759732230 1250 759730980 759731033
    0x1e04030906080c131205010507030e0c061b0102070308040c06020d080a090302010e010c0201061a031003151b11061006091806210c091a0f010c0507030303060f0b0403 73
    0x28481c0d040d02c22086825800300203800001340703003445ca82d04071102521030030090055680d40174084049440588a43e40b05a004030407009540c10250001c2c82c5800c0f004412a03807281450000c5800c0e80c0c050f00c0c085001a45010802090000172024540a0001c5101030000245c0b00c00f002458420085c11018801d5900d481c00b80800d8000d40c4040e5940122500a00c6a0010f16901a0081c0a14843d4450051000890b002d80021000c00c607841510116120520325007181c46060003450b100d9202e0020301e03034851281c3c40b0b1120703c020f81480c102c0280d0301c100154112804050400e00701500b48000d028a80ea0306111654001130b001081d101c00a01d040c0c100c020b0000c01c600540b815a00a0003009681d11840310310318814113810203554040c5442c0300c18540d031190070748120b400490030030610b003d0032042c0484603d40100c4c0d13002c0d0b01405141502000d01c09444003070078a44640e1088000c25502c2808000c4190301000b03850003001442d5595003810310f5510b0f03100400b240c083d01c01040e120704a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 759733480 1250 759732230 759732241
    0x2030d050c0c1b060a0311071407080d0507020630191a03071e1d040c0b03090a020f1201020d0c030b220908250606050d0f12051b03031e0403090608 65
    0x1640c02c01908004082703010307454440c2070b548807002402911014014040107620b0719004904542d4640c1e40a4102c510704010f42241e002004211085110084400c55502007104070b01c980b02070060320700c01d01031038030b000d4681d001504444000112000c014034070310b1b29240070360700400e15000b266032526207000c5103401d69050603c103c200380c01c030045546402d24100008844412114411031107008a04082c9441c0c45e1140440d0004941c088481d034000c0100000500b00f582140c1e40785980541090451043c00d8881820398014110003640c1658507610080707200d9060090030030040056510aa02c0001010001c10742e008180503004906d0320381511030100300b036130740c100d1300c101c100688000d15066121071180c560000d0120103131641070800380c011030285000c013880b00c42a5844003003407546540b903542d402180714a010000b4284102400b80e21a45000441c4500b00601014040d5660745003c4044820106401795243c0408918204110000350000802c000f030351014240010941e441 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 759734730 1250 759733480 759733511
    0xb04060518010614210d0f030f09050313050405190504110909070609060201020406081501020a02090a020c0105100509071101060305190b090c1f02030d050c0c1b060a03 74
    0x250108108190b00c0d0820006294a4408400452101c111249030311705542c40503050b08110440c60605080e00050084169140114940c4070180940c5c20007041c041c2d000710181e01112034000e0160b803543c100291820000d81456442c4026100445e0308000c14141703c00c2d900e005500d00594031020541d1070002c14140011110b484031600001031045c030140c41c04413035540e10f804844c8104004a5945080481d07010b00600036034094610340e640c1c0344565503c98941a00c1c0c41d42c10080b05040d40510000700000d6124034161a1145801440240c0d588032429201030868800270100100c0c9032111609014a54401c0403d0f03030060b8603803503c161040d042d02d10460040102d135100400b24030504074401d5104001c001c3c002d00c494001c0710080410351740c50341500c1d201c002041c01c069010400c0254940c016100c000e0020308080180f044a0920004103214000c480050321141e00360f280200d0940c00e8414104885a42c007100500701042d84444c1070045189401003001c3c0c0c4090507221008201e281c01d1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 759735980 1250 759734730 759734761
    0x15191104060c1a04080403030f09150e0402120f061009080304030212120c1605041803051b160312050a0509040207020f030a06050615160803070c0f11090a090b040605 73
    0x1c499100f50340c604152030012615801840114007013104010000700160084815030221210612645c0c401c000ca00c20841d03030707000d8507400a540144c0c2800010781100242c0d00b103610414404600d0708181c1009002c1201101024a11b8030030000600000c1c8113900c0e0100076581126415600400d8201842c401181041000001c640480801017071f0401000310020740c02c150410011003040350385444d0000c2c0800e032144c140d00300340c2181b9045444000244181d000700305020b212080d0a81c440c525417000781c20201000c0c3d844015414004044c024002d64070000410303040c8a08165180c80d20300c8001410340d0250b4200c03e071107070360b000c03400605640382c0b00200d1a03028030003800d41c0c2025104d8500709005140030fa50050141d101e170002c241c4050400d01c200e94914480b503095804187c0c1d180e413400c50550004003007108000c414160f00c400078043c2010141007910401d01c240500c2465014440b81102c01001e070080e06041042e084042000030605a80142e0006004a03050b17513481d03586028081e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 759737230 1250 759735980 759736013
    0x70b07111e060c0705010e04050f0720070f0e0f060307060c0507031203020c15070c06021e030907210c0308030a110408010204050901050f18130515191104060c 70
    0x201d0010f1061190b40010810900b60745098850040403405002800100c0d00221125002ca00d40301d008204120300031342e1440c1698082c11070b04403440c07042e01141414a18694040c0346418900b2005001514070350f2a4143e01c000004801850b5181141c0007030b44d6004184600c10520810ba40c14a0500c1000d0050002440c0c0280484036140709450000300250710690301d200c0940106001702450030004141e030382c0900041c1c0c5c2d500340c4c0030400c1e0b1110740095009080d20481101e503d2168205005078002461090389120060700c4214a403a000d90b01420340c3c510500d0703040e40503116075000903441030a41e1042c6c0390808080754130b9540c0c0080e40c400820440c8048014510080b400280c0320105400500582c1c0701901c2d50041a40da0300180418800860070507580305c400040d01300086048075214a600071220000118540e00e40d44946082400d8158000b1010400c1c00801202e003800c100150501603900e841002150f461545003081c5016a0041f4010040c1c502c00080501c0007911842031740e81d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 759738480 1250 759737230 759737239
    0x60402010c0f05071d061003090201080604020f090d050f0f0c0603070f050c0115060e0f15090d06050903071101020307230a050102120708061e13020f0705070602070b07111e 76
    0x4482d20761701c4a1030f00d0707400c495040c810b0f05c6d45101448064468003032138000036810f841d00f0440d034688004010103074118800b080f41c00241441000010340d609040319041600a1020b00071042e01110181e04080580042141d41d40c008080b07403001d40c981c81c04403548212140350038071014400e241c003110705202e12040542d107907081400f102034040e4040c51000440d03804d5200c0c0c940900d241002d202c00201c0d440712042c0e200701002c001c102d903440e000004240200008280341400711403a52958220b40e0700392401d47c142c1d03001181601c01c1080205040c0c4d0390602c03d000a50806280741d0300c0340303050301da041c00c500c03040924000e01c0c5c0c810410410204844039440b4000f95201d2080100346078072564101c1d81140040c0d5410041401410000610f100030f080c1b24450710b00314075015050000b04410045c03884407aa03802c021655050304010064285c80c0c2c86000a0850b0368544503000b450300d00c49400071084004104a0080058032041c42c038901c42c2c0c1c040e503c4440b105651003540100e0703901210f81a400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 759739730 1250 759738480 759738509
    0xa151d0c04031a090f12041707051503010315020306090402360f150109150c0c0902190e030703230601170d26060a0906090606020f060402010c0f0507 66
    0x1140c068002861013000468111181c40c00804505a51100380785405224400d04010502604064602c00f0084080000442d01400c0e80c95021848110340401e400d41841c00203c0103004003d2484010140046101029411801d01400090031910040e00003071096480c01c00290828155a201c08120080900c1024848034003d11000340ba10044490a000c8003601001904501180d0b085500007035060303607103020803400d10039103501000001c0200000d001a40070a100041e008040c0724000d040d0400000d0b0716420f08901c003803a00b80815090400707100c50411041c600c0c3d01c0005180080701d07040204075201040003204030030481000ca2080403903004550000c91385908003500e10b51900c42c000100c1d6920b8100c0c00d4112074a001c580006003070350390741d8441c16000045416095400000080c070a03800c00b84d0b55001c0c081201d41640c410000540ca40c0c0302003048640601c000030102c00c0d4600540224030749540020142c00781100700402c8003d40c00c151005100f000c108500103000007842e00c880 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 759740980 1250 759739730 759739763
    0x303340209151315030b0c0405042a0f1b02010507140705101b140115030b09010617070302010f140406021c1d0111120706050a151d0c0403 61
    0x24800d5120741540a0081c0c42c043c561505800c1c4034144488032500543c504880c21550381c00c00005015140170f0004405100c082155a501e118031508910019000310107080c0114101030710360800da0f0030405000c05c010303550719010b802204241800c11666007545040d00c0510042e141070280d401e0240c4001c2c0d54a004d1a0b54440c005031003026108101c4020320042c415510454012004032130060724500d00d0010040066031b007201c0e1300b03c44506100041034403500420380c40103e400c01c2d482612801c48007428460014021711031100945003841028034442c6021071a195240380c03074400241002550000440803174810200c0c45600400100300d544d5450b62a08020340e10403161241c2c1c1100038088500c1c42d11180141248020409884641207075540d0000055a0202949100d04000e00600c014604500b59817002032110a00c24200010681440140f40003240d00b900ca800c1d40350301500b00180a4010304940c5240f03072400e100c14210301591000800c6c1c00f035001b50b5000074400f0219112815 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 759742230 1250 759740980 759741001
    0x10c0f08130819150b030f010524010203090613030b0103111f270b0f12010602030c10021c0204120b060603070c140a0c0f140303340209 60
    0x4a0800c0312070312810880d8031042099182d00c0410181c0c0002152414148005046800c209080c4aa103860000305e201d8002c003c41e0802c9001098408281d56030b43c01c2041510074644e1040c60784103004d4141200084010010b0350301e104034464103100d04c1000c50b04151050301400d541001d50351040100c01305513560f25200b40c1c0078141d240018891158801500d85041d00e0300c5500c1c0304410340d540c40c0100c1c078040440c41c1e004003890940000d209000290082000c3d40b4240040c0308004003484230300c2d9581d0300e181d400071a060068003c40704640003005850340c4410006503000001c100d10f500140e490808842504a0714031940201c5800390020800080510381191190b03075007800390703400704020750742c150030030420b0301c0101c0304840414940c444101c0400c03009a038001e5000941011a18007008607150701960044a5104684030b0300c0c000e00034019101c1107032485078010800d90040d4108510041104001c071045190045407081c038918504040b09403008040c1040d4001e8080102800c01c4040309 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 759743480 1250 759742230 759742237
    0xc02060c120a170a090c051011031b0609070b1e0405030a0303020a02010b01080907090e0114040c18020a05030c0c19061d0601030209040204150e090a02090708060d060b010c0f08 78
    0xc407442103032400201c60804501417a1305166000e01c191514600388002c2001c40e04003503600e4070030070a00800c4040c00322410002801e03104442d4050030120001108103514201e00104014500d0f00100743c2041408415029140145140f00c0707550035140207020340d046103000f1035009946c9481805010801d15070194000d08100034a94000e1050f9414600107407403030a402c2c2da00d1401a4400ea808000d0510705510206a9200b64000031541280c04c11001d46955010348096400d07810b0420100203c0c801c0050f10b005581195505505110300318802a046000040c07440003d18800207550032415400d100c0c00d40c440f03041c086645c8507201c04d814400028802018205000c41c0c4100000c64100c8002a04078100d80c4d004103842207981d10b1f58240009440e0b42540c1390603602942101085102500d132286208a5a035401810038040703074010400c03041409441241445114028080241c980000c4801610342040000c1180100c540c01202c00003201f000180c050b440c28840d02c400c0142c4c941c000d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 759744730 1250 759743480 759743507
    0x605030106111b010f141206040b03060c03070c0809130b0a0801021c18020901090b13020a08070f110d27080a0b09010f0606050c1c0c02060c120a 64
    0x1025951800b545200d503607490b0328810240d010300d01aa105929610a5485055811291402c0f010240d00110b880107541c200c415034106c2e11b070720001045050304141c42002030404d41203000b4282d41c02e201880110300d200c0507000d0410007142410503030a011002c0200c070070840c0080c00103a500440045518000d0200105680c4145038003040001c031090140250303070320305441035447e02000908003080c0000b40707110701406000c00c840c44003000150360b90b804c40a0003400c8503030340421124841c03410006103140010030350703802910600500386030030350041031194819803600305000310301c1b956141915100d540f4003c445080c840c04060300c0f1943c0d44060360003940740d0100346071580d6034880c01c041c0710149490300941c0c445074000c0d58480c001c101041c00340c9070845e6603c000090502841c080e450203a032166007003000400c100041d8440e80000402080305030314030b46090180c0b81c11020784014620146900041e00c20040440d4400c8a111305000707019502e4142d400407a40d030350004c203029090305880041d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 759745980 1250 759744730 759744737
    0x90619112b0b1f18090903120606050403081c0e030c0c0a051512100306050a020a110a0309151e09030309090b010804030f020f1515010c02101b0c0605030106 69
    0xc0b44840d50070429403c555034a400180e0125a5007007010850705524604081c00d44400000c40002e210400791103001d24040c0a562001e86a110514a400584200354800400c000381000100003007042103084c0d070072201042046005e800c41e080708000c0680070300690820310380000206885013900000d14843c0001080d0349014070b03150740b4410086840150307040c505405000704034500d04902483d48465105001c865900c0707000d234032500c51034112141200c801c1d0003030780d000802c0315032640c010030710002100501000744110175256400074400c0740b4a1041024129405845101083c041c248e1702c168140d140320800342c0c010320240d0082920040388000d0700450405040410724140c140100000300c0c1068548510a0301e40799021039000340c2801548045001d44030301809003070024000001d00114070f90501c0281c0c10098142070f085408106664140810420540300603110703248a18600c1c03000e800c1145409010804a80000944640040183d40001c2000c64840d40110103103069888030707903 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 759747230 1250 759745980 759745991
    0x10905010503040b150105190905010e2d2202090103050705122d07031d01060f0909020402091807020d110a0b0c040b04030c0806090619112b 62
    0x1001903441d8030082c3c2d005460100b803140081c08400ca10402e8255500043c0740c0b95240c0017040d8052203140d064032121500140303958004001960303003d440c3c0b5016134001c90320780d40c601101c00c0150314401d02036403028580e01125a001c0c007031543d4030881503070080860503403100241064103c0d40029131114a1003030120b803400011800040c4110240c5a244454076100305490b26944100980c01112038001409200003031100f00c540003500114074010103032600c000c918887d409244548005240c820810a41e1504904012481d40091008201c0d00300c070000156850250002c503000c0e00c1000c800035000040502c0e07140c3c61142080b1183c0c40f81c5070035402d81c0c0340342000c00c1c021245000400040e00c483d03032143d1442d20120700001107040c4c0190700da01d1280e1805588900580711604260300980b8006648503080210f0b203002d11070b0035809000040909500d02d08083d50134040c88006180360302c0e595036070140002043c5404115003d03880c401682d15080c10700c1202c188442810805a42c071201d0401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 759748480 1250 759747230 759747239
    0xc070e01120507171f05190e1b150313030e0307120204051521011103011203050c0304180603120807020d0e01140f04150c110603190e03090109 63
    0x40e08007125501c10081c0103258540010500d010404008080c00c5008428240136403041c044901c82d0003a003105804107031031038032204d0040019151615504a2420410410390100010410000b0190a02d02c104c2c1c4071007540f401701d00800c218a500700504040081402400480d0b5610f0b0b01c4140d21980e03d101800b0f902e4428991150414852200e03205900c1f04040014039094010725804160040d401d0301058000e800518a1000307154045511509030414811850080c0124210781170300d80162171842d49805140744c0c03070120034440034041101c0030680d81104142401280c006215030700b00fa010016480140c00300800781c501c4110745000300344883d242d07428000c290051240800d41c016202c050701070032064500504000299040010403561000f200f040500039008040c00040c5046d1105d00b041c00700181200d003c0641014401c0c082c2e040b50000303205e40305012552005850003612521030703407110030003013030110300304429070b400d00c4004451880000054003c03100309981d15502255074 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 759749730 1250 759748480 759748499
    0x110309071202131d010c0504180902030a03051c05070e0406081b1212030405030904180b0a2c1c0e1804050307020316050103060e280f020c070e01 64
    0x1900d000035041070700b920005031020743e19404150850240b08250360300c01800d604242c00c5900c10130412001c50b0001c01d09110118150300700e5104141003071401c0007440c0c01900003c2c1c1e200d088400003000c2240000b00000c640c404c140340d6101c9074030058401d120a0401c3d00d80a0310443c1400c070303860301a614111000540324000148502c00643d400c080c0d000040b8400180000c507660498100d005104550310000f28080b25401544142c2c06440915140c001440410007070b5440d48084900d606001414100451400c07a401034001d18620700c0003505c4809040e00188a89440a10b410803048560301c0a601072004150b030340c080704658905a060f900103407011703141601c020075282d40050142507581016080c040e40036800070301030000c60b41054255400079140c18000411051103c0f07901200b00715550700b43c02400041d0000184403421403516a0024400450074800603444101900d41c01040500c40c0c1d00000b1440034560782590385643c08045c441d51144940301e02c6890450034000060b84002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 759750980 1250 759749730 759749759
    0x3061406060711101b0309050901050d0209070c0f02181009060f030201050f0405060a05120606190c02010e1002030714030a0f0c080f040e0105030c120616110111030907 74
    0x24000c05007508094083c041c440d60a0800002c40c09100c000c901d002d070b04100911840000c140310740e0707070120028280303c24094812010f0340058000d155081ca050016941c46009544c841401e1a214001180c541420501c040841c075019401c59500640035150b0070078601654804c5400c081085126a51226010201c80182c0310700f600f9490071a000348015841075004100e01460384511a040c0f548903400250f05031300080b49080841d00004013100080c0f5249940d42d071194080703076a613040c800301a420301400c15512120804018101362050116030103058030b0140d5000c054014401c070200c2c0e44000c0e540f0740c41000152a20035091016810701da100000f110702d81e6010b56144442d00e0800002980c001c9811402143e40380c406004448504a140001c5c1c8003c00202084100f907526120501d401c001010000314021250314030680c02e60400010b65603000120142281d1283c00313007170b1040310341c1009440450400c0d400c10300c02002103032035400614080c80d800c3c42a1000d003580c60445805a01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 759752230 1250 759750980 759750983
    0x6070915120204090e0c010f02010203060d080d02070507081b0a0f0909051905030423090103080a110a11010f090602151b0a020607020d110604110415030614060607 72
    0x150200a090034592180300491422a010480581804e4036049408151010090021010303409400b180c0904d6911000301c0843c040c45000031807541c1003031000300d44071200c80b440140c00c2d003200080c06220b87d03072944d0403500d2032a04041500c01803a200c036030743d64850224900840542c401c0701180c0700c0f0b17864800700b450100c841c03284805914a1800c80e10344003070181400f0554050180001000000c02d9008220441500c104051581c5074280700c3d80c0d114107500c0c5400600303080c880000803110b41e100c3c101c55078190b94000c40f03401d840364104e90040b076400c00900c2c650a13031801594104400c1084c0b000104814840980b6240401204c80004551540c070354807412005900100d000017124078011821a00040350b0120f81c0e10003507100403803001551005031000d005a22020821900c5907061020842400c0075103000b1004550506078907594101c040c0c009070003200851019012580c2c0e5a0007480d070b2102590300309034000d69074206140140b5022411100b8504504001070440c5083c404446109 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 759753480 1250 759752230 759752249
    0x40f0c0b090901181401030c0602060a1109010e12030708030402040f020a080a200408060703051008070314071a0c0705010c032a0b010f090609020403050303072a080309060709 77
    0x143c1ca80303a6403080c035640100120403107950b5541125201d041d03076102e05007e10b004400d10241d60f468504021728210004124507491460250f49405a10448045a51004d42440e010045007030040018040756103000c142c001c28800018204c04002d01100030f035200d01d008940400503402c004d4040c100b07030301c02c80c2902c00c0061101c000044090000b40c2c8821149003004c00841124034140d614401168429086426281c0c8071404104899615000d42a40f0a8028040041781e07480c044a141e50313500c182c04000c1ca4410402c9400c131804900300003400060a0383e508024605c1d20394511003800d6840204001c1e118014200082959405070341c2948542e0340c10781da00386c1d0001d81c9070b046150400040b652620782000d03584405010480c18054035010b840003580c40585503180c80e400710215a0039510101071140180400c01c00f00342d0200c15290701c40900d04011408045045194070007299010b003134482642c01950344400d00c084070303028501c901d90040031540e161300e40000684942c40d2038413a50100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 759754730 1250 759753480 759753499
    0x5070b090a0b031b040e0a050604090c05041d03040f1d10120609150608010e060408030403080907031406010509060d170a05071e02100f0f1d09040f0c0b09 68
    0x900b520340e002550b11044010749680910505400188a5441031740002186004030041c4500f01c169480b915030800c0040303400f0400021a0303038030b20b58181d406100305449603541c0c00a000101c18401c5510301088418010384e07a4a581714000e5082c0040c04cc02100074100307010050034490b02d4050341145c05410a010b2100400b4544120b0700c0d6504904201200c401380c40d085100009011600f405040c0d112003080840c0075810820303102d084a83d4812902885d60041083c04007291441007281d401a425150810956071015078043c50003034a0340c0010141c004690803269800d0021440c541a540308580c110603684591042244140f00c1d00300140841c05002e0740c2c100048900790051041c450a800d150f410308045854115030740740044480a00c10805846410443c81c0c440c80c001002e44103400c24481c02c030501280109001e002400343c0007031100d94030005003030010642c1d60740d510510041c10032001c1d1900307240406d14a982c0b402e049940c01038503000482c84c0100201541c0700400c0c0541406030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 759755980 1250 759754730 759754739
    0x7080105040c09080a03091a091503130c0909060b0103020a05180f120307060b09190504080d0c020c0103050711190807050d170603010c0c0305090103060b031305070b090a 75
    0x14000381218000740f15001034000b0780c0c00030038050071011a01130f440e4075854500d012680d003408803429051422022042200c070103c0e40ea0020804035004106004a0f1240d80b0a1450303209060400300141c20640a5280015050015040302e1000c605c81e47d01440262203000c015020303402440c44200c082901400749500c1d0602054a0302601030009103491901c00000c030200e807100f84211b01c80c040c150070026840c07051203818003621811100c203907444119498045a00c41c42103014540460704103440304082000d008813103094079a400b0303015504001031855240040d50b9148a6890940420305140001d95254007900c9640c08440904014200005180107107100d02030000034211a2004288420b00c04200c0800c24180000325645403402c0c4030800c840e80f4950120000c2059210b6030404818178030301c5501c0103030641540d42c581816500c403210000140d015000710f07040341c0c800f600d000c02004040400d1012100f00140500c043c6c07460607071180c40e2a01981b203081e080503008500a1420070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 759757230 1250 759755980 759755989
    0x120c07050c1801062318011b080405060c03041d0105030c0a03020a090c03020f180a210602070204021209011b0305010305070b0319050f0f09033108011b021507080105 73
    0xc500c45044903100c00080345103040520290046011807407031b0f031a054461141960025500f5034481558074999803581c1c0b10b0350f141882813140e40200ca0103800c0100e001842110108182c41c003030001e9050705980009004416011000c2c01d106007886071265000c4107400e4207203000c500c400d1740e40145c101c102080c1051a8640a01400b000360010998200040040c50307031540c000d040c032512482007131420401902c08004c00504690864102d40c005680c0942009a80c0282c401209a00c4a409612160240006002401140d140b104556046001c12494120662041070750742c48050604d0500c0c0c10444084040320402d010007040d0741e0003c003040c4170705448030001e5548100c011a982a03012000810007003a00c0058403080c0701c02d00c0c020140680210b190304101c1d84044114000c5040c80c10f2642d40803545184804080b01d0070a0515080b24035001d0301566601420349000280300c03500c00900c8941400194480e0b5a0050044c00c080030300c440300016189000d049203650381c240c283d08020400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 759758480 1250 759757230 759757247
    0x221a041b0e0a0f0905040b010b131a091804050d030b0616020303130b03061c050c0904021906050702030c0924030307060f0b0a080d05070f08120c07050c180106 70
    0x181e80c00b12240c000010ba10411010480c0074000f00f602c00320359401d261a060282c0d0106801c1030403242070a024610900710320800706001c8652421691600c0000d4005020271441f41804c40340d0401083c01c03015402040040c85607000d00c1c400c808030b82100381c1c0f0f540c1c210201c0740d11680860340518100039002c5003101e0300d2400052580005d080d20300d003902403001d10b1400c039942c2e407140c104040007000f04400f500d810502c0550b114200310b000c00920199030390303451712040d0640c00c0701e11070f0032898089000d40d1165000401214078044041006a0f1101c1c4050030940204c41c1c100e10a1280d51084034050410543c15030260280040a005030f042c03040c4103141442c11000040d4061105004903408200030740a0032048a004900004e007802030b02c8140f1504401d95003080f8110f6005841448031035601c00200c5940350f4008114803c001000d25003a00a881200c1c220385845400c2000e100381150004000e082251041080b505030061f14028407030203004c0a101c0881070016000100a420301803080e1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 759759730 1250 759758480 759758507
    0x40504050414010c1e08071205070c17040f052b060212042904080412020f040c02010c110105010e04150e0d05030901152102221a041b 59
    0x280d0190390090340c0224219000003600c9000a0810114040d41451861401840e01282e24006c3c4c0c0901c2c0c15034000d450000a40c1e001c0b40c20075903c50014010510814402d803605134403080c0e80d0440b420b0761400324680d070864040e018000c0d414420005103481d01c4560702c1c41c40951070710015a11052904406040a110201650318030780030000d5080c01c131449040701d44501c0c0700b0740f611030b2480071080c02c15024446507a164625442e064050001054002040da4101c030020724038241d81c048144040fa040008080c1507581050511244000664040d00101e1108142d035940c1d91342d03d18030380c0312542a51070a200701d003a540c0e00c81d03000c01d020032407440a4032400306015070040b4100c41a83c0040d03181c80700f8043e08100190000c428800d80081c02e0050004e49030702a10550095810807100050744075845081039680710207100340001315219400d41004401644213401c03811005003a6940280c28414150b0143d041a80050100ba14041c81107980b001c82c00220900e0100f180b12060707403145e01c401034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 759760980 1250 759759730 759759743
    0x1202060708070b0a091a1302190b0c010f0510030f0308101715070306080715031508030301030501060e390d0b040c030903020d0c03170108010228050405040504 70
    0x9040b01003034255002e180202200c1c00000303050180c0e420049115030212629421001907082071191492417026050121501140e00021144600079529802007003580504c06407003000c0b480c42c944590660210100c843d400c1014011642c4800e410740004040d400010072000c03144c8140800700c2d10030076140d6030041400759005106601d45203544042c40322074600e140c0729405039072403160146124007660b40215072410b0034440281819a1300303480b8221401a902c809101e40c5080c0c0d50f06210340c010002454a000354103040b291280ca07029101d6000340000c1e00c2079030071310784001000c40e18545d1651045509009118085406d020b10b4140c42d101006c19221100c0c00050001550310804010490b03010106030000311403e03904240b105488440f01590141482c1408441c003082d004200346441040038901003130b21039014a000d843e00c1c1d0403211008446c0b032404001190903271055004108456600003440003003100d00c18440d400e210340d0480304000440074003081085090541003d074003c2d00c00c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 759762230 1250 759760980 759760987
    0x51605120712060306110913021e0304061104241e0315030209070c0309080318130e0105040309061d030c130b040908090a0b0a05070b071b1b0801061202060708 70
    0x21112404c3e40c0c60014644e007110400103a04600c0d20b00702182230f88200c0e020714154105003541101d50b9600908242d0307013420200000000f030801c000c560110000284c9061882d4499071180482001007450001e812100b54202c0304568441d03000e0103262000c03000030181c40c1c800d21048401100078081000516001e2000c0303100c0480180d40c1c90010510078840359a511580c403900381401010107000780d202401d160400c00102041c4001070f0b40351008004152808400032107524403e400070040c441c4115015464402800101a804281001143e0b6903940700341000d040c4071600c170f0058100c0d015043c0d05a100380c1803040903041c0510f40490102c1c1c1000009412901d105c00700c0d01343c0b5100c600c01c4403c1343d0f0000c2c40381414036107118a070029010078105141083c01d403240240142c400c1c05000307003003071064400241089114443c5071007015130801603020359000340d1800b400d03500400c01c04010034055861000c00c550703405114030411902031001112848040380c00303102c0d03540e1080c00d003907880d40300c02c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 759763480 1250 759762230 759762233
    0x5010302071b030b270303013b09010f060509060d0311150402040c03020a3002180a1d06090c1c05060f030c0307030f05120301060203040f050904030e0f01210516051207120603 77
    0xc041d001d4034042250627400351441d0020105003103589c640006c40c0c50524001c024441c03038852290f042d41c8100266110600305140741400e0390740004081030080507104e0f04a40b00b0b104100040c103035004520030b81e000c0c0150382c00703803109406070b0085c80140030014a1504003001d0803041e1900c400034000480c8451040c455090f0750840513a40f100d01036640030311800320446801c1c101440c4840041c025250b02e61644900e062840c7c13100b09024100500c284030b26004641c00d6491803003100e0341c2c01c0200213948403070700d404401031020780012500284500c041e400303200c0150401245022228a004000c1d21116085a94843d9008482001541c1c5c9205502c143c40c00101035100440c06414250000e40e110341ca010100061031b0f40d542c104501603005c1c80c05200020750400c0d41e20b658664100c0324000c162040400480d04404080a8500c140009114051044c3e03020360140c1e00400d4018004198081c12603815511403080020f50940240341400050b1800c5c0310b02e6007401070f0f04480c02c011880c26079a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 759764730 1250 759763480 759763559
    0x10302061603110d020c0306010f0e07140d0603030f030e01180312140903040807090b0109060509030a08030106031d0106030f1401090215040e0f1005010302071b030b27030301 77
    0x6040b92005d41d012a10000a51404100940c018084d80e13500d503401e213040c002924101e29024000c001440350a080c1d0051448900b030543d0a503180300d107010000d9550360706009050311061131000c00483e2038600c103007200b5201802900c021203621074030007020b50078a076030032260356040c0c07040340301c0721a0b482480b510140008a003aa01a1001c0c40045448a050001207402c2c54403d030701080740140381180c95240b59801116034000c940c5542003d40d100d61400c00072030304010800c4001482c03100300000100d000780c0c240c2c0c0100088941c2d03181e0008014a82d40b611802c8030820b0002a02d9110000340440014241064000b014108040081244e040079400305110300f0f00d403c1710054594000c0750034072803580e4004c4000da00201150902e0036074146400726807840c3d00c480c007880d4101500003a10206022182c0c00754480c0b100c50130100d155130b17540d905041c0c41d0304200303a4a079080ca18000020f12140d084020700d030780b407032980e02c1c001c0c51643ccd10b00840f400b20901034001520703802600e1003452848038203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 759765980 1250 759764730 759764743
    0x715120212090303190603020f0f011e18060203030f0a0902030f15061002010b151b03040b0903070803040308120a0b12101b09180b1207050f040501030206160311 71
    0x10764200031904e9003003100020710514031002180c844185000c1c003c0000d40ea07400110000c601080d550100160041340040300c000c1d1524450034040ba298140261103075510a02c400340d400030810b00380300c5542d2145000c0740c0380e02c010749070083d8055006012880c0d081d03180d84190100c41c40141140c4925164a40190410001642503400b0901c10820051282021004000c090900e48020080e9007074500000e0f40ca200f220410111400340030410010110060110110f03c1d1070301340480c2e482e01e54658201d04540d2110780e00341c2c041d01489000043c0e0fa00004107940507a82d1104401d41071240311060f400100400901c21440b00e5206d070340d104441d0b1a0039104000604104000e40010440c00b42a40d064824209400c003d0a900e00c050346404c5600240e0081559400585d00c01d51401c01d000190107040c03840b0310554008042d1030403131007020300003400c0002c0b01c40c180c0d03d10041410100401040343c02c24400a5004003041191005aa810000c0d401205200381801c20404540c0313180c517840c198 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 759767230 1250 759765980 759765991
    0x50f03040e0a0204051c050f07031119211b0311030111030106021009050703080408030414030307120e0102070f08010603061b020a0f1109100905090715120212 70
    0x1000094207215001114030440d601810010003945480d1030880404c13100860105002542910b06039131008001d01400321003000ba141c1000c0700c0e01c15482e8200200b0340d070203c0b0070301441441c01003942c1c808240111000d0701124000307038030a05401c65020592030fa800b2158021651032165075120140b02c44401c00a502540c080c041200400b180f0300d0a141c01c60b24490841003c0c1c0b0000e01c010816144d00061580392502c01e6135001c03800c1e210a03d8494a0202c603900010300300c107000300340855138000000140080740d0704840c10303551003407414042c1034907482802405000d07040102002c60600d0b0241d400e000c685001881241d00c8243c0e21060741e108180d060308140c06994441d1020028480c036409034280001d0481c4c117800c1c5107089013001943d582111600100385044c00e072501c80c03d000192901a1506101a100c1c140d10300d850f1440880007601030041d0b0700300c01e18000120761508800680d4006481400000c3c641c036441405054400041b41202e24400507000c000f80d03a903010300700e00c159001c0c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 759768480 1250 759767230 759767233
    0xc07030c0c12020112090b0105010c05010e0703060203040b070306030c0e090c0d03020c10140304110604090e031314011d06040306020c0102070c051c0f030c0f03020f1603050c040506030a050f 84
    0x140d00c0010701000c585c0411211060800b0200c2c0d021980d1314503e241151403d003400113059000d85050b9002d00003184040d08a03000f000000003d02207150001d5200320308ca040c420303045a944110a40c1229421b00011708040c0356070006000d028250f0107003c1e04a0750300c2d41240c15003940c0100140c01d10030b5003d8102d005800603050300b203007805c1c4000f1318003960300c65081c070004501082808040c81d02000b8400b8240d08080c181c5d120041d101c6004407001341c0b694450a20014603007925140c0c0c4c07030b84401403581d403015a0300f00015500c00701c05d4146440c01016942c00e50a41e440052a9800c4428284003070b9112104000c00330000c3c00a10003080c4268042c030001d41c4540980c20940c2c402c0c400d542c44103000c1c1603a04001590104845080009180c0c030106d41c010510240c00d044900340e4882c9401804110000c8000c001e264000803c03500d428020801c03216840394009000c241002144001230003070788a2880e0300c50a1074185c12043d840503000e0f0459500c03c121b41c659078030704002d410458040c1e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 759769730 1250 759768480 759768509
    0x30b061923160f0c0e040c050f0906091f17011b02190b090a0c0305010b100f0f1d0303030c0a08010f050a09021315050c1c02060c07030c0c 61
    0x8a80c1e40300c039452031a034000d041c00342001686580300c41d101c42c01d07003002420240c601034160100107080b0000b0f00505118400c2010700e2615181200300ca4600d40034080c070070000044648110720f03000c01a40c4c030401c4043c207120080e03101e00c5040190052203d8441c00507451011008c40c500e9280c0b0020003000c0481c0e0000300da4290b00251000c003000c8441e03181d00031900407124400c40a960b09031400c40407035001504010981c1c5000324070342002c00300f04008051000e020b0300002441015005200250401c03146403090054502d8152055905081c01e0000325080b041c054020500540304481c00f03207003048102c00d00c1c0324072400107170440e8411901d03e003070180301240103c60b0580c80038002c0d02404804011928241c00e110000d140c680842c0301b8100700c1500058228400c140c1c8d0314024000700300d41c008031001100540340141241d00202d4010f0b580340700c0c51200359690036100403824127614035600503143e00d40712580f84108560200000b5020b200c2d100128074002840400254018004104a590b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 759770980 1250 759769730 759769757
    0x181f0e011404200d0222080616030f060303030e010c020d30050406140c03060a091113060305060139030c0b130212010218041e050a150f1401030b0619 66
    0x1140d50003030841281c81021032209104080002030040c9d0003400c4042440c44140d22040110058001c0c6241c41d10790798180000001015055040f0341c1140030b005000b8070203000d2185080f69a14140141d01c4d00064000d85099400801c44403608400040141156034006408440001f03407a4240c0f021605955250380003818005050131700c6801891400c505031070b60030941e0001e02001020300644a02ca6a1050301c071f201008030b4002c44119800c4040da00c40d13482c0c2e503100040d00810044864a01096520240c0f607070109546d070300c0d4074803800d00750098150b05030031407001440c0780070a08044050006817074207500402c3c2c00342c031a28800e810f04200c1318180111441800740f802c40ca0001104281e005104092240310042c078401302c004402e50300043c4480311001800c401c001c104140040305403910701400003031155904110000d171102c20703580500303d0386c2e64400c41d8481c032144a441509440e034050101250300c60f810000811100403c1c06041c14054011070324200c0c0c0603c805030108005601d00ca4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 759772230 1250 759770980 759771007
    0x1080c010206150f010c050f07080f0c010929070510110c15060307090f0501080111090102030d0504020a05060f3106050306181f0e011404200d02 64
    0x4a0024007031000c0d141d40d0074007a0922101d0a90804054460300142c094082c190348164004051590172034200c0c4e4018140c101c0c1180c85801502440c90315010304611056042d90000d134000da0404d040e901e113080c4a152115002d032000e80003409813441071850111800100411002e0407800380500b0290101c2c0540c0101c0a088a10700004090b6010b8280860114204040f40c0b000d1844030282d40850141e6502000038201883c58100c034071201c0ca403600c0c5880c144e819a00c0141a42d0f00c0c00000c2082c0015a541039145015104195005078400c102c0c62041c514150003894105201408803001103031a0000150a90000210804811800304032219032040d14042580325980f44100d040b248143d41c49250124102070288505000c0b0000c00719490b601c400103071000271107004c40b000404d810000741045607105109041c914502d100440495184d0054502074103c6241c040000000140c1c1c00501c40a400d0f08410311429406007495512040d01a00091002c060303002c500595950389602900e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 759773480 1250 759772230 759772243
    0xf03040813080601050616060b0411070c0806040c151110020a0f0c02030c06070503090901090c0f18140316080c01030f140a0504150c0906030c0216050f270108 70
    0x2c9060b44003400400c00e03510385200315908084d602800003043d15403424103c01405c0102ea840c0d410600d07240c001242d12102401501110b44110b0680b2400359881403050350b0380209550142ca02ca6403840200480a641d03101c2054000150070142c501e01e901040b064249a000024040340d00c2c0c000401c05646a48050242071841a500b01036100d266541c02195403290b0003040765000b02400107603038080c003034104292401d012006001d24403643e102c61948010308070407150940458a120000f4603220b01402c2d0300f0f000c04807000024401c991a00c1641c2c4802c0c2180e2400541500a80c45882c4020300480169806051040001c080c8490200f00042c00c4030f8444514000d900d00d001c10b103d820b0f0362088510f40d08055840b03000720b6552202c0c103040d01030f03580000240d04098540030001c00350700d400611400c2120300da51000c0000b400581300070798588540c220b40501100b810001440b03241f40c00410080e101a004c3c000d081c1284126488000703205000074101405442030004204458040042 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 759774730 1250 759773480 759773489
    0x1f030b040b06190b030702190f06050f040503030403031a040c080108061303090509060a050d050a0b0c0703020c090703021308011b0e01080a0509012a020c090c1b030f03040813 77
    0x1080da403036444103804503042d40540207013404014004041614280b003001a032503500490403902c251400c0728908207280c8603440c0c0d000c031100c504100009820100084130a882940c00c42e014520315a107940e0100d00401c0380980c03095100711180305244a40d11035120f581517050075900e4644855040080940ca011401008041c034050450b040400099000d60050125041074407010b006480381d40c0012071442140c4c020313540200d840118001840000903208840c113014041400303840c2c968409000341403046c081c0141c05039010203491207441c10007100d1158010f40074940141895004041950b00c5d110960002c081f6a44484072100c0f0015504004106441d030786c1050074429150000290805030000c006d85901540c400029500c0102034115103036040c00c020090301c1c1d02d56150313251050303100d040e04450010322480b985001c580c1820581035020301c41844035581048180303a440c140c00e008409140c1d141c1d0005225181c51310b07040360069401140b103404401c0d11145681b01302004551a60720 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 759775980 1250 759774730 759774739
    0x30705101403061f0c060515102a080a030b09011212121b02070e15010c060f11030103030e0406060207092a080f1b09040f090c0b030a0e030712081f030b040b06 70
    0x440e00e070340e841203c085640e9651303003040340d05070100316500140c5201950361402b00c0400102d0150810002800600b0451855241080700c50140340611203244802d010f80c1006c2e0320a4000c01012030f02d480001560000d030f41c6000310602818400480643d03002840c010f400794021114102500d40500068014000c10340b9001030702d140140f00450810030349481c950501c105000c0103018420b0300d40001d44003040c00300c02401844c82e102002a80c550003484150009034150209210515040c020042250b0a40d40100010740c240700003d40100001c140d80304071031903188142800100070404000c1d0901050701c5400240c600a00c0160740f03100010071001c500110110482c820305810303410788110303030800d442c0040d942c2066080040200181340001d00244404c100004041e1500d20045100f0000031401307000c41e00aa040e180c3c0e50380105140103013031000864800d0042071140f882aa840040c60045200b000250501e65403491240d40082d203006286004000500204447c0c1d61340003541600c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 759777230 1250 759775980 759776011
    0x204063206090f03030c1f060b0a0206010501050a090f0e011a030f01120f0602030a090c09110904020d0b061c05100b1903060b0a020c030705101403061f0c0605 70
    0x145a8858600083e120300d21030780030000c898904000fa51500340c0d401040301c0045801205054244211111981e0a0f505106010504070036a40c10348440d0304080c1c00814499081c0001528540c20001c0e0303600030080c0d80c1c00c002980c041104201d2004104100100c4035039410409440325100037804001e0040074204140722100c4080b29940b8111039001c4460342c0c03203021610740280129402800501440c2c008818418100195400100b6140c4506142d1b0f049680d94480c1c0401d442d14500c0e894440ea4003030041428a0030260002e0400211110002490700e0054001622541225055621685150041741c1d00c0141a00c00c0360382050414003c22610361a0091a040900ca00c402e003a00d034140d44c2d100d60796603034003e400002c040c06082405684850380284020741d11400c21041303501c01d02c2200400582400d010030300242c48002941c0b0145d0b600449008071030035600282a244d00100041700080c80c0080c0480010307500d15185c2c0d0b031183d100b1303c181044800c1e54000b410700d560000160 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 759778480 1250 759777230 759777329
    0x5060604050a1502151e0a0509070e0a0603060c020a1a1003080d0e060c090102060c190f0c3008010b090d0309080d231903050c07020406 60
    0x302c8480100e401c05105800541d0141108900f4420a4044020b813980402c06100c5007001d0105400f1b003403c0501020b2516656071003d8906a8606031400314003a0407070700e418002d0b00101d050440d480303103800350042200d550760f50329201142c0510320690016003001c00c00a040001600700d10889142d1021310f518541010081d03592080040c0c40002c0800400084854964001782c0100085022a605941c0e0340d2400c090006942d52224140c5070042c002c01001a442103000c3c0156150354000c40e11761120710b11010000d540085c05082042e09110440c0284130010703842040165441386d25440c2c9441e0030303e0400102c1120044840544140050200180914800c602c150f4148401c1100c1100800459007000c1d02c0c0d00b800781d007004038940220080708400d039400030030284007072403101d50a182a2000310780000c501d008240c05c1140601010911140c582e1003a0031098022098040d200d280c946a640080d048590a600404840d000d8002080007420300d0b00c04000791621180b0102800110b1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 759779730 1250 759778480 759778489
    0x40e09010e0d02030703120c0c0f06020a14040815060111060703061a070b0f06120106080a29010e15041b080601091206020c0307020d060e0615030303040b09100603060b03010506060405 81
    0x81002c0c500744075581d01054408948100c0c1040c03110340c2c2180d2131803403192b9242403880181d4408891500400c128803072051088290204031350882e0020006049003208244040d0305007400a80080d04000c0c2050186420390001c4c0041401012191000600380745802c030a0042e80b501c44042d66510703a0b007445946c01040c049000300c1e40c08060081ea99a00d983c452001407022100e2601e0444598138010010411050004444030101c2c054030454940c1580045014000a20581541448801040100803000f62110030a030422620f2810400d01007195001ca801c5441c003002e10724200c1d10241596200c5078119420940110080c44e0240d0028203140c0c103405001c0203030200400c82030340040c9240d02c60b4070601c195009164020480c0b00f81420034108140540155800f44000740280c0002c14003460007402648010070010740507504580d5191103950035001c00408030201c0d802143c00182c4140124825900a0b5201c1d91000800050304010300d400c4031001807006004901c1040180720700d984 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 759780980 1250 759779730 759779747
    0x80103150e0f0d0509040e01020408120306030106030b09030a031413031103072301060503031819031e150504020f09070201090f060f0c031e11040e09010e0d02030703 73
    0x3400c500109610400980d0946016003000d81906030b40a11210380380200d6000005140204048400303000340d041ca040011308034456403240151035440140d210304031054070301c00b0b190310040060000600503a40e445e00c100c02901141c0c00640e0380c1000400b452200d805d0710501040b103000c589071202e02d02e0111400030030003400020182c14009050a90310b80c000c0100300316886035602c80c061241440780c1d0340c0180c489032511001c0d80020b50070a880820781e8140002515031000320480d624103080208818414890305810b01420024505440840460080081d8412541c451a28101028100e0600141c0079401c50203442807541020140409603580785c00d11698840215015461034491850690042c00f100000a105900d1400703800d007841865441045003089112003030200250281e401c50403101021040c0c9420b0005694070540444203500000c0040b0f100070f0994036242d15215124200d02c403c6a000b80070307a440d0b452010070342d40d052100c01030307058143c0021070031b00d4419980944120b8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 759782230 1250 759780980 759781013
    0x61005120c03090f0a1716060204120c090902010807050f070605011401090602070311151207020c090609360f0d110703050312280f2007020918030406030b0a06080103 73
    0x102d8002401c14144031f4042c50554045400c55445607a202001e04150828000b540d14203502100040c00700725074042e074901c4982c16500c9240c5580e450205450b02c0d003010220b000c1c032000c14000306000949078840c0c103000c0c10008586548001080000612445c12508030104641000f4010030000d0700c9460114800101145d4144142200200302109406407140341c00d5141180b00034445200c1d000309414000c464180e907005600d59940c401e100c0707101d10540e080d08413140c0310100c400d9485410414085160414221547d48000e10301800e0f20305201e0b80010b40158101080319448207810080b00c42e00d0102c00c001600110707241d5100d0a0b1240503180e0349000c1885d00c84005000e4040349607128544a4012820031075144615101030010801d4000b11101c180c03800f003500800b01000b4014210220300c40d900d2601e0180c25600b401071300c050141446041500302d441c0c0d640d0b00401480038101034813039a6400280900d0410800c03d00e618245e0011041c88200710060010580d0085a03100701c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 759783480 1250 759782230 759782273
    0x11a0a0e13030e0d03080603121801110111070803090d0e03100e0c0d0b150a0f030222051e1e010303200d02010204050a050414061005120c03090f0a 65
    0x14018182500c0f0071624186840d805035800045004050300b1403e0a4001d0100340c04942c200c0c40c50301e420030120722400c0f18642041c00440000035881d8460104024101c9000c400440d01c48080140c2a00b1a0030001742100c01700004000c109a4410800c40641001d61138a881b000c46002c04020a807280c00c4a001c408250b901c42000302a00c1c001002918040300c00034100c050b0b80c808600b41420244015680542c0d2210303c0701c046000e500d01401c80c0b606844a841201c0d1085146900300558803811a050801c1c9841d01440250b8800076403090600c20013820501030203010645161080002c402054014144040300b614285502e454001506680e41414000c0a180c00c000101d0500300c3c0d45841c030714852203036031210f40d44994103402900071030b01c068418218a540b25000c002c02e4840c24411079954004800002d9034074036018826010107105410441d26120100044035070303038481140d042500103c00000d0001d805004c00c42c03a8200441030001d002c00000e19640c2407101c802886040154 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 759784730 1250 759783480 759783511
    0x3010b0a0b210a0f18031b05100c0c021014070b13050610090e0a050d0509191512050f060906030c09090a050f0f070b030403030207050f011a0a0e 64
    0x2140400d081481140c0c00c0c141010690746403c15208001e0315141200c840d896080203805800d01403a040b41c128440c0c3e141e00c8250310222510800c81510f5041c02040e52244241e00c81040300c46078a00c21000700441c290f4402082c84221300500c00d41500c4560301d00100142c074281d8481000d14001501e01060707101000018030b0315600b000d00c5178078800150113061750240c2024080507540030100b503030456118500500400802c50082d80d1241790804015045811148407100c54912550040840400043c80c17a261218032150301e83c90f00c1c020380c0100030f55103000344151034100d800020105020704410401d1040345403400000c424080094a0180641540c101103006039900b80501c00e6003a4000c3c4c0b0003050307407510b42c02c0d041c0e45100541080da01401800440440010041043c503803507035040b0b0040c11341c646822941c00700383d440204280c3c10980e003880000700040d410702c9801a03502070300300080f81281100101404018041d40214424001040204403058480818130351100200d41d42008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 759785980 1250 759784730 759784747
    0x61d070f0e04052e0602060c0c19061e020f0912071220090c070f08040e0c0d1a10080a020904050405030a08100501090b070f05030a0201020a030b03010b0a0b 69
    0x1c0c4501c028900380e900c14202410400c400c094070b0b00c18240300c0c441c07400140a0704041c031030084090786180101c0b40140c001c40700207100000c40900820b4516100022108052803440300c0f140340781203410b000c64a954030f883e404140b880c060640304a8010307818008616055407050303c180e0310b00c600c1c08a0f03801001002c800c21001402444414014040d802e984404500545414410f60084119034810351032080445003460074241a010301c101889041c0a103013401503120692150b504820844003d04204000304200d5152100107005545c50445107459010740a8400c0a485070400c1010300d41110702d807080c02d03030359aa0346031100149440c20700f070980361504004903000e8400e6806840d0403d08103001e00042100000081800452613902e84080e51110300c04a400300c842846494002101034105212400d9101c0c020400f00784268824040c9103055580c0c2c40c2180c201c0d022400c0942d50119070039461f0354040c0116440032800310003c1010700d9040d0300040d8040441e0058802c0301102141002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 759787230 1250 759785980 759785987
    0x140706050915091f0b1c11061207081302030715030b0406030f0512070206070305090112060816080a0510111b0d090902131503020714070603061d070f 66
    0x1100740555031100c85440d00100f069603d40e54803543c0914005050880344840403180704581c1802e1005203020710a0000c060103042800541400b611407140040c00690030356a55001407000c40c01480c402d040a19100c3e001a00001b40140103042142a4501040050343c000c1000f805a1f100800000300c0060150030840082c00302c0c0084541041c5003080120a0002040b03140b01d50a12440c11102880321a83c10b0f0315080c041e0900c02500604244a01c100103400348014001c00d0b64185490004413858511503c19600350b82e0001b078045e044030b590b4102100340055007070f0260450340e0042442038000d41c1d40c6a5210100300840a000380d44104000400c069401215041d0b15003807141da221900000740d094031950311130f400b0070108000f81000154030704e0310b0081c0c4810440380d1600039101031801e11561b540c84020300da1041016400c001020010740c10060f46622001c2e9a0000d00849042031406030451b802a0080041070400310070320100320011000d0a58043d10b2072500c0b4480901e25030068 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 759788480 1250 759787230 759787243
    0x906060309240901050601110307021003090b040c0302040606020f0304150c08070b070f09030b06090a150801230105100c150507080405150105061206120604120801061407060509 78
    0x74048800411260002c40b9061a020740c01a0843d100800960301da500055420007040010240039400c00d20012015241080c00d01c02980b26605010940c030102c0d9440207040081201c00b00c9030040914011301c00c3d424903120700d5000c0c10b1280003d0910480340c042581ea01d000d5440341c400d4400d000800d0f10206441030484100c0070b680721544507216000d42c5811400100216510000103900b0601000190700c0b54401c5011641c0140d02d60184d500d601c401d0201c905401824905840d455080320b41c10b92a04552040050540c400001407203c040d941d01b0f8602c10411040342d50094072000103102550b140000032151890030309000010903d240b80045182e80030b0588001494542010450020341151205120b10303c600c099a00d144000c00000200040c00e00030107401030b905100312880450038080d034580240004181c810390a144070045071401804035822125a812484000300554002200502400860400b9103103605d41c4019481c2330701815402401d202d4031400450603403c01130155 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 759789730 1250 759788480 759788503
    0xd1b02100b06180a092f0301060503010b0a09082a04061d04240c0e01020723120105010801090201080a0b01020d0c23061f1a0a02030c07091b0c020906060309 69
    0x30300c95002603003200b4031101c61804400c015103000c0b54080015941b60000c490580d080340e04c038a401d59081121086843e042580d242003440f00040012407034440c108001e45440b03040b007201c4510a40421900d5001440d80c9490f20301031820644103002440d0440c22890107041c10b00a9805165aa800d001000c0790a140c1003400000326a51075071100303001c603040b2040d240041e4980c03104100c905401266201c56500c07442500c81140c41c2c164450920150940845582c001c0c050114192410780389801c468003a070210b07481d695914440030031540c10140c81e6500c00100d140420454030420700103910740d500d44424038100100d1a5121040224440160785182101082c01c0c1c01d0070500e414090743c5400c252940e0405424031610074811080c44298001a00d050701c0030440c46590030880d020458005c1080d001c19400280241081d00c0710800440005100d2100007042c03150080551500083d120040d80c4100702500ea85030300945c580c03120051700047c00384d5040380c2d242c1d0b071040e4590030650f40049 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 759790980 1250 759789730 759789749
    0xa081b0d060e0d17060a06030c020a150e071703030a150305030a0908010b030109260408100c09090b0f0f0427051603030c0602030c0d1b02100b06180a 66
    0x51044980c0300008036615600e505072980c6900d640700f030104d4400c0c41c100721000ba5200b00e00400c14072041e4801c3d00040380600c01c41c0120f40f03401c501640e0b02c14111080c6a160640c695440c0c0c0c43c08928002080000014460b9420890982d6407506038a070b1280720007010f41e0801c2e81c4521108031030740000e03500c17a002941c014040d82c0c0c035409003842c0102100d05600c02d00c035a40d820465400078915062040b4402c050340f00d42d01154605040044459044801c0c600100c2001d05002c00500c0c4103081c018600c1060b900f500028809140c0c0c000038020030101d402c002d80c8680b51040d010301c070703803107100ca80141e0840031260a0324240703c08001a0244c81c4013142d0000c3c982d555400040392103511020454054461401c0e1540c640c40e101c240d040f550803070710015000440030000c0b900880d4842e4001c0d0b400c04203c180b800e00c1e0610484580098403521841050698030302c441c1c50f1203a03a410b02c4401200768060b07200b486001c6040c00003032040d02940c00e181c0c040007202c951040c2550398002c81500180031448 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 759792230 1250 759790980 759790991
    0x3050309030d0e0f0d0e0307051c02040935090904110301020a0f031404020f01120209040510081c0807030c090302090f040b0106080403051b01140c03010f050a081b0d06 74
    0x4083da44039013100c8540c0e0740902c200c0c9110b07000c490040145600d81d10f0007a00600040340740004202182549603110b810103200e0100c040090b0b01c07507014105006014800a50a64404403021001d40c800c10030004880c404202044c100c00140b88c0850b5a190411a490481c0b03407a503040c51490311008882d41d590541c4005404510903400c0304400340400b00584040060f49107848442010001c01c40d4002c0d07103c5200c0d11500c4666004005c0c085041310268001411b05071035074041811140300ba42c50711004070240d601040030402c20000d10303014820007400d401100d0300845000e841a180904100181521030701c0201203a445802020000c42c0c00404041c4c01d4240700c911410750322800d580030341e50105a039001040642c0a014a18081d90781540c40c14a48403983d00700480d1010340318170084031035480c0d0040e0f10300c89006c104841c0c0070300446924541e41e5450700e40c5000e402c4411754000b0703016004c150300400980f2001b113101c10f52000b640b500700d41008000c4002a0452100c3c95000b0800c0d0f2515 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 759793480 1250 759792230 759792251
    0xd0623181e1e0f07110a0f0803180a030c0204110c07030b1f0e07030b0a0608010902070c0b0304061a0d0c0504020f22152f010b1e030c0d05030703050309030d 69
    0x10b00e04180030fa103c1781c4940713100c440440313001c40c1c460400742c10142076205600468800200e0840080d41e000a02041900040380741c41c2185040a01d82042600010700c0036450800b50700d89481001d101860100300c8030318041450010316100c405920014044e07801c0d4034000f5030b0300307410b450b915005038910700002c1510580340e2600713200144081e01c5000c0042d207007050102c55402c06503690025100f6984484416a01c2d282c1030101035400040c044410701c0030b1081c00101c041ea2200510f00a502c2054080b958441078500c0c0e18000b00c9201c0e81d284141c00c081c0302640465101d294100684809480140e0f0711300c01c00c444003244d40f0900b48508425802d400c50340309900d003001c01c210140c60f041c1404100f00d880e5100101d8a6080d1041603002040700484c68010000d161030f6500d40000d105400416030071030550000d581c6d55499504445101d4651072604003c1c07406005444100e00200c0b4482610300550329425a2400742042c01414400004080f64603100100192142403170b45000600c669101c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 759794730 1250 759793480 759793501
    0x80604020411191106060103061d0709030602031e0603280501060806040309231c021f170a0c0e060a2f012f0d0623181e1e 54
    0xc1401a10245c001d0501040d034640c464055001210342610283c00c040c12010310380601841c000e020716041c070900450000025005001130f42c4240d06895445410004901c003040006200414041c030039041852130700b844803080c50805175500c140d581003e1f10b10160345011401060580c011080d14800c1c841000100343d4007002000590301100803a00d420106030107030300603401400c10100d43c04408144424a42e40d8080c56504640740002e101d480c600900454595510380c1d042c010000003102c02e0500d0751380042260320309401400c5018100000720b488840107100c01050440c0070710586001958502e468441c3c3d103201032070074010803021541c00380a00c0901d080c2c811091401c134294242268041c06c0c4244003510382410751480000c074104107100f207080c52144c0c1b00e50f1359441440d940340c0010403011002c4904140c69040b0000d02c00f10800750790b08000901040100060805902d901045010240326400c0da8025123031450050040d20b803102c1448944a10340082e60f50001c481e410409040b61 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 759795980 1250 759794730 759794747
    0xb0c0d0906270e090109150e0636010f1401030c030807050a0507080d0906030509073602040533030c07050307030c03030c2c0a0b0d06090507080108060402041119 71
    0x841c01c051605070300d000c40c1000c00c0d50300d011040e03000307030304041c002030144141e02810b101002b41e5042868003046201413040350f112030750340c2040e0003a0754030010b08540d030b00790380b14044121403c0d00c1d4603001c030340c51961000300002c407a02004003100c1021682d4800c000c000c1100b0070348541c0c010140d456282c2c035141019551101140d0301c00004412007000034150b80603114040c050103424001d88200e9080c40e2900d0b50040c445008034800007080c00c2e00c07500c0003041c0d205001c01031100c03032005666185040100308110142255686c6146a4404c080b0007241c03010501030319080c804090540c50742c0d00d0451225072405042d00142c0b450200280090030982d001d540500c090b80310b81c170204074441c0c0704107048803000b04c2558504140d540c014118a0449003841440d64000c800800d452a00c40d100c2040c02e02a4201443c011181c58a45a0a0000314102e008007a404250341c035202c620f80d80b400c0e42c407a50765100588041d00441c1d450121081350500b1504171183d41ea0500140e50300d15440f014001d11026 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 759797230 1250 759795980 759795983
    0x3260405100f0e0906010e01080c0c0708100e0106060c031209020d150c0801080a02060c0a0219090f05040305071b0b0414011407050c120a050105010b0c0d0906270e090109 75
    0x3070f940c3c0141c4540d8a0203072001c134010601a50f03502c508040800042d141c10030040d06d005a4008180818212600c08010380c40250809002401195030b21403030840944e91403150059a42e414160103011155000f04984503903034061034803400c1e060758580c280d4000d0441900181d0050b50042e800002c0c001c1010702c1ea200182e0041080020744121071085640480038010403001c1d410180d40c12002d4070300440907203160220320007500c20780d260603800600c034890045421030000c100301d08204801480d505c901420042000d106128515003239a00824611411034003c068503240050384a091041c00d00c084080c02000c02040d940341d03210081c151000d040d080d29580003409a80d03115014451010a55520a038400000c1900080810420212400c5030901c2ca40a11400d0031b080007245090113a1030013418800728880e070f60f5249801d0b0a0428210340f12040c1031005191081100f6640070303110307001d14420001d10f510034003007500b00100c5a155503807003158121200c0050011406041d0b00105c10307613 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 759798480 1250 759797230 759797237
    0x80705070b011203120b0604050d05100501061701140102060105101101051f0b040e0c0306011b08070210110714040209030f01050906130803241806030d02030403260405100f 76
    0x54105d00d0426070300c16852a42e008807003840104000c0c240320044901d0740d0300c54002d440b1031034204035940c0b081b070302d00740c0c81400010800b080c1c0c12005580000042d01511800c558168032615910002c0e594007018805c0c039001d00300c00c40403550460300c1402101340c1d8043c41c1000b80100e0400c00f054050382203040302005038050306501c00040440020081b5801c0380d00b840f00d44281a80c48a400600d590402040135051185821444c22150140c40000c2622803203142010346400f410300500081c4100c000042050107404071003c00307040c400280d41021100300382d0300c68520840c64000305010b0302440c500303583c00d440341d02c4402003522019042a803140745401d0480f20155210200844c0b4094403241c05814140e08001143c600d950782d062615082401c4c8040e4000c0107140b10100f8000c11b045103804001d91414014000381d842c09101e0059021003038401141007a0445d1510601281110ba07440000124241140070740c21013403080e50300402c4010120f58184550400140c12401e5040080001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 759799730 1250 759798480 759798497
    0x905060412110a060b06040f030602040801060905010602100f0e030f041a030714070c122003060712150302100207080c0105121603090516030302010f0209030d080705070b011203 78
    0x10744a41d000d180300c60380c0b0300000d014854958440100034072404400325040b8104020210f0701c6000002108000c2d03205050040c0e40d640740c21009421640650003041040b4180001045010b034000b0791003c04080e03540300000d0700c49440b4240d800802000c40b613544a0700000c900115981941400f0340125804048503a050440704003088016100880e081c0300840d9110400f81c05405008001d4140035209180625400d611655200c11410728001c080303404030102d80d07400414144042110344949000e030024079483c00d00340b401030054216148007180e003a990b2099aa90400481c420500858029040702c0c00407030f89180007500e0305404e0048507400d00c1080d1030101c0552080046600c840c80b90b11703020116458492000000d11054910312040549801b10000407070340600c000420507040c040039001040c13551402a082d9107151700b80c500480c1c810700c8040d070f183c2c5010506001d0300e1460324040075990f039100000e40e814000d0f04400f4112040d83d40021490418120030f491146000f512a17030039 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 759800980 1250 759799730 759799763
    0x1306060c020406052e02030f07061a010c11060c010b06030901050601111f240f051903080405090402010c1a0609060d050c040203280b01080606040609050609120109050604 75
    0x441700e0712a8809000c4d061168039440210480d1000c542020456106983c50407410302800b404c0e9401c0804180c84081d41c60858800b100b111213201d061041080c2010030402c442ca8071400341704402a100c1e079025000000e00c504002c4020741c001e60060000a281c01d840c0e041040c0d5080c000c1601315070307290100e40a060802410300c400038071003200408040c2910701160b01858500050090b01002d10001c070324406c06805e84c0045580054090409038a4141c8840d28041c10498041d2010340840f90308900d80c2010310108180304111426100c096070441e08503120382c0300407100031408190140c500c1550301903164a140e0a40f85803030160b07800302c0e002140381e03e0700d004000a241034842d00618503444914404001e00b0300343c0146034084104018a44603100d00c210f02c803a07030344d0001d0364040c00980e01c603028641580c200502c1d54000d0419500c4d10b08007030900c00064100d9100340a120701c20103020442d48090b035207079241c40740300324480f00080c08070569900d80155518010f4404a5080c4100103042c0d1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 759802230 1250 759800980 759800989
    0x4080c0d020f0a0201030f090f0b250e0f06040e010e1510120e03041502030c12120a0203041e03110c060901090b030402040924060501020d0504050f1306060c02040605 73
    0x100d021442805001424600ea0040d0f0081269088071414240c8070040b4030003003000201c007071007524015140f000c1e4030b1400649074192000bd5001c001d1501c00140f05203c080c0b540701441d0500280c064600d1144101321400180103402150b01c204151724114001064402d4205090b0b4003c0424941000144560104001e5502c80f400c40c2000081c110044d03c040403002c64202c8048161000162807a15403652103c2400300d130204922400342c1e00005145040ca08100013110580041141460601c07443c82c0c9801190040541a032003001d40101c0403030184109070f10300188891140014956241044c503020f41440c0c6c12403424186400740210085060030158201c0e83c541405a56104440e0b041ca10f000c14507800107031090344c005039950000c40000b500d680146160f110941c95201e003807210384101c5c000350b54083c0c104d0790454000407144240c440d040300540301a035104503480400c0180c508040740c000c0718400a440c0400e0300300b000000311071303400c00f4264280c24000c0d074060180381c2c0c4800a00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 759803480 1250 759802230 759802243
    0x30706060801061a091519090f08030a0f2a050610030206040b2506060e0106022406040b09190e010e120a051b101b091a1204080c0d02 59
    0x4071101c00b1307414508200518598010410344000421304006450b443e000c0c11010742100c15510104400c00c02500350654002d9400030050560903c40c0d601541002410b0b5217034010039102005100c0350b401c0c40c00c0d01a000e4030200505148240031680c0a041c044070386100002000e0003580c850180b4000304070881c28030720b110b009403a00a806240f801e0b03d4000b10071314550164110003948003092400054160364100c400a80901409020600c603041c0048a541d030301c4103034040019980b0800100c4001c0c9081e0368600c90945001c110600780d0b81e58500424043c0c8020440e00d64400c03032180811125003010b07500d04916201e030090401042420080f0b5508039000409514442c0d440760140c1d00070720001e82c006111402262512a05280d1a14441e2848074002007030b25085402c50442d42194001e40d10840d2101c03140084000c1901400010140442a41d0700488207000c9405070f03a440e21422040441e400290032407001c2c005403400b41012203050304902d0080140340111180b401d281ea10000300e6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 759804730 1250 759803480 759803489
    0x308011d060f01110307061103010f050d031e050f07030206090d0f020c0f0607080d2316200d080603190b01140a1a073018120503070606080106 63
    0x9810a0001400645403500e1400961203130780300c1000340c0380001e015405030303807240d00f42021140d440303504019992840041c6900310728000d01a1500000c00310303910140074034099a406070064202a003054080303800d0310030141c2d1180e003080002544002c0503400580d00344114080000d81e0110600c10800315220300d658200306005900c14110704000741b51202c0040c5521100400b0513240694660341c803e0240c00000388030452950b1980007940000c0c0c00f140c0019070015151440c10a440c000049814aa0051210b1400c000c04903441455500f42000c503210901d400c42c00710f9100c240c0720700006000403c100c031614080c2c0901c0da80300c580c15855002800c0e80941c451410350260382403813240b442651000c0c4903207500c4410418005401d4881c0140c000740003503082c550035555005400c0c0001e164884c210304109000861440e044040c4089104d280d03040c5691078441039100300912070014217038094000800d0401c2070200e5404001000005164030f9110305028007030300d90ba600103d0300b00c0300c05106 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 759805980 1250 759804730 759804739
    0x6020708091203090a06050f0705070b040303120b10050705280201261305070b1222020604052205070e01022a040b040f0504030306230d0f03090806040308011d06 71
    0x6c0c406c41d409800603100904450441d02d00b8111a81c4402d842d08016078030064100600003001e0080c507a02490030000f60110802c284080803013040880d1300000007075045002c00601023242810024140881d010820103900302e03501c00c5815002c000c84440b0000300c100c0c046071880b1501c104a06450008041201e107048420480765110890b02808000c040700450b41c6000d000c0d000b15429440f00050140ea24403200340008914140794040413290743c5a1100c100ca100c40b440340d00050355841c0031541078440684110141e400c2a80c0341540c480055080516a00c0c105410031051550055003200c00c1142642100c2074184103a208142801c940c0005c1403000c41c5002148140c4d0a0070303040100b0340803014000041202a4201f4507045500a0f18220000307511081c2c2000000d6030a00c40d21504d024000d01824004102c0c400540d40350b00da444000c0602c03c20b040c03024140350080c00ba034002450500300399a40b40c41c0618004250510034051184410384000c0f00450401c400c0385802d1040d0300151 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 759807230 1250 759805980 759805999
    0xc09060a0311150f0d1805060406020d0e070306140f0f0402061b0d0815060c2a03031803010501230d321209130203060a030602070809120309 62
    0xb02d5110311104050340d100d400107020703e01c0d410040e48503030040560324a00282542c482d00e101c55694199030740918903407100b46007a58110041180410184d801aa00020050b60352244d00c8001010f0004140001180c0c010204c1c00424070255400482c1c220004a500038203c0c0c0d07588000100425058845810589403040000c0c018104000140030382030b40c40322000002a05c03c0e000910b0b10040c4000140040ca550341404a0344226141040460741b080f81c1e418148100f0084c100da40321084d07458800c1603d03404440305c1080601d803a800480203809025039a5038580802d140070850a0b141c0074601070740c80d180000501d040761642c03c81204114040030000d03840d0440070800040320f032800a03200c0e03580340049414949104009130b907410465480414451803811013060900211003c1d4102c2c00320b0801942355903070f6611481c1505c08000344801612520b9400100788000b045420007007210348000380040600030500301a00a0050444520f110340400300e00141d228000d070700081d81c00100c0ca6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 759808480 1250 759807230 759807233
    0x1401080a0f03031415010e040516050d0f06030c0e060405071428170f160f03090501020f0d0b030a0b2403191401061410171501020c09060a03 62
    0x45050340c40034041e10f00030411850484500100d44410380349040c4044120111440b02d5811021207913a032401200c0801042c60003001e50b26042e0781041c42c43c007c20400050074480c038901c0350b024031000d6080600401c8565180d2621824144c254052034030310460b440000fa1241c82d140c010b0f80d10680095503141560144580c0601c05134118210745014800c500180f02c0340c2a02c002032090383c2d0001d07035444100660424038030781c1c0441005000c80020705542020003c807109104d60710348550944d480c19080302801003000724010300350340344000c150b5400000c0004542d012000a40500219400d007004040c1c0ba460801d40d8468108000410b501c41040006142072074401007000c5005580d4500e4003480042400641042c580d0000d80c0203000610304200240301a940c1c80c44490710030440200191820090b9421004044619140c464070700c10b44501482441740c40c011480010140140c10b26040100303c4525042d080e00c0d0300750052080502c6c480d4145440d254040c050000548003002c100e055 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 759809730 1250 759808480 759808493
    0x70b040501090902030a0e0f030306041a09061207090e0a0c0509070c0206030a1508010f06060f02030301050409060b03061e0c070201050301030b22050106150c0803070806040e1f1401080a 82
    0x4002c1c210b9280c0d603490307c07071401d10b042c4044203004c0201e0000e15501d01e020790421044400c2207400c3c175103917401c0c2c0116070709546643c100c1c0ea0f0042030458000c6400c82002c21690725150840d0068049181030003100e01d10b01000185c6415030034420054030145c1c40d2210180000c000c8102e68010002e03850076081800750030100b008680003414620081101e446518a41c4140c00319580607065980d992000e2720f0b1400b055100b01c00c045d04251400c9541052441c0c0001c1da01c1c00103000701d0784142d0303039214418100085540100d08a00c4051306903102854442200106404900950081100c02000003661215800700315803100d68161611800c503401d507115513450306001882404441c91519100ca0b4400d40942022032040c13180b40080303100360901240a50696440e41e41a0501c11403002903800107901500303407603000380c00e8907141d1407554440c00003c001e46101020100b06008001603100007910070340d44540b02c500781c00c80a0049050030401d2484101091050500a811004c01030000448 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 759810980 1250 759809730 759809737
    0x280e16121a0a08100b040203011215150e04030801150504030311070803040b0c0c031507030c090f0f08070e07050f07080706061511010b0303090d0219030b09070b040501090902 77
    0x501055070a6140040002c185840c40b41d402c80d07449580002d1022040303458a024040c045c040540d020350442d494214060030380c41000400a102240d0a03410b1464500e01d54420b1400070141402500190354507500050801c00a035015400940c140d400440c01c9003400102101303030909a0f031010b15041c80e5860031501c407070784041d51028500968000141e007180400c094005010754101d03459854000507103491401c09004522070194100d0444031751841a0342143c141d00c00c102d800d02041865514030300321440d62f596000f20504800f60000810240c11001c209410f54115200315040319845a400c4200031000311001d10000d074080040411040c3c071103020f4a00c2501c610b00883c18440c03156160301c1621000d801911920a6282031228002d611041d0260f010035510000c000d00003841c40800e0312441005410b50140340d100850030219213520200159044101d0726042d8100d8030f130302d48811860030a4454051900c202d80000c103400000c10101d44c100c8030140c454400030752902d00d41101030340 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 759812230 1250 759810980 759811001
    0x80f0c0a020111030907051305090709020c03160b0901180203030f0f0d02040b0d0507081005061305150307180f03030318050a03091a2106280e1612 65
    0x54a0f1221070308882000e40255000e50513031806001280c0c10041801a00c01c190b0400202c80c1e030600050010b13019000c1040e20035620450409a40c1c3c900c200c0c02c0900e944074400c01900308180a00040c8140720350003c086004d805040000e10070101d01c40c0c0c0c43d01a07010008000380d4180c108225500d08513000000800d1060b20300380c81c90b404e1050011000381281c00961101e809110005903400c2c00b040c0a1144641c80100c41c1419500c0c0d080c10300001002d00442c5c06514000c01f000507007400002c00c4c0b00000001000d004028018002c803004103c2420b030002d486500118003850b902c061444942980d080c01e42d5020044440c0e181c4c5141c40031000380070040741c45101840810a1600821014041d00c20103034000d031035000d0124500b034540e0810b030b0049000308102c0340062121a40c0e10500c541b500303400e91108031040c0607645074000081c00044c22002c90b8500c1000181e1001c1d944110020300348111090080c20007010394400c00680111081090300c1000070780804031400783d001c2c0c0c9611080b00903 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 759813480 1250 759812230 759812233
    0x6011b21031401030f05150f150402090406260304030b0a24030f030f08090a2d050a060b040b0904060c020a14150a1820150904050601080f0c0a02 64
    0x102c1804803102141032007a0016100e440307012074480240312041104c071400d1280fa94102d51a071500a4140071b41d05000b40131400c240c0390140d1003000694540c0c051340c1b400d89000b00204034855840400d807281ca26040a004801202e407154400c1000d404419101129003041c031410036551a454460004d20203031584214050a0100c0200c3c0000c4882600300507503c11001d41003503244500b4098122550401500200401ca50400042d10400701c0c0b480e10b403540c0505001688840d45c507090741d260104084c65006c4001d0420510306002001400030790540c054182000324442060038001550f8500340d182c0d030088c0303004001ca4001016544428890502d88c4103840c0c00d40140d0751001070b40115418658155031041c501107c01c4016481e030103400440c4498100604101006c0010300030181b007401a06441c1c4e84030007111100b031502450804200010180b03030880b0312a148003409a005003e54500452400340010b1840d4011081c0600840325141420321990f03130b010182c2401d501103802d48007107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 759814730 1250 759813480 759813491
    0x80309010e03160212060702100903020f1902120106030305480c0f0d060c051b0601030309090b0306010315150e01051f0504050607080c0a030806011b2103 68
    0x320410b001034036000307240030444044181903004202c02484580090407150308890b00740310700c0b107400040300c1c00c4216104a0124039680c80f0f080683c01c000c0d0880421419001d0042201140b80c1c003100c0305c2e60124401ca54020f204c5074200081070032124a40801004200d04000d6280010954107003040759010000d04080f1107983d007801e02c1c01c5070740450b8503607600e5000842d503a1001c201c144000192902c0503907800421510640008100c0d0220b001c0c06480c1564480368034100034070a030b049599641003d421041c080540b002019a504024441640024004400403800e442680601c0c40046001401803003140d0840d1240c00004440c44c070101060b55036080b0318816110284087c0c00201180070701c0444541c903240502400800781900928049a40760000e035105800c0f0007a02c0a903201039030842d031900c0c40e91400071194851481030030354521070040704030704150b440b040080c420402aa85c6541c140e41c0e51090304070580d2043c000401400c28007084501003080d00c3c0000c0c001c0c200e9071401060 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 759815980 1250 759814730 759814751
    0x61023040f0216030e030606030327030c03030304140d0801061d010e0d050106090f1814071211010207050604060c0807021315031205093f03042103090308030901 71
    0x25511001c3c0700f01d010a900054011951030184445039101c801035010310300d080d00840900054082c60f07501c0006000035000443d0312510304014411480038050b08480d5682801d08060105400300000c24955104110313000c99890702c9044602e040742d0058a40c40b9500e501600c03c0d128443d03c81540074100a40314084614541c5c1d10b0751440c00c414068000001e119040c2811801594448010b410450303090041a4000301e03030f2010b0268085800000f2601c40c8540d100d1140e0400b50141d004213070140d040400d0506100e480090003840398000d800319002d03a507460b02032103000c2c0034502c01c823404901d205111801140840c03004140b1684000c0c42e15680c5800940d880c0100c0f02c17030007180708100c88071030303400d108000103580c0180c88217889080c04c40c00e2248400004081c2d0a803080401083c030b098800b24109102e50b0f0080c60110000d44049550a4000c025165903a412500c5502c12050b602e803007003800c42e80380a9101102030340580d1186103660850322014060380c40681508400c0d9a60780000f00c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 759817230 1250 759815980 759816007
    0xf19140a120f0c0f1103090913060e0129091902180d0c031a09120c010b030601060f09050d08030c091504030b010303030608010203090c130902040608061023040f02 72
    0x100108500e0b01e652440008824000301780841800d07550003d41d00800c690700d404d981340a40158040402206230301d081640c0d141400240c11011010030b100d608281b117040721004204425100e0b20f00040d018500d0102000400000003020f0b2030314054482426407040e2710402c1a001001004149402c10013a0391010740491016625441f050b16040c0c3c00543c18010000d075421503640114046955464505007210060340700c40c845412001e07600c4000600641d004000c0d001090a807400405586441da55171a0107040350410204042c00a448520f0200c5c1c80e1403e205044d250f503401c00b207014156075420801e01d1103680310314001d0fa8801c404203086841241d4030700040c000f4611a00040d140c07540346150181c00d42e405030b040459264018000c021001c000090410300500341242d440301f0b1144198102c000510305600081d4016040c07950201d4030f00400107105000f200242030a5082641c0c42c85a040c604440000003449416140202000751a2940140c940032010140041c600803c202c05103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 759818480 1250 759817230 759817241
    0x200a0209010b0703090b25020120010e01050901020a0206011418010602030408060a0209101404050604120b070f140325020a021e0a0e09030f0f19140a120f 68
    0xb89005000140c680c04050344545072038024408a4040f90510f400300200e0188040710b0318118103071000b40fa2500e425a84500704140107880000d0175103440081104806002c0e244600d41e46001d50300f4080400d070344070014070840312440700c03560141091380d003003256004040c01801c10856000404814120381800302e021003034000c007040c1d0010b6640300c1c6130144480c20004001c1c415072800c1d1050000c003405441d03c1c0700120300c2420900c2d10b0040d03140d014840300c18a002e10f03040700e43c0120002c00d0114205404c1040300352110b000351b00796061a0b0703c09600300c0300c4030761800c600c50001c1c081111000c040f00c12400915001222510318248209595044050600207912114016801030820340d003941000100f070000142182014211b00d144003001c22107001103445002e40d50100d4a0010707032480820300544001c050750030030950b038442c03900182250079001007148041010b541000180824021191081e1550500002c00e060003180e60098500d400412014600c5503212144000c0ca03120601c1603 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 759819730 1250 759818480 759818489
    0x30206070203210d180b010303080a060305030d061404060b0f0a02010902060706060315110a1404170c1201021e07081e130605090319080f040306020301140f01200a020901 75
    0x3c9a03100c1860008500590741d002d0048a0360815080d00c002c041035403508100d041d43c0c2c1604200c2c0854845441013401014207920180041c080410f00c0c04010640b071b08110f0454002c1403900708500c41030303810481101c1e8103104521383d840c8100000a0070210400161841c3e40c501d000000d62101c0390f0f004504d50341d10a810885000350b48902c03e00c1000141c07103000c0c000c0c5010050402031044482100d503028030400b805041480f0784040c4000b01d0040c54411a000380c013044450131a0500e10344102070390b078020041d605210320030701080090000c07814401c1da002c400d41c0c4c25285c06aa200601c1c0ca41c215440b4890a456018080115401416280200b229602160f0003e1030351501907042c0920901c050741c01c141d007008020001d03040543c2d000500803c403414880d8021105280d1413900790114842c0401d40100850082000000d105540d4095070481d42040c03e03690340030541303004201441024000f83d1340400c3c001100030803100d000c44000c0a8440b100c4003241c207120706a80000c0c581c3c0009a20 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 759820980 1250 759819730 759819793
    0x30405010e060d0905010b0a1706010614070c1d09030f03041101110d0f080601020c030a1e1707020a0b03280f0204030809040f06050312030c0d0603050133030206070203 74
    0x2a513440b070070010843c0c2d00500d40d8240c012070004000d200c271500d0b42410720a20041010304115020f5645201d000c8030411a441991064541e40d201d0355405482d000c0841d40c0c2c040c20110000500c600f00c0031044036106207540403030742e2550780c0d696152504240030301d00f05c90410400f544194043c0c40c0c2001707004a43e00d40c503158000c2c041c43c1c0c64001000200020001411034000e0790041419460000d1994070036075229050380015142d51440c07100c1d440311020b0140011241148601014001c0700090a040d0b000f980c0420481d07885d205005124442512004840c2003d80403981c10b040e2148114250001501d4001c03560f000301c000300300280d8000740c10640b24101c0002d8460b1261409121f01c940001c404001407104601d071100007a00c41e40c00100074280b4120020001d00c87c800030000b00c820b403102c105010412a51a410414000c1040c403220b40e2441840c0f03c200d400c0c05c3d424240c01001110000c5024290034210340c248166034000c2c42d800ca8040c41209120113100440031001c1001c1041d0a0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 759822230 1250 759820980 759820991
    0x10c120e13020d0c051903091a1003050f03030c0a0f110322080708032b092406050f0f1f0819020702010e010305090a1209081b03030405010e060d090501 67
    0x3c203004076040006200140002042044480a00501c1c100c044040c2800e000030003ca082c03c106010060300c0c841002e00280c00402c11030044040442c00050724003c504650000440c0d40107640d580c441622070701c151580a208950340709115030401c00081d1824605001d03004003140c1d4262840e08400400b03208038005940c80e045031001c040c55035000b00010700003055118030b4038445c90340741d10441204800c0c0100154481d50f808080c009075a8030076079102800c110254540c1850040003501010340c00b000300580d508104044418080e403800e82d84014400514044c00c030307040100800001180c96080080411401e00e0800c001403030f19000003203900c80c4d40262419617134180180d128442501101c520500c80031002d40d82c000e803020f140c80400c2c20006595103032900c14a07d0005036000003030200b00c000e070038600c40e0740c0e0120541d81111480c004a40450b2490440c070921403102c075031030710340540c8180810031456210348070785044540049e2040d0315210062116074259658090107480176919107 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 759823480 1250 759822230 759822247
    0x62202150a120b13020a110610032f1c051204032d170c0f0c090610020604061508060a0603031d060304063602030c03060105010c120e1302 61
    0x40e240c0302c00502401c08104443d406800103592200311001d51079120303404070b1000a0300e802000800c130003038120007c42e043c074606040c20210807442400100d40c600f060381000c0003150404403003003041c29002c1c0012010a0b181c40144034103070f11401105898103804400342800315100340204884000444900382c2d0322411818815240744a501b100c2c0c0c0c0e8450003038100c2c01e040d5a400c0540400561280d0715100914003012180442d0003015424001402050000c06a210b03000845608001c0c00392a680103942d01e11b01080207298403403e0940160b00244006400030701964800582d000700c1a299140e215104c40d0010300c0d181d4100c0745c41010980e1854184185500105210443d1001d030003c001c400f550b00c0082044ca0001800c0100880c0e19099488201013210040d10306840e609030340c4120b6007981990000e0080c10118052b80a03005540307405155044c04180ca42c140c500c1a118424001c44581d91040410000310300c0c3d108008a07024001060b5407803504014902d5000c941c05038862420 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 759824730 1250 759823480 759823487
    0x30f11041d1b030c0c070e0c18120a08030c040e0c0a0831050106090f1d0708121305030a12020c19050d0c0f0f03031709062202150a 58
    0x40c10b45258446a140140d001c20008012258030800d0100441d450305298000c3c5841d115032074001412410410003007218504641003d8404040400e24030310600029006000da00c60280d420246160003851001002c62a47c100858110003070100d072030700d0160b4a02803034855850540b8861040100020031000065120a1050b00000e01070854000403100414070b25005644c078803032104c603c2942141d0018000d0070b51044004020340d1400b40146114505660014000f550540a1541420360b5501d1700104c00107107a4152000000282800003030501e002420b508078142c410402000c81001260340c0d00d0611511800c2e0b0711484245402d0401030b100a8145000d580400d80941107000c051701c01100c8504c426000c50b581500c2e8004481558100954110001e80080f40034400f2040000749000604d803051080324040d0f51441104525000c4402e03408009540c0009242d1041e0702042268600056407510300708048107481c03001c000c42d8040f691001400317004c01d1035100045010002030341c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 759825980 1250 759824730 759824789
    0xc0e010608090f01055101030e0a0b01050127030302010c2a0201050c16030c080f03040e0105061b102705100e0316200105040e0403030f1104 62
    0x19a40024005846d040d0b6101d100d102d1584410729900342d54000001c10071403140365140e4488030680c0c80701040e0f484048410b583c4a03005280e0342c0041e24007a5280c11843c2c0c085400303050385500240903006640317000011030b056420340e1181c194110015a501101260850b80140254072a40010078904100300b0040d001104160450301403640360440703c44042c101400c00600b055090900030703105c80070f00c140c0038617250090000d800c501100d410044103202c1c2c08071250081700c0b0300301c0843e220812100405502c900440c814000040b2580c801031003a45040030141840207010141890000890b56040e481c1c10102810085603075030340c90b07260f0032800102d800d07540f000301e5610310031502d030302ea95403410790b54600c05c8414130f0261b664125031a000c0505000300c41c2c00d113400804040800d030a40c1446415a240d01181c80b49543e410920010380c3d5015006580446800c0c103116183c03546d8586040d0050a0100d401c40ca500b650741d620303d481003198001410103045458802500604100e8166800a0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 759827230 1250 759825980 759826003
    0x14120a060e07080412050c010e03070212010e0a06090f0c0b0c0601060318020d0203122106010305010302130c0210180303140606071b0e010311012d0c0c0e01060809 72
    0x805070070410100c0390f00200c03440e0300142d00c11182d100900074480111103c3c000c403601e01c0c006500b40040404620400005081e60038021a4245440140b03550068201c49204108125580040c00c018011840300c2e802000e801d4094003c0350342c1c403840c1d0751350740e0b128054607082403000c002c004c50020398644003088414050500c90a08200204004001c02081c2040f0200244110b030481c030baa004644080c800c13082caa460f482416600c43d4000c8641c034442c082c5001d2000054110280040e990390f02c2806000e040b650050020003c0e407950700c0d000b2002d4a24282d4607001d500c549407c07c5a403105c00e10800d2000400e8051a04441c8500d01e0000c9c1981d0f000203100440aa503a014010340d5607a100c22a48000c0e8004007100d00c0e040202d20344005540f86620218003821218000020710140c0c80d026807019400343c0e1159501c42040d400c2c100085800075182d09500d0050802100c21400303100d841000c00d000f4000c01b0ba8242e82c401da0034000901c01d030040c400040b141070501c4640c0c00c0c01c104081050 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 759828480 1250 759827230 759827249
    0x1401020a0203102c010902090709150804060b030f0309150403020a0b1e0d061a070506040b0613020c0a17070803041e05030703110d030c090509040314120a06 69
    0x518098001a03a0707442003c040004056881d00294907140d0b900d10100c54a6800450013400b001301e062420380209074905040c3e010705911000510010b10800c01c1d40281d0f0514070350461000c04d169400c641c400001081141c0590395035045e40c425680c10022903000c0070040004540c1c504082052008171115482c010310034400070700060006035180c0c95420103981a40542c1e54951610809108520303a10480c081265080006c2032940150f203038101c20705485403d030382611220445c5036003054a118450004c2d26580044011400041c000d5205542044004050f039111030300190141040381d02c68031070b0b40d45592121450400304100c00e05c0c0003204041c90b01e822030805030f854035402c10720320000704010000030108004510382d0040040f00c219454101c011070391140d0b0b091901420318514002209202e20690b440002050320a01030310314140e16699a03c0e49080c5040248150380c8009030044080c031040114212201c0c0001d00a46021451100107070300d14104078811804882c0582c0009655 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 759829730 1250 759828480 759828493
    0x60f10090b0a09090c0f06110c0108280b0303040603021207051903020d14040809030f01150303140702040207050633060a090f06030c0201110702030a03051e0d0204140102 75
    0x441da00d950100c2d04840b082c9002240d030300e586113485640301c3c0c1a50030503c2e04100f100b10103c0c0055100080e280411103080480c1c9401201c04c00642c6c10a1044400141c800c1a488070000341410010844520f480720640c00f058800c5008000703801d540282d000000001d42c0807a04c1948101e0440c02d04d40c010110b030803d0703880c15003c600c81c2e07201d007403024511500345a000180005003409981c03000a850116503040101c6042620b0402e2441d80301c1380700180b080c031034590210030101042c030854508000a07a035500e480b61031554280d170341c113041c0400c036900301e030f0140555070160312180014805241300b0390142600d4a413845c0b0359010b0307841c2140d19500450480003a002508031103502203036510f004440a035103032110303c81c0403540759569801020010405d0100004c0385070f0180c0024254440b1a0028848000001c1240c00c00d400b5511019615500c001a20008a4052002002074242e68101000c07049100100d0701c0282d4045040c0c1e013200350340010200504a81c183d6400071415091024194 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 759830980 1250 759829730 759829751
    0x507021006231203040504060f0504050601080f130f0605041115161121030c120f07020d050f03270118090b0105040e0412030e070608130311060f1009 66
    0xb00d011601c1283c0a408410500140510204103603002003d0003030062020a8a40304400b00b018841d111702070181d42000c001c5031070b643c010311000b03100c0c00c545c400360b600c55641c0038101190018050000d0741e902d2240200c000100780e0038020079101e075029100011445165009000f03030980c03034400c0d14401100610092201c03100400109900d9074000c5010100030681c40001503008028040e01c90242d0300484000c10b0741000880980031aa0941c0306440d07100101c404698410701c60304110421040040042200510f041d00c0d410148502035412a640f103a0701c070082c00c0c0345600c6245044245100c1080018460140c09281001c102080c40c18490380c010300c2003458071215aa0059010700368030b032120071b01d05900c0f80782900c000f41010083c1440c02d08140c101f07901010b02517405080000e00707001d0798003110040002d01d9000c07a0700c10798841070f030345e605e076110740205c0215000100e003000030402c0e440402e000d040180d00c3c0103000c00000000c075030419912840c03511315a503024009182c1001100d91 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 759832230 1250 759830980 759831029
    0x90f07020a03050315090a06090b0105160803070c2f010f020312040201020c03030403060e06070e012c180a150503120c010e0607080702010606050403110f130507021006 74
    0x5104a0b0b041c241a0784030389400300d060032806400038031079400400c02e200f0003403007000c60f812183c02c44010040c00c00100881c10011140c0b0312030002d54001000f8082c0d45000010b20160066a000d07a413032800041c000b00030f40d104008001880100c4032a601a00c441c00301d403200c04a65003034250400d082034080001113410107501ca0080e40e82d960701508400c000541964001d01c10240403c500406595440351240303040c00040644524a4444d031080d04000342040d4000c0c0c8403a4520f40b4140c454040030380c0020400c603034072000c00c03030f132003050207000d800d928002d03120f811280784942d100300382203c05031801480b004204c5070400740758003500030301d007400300180d850200e0107645240090341040c0ea10a44071039114094820714483e410284039040800c0f0700a680074103000e014800c0b641c0244011981e900d4122550f02681c00f02a2030f5409901c8020a6444c225036a41c0c0500301c0a00b620030310040c0b400d4440d0442d00304903180000b40e0020303a40c11140b25070602c00e031070152091404076074404110740c3c100b0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 759833480 1250 759832230 759832243
    0x70606140a030b041a3603120901020c070b04031a15040c11030a0c0b070215010e130b1f08060f01050103020705070f0807030b011d1b0918010302090f0702 68
    0x2d4801c040210200c4c003070115040b842c0c00c807504004000c5d1890706003952000310034484690b20405188a61b80c1d4900d00410905818140944680095003814a110950b06a03460040c003042d40565082000300c540d030805004e128010001c4654050301ca0385075003451134002c03094402600007030b41c8200800c0803460491038103c421903000ea600248000030070307105640c505a480e1003a03005210204415201643c014290300c2024858480c14686440d52a4140d0740d0751035120311003100320756010050100611010780954801c0f204044000c1030000ca8482c2400b0b020151449624510f00b8181c442420b20500110401007440b8001803883d0b00d0856085e03820000c7c18010b003410190005032060902c603040021f10080c1425240c001d4481f551400307001d644035154030048401d00c100c01e0000540b0800198415020483c1c40030089040c0d0300d4200c41c0c000d1014118220b00d03100010f200c411a15110716054050303105008005200c29411030040243e81240101081c85880070b541c00c00074050ba020490 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 759834730 1250 759833480 759833483
    0x3070e04020a023706090201020106150503130314030907090b0a03050a060c050903060a021c02070240150e04050d1101060e09031c0b1012060801060803070606140a03 73
    0x1040c9004951100381038110198518441e440c0c80c02e10b69443c140880c5c1c0e80440c590f0380c403d80080000542c1c0300c2049194400a01407100421010f0002580e00002c500054032418031a01c0e1030b1030302c1403100f00c124110b078000f5070b2491581d45c84071800f400005404c0c803820840035811135801d81c0720b501e180e131102e0384c4242d804c100078200c2d41c40301340c40010360340038805070b45010000906560980c46d016158800a400640e40034401000785150002c10301d0340c510840d01d20b150041d04920651043e200598401001480d074070301da080f0304d07900000200c4120106071141c151248800718102e46d5204070342a11000780d4102e0120715200c2c5041c00006480000c515050380b54030700b070407a407200940e042d50b1300500590380301144000c1c110042080000010000f42403200065510900248046008600301e40034290016040007050761981681070017002c500b002c0314850100410031580f181c5110742900e4a5a000b45540d900204038a0308001044c00307614050205141c00094465005001440710200b5100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 759835980 1250 759834730 759834763
    0x110d0902041d1011090a060f03050f010e0106080615030703150510081605190c230618010e0d0203030603060c0a020705060a0203070b0f010518010e0c0c071a03070e04020a02 76
    0x410762440080940c0c0c220b17030004101c040790035907072040135148940001309640064a032100141d000c90030036068505981c10050010702c640e0911000f50360050000e011642d1200c0002551504201d828000314843c040c1e5960102d1420300807080503050032040d0300418450701840c0740c50202c49501c91405584000c1c40100485800304d2000280c559106030000003c0040c0c038200d85452a9800a0000c4a002e00c0380c020346040c01003280e040500002100300542c0550042c10100b85204600c4084900101351701c80009440d280c08420f0300d180500c0781500b0400b5030400b000304900c6107130500005520901d440c41540c6840722028009485145030b000c0c2c07a104a40118031500003034803c0069403411a84500820906c0c01c0c140d661710f100382024854140700d0807c401c01e9002c000e10206000d4120f640300c1c00c18814985401c800208690405602001c0501c100c1d480011600041d80408440000c2c07503158030b5032410200302c010a841010405540034900402c002442c50750700207200c040707041201740d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 759837230 1250 759835980 759835991
    0x30304080702042c01022713050a02120f070e010206150d0821091e100509012a020106141819060807081507051c110d0902041d10 57
    0xe00003e07504c000c8aa01c0c9041c8041039070504844039056006020381d1110485030320303d514210a8098240044180054004520000c21010070101e50080c40c0c100b05100b00c09030070078580030035404107010210380b09010b4042010503c107910b50000040b2050203020300c0940060701d000580644000700380c8070030500807214004c1240c1804180341c1901c01014048c1c84560410182d00310314080c2841c1a078800406000b440c1805010f400c0050102039441004005072080c24408101c0c0e000801c8014241c2481e5500e0b440c44400c0706c1c003c140405880e03e40042408011912080002c2c05c52340d03260009951051200025102642c1c0d200b05481c0784411304a10070010f0b9185c0b03440400300300c466842006c1c41410140081582d86000c203070a401c5d100d06202f01d40800e40b01003212069030030161900c9021400402c00020340c155809800c000c407035000100401c00c0b03005500400d80d160700c03405803203c02035921480302045140c01e0062900540843d80200190300c030b40c1d011030380c640a0111207807101a03aa0b5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 759838480 1250 759837230 759837251
    0x412051e0301140310151206020903120a09050306190218030d02030406110d210b03102708030c07030306050a090c08012102010f020109061a0f0303030408070204 71
    0x5400d4004115421109840e03503550604546141c0001d50858030900520203052640000c40c800d0b5007008284118801e1540c0c03a004034020145e00c001c0c003c0e62841c1c0c003000f180c076a680b0100311032001603940c09150759441d9040c0c40b00400000705c94000510940102c4180310480e1281c144408280c03030041c000603983c0d030700400040802c803600aa9242c06003d040c107005401900440030b401141c280e80c0343c40c031071104c08221150700c0d18440d0428001003500080880303013801c860249002c0c00d0030301d1721f400600c07803005030002840d100b04101ca00300c840e911580f4003105102c0c24039a02d4958141540c05d00c0c40e980c00c0d03580d0080c0c0b9020040020075602400300d0142d00b03052207600160010301c0d02400700228152039504010240186100030303000b0a40d0710000055419030254440c1001d0b81d0710640c01e00044095004443d001d000e0b504070130440d926580f254005c02d801e0f205039145075040740315000021701074500b40902e00100800c01c40c4603070024020040800c00120032210b256504440004191014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 759839730 1250 759838480 759838507
    0x30606071502030108160f030308130506010e0402120d080a180204050c2d04030b070504090e0a0b06040c0507110409080a0504080c0a15032703090906060503041205 72
    0x15520060411211030085200d01207941d40154107072121417090b11741c0c1042c02060018048a10b1082611002580f02d040000c02c2c071611301ea603000300c00300504c618480c1c09501d03011b1400c002a00704420500c130394002d10007145071410039820480c271020040e14602900e94070150150310000d00018481d51256402d01e921040c0c4614400840d80c024000c004a041c640740104080c0c22000c83c403140f170101d41691410405502c00503040f601c082030401882d00e42159215801c400b0083c0002051203400e00002c10804250301a90324100020710080c55003009030700749003803a000094041c0f40210b03d8021800c43d2603034030100315020240c0003014204010252004500149464600038150300b0b400306446424a52141c0140101e854590480f201c0340000c0003000400051840341d00c1002e1200d88410317003400d0090704105070300d180c1c3d121400310b403050041c5a890204028107040340010f103204030602c0a10345d03d12601d4003074a202c1c43c1103421454030780d444e420a006280441e805000f000314026511074034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 759840980 1250 759839730 759839737
    0x80f060609070206190b060c010212130b191b180905061018032f0312190327170a090303050d0b0d08040503060f06030c01140f2a0c06040902030606 65
    0x10290207c0c2c1c0e04d800900c04103000b50822a0003250b500c41d18404501d00405c1380726604c3da00c9402c440f4051254503504012135114016805882407a5142c4001280402d008104c0d00014a416260400000c0060382c0c0c005103045980c010f400094586400e00203540c494200070080c01056050062059004019440d40761580e944020003546c205020541c1102c1d0850342c003000859040003c2200700025000c058450004103c0c03002c1c0094180030711220f20a030071a03c0c1041c500b160500003101300000b4001c442c000c02c6400b20b85000d610384042d04080061003148030050340d00c8000c02c01e08060400e0002000c4901c42d210240400c040420400c200c0c0160f5803040070441c50041c4040700802c0240741c0030100b50418810144203009c0d1900050340480002c021500c1040010094555102c0c580010345854210300c40c90311540b07406200944d00c1e040084024040c02e000150018101580d0005411402c03030034070203940d0b4a40181e92500c010b80c40d0a000c3e0740503281c102d000980c40c3e40d50200032a07094003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 759842230 1250 759840980 759841001
    0x80c0a0f14040e010f02040602070e0903070305070f20100306050603040f1b03050d030f0c0905040c0201020c06130506220305310e0703020c070306021b07080f06060907020619 77
    0x52800b081c101d0a02c4c0c41c6c0d4010070840c0d00a8003585c030301c5036840c804440300010850f092482d0f900200b15040019204200400a080c41090074101341c280300c0d11200e1034042c9109032004401d0403006440d03003510306841c010426000b1403170103201e42410034020602c58000030340005d0840c941c000b034880c01c01136420300d004552038452203a042c5190b940e00b031542c2c0d01d41d0a020342e41c0100b441c3c201e1544000f400d60280f010b0040903a203030240e2003854007045c03200400e509150201155820303c01c1c0072428009000140c02010048a103880c1c500d00703410a1424250060101018820040c442c44030360104806400b903040e4040c20001d880d40c01303a40495914204d65211440341c0c40c50180d0301c00d8400d0b42f114801c0700351900903001544135524030006804034490052050301c260301c008020400a86150000d001070104c919041a50700040049103281040641050300d0a40040000c4941c41001300406540204111610301d20b60512001c040d48888010b012442000e81211020b080540650494030000d07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 759843480 1250 759842230 759842233
    0x619090203041109070e010314070f1d041d01060504060e0a0203100e091e0606010504090b03070b1b0f01090c0509090708100209120c1c0f02040203010b0301080c0a0f14040e 76
    0x5d240c500320040c0300c45180c41102d03020920340003803c03000801d0840c41520414007610b408034003960400090721080c040d034540784038441d90341d8041d107415100c3d0301400e03084c03028480051803000d8000e85140c6c20b45015400950186113400b40c01c000d1b4216801c520ba4116800b0030005950340ca4280c0400d003010950341100960b41030700303002c0c018201c0c400a0b01e000c280010180301da190300307441846282c44803400e41d41035000071310901040c04848441d61101030414001021114803a07506c0c2120000d680003009101004500030041400c101c005103c00c1c02c540707843c10001c00c8500c3c05030341c1d0340101c448030380600c0d40103041000001d180303502c040000304003400708070040310112212086000007940c0004500d6002d2240d500401044140000b401c610000c0d00901c1d444804000d8916041001082d0106440f80d1803000a25005615644011400303000d500d4480e039580c3d810014614500b6a50300380340f0b401001084070802203270000c00c4a450a40319030300036001e4001904800200035251400440c4440e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 759844730 1250 759843480 759843499
    0x10504170f0706050c1501030b01180f0f1409120d090203250812040b0a050313080d0f0b010e0d03050a030902180103020f0901080c0603040201031e050f06190902030411 74
    0x3d26400001030a10118201c4c11514082c0c2d40a90100d0100030078440200301c94070b8403005100b281c1481a00752000c0600d050001420700714440782c401511803140e406920150f5400f030461407003c91b010307040c0d44110390714024100151012080c1505200e07000070ac0220603650518241150b40a02c4022079040007800031440002294403107001c411400d1140311214030030a078050705c0944c0c0b41e0054a00700c40e2403542903070800502d40310039542e80c0d00c02803600d805100340b0344090b800650008003600d0030140700cbe400011810348000b8a05c08030b850100070241444640711a08180c2e54901d40d6900c0e105a040c80c1c4144c41d004004000d50284c083d405000354000c0c0e804000c00d51280d08017000d14100c034000ca0320200828400000e00c6100e000c00e001e00c8032182c01442071070b101420010700460304244107140c0001c1c1c1286102e81503000604140c07a44140a484d40e082c0f2001d0410300d64425001001121400d240f08803401c2e4201c41c0300264810105d0464002c0005018403901e4184100c072050b01a100d00360 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 759845980 1250 759844730 759844739
    0x50609060f0a270302010804020f0d02060c010c1d0f010c05070918050606010f050d0b010516050f0c031605090c0405041d160e0720070902041d06010504170f07 70
    0x101030a00d50501183c90000c5075400000d20300c001a100071240c068440d071180d80c0ba69000d000a0001d18a102074010308500302034001070b02c880004014142c032010000032001d44c52440208400c0c0098000d103826601c010140d005540d619400d00c10140c1e09080c40200e900c030500d086820601e140d40405242890b09280d10030300a80c03d170400c003400d40700710161812030761001c0056074008448507078600010410b00c0115040c1c0b05a911407501450141000f03414a040000c9007084550129811595034010b852030410001e01000a05000001103020303040d0011480300705000f266041c03040e0341c0300e170075a03401007942e00c0d404400711005050302410030f1050410142c02c031500860514003000c0d2911480c0d00f00d4109101408440c000c0e981d850581c01c0b00e54842800895900c2480000045c0350705240c00c11107004001001010005c0034800e81c0580c40340c1c41c0002c00d01086404200d942000c00ca440200078150ba4084c04440070b44e1980d08548078113901c4c072070b00c6074a001f40c200e41042d25803052500105 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 759847230 1250 759845980 759845987
    0x9052e05060c030a09050d170a030e0303160219031e18030b1f35062503020c030a180315050f0c1602010324140108071701050609060f0a 60
    0x44d541040e114060550f03900e005100d500c4180c008040c0c00c08884000b96040039800800400800113546400b14114080009250942d441035400310b001650358803042440540600c1044100a415510310420540c903803405010300c0c401c004a401c034241c01c000000380395030045800324240f03a180203181180b26160b103082e4540742d2056400301007600d90705540300c903299040305140050b103400c5408240d80c6104d20a0f004201e035504030010801d12601c04011503042010445070707201f00c0e0140001d501c65124101c050f03840303c1c1240aa8000c05004008500302e120000085400403100c0d0f28000701030b040782d120024550840c6420040003140c110904d00d0300032000b41c004038021100e410390501252140e8002400700d10403489101c0000107159605409580250b00c103009140f616031100c840c0d00c00000c4046110308103600448442d00400c64006c03010350b0712a030903a0340600709060255521038800303908040f5020512900348540300009400b54281c51380f00640b82c803444288a20b545654038544080c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 759848480 1250 759847230 759847237
    0x30604060f0f1e03050a0303230f1915051509031605040c05070f030e0424030b09010203090613051c0c062004050f03010204031205030a0609052e05060c03 68
    0x184250110b80200d5030b8a50f0181e0895400c40703501100400308025143d806070060281c00306030401403411802880b580f100ca0b40901c601c501b07071803050140c4601c1d00030600c146040e08200c0c0a0081850040d074008032000f541d004e042580c008031000c00883d001103640c140ea81c4110100c09415000c1d0741440940302c100b000c0004256201154184103110f1451002c880e030340140300001e07100843c42584900800d00441a003840a200034001040350034136031115a141007417641076040800034100c010001e0001000042d500150450020b518600301907002c150b44500c06050705000c0703410701c05002c040060400546111444e1010404074412691102501c000d2003400c094903140d040804145544840c2c080c07140e01c0102c0740d2145401c190030282030000d070074050307031078036816640c00c001c0400810000050524045200d9441c699a80360124001003903428680c800c3d100642130a00b030214010001d81c803034030154215030203854985518011b0441d8103503d50b00c01e43d0800300c0003c0f036841e000c1010004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 759849730 1250 759848480 759848489
    0x9060c140f0c0a1a01030b091606050310051005071502130e0c0c010609050609130b011205070801020304110a080303041e030507023601051c08040f0b040302040e03120705030604060f0f 81
    0x15506241c0d41c1c1000300d49c50381c03800c011000b02c80244400c2440b1080c0150065504030740100c1e41c1d1480262100b002ca1030000300200c0e1b42002c608c000c035000041001000b4101e4580060f400700394201500703528403491640071030103003501150b8020700207402c00c80d4032800d58040e150110024050349030348851101c0240001d84020303000e4065880007a000c404206a100c255030f82c0520b082d00b207a864103c040341130281074081100c040c0205e00002512070000d001440c000e40c0030b442009210700c181c07000c10000d042c02e540009142d0300107200b08000b0550100d4030f08400c2358020b0b131a45e81240349103402c4501d80710720034000307600400451248041c4450a00480888001107204002085101c503202d03003504424881c543e8801603030008074400c1650400f02c0009244900480740c1050f0320390001c201c0e020300e030f03410401d490380f000716041080d8602401160313403140580303026605e0306001e2000020040303002002d400074004004007007841034032a94803400c014844a0000d45085031035010581c6940d52a204 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 759850980 1250 759849730 759849743
    0x71511070c150e03030a0207090e0c040608010506010306230609040908030712050a29060712030b0118030503090f0307080a0302010207060e06130b04060f06080109060c140f0c0a1a0103 81
    0x2403e80e581000412101d54125540090480d203180c03840500241203815081201401010900051030b2038602403403015081c1080082030030b182000c0018222001607114180d0580c40320041d00099008043d5038039001da0a5800340d80e50b03600040414094206031340300412000e4008200103113940d100417001c4081e00000c000380090f481d412803100c01d4400c5481500c2401c90794044542005207080300c201e82002000e841d584c100381d501e8481492001260074900082074840c07120303129960b8800302c0241034680c0c4400c2074102c1c0d42107803603680d034034000c100354103004104861152501da40c08000003001424400304030f40c25a42140780090103900006001c0b01c0d001d0800964250009010800074401c1c10740e80140f0304851720a803550300a40b10054402d6030616a90800392041130b4139400784030081e1800c0d50002c58219842d00d414030841d09682180010000040b1001816002550440e240e0714606041d0035142e041c03400c81b4500700003450100402c40c0b114000319606040702c803851079040702d00903070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 759852230 1250 759850980 759850997
    0x130515030a05360f0f1501050d1106160c0815060406050105091306030210080106081b0904330807060906020a030f020a05250b071511070c15 62
    0xa041000d64040544503040440300e552000124005142400441690b00c1e003c07502e100a0b544c062904241e505020941c1c2074020800700c004000d8502c082500400081d1805140c601c81134540080790801c184190344a81c0c0001030200116084640c0c2042954115150241ca155038100ea983d80b00c18901364110306a1466000802900c1c0030300c81c000c119041a1106490800c4110401c00c004118000b82c00e1220b54130500403000d62103c954801120485d43c0b1400b202d5410082c02401c5800d005140d200c1054400412903076074a000000d95001410544020800d212400414402614040303000c4914001c82d10782c111460344003006a40842e51280141c0d410613440d00c1c0c088820407803074000c441c00359109c40c2920001a100b08104801c0c040c252060b83c840208030b540c2c890800d800c14107041c0707040040c141000444003114003001c000f05080b140c003900e000d405170740e45840c00011603480c02c0d01c02da517041040c0400800c02c081700c0b852030307003c0c90780301401e600c0d1864030100091940309000000d40c8003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 759853480 1250 759852230 759852241
    0x31501020115140a172406030a08090a03060524010504060806150d09060c09060201090f081810021609020403080909061201020c0105090f0703080d02130515030a05 72
    0x601c40c098050b1441040d0044450801d4041c201030118441001c0d0800114100001c2e40b2004000900124400d40301400072240300100051a20040551209150030050144103199400290716a8001c2c2d00c242280c0d110743da004001240a00280d0000d0f0040c2e0400003040b0084d2200c00c019401211106496500001c80100441c1c850080e03005010100d0041d10216400340390141030b4883e910b43c220003c0c0d14050301d841044091b64003c0504a400548811000e01c24035084090040640110710081010661079151101c0c60303424104040c05101000070f01c840c00300c0308420300b4068141302a0201c2c5c000201b8010081d03a40c1c0340d807000d04040c0980a14007080c41c032002e0080b40c1c1220b4205201c0343c180b003902c50400c5100c0301d0180c40c0a038400040f2900c078035000000e0000c0c062440d100400003800d40b9000058a0030700c1d030b61858080840e0445102070001540790300694a008c01c00b000f0068540c00e0031051210701400139080f1360341c041f51102d0b04000381c3c0056001184950000c900501c0b264854 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 759854730 1250 759853480 759853483
    0x250e0901050919050a061e0b0402030912130f0308030f1006080103030e1f18090c0c0b0a0e030f040617160c020604050a08010902010206130305090d080712020303150102 74
    0x20b481c8000c00e40c10007403081c418000741c4007801e0107003400f0314242c0b0383c18003150380c0f010201c0b01000b00c5034181c0e40a10b00402c00c0101340c0e104918007254241c405500e1031601107007407a2240d81d00a84003070807034000b01d10016035140211001c00580f5105510300000c41d00c9061252160b000ac40b201c204c4600381c5400030703055803c00200a01207890300c0e01e6882d000e03401d5580c26122813002513061a0402400054100019100c00900f84800d58a03207039030013001c03443c02401200c0c13011600711600503820890403804c09075105a00c0704c0059000788182015441c0d442070440036006445804000d44004190b48045080e180000c0040319400d459541c142c5900b40342d03004a0b001c0403150006270880c015624100a8003c0c00c51600051005050328035041e240d000207000905c0c103403c1001540e40da081ea107421942c040010a070481c11079101c5c200507840c10340d00103090b0f00c900e821060003402ca802c0c3c0c250030440e0200c196001d440e481040302c00b000c0302c0120300a513282c00842c3d02070741e070311f60690703404046500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 759855980 1250 759854730 759854741
    0x2010b150711011b0c060917060402280306020403060227030c0111070503030f0c010c02031204120306030821060a0b031821120c030105060d05040203250e0901 70
    0x501814964000080b2401541c03400728400c1c541220500c05810703040018180101080a003c040c0c4a8101c107034140b01e208006542c4254070a0210350000c030600025a81c2c41d1000c2103038101c41d9650440070344480190008a80b46580001c1030301340042408800c200303103034010741109807050010392a6403c050311104100c5080c5020941c054000c428030705500e510507100d2500c0070304600110307814640d4a0003c0707480c6a1150803200d20303108000c200d100040340c080c0100f400380712440c4025400c1424006441c00d101c400580300620f03017401135511920702d5000f80c200300000c42e0808815a2100b4480c504441341d542e0030320700300c0c900c3c031800710002c1c05501c2d000030100c0a80791000340341400c6581d03100b104c800c5c110044404124074071440e02c4c04c00c401050050900b0624202104854036510320400041c4400c80140801e42c1000040c03006000945807801030b241c0d040d403281804200c98480f40042400c00303a035130003017103c1c03a5035514040048042c111010780403500c1015078650180d8802031054222031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 759857230 1250 759855980 759855983
    0xb0a050114150d050606091c05060a060f1502011b0c0c1a0702090a060f030f110f062b0f0b0a2309190c0e03010b2e0504050a0602010b1507 61
    0xb40144444042c400240d446140d01100140003e490520008001111103025840f02400000b00b000741d401008402c2c460643c04c0705141344140305280c200343c190000b1610074012104001c04821040396101d10035000380d640d0081c001c010341d2510711100c500504290b54404260303160410720784001084800d1100c00a0300700b001441c003900b4031245608101240780c001d000f5012080c1c88020104180100002410043d40300788034040d001702c12860503d00600142d034940d4424a0010b5503101e031511890300f145e0645031482e40301c00110616022400c0c04420545901120510384111403007130500b03a91001c000c1c8141201c962600743e90301c46402d888808104813300d841d0383e0b500140706440c2088036503a0b4102d0145c0d001804080803008200040300c506000d00c0000900300d1403003d41d182420300c0742e89920702d020b0b1200402a96500c0c100101143e0300c0c0c1040c1400c5456020038445980b10341c05903009884020000414a503503010024003278081200308501c01d07001441d500606800180880f12101d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 759858480 1250 759857230 759857269
    0x5030d02161703090a15080901050f041515030606061209151121040b0106050a0c03121d060403181503020a03020d0f090b0108030f160206070b0a050114 67
    0x158100102c8500d4400890202c52640c84203000c54a05640e07500e401801030080d07181020403a00603420003d140c910007421040b01640b6100c103005007031244480322940250065104c65500408920040040520740c0b041900707055030000102c00c004050300028200c40940c4d0b242050140c451800e441210b507121401840241e000e000c025240c40e4941111107044910311815041c40041d240380c40c1c18030506458188407109650402080040d003000e4103000d070419241490400e814034401421440c40c1e00d0b0042c2c04d000c08403143c800030000303503000790036000340d40d54040c4984040c403208150b440c2b40568085000c61100d0180c812180380409804c02110001c02400b94035612017103099009510109001c07080580802c80724014022038001c1d4518000300e098000348086150424041000c41a005180c0940040143c040c0c900060b0055598295030780f8004980c4c0360343c51001408a11900300f004102841c04410419001c03156404113040f10f040c05200001e0005800401039054164400000304 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 759859730 1250 759858480 759858523
    0x405060903160f031e050403050d0509131a030322300204141311220b0a030c29091f09180c110a0203070e070201060906060905030d02 59
    0xc00c0d00701d1603400010713000303003441c413600800044003448088411140b00003083c00040c00b0800c0042c100207140d80d82e4200c2c42c001e0b0424002400180c010014000e00c4806151a0031500b0001401c07031041e448010401800c4aa8803a1601c04440a081c106181807507540e41c2024000b4040a0f0303103076101e002c62101c082c28008000da03c025941c0c01000c1440c1032b43c002c0d035641d0648400425404044d401404410100704948071a4034040701103d401e049204e0081d1904103000e02c60b10610301c040d42100c04004004508202c0c45000305904000590002e003070f00070b00e91000244034100030321a1100c0080310160901707103840c0d108800c401d0702c240003000d50400301032111100d11132a10b4500075008c016503d00300d0700b429a10b9000c0300712060300310000e2814a554100c42400c1540081110075060014405000c0c00b501d583c0010380c41d45010310900b114800081c0021300c02500c00c0d0320240103440c0310141040b05907103548004104c1221800340c2c602030311811a007800d40d0707070000590103200959400100c99 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 759860980 1250 759859730 759859733
    0x61006090302120f01050c072913060b0d08030103030807050c0a030f020a1b0609050a0806040201080606072a050409050d1d09044d0a03050f06040506090316 69
    0x7482c0f02c0f00948240140c00104034600000c0c09440c1c054000048600c0d02d4050b141050211300400c55440c2201044a82c15282001d40300210254040700d038a14100c1f40c5422400c001c0c0281485032412580249200c680d130080080620180d4140e80c0249d40e2403140f581d9680c0156558400d55103032030001c1d407252401d02d000a01c01c0c2001c041c164034520640f80d0740007503503682c103c0104030011661070310301e0075820a00c407040d03000940c180180812514150151701e00b001c41c54a960001d00081c0c10070a89500180558803224101e8002c41d40c0300d0a580500c01011480211504010150f031000b8030b40c0810004080c80c082c094112000c5d00070001d080401072004007075a0788030f19204c11a05000000e10100c000d0380e241c84002d03104a002d00052030f090480008805c000441903400c0c81540340e040210202c0741100880705100e449902441000402d1407200040e40b0040140d0008000e441200c9900c1030629020811034000d911560071100982c807417842c01d0307031031303020321400510a0308800c21080c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 759862230 1250 759860980 759860989
    0x6270904080d150e0709140f010507110a030b011401030c030e030306040e0c0402070803090c04091a0606090405070507050d05040614090d0503040e090c0307030803010302120c21061006090302 84
    0x25104035150548014013682c0e0b42c00fa0080c2c074000c0b07031480302050b60700303004000a5150062200d801401101c164000901000c0080d180b805201e0300546103901c00200b80c05a44c0343e0700d00c0c0002941c1c0010304410b5542c0e58a0080b80001d210450b51130000f0300b04503070721005500071b000e00c01c908158000914210781d1034100f4000148100305a000c000d00c544507040c416900c3d203100501c00c0324014040160f803468220004c0d40780c115200d03a824050f030324100800c0d0224074a9804901d610300724002860701920b410001400c40d028084a40758003614002c244005a60000c00402e1180d100d8405d8424142090380d023550280a548246404a80701580c2607800401c0080102003545000300040700d008565100c061640c1c0040e0016400625171105200e2010020002c05044500440060124030f0541e517800c0494001031000a000e81c00e58403d000c01184140002031001c140541118140c0b14800700d12040d500960703010486501405000c01d5241104c441050f003035462545452000314959820302 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 759863480 1250 759862230 759862241
    0x62c0706082203030609050a0207030207050609030715030e011a040b1816030e150421050f0d02070212010c09140901060e06040305120301090509030310060e0a0506270904080d 77
    0xc4003050b55802011480341b6462103000c1c0101e10b00000140c5502c002e00d80649000c0c4a038000c3ca100780e40034822401e40c8c3d03400003071440c00e40e0180340c0780508402101030306402900b030982550100354240312210007540c14048a10300d071500c084a0030300245882005101320203000c4031a8080d440400c90014400c6487c40035400030000c024500001d00d41d00184188d0f081c2120880c0c44000050108184401c1c801d0040802200d000721764248a85080040c0c4060a9486001c401030b040c000c020070443c3c014000c0d68140d54402e034001c0d040d001c40040081c03056009201c8009198007040c02003e020407900e0040d5880d8072611405010006540d00b4042c050718003031204240c0c0d5601c004100800f00000700140440717224180c00c01d40f21a225410264100d0075510000c120800c1035009004110366822702200c1c1c00202d4689003001c0c2e4003802d035800401c40f0340380150020b58000c0740000b016108040c2102d000203420200c40001e003841c1006504012800c82c0c1610007500b071030700620aa01c0130031b840c3e6001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 759864730 1250 759863480 759863483
    0xe100203040506040b0a0801053304240f020d0503060607081905090f011d09180f0a021201060338010806041a070516062c07060822 58
    0x459040c50ba07210001091940640c00c00b50403040f021031265480e503000484c20b07000d0031080b82c1881404106441c0440d40880583d116100c00c0c1841602d103000d03400f440c040798080d144940d0714411010f26001540e4882000703500100000390308462174104644041603684034840507a8440e4079544416003000f12941226000780c803a80001c004a01d4a9038010b4a04003c83c1488d4a45684170301c0e04000308040c070001000102d0601c110102d800440d0000c1941c2440480001c0b59203c0080d1209403900303c982e105200105481c0c030541c60882e4294030700203031031341c0c06501c03c840010340d8450003401c047c26201075110007460343d08400d20340410342c0c1c1001040034003010322031000c02c0381000700e503a04e444007030742a0b105001940044092006001c03002400d06403241c100c4412560504200f03400424600c01d40881d400003c413002454020441190070034241c10b0100400708001c1141812082c0780080c1c242c0c0c21421a00c01c9101c0001c1c4680600aa0391040304034500008000744004100040080450300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 759865980 1250 759864730 759864733
    0x20d021b01020714041b021f020304170c0a0b10030c0b0a08011502010b0d03260402060d0f0902031204061805061803010219030e010b01020c0f01030c020f0709020a030506040209010e1002 82
    0x1614686c0380c025100d0400e00c45500d034020406480f5010800c000b0900e0030754014041401041003002003640b11160240c0c000110684642e03400804007010704005c00494000c083d440000300380814220b110420b8004c1d607004002c4074041c40d9560030020010710031040f0717802c00308d00600c0040040720703050110b1f0f8100c803030103000110340b4080140025101d003501e03410440105904030b04020100303500c041030349100103d42c100c6058604113500000c0250040ba000649034585030041c40d00a00301c0390f042080c40b145d01604480003150395642040081c0c102e40100c00014140869201141080746607410440c0c5020b08998074081d240345c4102e010380d81e561207480c3c0541d02040701c42c4002419404c2640034403900d503000142c0c0c401e0b2032055425541506d813000e04540c0400d07104407070b0307a0f1645003c0c12544000d090003d145400c45105905250001561a01c0e5004a61001501d030042c0c3d00205000100350b9801c000640c1c42c3d8003044124001d440a050008107500440d50031f5040001144641c02810700 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 759867230 1250 759865980 759865991
    0x1b080603070b030717010b0a021b0a03060608060403020c0303160b0606040b2d070312020c070e130c0e04050303041412160605010801060501050f090a0510020d021b0102071404 77
    0xb0100007540e0302c04da5018000400c048940c08201c0809071040f8098101946002d03e42402050700a6a400701c2c0b4440300079104071007080d004241c1c0c41c84000c00082d0340c1316006001d1035954591803900c1d00e9040f0b030154054098110907684901c0c0110440e4101007841070030b840a41c0d5140c4070114800c1000307000d581c02960820002c034805050f2009451140315000040f90b00e40e0801c8501d03880c0402e42a030003181101e09202000000e600014036440194280c10011303190000c0c004140d103050b6103075102905041e100d41c00c0c46981040c0a0519402034007412507058116035441013418400380854018040303810510105000507454000c40c01103100d403130308481d03c8800395204208560712640c500701e04900310814400801c1301d903015082c01030000c1c9008000079441e00e80064040e01c1a41c0b000c40305044002064461541e8001e03a050140601901005026180e442c000c1d5880e807810741b0391000361090094440900742c02828a050469042c1d0107001c4551808899880f00380c46101410740c040d0702e50 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 759868480 1250 759867230 759867239
    0x2090a172a09090109020132070507030606030c1a12071d041d15011202060d2904050a1b03020a1e052a070e070215010b0c101b08060307 60
    0x11071429000e08940c3c8000105500b451001401c0e004010f441b01c1c40742c0b020404c013002e0581c0c0504058860b100c605607501e0381d8211070300d40681450801d400080c042840c010b000b1082c05000003151083d00c1070b49230321910130340000f80f501415006014481c014003c2000c0069000d40c451030f03401d4000783d0550512083d840c00b180008080e1400080d03002c24043c54180c41a1000b002000110190a50f146c0740c14419418224840600107032990041d004610000c0d02088551180c0d2191462407001d2080500410381607480e000b01ca80300c2d0300568415814070021641c030300c0051280c01120510300c0b014038460488a031064020b504000501c0e018408100c0e00310544400d540d0542a10101b00c3d60340175a501c1d4040580c1c2e800114070380e142450456801c0c1c48a50050b03000a000e4191010070b0b1541086641d0190228a0f00d1000c2412090380450707000005180310004020b041e0794413160701a6061410040c241008640c0009030080222901c201180318450040054035000300c00902500c1d0700c952074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 759869730 1250 759868480 759868489
    0x602030c1213152d0219050c19050304090507080a0605090f040212030903071409010e010b04030611041809020102060901020f0403020d02181905010f050607060c031d0102090a172a 79
    0xd51382c0d0b00080380d4001070b030f405808103051040190901a4206181403d10310403e03255a11940000c6141000060146409000c010005c1d0b0b8001c2c84059414440c504c2c103c00020031124054031203044050608101007058a098100300d0301c078960035024044145e40d99020010441c50b0111041c1003804204082038464030b0038044140582400c40c01d180d0380070859410703c5220380050b0301204410500300c005000803410841103d048030b402c001d011450b45008581e007101ca00c920352140060764090004075030f0000103a00000c0415000f60261091035030b80c00e807290300341d03c101d4002d000748020070082400140380c906d2210203403c5c005003104070b41d0220a015201464000e90310420b031064041e0007401c459901c1d015460242c12100201614645080c002c12118001c4003c001e044944400b00700700602d00c88d61001208000c101d240011070040500041e000350f0060b42804c1c040c502e80540880e04034980c913584404060001d00410b004020380368801c1000192401c00824050746a416154030781d42c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 759870980 1250 759869730 759869801
    0x803040305070f1406041205010b0a06020f100b0109031b080304030f060c031e1a1c030306090b03030a1133061806040b0d0602030c121315 61
    0x200d4001000d00900384003d4100300d007035035440b1060605402c1c0640d4101e40300c1c082940d04860341506001e4440c80507181c83c2d405005615126a04103a50b0200018010340c0051402c02004200050380c3e03444003000402c4040c1c0710700404440c04240b1401042001800944001c103c0182d6034607400003064071580030038211307445948103890984882c0701c5942400903501c200440d400d12424100201ea0b070100c0380c040d030103894880c0c002c00c0790340d82d20303142d40759038810440e200080e10700901d20504004058085032101d4003000f03050340001e20340040402c0b03100c60342c4208044008014002c0d4140341003241d00700c4103510800041c0d4070340d001e849900600d04440c425036000c0c140b0000c0d0300d500d0300c803107032811802c03513440c018441c0d4400c000d40d1919401001c0b45106a680042d0260383c04191080600b000c256000f00e03140c0000d00c1d080c4004104a440c01900d0003605140410b19001e0560351210b900745e030200800840e01070010100e10800c604242c1c00c83c1d20644009001c2092104c1d58084d0641c092680b03c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 759872230 1250 759870980 759870983
    0x70504062c150d060602030a02240601050904140a051e0c2b0c090501080702011811010905090405240712050a0b0d03110d090b0706050604090f0c0e010603111c020408030403 76
    0xa00101d804282c23103405200110039a00400b500600c042c2c2943c55200c00068090411418010001505859030322a074100c00d0030040c4c1008064161b040c0120904000c0100700c1d00d01948001c002d20f211081c0c010042c2c04c03405101002010b80c2030200004118001191856420022100c008110f5201c08260700981c030080c5941c0e02c0c1c42d14808d10b00400980128002041002103924004440d100300521804d40025035401c0300e039902c4800c5003003005a0b00100103800255000740741c207003004100040003030040340048890000111949200c4004154144155224004281d120300b86840b40300c0640e0145a10a01c9030303030041743d005888004160070004403441130380000c280c00c2580b00c4040301001111400c0ca850301e0044442c4e45030640c409036900408000500585e211004100703035135a290440b000142e0080c00c0c0300c94030481031078400b84151403445040340008490000180150081c0300f041c01c032480300c0302801d2410540d0b101148a000540c01400502942448082100c00c0104003500c00745 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 759873480 1250 759872230 759872233
    0x40b0f160c12020103050c120a09080903030f21040807060504021f0c0302070b031303081306110403120e0105070b07090b0a0e010e030c1f0c0506070504062c150d060602 74
    0x84040d800010182d4500500704501003902304000001d40c0c1c010300306594803175000c0500045840ca64a0510b20500c90854003940c14400814200c5a100712100180003c0d1440d40000316100c80c8040440d002c103004980c050311400090140601003690381d0445c5038824401468208800004110340a1541c031340d1028800041215500c02d003010b40401c40240039081c0440f1540c2036190600581600c1040d0a00040402c084800802c0441d52208140300603580c0c042d00500040301107040f110304070b801510007038800c9800d5460540d505030040300e100c04400070681d40c2c1841c08200e078582100c04030380078118004009000d400051040c600d40050a50403440340c2d50b21072072070702c980c1c00100420358410b0002d200307812001c075036012940e0301c020150205d161144000100c100300001031728220b43c240406031507400342c0c004101140383d0040040099032119207903030440c00c0589400412020b0b10005c041222501006034007424600b00780d81d0745210b10448022032070f140f18194035901342c070b0305035001e007026 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 759874730 1250 759873480 759873509
    0x303030b0f0a03020a06030e100504030e100504031505060d0f03080601170105030304171c03020a0807051608030c0c03070606080f0604050304091e0219030f02040b0f160c 75
    0x391908402400728003404541c80322040d8110740004280222510034001416a260240914030074140000d1071101c0003071000700010301e800e04000c0c1c1421440300900d40300e285e0312480d208003940500141c2e01903e402c80442d1800308002418800100030141c207281d48078110107090360000c1c0380c443c41c482295119646031805c1b401e10718005003811002082100c20072444600600903510004151821650b41c40c000d0311760401a00340c0d450420801048074072200d0b0305000740100c1690940c000b088a0805a0795042e540d58404400711001e002c0c0345440c0309002d520409640115902601540e0003841d400d0502e8909030100d841d141c41c580c01500300702d4040b500e410080114160502245003d11121030180c4030601e0260340781501c0e807040d40101c0307000760b980e400d4092a545003e803041c2a13034400360004650f5918144690b2a410664181e5007001a0400100040902c0a03000741d60489020803005410210918402035480d00f01219078005084224010790108641640c107034020241503065104 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 759875980 1250 759874730 759874751
    0x909030e09010506090f090a150602060114300c18010812070b0a09080f0a020102180a0b0406030902120105040f051b011d0d0c0602160807050a0e0a09050304030303 72
    0x903039180581c40f942c42008240321a00c15a103400d00390045104d01118a1040c642ea0103030340500405000706200c0c2e03240c01203500840e13207540014130176040c1c40a11455100c3c10418400b00145805d104400c0c03240c103101d820844a0f59490202030f02080300104081e50400c0c03c202020620455a034400707140c1e0301c5800c400410200b0024071140030030022000c0c215203031a8041c1c4982c0d003800302c0903062149480d6180320000501c600001544c900e56040280307980d0b9680c103144000d010350014081001c070b0011402d014951171400d00301034011113480c038460509140c54442c003a4024011800306a8100007050310082c8034030001e1068074462031003070f5100a500842c0741061860000c080c4258604c0803031071200c0d1160b603a000350601018000c1da10039001c14201e074801041c40da034020035008002c84452440402c0054000c200162055070302003c00e441207580742d407000e030b65606a10030315800411800d0240101c0c3c029547d41c60380021010700c045018640c03039131207031710b16171080c0c1c82640002c0d528000721711b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 759877230 1250 759875980 759875989
    0x120c090e0c0702130926090603152701060e01050702060a180e04020913030509130c020f1501060c1b150e101e1b050703120f0c08130909030e 62
    0xb00c202c06038030010416400b555481031b40010901401c880c0701c021043c180d0b0741a05c0b042084504c0014058229502c1e800c242010703144e0718488164192007110740041d602000c40e44140c054042c11004e00510207181d02c0c0c071078144c4140ca040c8182904121040040c040541c8170f55004100c40740340c90f80d070500b52074406844003a40307a820f90090a28801101c00740805680d4140c0d10640040e18140408031503038452409846901c502c25a194010001c091204ca00c900380c4e0780a1103803a0415025100245c444214a136103c205200744807085104030710041c402103100300c0c2a141402c2c0726294140707a50403a811024954165907120b05003c08000640c00c00c80c9038000d441d0041c542c0241d03404d59000c0b412520282000e941c0548443d02c003412060b004509921071410780ba144044108158040c10302c9080242d00c0d61440d00096500306d4414200d030090703d22070b42400803008025607620807096855610190144d1025107100826052030b900840c111000784241e0301454800d8803214000d103550740511 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 759878480 1250 759877230 759877249
    0x10902150a03540f020a050f0a15050c03070507080d0f051c0617061b040305120904060e0c0306040c0e0105250606030f14060403120c090e0c0702 64
    0x21182c1049003a003445011580c92000000860b8212101d0000e006042d101440214507008000c10401c4000001c00c0c8a840c2d0034040e0382c9802a203d071040a900c600920062360544020503401c00d003c42403c112303403203030701c21404901c400301c4c6040e6103080c55000280b8595004120240c4464000080c2084014810048101404414104100044d2010384003500601446803020000b0800111035099080542d0092015008070a0b03440d0080301020806580d5103412a020340410114440c1d030791183c0802000d5a0407640c0c01001000c0200c0452014103880c1c00c41456aa0060740300c00d000b041c400c0c207100115211740c07904107910707449250010400c015961010307011010300c00c8011010704240d0b0711004440d0544900031781c0190081d0100000440c450413040007902651a00c44040100008803490b15a01c0780035089011419406d00031890b1542400e0724024041021410f86602c0300fa1907401c1400c005c01181084c1400342d90300c1d060040c0014040b80c0c1e102c056200029400110328001e03012 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 759879730 1250 759878480 759878501
    0x90b0f09030d17071b060b04110d02040801050f0606090d03050d06090e1606080622051e100f030b04080c070b03090d08091009051023070c050a02010302030603010902150a03 76
    0x9032400707119020204140c0200170700050140303501e6500c0b42025440d04e0f0440080400c1c0500002d54407800c41015100a401078003401c41103508010104140b000b800c00d503070780070b03601c002c003150f20b020440c05c2040458207101d203044081c480309000030000742d4414402d0340010030392001d0200d440800c00002604001d865807201c0c440b00103100083c009281d00100180d40584140c0b681c2e03200e510f001d00c50592020100e8411001d081c03c0c24100000000a55000d09c1e000c41ea0070103011080c1c1315002d0301a120603007801860001e01c8402c00c108046a1038140a076003040c010b41c2514034003801d0201883c01c1811030303040481d89088c0002441071080c0c3c20080440719003000c1c035105980e0b040040a40340c076040f003204072682190716070ba000420f114080c4490b00224440380c000300035008601881c42d0100c0c0e00c0c6060842104002d20000c0e007814003c6141050342030748036020300420503013540150000d41002e01269015075031582081c0058503024a90a042642d54a11680380d40300342c00c0c01403c1e100c42d102e1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 759880980 1250 759879730 759879737
    0x305030418020a121a06130e060102150408180d05060130260a030c020d08040515040507090e0307060b120304030305070618030309020a0e0106090b0f09030d1707 71
    0x880b00e4080d41c865241c5403401400310001c200c0c441c02204807102e0440e2105c19545c0035034001501500442105d44d08012a45c0740c0c030304a44503940d140c00581e140c1a2000e803255001c1000c00000e000500e0340300080c0801003010200e90b94409040780440c1e200c4244107006c07152580414014810136000d420507101d41c2c0142c00030803100c0701c11980070210711002418000c28460381d480c0460680d420207180803540807000c0140700d441f1665040000d024100d0700c0000c0d0702500078282d0362401c061041c100d551090341c00c14002c110327800e01c01c01070b0120144c004000b5940c60064050110719120540550450466004011500d446060410504845c4102c03641031150110003141e0b01204008004d442c202c80c2c0504180351204014105030014005055144550384e400c09410000c054150703000300c44181c000d0712000c070615203641480040c070800f8051070020503489101001400303041c2c0001c0082c1151740c05181e0070006500e02007440c2150301760704132001c2604488181c80f02d0860813034955114400340f4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 759882230 1250 759880980 759880987
    0x604030806010216121a132004020304200303070c0b0901180914090a0b010e0405101104080d14030c0a03020c0105012718290103030324050a0b03130b01030503041802 73
    0x70b241d47c14200801c030f000304602c90042800301594550f242c0d040340f040010704259507a1629141c0341300120070300941c1c4c205036586014000d00505001084d102600d038000741d04142c207030410346103041700c2c0c100743d202138100201322000c2243d507050000144010724a201e008107050f1003e0b0b6030341e444d07101c2c01070a0b07000f50391244103001c000c02d84400721241141d41082c5800c0140d10303641803003800d05041321104848a0b04140c1981001e0f4081e20041089a0410003615034030070000381c0860b0400c24550300800070355801e00c0829075403200340e0000c4c00d0061003810f0040c42d08040801d07031425100300341e10031218140312401e60541100102c10100c440341c03090408118071041c040b0a01c4601c3e01c4008064658082d0306c210720032020007480303503010007140309051030450f603034a113402000703010500840c0d11002800e810400c500c1c40c22109100544000800c503001072070400220198641009040b082c0101440900c90003042c0300c6241d031406503000b0406190b560382094071001454920752100b0889a1040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 759883480 1250 759882230 759882241
    0x30e0c010e0a060806060708040f0501030b040e0c0603060301061802030901110c0a06050406020c0a0b18070e01030209070302132d0608060f0102010e0d030b1002030c0604030806010216121a 83
    0x1c444805840310f50608034045d0710342e20701141c901c0c0900000104003d41c0002e02055240040c5241c0b8203c0e002640d040c480c0607a00d10522041e0b607000840c8056036800140340780c42d2440c044015561002e409000040c280703540300301e0861f00002c0e0365120360742140c3c00024007000c1c102c20301400e07505048000402e03150a4a82c4130b100c1c0d80d94001e48003d0081696080441c040240c02e030100e408038000403084502d4084a420000443c241c1640d88a8208040c0c0900004286c0046800c03400c66154445030641070b0300c0c603001e1001440c0020f000c041015801c21008003004201b4140d6805090b040200c03003486540c440c003002d2064804012512003501c3c0000800c40641e0018040da881385060b15200e21003c6040010703400350203036040e80802d6000e110021006194540d1149040182c00c0ba68105a82080807050b41c49108120b440c80e1142c005500140102e4010801c581c0c00c041d041c411a0b1301590004220950466960800c6039608443c0040c002409494443e10b005004100620f543c0c60608 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 759884730 1250 759883480 759883489
    0x60121140a0509033009010c030e060105061209010f140415050606030c0705070f1e15080c180306131b050109050103180b1810090b07032406030e0c010e 67
    0x60342c01400810070350142485903060918960403900e990171410b081903013401d00410707001e4881b000c0f075280002e1a0008110303007032400055a83c102e03080600380c98580b00c40ca40e00101140c000070f0032041250340b517100041142d18148224802265511345850340c9007080e01d8000700e008400c101c8403102c42d0404090017002d5480c9000c50b42c04c484000300c0e4554442e140e15003581009456401401022402040011101a140c40404c1180c1e020826010801d03203540ca035104030400001c0c03140c00200d00380b0001c0c2c3d807004088010706010700d000c404001482420000246440002c0790345240d8004401a03035010044032004c0004180d80320b4040548580c00d1500080000d00079214481c105a110200c8240c1c000c0344004209003c3c4d00700e000e1501c140f070001108424000e841e808482180318848200c07190304114440e40790407a038001c8607280551681c00c82200030700084c12000c1c804030302d80c0d071661044503101c0300e9a0300202510740300410000c0c443c000d15800c1c00500f03405c050602c00f0207001d0642541c0c6 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 759885980 1250 759884730 759884737
    0x4110f121605030708070825030203091014010b07020d140a03081302010e010f0504080109110907020a030c060f0e03070f02030c0604080303010b0d090507032126060121140a050903 79
    0x7080d00d055442c0360b6900084480c1801009000a948800320288c1e546032541a00150301c500070501c211980344d0381049075441240c000603000382400780a10010301c00c900c00c4400400c2d2050009280c1e0700804004d07161014200c148241d1f5002540c020a61070f020180c0001c03016a028900b880604241d01e2a900007070480103c00c62000d0420500042c00d100041c0a00181e402901c040da0007007104010703902e007405454520b40440c52250480c8400141d080b4030000d204031a02e40d1550760547c0d5007103155145e001030300300080182d01160700c1d241500b08400040000c0c000860082090202c110410f00602d41403803955210b65009100c100014400e00b500003049034119401182070035aa203514a03034040040c805480700510500404c1c40c0001840345444c58200c5050141e106805616040c800658020b16141c07001240040c04012001e002503140306504d0788080c0604041001001d45412444000a940705030b0585580e2000410000400c40d0303a41940504a075030b0400a50410000d40d664900 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 759887230 1250 759885980 759885991
    0x6080a0609061b0e03100e0a030f03020f030f060a051516020406030f1209060c030f261602060916030f031e0306170c06040504110f121605030708 64
    0x207072128401000c12400d6031040340a0501540d0030030445010050041525a4070b0f04290f00c2440341d40c2a0a40440c030038480c07000c0200c0329000600800c44150340a6840c600c01040721002d0544c28840d003618910158019480b894015003040c1c3d1900c1c12200300424441c00e600440c0c01240300e0300314503000030794071000c880d200e0403813100d104484155440050301800d00703500010800c030b0402e403c5000300720124001032541e00c41c9880c2c00d40000e4843c0d0041b503041d400c9644c00342c0002d046200712000540521000d200312004910701d164018005d1a1403800318074140c031414189440c90789c055002c90f5052241079042800d1074050020505a0f03090205000c00340d00010785214403090320307501054054046980c01801001c40c01c154601d030341d50003500500840c89000080d203c1c0c002803500000010075408440d600060269007010b05000902004251950f0480e1010301c04005065840c0c0214020b00310320410004800001c2c9000841c211000c1c0e20228441c0511200340107000702c1c00c0d0891442c55000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 759888480 1250 759887230 759887243
    0x1030803011e030614060a0e0c07022701060e040605031219020717060a060501050c10020d0204091b14040b180607060f09050601080f030301122307051306080a 70
    0x840360100c2e0814201c2035000610032450110454600310401175650f21500003250941c4000380d80d5800310348007080031601c0c000402c004000d0b042c018501010100240c000517410101c0c3c841c05c0b501c401c0716660782a007054020940102112040d40340500480014000690181c02c203101c05001140e0300b80100f00d0001c045280c0e040741000341c64820001180109886000c15405101010000c1e8540c81e083da0842401800c019010a09501540131509026004401000c403444005a0000207400152140141c240c01308000501180e5038041d0344d4150b40d022003002608032039038201601d1103848500da00b074602c1081c801000030303520308010754074000b4094841c100840c41c900006000b80c81003000080100c1d1600144100740c1c2c00320742c08400c02c3c43c41181100c60310790300d4646613565032401d0102d001155004000505c4540000603850300c01c50312401c02040400507400c00d000300e45040d00d045083ca40c1c8586003c001a240c049d11600da00c080c955410000181069a0302d0340382c141911b0f014008 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 759889730 1250 759888480 759888509
    0x9030c061505090a020f0f210c0423011b06021801020c100e03031e090306070302190e060c0109051c090b07020d031202030c0d271704080d0e13050103080301 69
    0x30f1485d4101107e88043c034844801d6919001c40e41805610303000000003070300404104001410703182e20b1000300d03070540e000701d0a0b0040440c000d4032206100200049100d04210014409000455803a001007840794891000548c4800304c540244102107600714105045612000314840340742c50340240011032980c6171030100c000061340e20100e444c51003000c0c42400e00900010300340c0210300341c3c0e10103400440f804a0958844d500e404100300c00f43c0c026800740c0c18816a00004a911050094040c1e022585021704400c1c03c05480207101421517500c0c41e01075400d500401c50b2052448520120108440c00c0e80c00c10000d0320b0308200e081e180c5c41c001c1c008002e00901d4170180603428580100016100103420010a5550b890f20f054402450b801003030303040860078242070109001500c0d030304800700501c429031031100014841d615000400b1400da0712140c2d07000303001c01010400b4101400308070301500040e200c4c00c00685000301800525418061032031100c0d8079020050000482d0b10040343e0444003030101c240c04 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 759890980 1250 759889730 759889747
    0x15060c23030a0c140105010b030121080c0d090e0f0109020d181101020c0f09070302070f080d0618050424020405090f04062304030305150409030c061505090a02 70
    0x245444119408400d8480030808071529a031081c2c0e80c904891042c42c40a0380301c0c1500808034240ca07001c0c05005035a80e401e100521000e100a4100300c01c64101c0812a011000e2036112241994020b8020f11507540100b800f440c6200d400180020091005500c501e0340303413078841c0031a210b030b2106020743c0c004540c0000d510903255285800c0801c0940d140006c04050104500e45100d40c087c8401c60315003d8010030807250410301e4210a10710b070842c2c01501171111541c0310f0104400940c00713000212901900700d074200010403400405409600101080010694205003003c0c2003001c28040517207045083c1b50402002420442e076080c0407980d501d01d90011080b40c0f03c20080070b4091500541e401c0810310342002a61609105500e00990040d030301000240581d031150b18031000085004400041c8140111b80001e11960043c2d0303101040401a10541c020f003030010341a2080c103032043e0000b40c100500042805000d00c0b414a00300b081034481c141d43c0b80340c5000716203d00c00042034446907030f0b4049907094 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 759892086 1106 759890980 759891023
    0x90801060602012705070b04080f010506060c15150d050105150d210c08070b160801080a0f02030102040b030f04110a050603010504020c01090b07021015060c 69
    0x507000c410544d146000620020111014841c1110008810036014050000362040c1d501900c07042400349152401e4a4002e0201403003042d0070040f9010780800058150340b03164940d842c00540c0e54501210300d28502c0381d4041e80da00840d080090004202065124610902600d850350a11201d51414014106003801d8000c080030300c02003403c0d00c0b5070b404508580a8580c0352a1a0810000664401e0183c0d0000c0c83c0844810304140284400802e21174800000340400b840c02c0d06956140c4220070740d4a045007100038101001518012056450a40444d005001c2100710565241001e0201d60a0080111816101c41ea203420003814507103450340400742100c0000b8085801d40c0d0078035041000030350001d4940c4010f507594500800c006100b03602070030310a1241c4e40240c0b0340c511200d0200020b88002801400d03801e14601011301100760084040301d140c1390007000d8452040440f80d00350 = true := by decide +kernel

theorem cover : BRFrame.Cov 759712230 759892086 := by
  have h0 := BRFrame.cov_init 759712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 759712230 ≤ n) (h2 : n < 759892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
