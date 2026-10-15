-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4528
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:54:22.548954+00:00
-- url     : https://prove2.me/submissions/d2f36720-a5e5-4044-98b8-c88d738a2062

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 814208633 ≤ n < 814388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 814209883 1250 814208633 814208641
    0x90204060e0f0103150e030301080705010201150e0c090d0203010f0509010e0a0201021f1803270e0601140910110606090c0a030216020402180109150c0221060c0a0305 73
    0x242a03076942c0308401184600c0d55990031501d80300d5002d103403c03d07a00d22040e01c0d100340c019124400e0014500138283d44004100b440d09000001e4251100075612900c0066101400c10008840d114071070307000740803540c903142d44241400104000704441b0a01a40540c2003100c1d2150003a03440d0311013441482e10400802c0a00c0d030301c42100f40c460300c40f00006030041c0c0c454402e0240135555080b0201902d50002400076071000b040284403481c444041082d408281031100c9405080001d215850540c143c008003d14241d0408a4112421030003038044d50400c180340d001c0440e0503409404580380c04000919500458090130001450650440e229240c0760041c400811241c1c00c0c024900d6004000070f040040c28203c004030200c0094000344003074484260b20105150158403944020502d510200407a01048240c6a00151554989901800d80e25981c01d00d800601640010700b200200e40c11234504016144010b14504d00c8191000724000ca40500340602201c5401600200200310681d1070038842541c0f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 814211133 1250 814209883 814209899
    0x4030b0a110301060e0402091216031a04020112090f141e010504030c020d0c031b050f0a08061b0712030e0d0309030c080307021c03060f09091e0c1809020406 69
    0x401c0c41007a02085d001c4040f0b800d00c4c58150050009044040c10b5054044062040c0c5031504001d0414030f940d01401800500a0109603001c0310001b0380b45071a200d019042c2503000901c00c41864103244002541e4920a40c204003999012007034541d04045800c661041001c00b0b25181c1c0c01d041500300c030705446011652040302c0c042c002c0d5131041d6056140c2a110152a40038000c01500c200b1003110100e54050011000034828640e00302c41020000d0300000260030f02050020b400c650001c0680b14441d0500c2c20807400000040241d80040d8000502030541086840d111a03030082c01c4008040c402001054003500c0c0c2e05500130101c0c01d11810031902c94640c40380b001d808036080138130301030009841043c820010401c03410085410809910490301c020080c1c034000181072140270100780009031544c5041103041d0102d52403001405010340704011020250b510412030140c40310040300003441503410201480b0051082100074950012101c5089801d0302c1c00b0401082d0046c0200c0c4602c0c070300040482d9480c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 814212383 1250 814211133 814211137
    0xb0a180c0c02090c09121227130e071802030a051305030702010804030c14070e0601020706050d050a150e0f0f09030304031d0d0b090d02060c0a030207110604030b0a11 73
    0xa500500388035034903280e8120814040d800b108402c0e40111b8844107030781c104101000181542481c00c44060380b12080041601058000c200d40c00215030441c0800300d0080c2d540013091400300180340c0002402c034030303100446400c1c2800d0f07034080112801d84042d101c214171200d03001544220440ba400700b01590360740c0d010704003d500c4460041c045078000d11400005500070a017035500700b8000c0c141034100d4010b5640703030341c0248144c8002c5032458009000030048070040002c015000788090015080850a10000130603c0c0690710807014190f0300c0340040f8000200d25880001039007045400802d0158030b9500849000307005950400c0b51341c40740b10010310400c1144500c00c1c05030301010055461929582c41c11110141130b14840f030000305441541d48040d603510b007000440c031840750716010b405161881d0702c1c6d400c08032000409425904110100705c00c2462070780845a0b000041c0c00d0058a40c496410f1020608600c460025001600014040280200c07442d149202c2d00c809001030002607100030140d0454 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 814213633 1250 814212383 814212407
    0x15120503211b03040305070804122018180601060f080109090b0723030702010903080a090b0c0d020d06241d040e0f010504030e0a0e0702031b010b0a180c 67
    0x40401c192000c0080840c90b00640c0c0160280c0b80003401c04000740c880300d00c0d0390300640c070050078500380214410030005000099041c0c2c111007503003940c90a20308404507000700350b50100941c00410000015100034500d118860280302150220348256856a1010f412040605500c0e0040f9500f0000015110b40e0340c01101c0d00700d43d01c00c074415120303212548185e1ba0340d0041d25100c0f1201d5031010500c5d81d80031505000d14481d20140d8000b1400e034900e410081e101e10380181240c40e10300d0415070310b680031503607880700590000080300070079076500d144006880c000d005148002001d21f0520030b0001d5510328000c0700b2401011817903ca940100f412a005490f294180d001c8103109519181107540c641c5040d80c800c948100b481e806482880710503001150031144211003ca0104210560285041c18003100c0e4801411455001540d20709080708040e503240502c0c02e2060b038000f01015405000b000c20f4110324070b007003805000d031604583c070303042c4961060170000c900b0500d90340f0b001112100c0c907100c1d5906d5800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 814214883 1250 814213633 814213651
    0x18020a1202100e042901030605060c12090310020d050f0c1c020306060702030307120e090405060a090309090510180606050906070c0509040f200102030901031512050321 74
    0x2c40001c40c0040d611107411118071a403096540780300513101030b411300c0710340512080c1d580350000150b54080094219801a0440c50140344244a080c4160070300144602e00c3d80c04c01408141c44101d00c500081c5000c0760340b100e00203981d0000c501d9948000d81070300228020000007840c1000761355928141621401804188005080150a035031007031a503d40c01582c0003d409000c0f20b02d0b0411a0b004281b450b80410744c101c1b080000241102c009650184a0f103412640881b4a00400e04013174590b42c0c0e840001414882c00c840d981c17603011007050b000318130401c010240c4400a020710302e40841c1c014110780da01d200d9a251602903185180e24220303030340300c0c0030140c4045445050501d134501e414401a80c21094046038441d400407004500c1d030392492140c0e4407461003484a1814011a450402032010780d0380c21104d17100e02402261000e5a03008025608421400e10300001c03000344041e202042c07580c0342d130b001000f40c952640000092100210040c14220044180111400450403d10225210494650103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 814216133 1250 814214883 814214899
    0x60207090e0c010c03090b0f032502060114040f050c030f0903040f21140f011401031101110a0c120b060f03060f0727061101051005040905010f18020a1202 68
    0x4019801060000c004d18002d01d0b10703464451f00d800201c4002d500840083e5002e0380040f0810014005040c1511010351062500120402c0d00400c065030350601030094030320741c1707112058014440d21684d2112452004c0d02d00244500d080510681c1c2c51070340f017943c0303000706034035a10000740e00302c000003044030112811041c0d822411864204408809244030100300c0c1002c070440c0c001030204400016100a660141c2c0240504cc041c00c02001d0840b010301c1441009200b20400400109102ea164240e40304001e00b01094030403004000c8a0502100f003800400e00c1d6400034000c207048082c031035088403840c444c2031082c0054030b441e0300704030816048102607035155004900140c0c0102d01c1c11034603501301899040810b84039122400c2000c0309101014940c1c400020350504004081c2d021100c0308410b800640200940d0600074200b08035018140101806951200700398010080250310128402c4510700042003070000740e0b40703204800b0a69070f80a92207141c51110100e15103130103038540d460350340d40200301c90 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 814217383 1250 814216133 814216153
    0x6020118050c1005130303031e060e0105010e0f030601060801050a0e010b070f0f0f030210051f061d03120d110a0c060507030902120709110c1f0b0a0807060207090e 72
    0x5a0032007070142103c10010207108190101050001040285100351030204441d0b104008042d20780000000854402d41003050800141044586030b505440e400c1c41c140341300d0164100410b502c8a084028160144140c1d000004c4590f400010641640c0045440744079450f902c20701203c244000380a4141000300800445d00000d03558400342903424803c0b180707501c03500710a45071038030001c01c248401c4d8003603004a80100c850848074403406602c02d2200c11034405003080c42c00144442d682c0c9005200c10b104850005810900c1c808480c0d800500008003201c0303843c1c00c080080f208031b401086001017854200206030b0b5580491750242c0c1c91001644d070714070200400d00c0e2a0310020384405009402490782d1600d02d02c01584030503c1140c0c03d591084000c01200c0e140c02c000c0411101441c100101c0c0d180140550308184c000407a040d2441803c0d01001500c0e50503104000d001054500a070b50b40c0400c0d14140007506107000709002044922039000d40340101d644e50120300a49001d40d80000d01d41d0071030702c041 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 814218633 1250 814217383 814217389
    0x905011502100b010c08070b01060201050a0612110a0b04090603050106080d1403040f080a0203090111060c0a121803020d0906080c161103010e0703060e07050105032a0d0606020118050c 81
    0x1000c95040500d084000c06045da10b82d8504c5074070000003914428248001030040f00e030240212a00101800d0041090320310f010854174510341e064000900c03005500701c101c007199642d9401c640251102405c2c5170350311695902503200901c024402140e0340e500b0070b40c00103004903000c200c184a12400f1f80345d10781c940700c03c0301c4c0411250748001d008440e0725000c84051404581d0407005485803a035540c008541e01c01c00700b00050031001640444030b50551104040204030b1500800f80c961800c03680c01c21401041072000e202c0c3c050516003510b650141b01c1800000c080c5540000e00301a4850103444016609071500011a00a2000c4503000316039241001260f0001030718102c0c03e11514040e5a00070121540b210000b800c3d03e1103c901e104041d07005201c02e005108983c0304034841c10205200900b105464100040c0c000d0000802c21080410407400411910030101503c4040d0003181e6002c0e41c0e120650071281c40180454000d840042d80307400b000e10300d000200c2d01050b80e0207800c2001000f91106440070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 814219883 1250 814218633 814218641
    0x5041502010908030c030109150501210b1816020102030601140705100f06080705120c240304200405090703020f010e060c0d1e090306091713090501150210 68
    0x2690119940c1d080d1900c003050310a009503008486040d000c3d5aa035141901c41c0302030307680102890440a050280802507680c108003200d039684202411705440804040c090350080c03003094840c80c1c001d19416a00c7d032250150168103880340c0311807203e01c07138080c840400032400c070700003155047e01180045240c84004403541024040152082c0b044541c520070303d1952005407508002d207440d200da1100070501031401c05103d4100601010345042034103060a140c8a5518981d0440345409614032110380082e06000071130101c030b0210103d003d50760301d0400d85000c2c81d902a40704244424203034550703290201840d15000f49400b0706c4c2c4410052601609540810808481c008901410310416078810045070310307424060400d040100000e8104480003002c080e0103808030124600c0c400941c001c40d4200160464642010350381c004c3d000003061801071403c04c40345400c0b0a50b10b2101c04003c160902c8450340c0200b44d40c203841d90103000f4407a0f030340e803552036000c5008400c1404000da000410032022403212580 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 814221133 1250 814219883 814219919
    0x190e0f04050613261b0105070905010315030206031f17070906060c0308090316050c150a0824060d0c030e12070b090a1a0403230d0b0d020418021f0504 66
    0xc9007030b00d42041c00c94002d4035410340440c00301241c0d440d01f041191403600480c0c1000200020308092124107a0004001012034550000034850030022010540760006c0302c0c2c01c0c011010811802c0c1080a8541c0040c00000d100390400120798440c651020881c007405018400440d1903035100e407001c00342c05a5043d16002402010043c09210074020340840c6006161a4100e050152001c0e02c290309006040c440602d421203046d41c2403140400c501c1400607032010800350312080714401205d1074020005c02508040044c0807455020401043c10388503000d81d94091410001c541d04d0810540030710402242e110a8110240c00201d44103025000118210102c41a40305510308250b58510a507a916100003442514000144000308020070040503005015a0b519001c901c07103100302490448503030440d61080680c8a1000c94481040300b103030b6120780e510908480c1e07000300107002980042840e40c0e410403950704107a200300180c060385019007407003000d9080590102e540380343c45d044c02c1002903030f401d801c608 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 814222383 1250 814221133 814221203
    0x10c11010e1009050301060b130b07030509030706050d0f0e190c1a0a02070618050d0204021605030a020106120b1b0c030c01051005120c190e0f04050613 67
    0x4100c28106079075010b000e0b1400c0005031944010300307040a0506003162000e40080400c00f40400c1400040c001a085090454010699003599001d25190803103841c055000900d4040c481d4000110b800c54102000d00f003841c1c9540c0f07042105074000124001591380d20744410b94150041c0904a21001d500c0304d040c0d0616016060030300300c00e50356a41c028100c202d8000a08807034200402c039041e54030b0381400900c0c0109258900203140b10801c00001035204114032030b00c4c3c0f040554681003411501c8a406803840c40001c000d041d4280505400d00303603101d0f44010201c00040d4604400403c08540c5040d81c2034020f034000162015030b9a942c1c50701d8200c20628600c440101200340300302103036040104001c0c60b07100d034000d0010680c1d080003655414620700c00c0d0021071182c51802d1100c010203800003102200b041045940c0a00c000420404046104e0b180e005004400c4580c0c1c10090b2043d0422007207401036115a04407400c2d5a1400041041c048521900424880d0031900c1e0900c05402c00c1c0d5000001d032004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 814223633 1250 814222383 814222397
    0x9010905042c0a030e120d0503040c0801022802070608190b03100b15040b2209020d06140d0b191b0f09230402030a1b09090e030405010c1101 62
    0xc0c8400b510040705000c01c11000d900c1015000201680040d41d000e1080f0207440b45c89007000c180415580340c0b541081030b881000400300004081c014500181d50080c08900000c55440101d00c14012100008030040d440ca00014140035899503c00907002048451954955071251110006840503250700511072200e5070b01c03080d03801c0e80c0759014800340c0941003000d0400101e0a40107802c1c40f174020b03200724500704064400d200c00c0000340c024200301c86845900999001e0600099043c49400d00c4440d04210f01c0d9520203c2c1305030600600368810300c1a90460b00d1803001c0c0c05a000704005007000c0090000302400a000c010906056090101c04102c8415100c08503c210048a110040b54801481c050004004190701c804a680245011011388210000c200000f255502d40c52650844091060b014070340c000005242c002095000c41060010b00d03603c064483d0380210010094a29070140140403807a04202d002c52480010480701101c0307060b1a418502e031940d0f29021100300102c2e0305c050503c10381c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 814224883 1250 814223633 814223681
    0x30304090501060c0b060a03023607020703060b040c090e0702120d090210082a0702030601060503011e030f330e1006030f0209060111060a0906110901090504 69
    0x15030103828083c00b41079640841e210054200300400001c0504010301412100c80184007588490501c403003000d102c07610f02032490a15500584241145007840179a1202d9a014088200c0c0d000c81c0000849010f4001841100054420001210f039000e0f19400803500507601003116100440e0300a034040d45900683c0e00b9405d28110402c0558410390141140c6540c4c0d04400003180752420303202c00703101000c4c84e202c101d625110307400da00036001400c12001c1d41600d030710140e120642040c0858044d0350303011f0150b0b84503581da5030340546aa0020700400310300f41410303440c400c2c03c40807040e040720849400040101380d5003065101c00c000030b920840b03001c50010100042051756040400c406c0c0000c1500a0002003104c004d10005040581134094a0b5020b03007001000c00100e5450005800c00702d4045800c908651170390001650b51041407024280103009201c01c20001b40328a51001e1380c0c040c02a9414060460017200c0c0c05032500c24030000d1030101d8250034081c00181450b9100b91903254220340c0f00010804 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 814226133 1250 814224883 814224899
    0x14150a080a031119030f2a110301020f130302010306080607170c0423090106030924020c0a050a0210050a120504050f070b09150a050f0c030d0905060421021b030304 72
    0x81c150038241d0210f440c69041286c5c80d80e11400100a0b500c07841c04d0740c05092241040300c2507901d100038003d011801040b00500699400717504640d450004130070040e949000d00d014229505805120590119150600009035075401144980c850805580d070fa5006000c2552a200c500c0d17406882d19407002424070011800006602d8880d1241c2d01032240c4805c00e009840800c00213182c141c00a200301410314507070a00168a40161241410506004405020b45c0c072080000034013400064000038030170142e03a807040c4040402c080c1c0301c0300d00aa403848405698030304280d61500c1102000000070f81240c010b0111000300e580120741052007001540c144030900c00600d03145c0009a04443d100003400200d080462418501040c815200002da050510b80244001b42c000c1c01445401d042c0070800041407011000240125541007040450400010350719082c06075840d0021542100c5c24496120300034001080c20048049524541d4000c10000c400000d454141016841c0d080342c251100303200c0861600 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 814227383 1250 814226133 814226173
    0x90304210c12080d05101a0d0f14011701110a0309030e030d1715060a08100e0c04060e0f090c0702030307060f05100b04061704051014150a080a0311 65
    0xb400f5052590300c8104c0207244c84200c2d5806403601402211000007004507400102e0a08403c05003180416100e40e04500039602800083c00035030f20552520142102c02c0904017010b505840d01780546020903080e5142190072108450000c00744040140441c0c225544240c003c00c1c42d0038480e1370201290020030001c82e14110848800d00049029010007280c0c480c0300c082525403210450040c001455840c0b00810704d070f40714110004080100c1030000070b58442106030720f00010001940889a18070744516003031011b42103401884001501385054060074a00090b0307940882c500103150b46a035840d107d075900c102e41d01840b012605404103224030300201b070040c4181403460303501c08004145880e2600040440e0540350f0004030300c2c90300034001031141a0740000c2480c0010f51102c026601c648071414018503021100d00e10400f03407414290500006c0f5030020b002ca000d1030a494891450904140402040042e5405529559070089030300c803004c01d10440c141e10500c180f1509441080a6081610002c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 814228633 1250 814227383 814227419
    0x2040905010f0b090f040615030c0e0105011706030606090604240f0f08030a05210405011d280303020c06100302180112030f12061d090304210c 63
    0xd65501c0e40c0b205000581805034001c9454101c40c4890380303142104c0c28145060000d0005010641d540300e851071000c6103060001c02542d000b0b00c80c04031440d922109852110b40034007540740090795601d880f800c0740c03094070b00582c007451000300500041c3d5681c50034801d040600810305507025031541c942107204d50404201d1840708407100c03650403a0a04140c0300280b150810351201403060300c511410410f00c1d00101c1510710304089803a045603224403201d1103680da415008140c58404a150050208001c81503004000700b0201c0d900c0303100b00500c142c032a1074840038040014002185d1036004001242d8401240501e02c2e4440c0c140181061084d800d51458608200ea03085501546034000380150300d020158442c0c0c0a080401c01200b03507050482c964802c0c00340110007420300030090907030802c05020780d580600024040d41d04000040e621010504690701c5c00d822101001c601c00003249000d80007004840a95044028618602a540c201041600c910b4442924140d05c1c9420204521804011400d49 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 814229883 1250 814228633 814228643
    0x2010c0501200909070c050331060201140c0c0d0302250515150a0b0304020a150309020406080a1211030c03040b0c06160e01030207050c0604080106170a0309050d0f020409 75
    0x450785083c041c0141040050711072404d0004219080f000160300008a81441000045500030703500300d0100f20481351259100090401c1c031004006c03410325415071080c840b480840c07012030f01d41e440ea0000184a031080d0081c5480e69000010f80d002964040e030000d02070303d003002e2000c4411404804c2c0201000788000070864007500920595030700c08501c1130b000d0307410580c0b0410b51407468036014002860800c0d07600c100c03c2400c1c00440018150764441904100030200404000c10b40303116004000c009145802e0224030892078400085800200007480d40301c12030f400380701100800103600080d61302818824003040544810801d01040c000306002403c0100f2040f01100c1d10b4428105d400c03401c2100081c50b60361241c6440c9201d103101035114a00407803080c803c0c03c0050b03a411850500500300142c03006600e822203400100011312100540c4124102c1d56550036a000c030140c80004280c890396000805000240090700901551400071040058188035000300240009a58042402d0301e622840030380f0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 814231133 1250 814229883 814229887
    0xb070e060f0a0c050106061e030e07030209060f1e100503010f0902092103040f08160e1504090b0708090304082512112103190e0303030f15060703050702010c050120 72
    0x78130740b011004d901c0d40b130b6802e040c015482c428903103032fa540c40c103840041d10420031100800c14507210720785a007000c0d010240903c0032242e01122004d80309003500c1c07013150180e10242c409071b040c43d110380c050364140c41c05800c01101c800c1c034001711200a50410035003182e20110300070383c884e07a000141e240041008900c00c0656100c030f01d802d6581440c04115445035529401042c180c0115a640c0c1c00d412042d6090300c2c40c071070220f440e4119142e601c420502541d41e00140b40c01880024403284021051141040360354510f061b0b0b80700070f0000c1c1c5038041c0c2d01c00c3c903045a00400700c2c80c45460b072004540c03403d440511a113658113550703070500f00410780c2d400340d003940c500e038420794650000e0500302e401080f0302c515003e10104454210440c556a44111690b02d40046074883d00d01002c3d9101301805030005600800b01c90700d0b82890f800c00213041d030301130344e030001c40b118621072003c0d0504104040d41c1d104c54150712901e040075010703001924100d100c4101101c0655031a44d000503d81501d00810203401143c2480355 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 814232383 1250 814231133 814231157
    0x9032d05010606021219081504020a1d0103090f0809031f0b01171b030a3801020d0f030f0f020d0b0f030a111c06050c03040b070e060f0a0c05010606 65
    0x1a080055407010506407400401c981b400303691a410004c021024645000e4040341ea50824150300180401c505a503c00d000040548401e0f03030042c00003441c04414180d608405a503040150111000d40d03c0080c07848480d001e0b8140400d861002a0040d02001307400d42c2c0d101041c41b42c403080d80e000801083da0204d55248100b0045d541d00107940c03184041d05c0441c6500302d04080010381038021486407810708400b0004005042e200954003c40405000d0509011f0414180d2500704441311080310b0300030f45101c101c20078070540e6100040c0d00301e8003081521244a08204184100e0240c02c5002d03e103904552141881d0b00801c2d060304c010702980740828800201c000d24001001850700010840e1840b80d0700c01040ca102041c0904911080c0e114215403081d41114041d0300444030615060000c1c09561824040261442d0f2050003144181e2140030300502c0c0da40c1d5040261241080ba061068004000b40640030050461200404e00c2e4005800d00e103d180030f050343c5250035680250400710004079004c071b0f22 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 814233633 1250 814232383 814232387
    0x4420b070623180d021b010507060f0b1302120a0c0c020a081e0c060409020903070308070b0f16020a03052101090903080906091b0609042a0c0309032d05010606 70
    0x5407030b40c2c0f41503010300180146000000d40e2410742d01c0c1c131143c404001019084850b030040084a04a5901c884144101726890340c9120041c03455100050041c4e020b99900040c00f00b0910840d440d610000403944615213502804400401019805c0814464065942e1000d6611403070100b000303001080042c81031003038410708000d800310f2411040c07925501c800b48904c4d4580e900700981302516490400113072101070410010f890100350383c0c00a041d05c1800140d04040c00044802c091141d030003011900c4440d161004003040c86000b8119210040e045505c0c0207000a109000805040e28a0f090304040c182000d50f1062588030280c2c030500015548003080e6003096000301440383e0010050007d0070b00fa203020540c90351203200c0c40300040c8540c030070040b0504641d550401952400d200103081000408402c1034900d02601100f410b03210000300150034001c11921490900208a515554071807000b89199100c13022507000b42005d02c075803001c050320745400903103910760300f52124020f100100e0500d01d00300c80 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 814234883 1250 814233633 814233661
    0x140d0509160f05060306060712091505091809011506030203220b0a05280f060503070b0d0e0a06020a02071a07030f050c070504420b070623 61
    0x14010307882070849000c0012250ba150120300300d0354103a8a060b81c9036940d03000030320288218400100314081420b4043c24260f4080b440406507041c01080c264181e1300464140d0b05406580f20403948030000400c030342525000c4ca941d8581014601001089903030a1102d0303e44c44a01316041507000a601204218240d04401c4109445143c658002e00305003078640c807100341000000344071484481c0c030344010030480c0003908518581d5070190200d4240390804941550050058842c101c035415042ca0030116a03403802041000c01c50b1560540300e843d03c00140b0220028050072042402c560144200450102d492800103000300010f0b54040d0410358109035049420a00280f80207018840c03d2202900281e00b00082520b24807890400036290840814007a01e03200d0b040c0c11441d0440c0c1400b240000b2070003400ca200701c4094080c501a541d000700e41d1054400e04d1200710f41407151083d045020011f5264540c0100764203406214081140d01d00c541346a2115052940d50049440301c01d010030a003d401c140c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 814236133 1250 814234883 814234903
    0x5030706170f0112081c1103010303030e0d05042d030b0603060a1e0216021801060228030c02180108070303030501050f0f090702070f2301021219140d0509 68
    0x140c00740194180307440100103e511141c001c21780d000002d00800040c45800e12408800c1041c0d10a0106415074072210040ea0020b12084020900700821400000c5002c83d0700251005190798540c205881c140900741010b407e20214010014036041408040c2007921200e00518012000c42e826810440240f604d0810000c20780d00300c00d40b03010000a00f00325070311070342c0800c0c580c04880035880b00c928080082040000e40e000035400110390042d605d02c480d81c01d003814101c4800380c00340d88903010135940111180c4165420404030f0140b03941a4000680544840c41500e40050124007146804124503110b1340d80a801c10f00b000d40c0036000401c1055850300074180500360960720360303054852501c0890300c9100404c450912610610000a51292003044003030020142c0705d040d051480da40b80c1c0b100382200001404240021012440044076500004405c851000140500b51402e29070180d21032041d10b5046040301040000840c0c0d0303c460380d40301d01416502c0b00b5200700117647c1c100300b400b09180110b096 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 814237383 1250 814236133 814236151
    0xc0601061e020c010e060c010e160503161502010204080a080c060a06030b0f0c0c0a1b05010905010507120203070807120305011710020304110a06210213060e0103060503070617 77
    0x201d6030400d41903002c40d00c245403020a00304814102c0105001804e140039180742c054580d0b01e0f111074a180040c000518403d0319400c0c50f646d2400e00d89900c181615024107148444003034403504010403142d40c01d217010100d100b0903440010305068460f030446080c8040b09005849009011800f031488a07800e110284e088241c8507000c201c201c0c990758640840c0d0b03000170443d0b4090fa40080c0028004400141110f00c09290f0200f520040d11443c130f00403218000d4000e40c01c19002565030041010b50007000001d007a580161075042c1819035682d160101800328243c010b00b180014420b14000481130005004460b100e0756074110711020240303009048480580c0101184602081c030940b0307a04001c1010601d000e40c0c640c001d43d0301d5560f410a041e00480150100350030001040000602680c811104020360034482071900d00c0802d034501000990003449211075042c40e14040401009005040200c00c2d000b040c1404507400390348000090800c0c281d9400030340429078540b240700b502c1c00880300352640302800c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 814238633 1250 814237383 814237427
    0x31e0c06070810030210030f150e01090b0918011b09151e110a0b090f0601140a091d0601030c05040f0213050108040c120f0b07033308030c060106 64
    0x1042201e0810307841e07200c003900901c04007030086c0005110390803517030440486110603c8201040750203114412070b544520140d10b108a0004602042d02d8040c0688003c002800319280d034840f901991540d00d40080c01800070340d680c3c408400700701c9008012031580300c0340e41c5498943c0c915008260030a40d9070401d07141c003000f80d80b00712081c0d80c0860000050a2011b2032030603c1007940807c020a25040302d00d000074044035503801c10032516100014030807981021500c187c03503041c0d81e100d45031b00690300d4403107246a0001210f802444a085141d0150f5203e10a103441100c03200442c0526070304064080c0c1041d54101158070b010320041c113103401140403501c2c1000342186021000404550580d0072401036504010804010070148625213042c1005005680c1c0c844104450a01e40f41a8101281508072040c1043e1400122003d0191040126281181c46a14542150704a50503100744009058400000f4406030120ba0f004042000c1c01d03016813444020074055042602c050b0115245007403400b036001072 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 814239883 1250 814238633 814238641
    0x5040b0403033905120901062d1a16050a140a0209012108040f092009010c0203030d09030806030c060c070e0402180f060109050a0f05090603031e0c060708 68
    0x4a0200a030440c0100ca0744005070b000221001c840300e100d4801c05c400c2c409000d40c18003ca401040d4801c100726043e0300d4a00c451a1885070b110f2000b4641c0e0814030568090840c410000d54020314550041203402074041c40c03500b10580c4005c0ca40c1d00780440150366561186082904010441302200c0b0f514820400030b000501c110303400030710075282c14000c6620740010301c50f80c1d015445905000012041e84101016191034a900100981c941c440c070030001d9150611840c0c240ea00119042480510181c02e0709a26201100d001910b10202d04a400c0740c16200070400b140503001c2a205040456100c0da84a408504101c4201480c0c40c0880c2540e03403055000300424030b02000001080f00494850110b81d80386a603850001a10007410061022903610750001000307442d00807050100c0c45000700b6203a026249407603600740944180c05005003502880740d84d80502c6940b03040c1104652060300202144e2602c0b086520811090b0000300094540341c0d00490010070180052100641c010f0303203864040010303d4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 814241133 1250 814239883 814239941
    0x1a060103020f25050322050108060a09200408070305010e0c0d142a10020c24090a0803090306151c0201180e06030c0108040b0c031905040b040303 64
    0x100710502c48103251041c83c807002c8030690000300103000c00c0d0404244c0707840c0d06000c0c3c10040002da01c03001807110b4a800c3c1d0703000714056015011042c01600e02030500342c10380741484d030741800070318103850f100c4c0318100c10301c030060f1030070842400901c040d0140304003074080149913142c10350a40b40b031030010007203e070455808a9241e072120303800d803004642c2007403041010041c10b104540c100498403e6420780c0e0180820310500c041a100ca00c561151004c0e2900c10105001d81340c1241c403808a44200369100403081c40603412400031070000803070110a61890351070241e002c0001502c220340f07036000707001981001c600ac1100e4582480800e5120300e041190302602c84600d4001a1801d01801d2000d40310422503801c4800e59100303c80003000b002c003424030f00f21000d8441c0d100c03244254007250454402c1c446d100c0d0703420711544921079403401240d010409803115140c2c2c04c108103882d040201100c100724040d086035500240c0d1402414085d42c0102c10115182c10641401400e03540e005407150301c4120801c815402481d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 814242383 1250 814241133 814241137
    0x10e0303040509060427080702010e010c1203050603120d05010f170607050d0e010c02070f080114010b03040f050709090605010b030f0f041103120408160608010b07030302090405041a060103020f 85
    0x4100c1e03000031101243c490071040d0030020170a5450b44031b68800120100304400c4014521030303000743c03a0140440c22240c0111160800608014030074510341c1800c182c030b140242c002940042000341a00d494025004d003900140d00a00d018026107600c600040240607110000032000c1c1c62000740c48004c1d4502c0404090341c1d070720080c0c0010b042100000c0c048080704813645c480c8054483d504024440b812504400961f100a00d00400720020310000000405840500c60080c04a5002c02443d20582c03900d01160441d030001403081c2d800c40c0d2407100c12800544107000c0c0001801940500003090070281c144a01143d10580019010a05c100280459103070443c01d841d6100c030442c20841c84c030b540d84d032a02c00712035030ba000390080e054400d03e40c2d0118150689809002030301c5c4410304030348482010394a580702455007072140f032001c910303880700601c600e503603080080031518045d04000d0300d0b18014901140031900304071070540754041c00c00c0040101d400240169a0000320920f015410f0090301c51070a21030f4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 814243633 1250 814242383 814242391
    0xe060402011e05042c070f2709050702030307030c0203040f03061d010614031506010f0503100812032d0a180506183309101505010e0303040509 63
    0x8402c0400c01803107042d00c00c004440141c0300003284c0794072041d07140c000303801502c0d4412a0b407007030244000005007020340711b00f00b0724000a1155843d8106c01840480e0ba6a100034420305482000410403804150803100c0c2c0241c602a00e40343c2e004640d40d10709806c00074100c038030500c9290210342040100308101c10140d2141d506598104500140b035076802c0004142c0c140740d01c0c480b1803444d400e0240001c0c0501c905408915050780a805440820102108600d40c40350116800c0d0f02003810700050903103591280c0d0145031301c000800005060551149181480c01c15002e0010f04110300000411101c41c10000c5107260010448070302c440c02c100607031540c17176035000d00a0101400c035076038030012124110f6003582c2003862070f000400ea58640c00c06241c650044c02135049441d8061040343d2504c0880c1c541c11061308020f0304000c01218421000c0c41d210040c0f104050910b003414031692842001d050014496102595002c0d1394a203a0285004005003050030f51100e01d0b4403c1d00240010051034940015042d40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 814244883 1250 814243633 814243667
    0x50909070815092a03070303050d0b0925050705030c16050907080109020d0908040902040e0c0715090804080d090f080f0309120316030e1f0c14010b030f0601090e06040201 75
    0x2280a04800090551300a0b0007241d00d8469000e0020505410800030440071400440c180078964a803018170000440650b42d0300000c03100013001901503682c0415204410340645412450301205850b0b503444c6400a00885150350407080c892aaa81115100040204003d6a00b43d6240c640000f000d41100e005200f8428415000114680c0302106580f1a410035a40b005850303864a031030720900c4000350001d010390755010a2400208152641b50f1003507582090b801410508510b50510b4028064502000101c62040b4180300210360810140091200020159510740700c4074035204500c40e0441d0a607019602541103060307480407266021003164400702c000d60302080040c40070f203101813a40c400c400d00005007200f0883c01c6010190300103128004010112030155014442c5894031900c408049400000300300c085410400040c03440b01d0300034031380000c00c00010b044e11100d03021a040c030200703001c00c50740c1c1d8200b8401401104047d00c00d00d08280c0c1c0c0840142000d290a030b00103850000a130145100e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 814246133 1250 814244883 814244923
    0xa0221070503072109050c1c050a12120203070c0203281113050c070614130b04060b04020f0904050907030c06081f03060e0c18060d06020405090907081509 68
    0x100242c0710113050164102400e00300301814850910b40e8031540329200075445040403125950345804c200c50800a2a50068003601d00e03c83e03e40d8be20800c00d0804603800c0c080c4074003104030101103450b07407020714031994050711444103140c254070400d41080c2442c24140c18504d14102825108140110304030303401da034018100c1c1030002541001403512200400e94503c8a0305001c100302c4035848480c003601c2c0061269030140000714140c3e0103440340f00d10403255038540311040f03854400450700800c100e540043c014a40024040040d4000c2800da2784034001e0782400380e200241c0c07542242003e1080b1540082c41c8400b0300041400c42d55000080403803880303094100b140940214100c5440304038000b42420000c0b40640c4015a24689480581840881d07081349000d00e090240c514101810850141d0001e0f411515007561600104420b50300c0800054462079130901001c1001e8450002160244018500408655107040700c0d44e86440094004c0d085000420f00c103002f4060800228240312940d4a0a280 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 814247383 1250 814246133 814246157
    0x312050f24040e060106021624030c031b030b01090e01050a060503091e07060815310908030a0e070b160f02030d03060f170a08090303070b0a022107050307 68
    0x1801a01d94500c3c50500f902621000103840f540000340504d42088041580040039501e0a00301408100d244200c0410300c5101d0300b03481054803a40c0004031882d11400c0c0016a6861098607100c1c1c510b200741c0f5500829562510502c8079a000445940142502c9000c4201c0d50b04100108036805040c0c880d50042c0a40031002c80e0400800340100303a2141c42000e0000b60701c0b06801c144550702c84003807168030080307208400800c20134490b9010703d491041c000382c405001e400c01608110749488041840b400001c02803041184041c266001e000d4180740503841094407030600d0300c1420110b070f100e000c030801580c1c810b440c00c1048000b00b00c26950030101441c5282d4041d1850700b48401ca0b0040341e20025450300403400c480710115016401342060300d58203e49001d00e2510341440030609110383c07200d5023403944501801d1000840c00130007045120340c0039094909111035580e0300e52041000780c13918044030fa0041504110201144034075244aa00001007811b2400c00134005407680c44050680b00c01c01810704174003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 814248633 1250 814247383 814247389
    0x18080a12030e0609010204031e120c1b0f03020a090605090a0f060513020a0305071409060f040f0f030b130f0b04031e26010305030f030703060302030a0312050f24 71
    0x5030407401e42d46010388074240741c414602d5000754054041103c04d08016206900d540000401c00c0d01c510ba0321060046240044203c1501c98000766035084074140b601d01c0c4014040540c8400000052000d10000380ca80ba00b035204002c1c07014441d811190004e89003400412235031351402107468102da003001001801d03c0c001c00000001d04082e4110640103162040441014641c6500030289611541d80420031502c03080385c11038401d520016040d14130304017070000850078a41034006102003508880240e03d010f0b500c00d40891356400c3da9005140d0065000c0c010414094400f285039405010401176024210482e594180314140402002d09407600400003e4105802031030351a030f0401d41c9900340c40504450040007420000359000c11810210005207a441982c02d40140d0b60680380e100010790700b130840c06409801c0940004020000300b42d00d9540c00000340e1002c1c4465500c4a01a40c0c859443c101c080010310140c60000c0d2210000700b00c45400c00c4a86182ea0200c6400c070341800c441012581002800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 814249883 1250 814248633 814248641
    0xc290a1422061706090c0d0f0b04090f0323191803060b030c0102011a010f20030d0501060c1122020301080319050f301618080a1203 58
    0x2000707003001c0721440c081500c680208680400c1d88101140d401d003a519002800f00e0298165040d1003040703014401c440b0640307219084403c6021742603600003600c402c10320001c0d045e10741101d000d56502c039150b0000010300d03a00503c1344a100701d1558100b80e4a81c84524103c8a501c100384030390311071886515034001e0491280300030f031510000c034aa02c9080300b034480c10118020140d03400c400c0d00c80d00c190041040554018065039180e02949110304c000724003441c00540c2c40402c0025002d04120508400700c000388d80c061100303030308075000000964076100680c0c02101281c2d01a0401e10a0020b090340580003d04450050ad186135019240c40e5181401040082038200f181d9400842f040c0c00400040f62500000028241d02e244410206601d086a80c0301900c840c8583d11032022000701c01c00030394180c4e880781c00c21405003100ca07048045000a08024a502006013500e80c6848192501c203450580c907030042c9000b400424980010411500e418003480e40c0f14000c0400a0034500040b07225680d0f2070103944 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 814251133 1250 814249883 814249927
    0xc0203180f04110a030e1c02060c09180a0f0b010309080d110d02040b09030c0415290c01050f1005210307020301020f070308010e060603010e130c290a14 67
    0x1c0e843e21041c044c0b01c094042c01101b41100701611600ca00c11101c2e00c1c1d500003c41c450300c51a0090521070700c6900c18401c0680c08184240e4201458000260a400e55038004521910300c1c5c400015041e01503a02c19410f80d294000440c2c1098100011140071903040c0c802c03174249420f59100084c41c9078080e503500e0860301501c00c10507000d81c030109000607049904002025240021004ea60540e4000d900300001c54110322031103019142c09510600c4480072056010100b0310070702d1220140c4c14002e0200800c507a02000d01c05013243d440b0401e114000340102074244d00000400b051000c113601f0100440c000383d010f0205003081c61110a407141a0340b20600403a00801c0d0040d001359502e907002811020316500010080300082c200100000d0f000f2018442d460007814014001460340c0d1828003411080784e80a403400c010079400d01240b50002e0b086161240040140c1400c7c4444201c03210382e45100005441e601c400512000c001419a03d540400f03010f00c15064410126111408000100002420300c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 814252383 1250 814251133 814251161
    0x90a060f0c021203120a1103040813150c0212070e0c070c0b0301030506010f060906140d0f0f1533020f1501090507020a020d060506010327060c0203180f04 68
    0x82d8001000c3d40480205851141103d24020a0301c60a5081084601400160040709070600c0800c0010301100300800d0b600d103815040c45a825201c4c114044820098a01c00f0041741d04030b080081142492404c0700c01090000010b0001240b03028483d01c80d45600610301e400c0304000040c00710402405180100c050100a40703031036200d41c2c49141c0395954800a00441040c0810030340001001c1d031041c040d01e4140e590b2552441e11001800303c0342c030141d4000b40d441400c2c1585a0040d1408910070344101c4450110041001c1084006000c1d940c4108200d604104076004118980c5e440c0781074940e05d0078030302c403ca4a544014038504000c0032800d285030703554000d005000300b0704a190f00700f0714020164140c0d18104410070030398036403c105030396880c54444000c0d04054954080404101e5550126900031410305011501c1181c17035187d905080810b844002544071000704031018444144203134200d50301c07640011450400000c0d40b1441c0030043c0c1c204c2d035109800d4000e111000d0340b500d07001541120014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 814253633 1250 814252383 814252399
    0x18030e0d06140901061a0405010f050421060506030d0813021f0c05010c0903020904030e1c21030e03070b06211506060a0905090c070c1d010b090a060f0c02 68
    0xa41c280d02002c60261400312041d800d20030080759540241302c5004052002d15440c502e002d00d400019141c004079140082d05100050000082d00b603820702c1205d80c604103100b00320707800c00f0861800d01d0032a00090701e85ca020b9407044490a43c882e40041900e600003c4011090304198041e1002030000c031441c2c0900c610282d07110301141c1219411000c800340c200e1180c0001c1c8426454044125040e542e148030113135101c80c03054040b40101c1d000d181c900b4003410005d030080140710900e040301c4030340c0303840d84100305c4403c01c1461351280440e08548543c0400c2c20245414890720400580403640c0b80103e4001500c10301210002c00c507642c0d0740100d041000c455032610700b185290b80c3c2c4030300c40e281c12a030582d0250103c412400102079140090881d00d8003019611020110350501c000d0080b00c9030020150002c0040c1003048001240d1b44055010042614002c240850000c0c5640e00c4103240c410f92085c110400300f0702659079140e1702c9503803c2058031700724601940301c2c43c044442144c2c0d40e001317084047c0d08141c007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 814254883 1250 814253633 814253651
    0xb060a05030907060c20010306080d0210050a0204050d0b070306050a14030f06070f0c0c03020d0b0610020307030c0b04081c230f040f140706051c18030e0d06 69
    0xc00654850004541502c500940d180303401c2d101740f240050024800b80100c6140c0c0c0b822500e01c441d0604840d018540060b1498585541c40e107814603400d200400b60b84400842004041c0741d02405522003403070f450560500d490700012446285102c10002c1c4101424030014810b03500c20343c0010002c0000506e0010490760304c2c41c080701062100200d41d8002d002c2d01d501042441c070700091b0a8007403007403503070f44121829a211084a5600e25510b085844c1d6014190000c0540d503a4108603074028000c8014020b2810100c0400c121400c4a69414066400a12405c0301094002c2c0c0c0d21030a09400001c1900c182d5214605045107118070403070710080c0e04008025200d417219030340c002020b843c8014054481685204118000240f0460b0030031280c0f03900400040c0081c40c08064002d01511034001c15441c0c000c2340e0145402d22080c1d400c01c4002500c0400c1c0c8900e5400921691b071140403040004000902511a46070703400700e145a009020700c02d400b100c001840e1100800103e415420890070040c040d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 814256133 1250 814254883 814254887
    0x12180607090609060f0c081806181c082b020a0207090b0f13020a0203250b0601031e0b060f210c0301060f14120711070b0a09090e010b060a 61
    0x601d07030040c01c0004040510209920b406201105008566511010110705a56407080300544c0007000311054900c1103c0c4036a15601c130035010f4016038170740030030f9024410100f1042c040554141190050100c40d86001c2c00041014001210400502c4011081e0319035800010310704521440070340150007a1000400d06900b40d4003090392026038000800c1445250000d10800c6040c0796921301c1c1c40c0e0f021240c001d0b080101840356004007091240c0b070044d01c4c185141840203e1000c08418445000c081ca500030070010050b07442c52040d031048007404c00f00040c01c178950303100500100820540c00d1040c0d44d1880050316a454500341c40d242000d500072659134210f2008104000500d00360740030f002030b50180100744c80c035140e203055074140c61051703030340e460f480c48800f02c2125408009441403810100c00c00a00000d1011075201601c91401502d8204240108242451418001d64443e40410340180079500e10654081040022280504004100031003060030081c0102002114181d0120000030300c1503450b5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 814257383 1250 814256133 814256147
    0x20a030908040b0c010b03030901090b09040f09050d03050105030613030f11120405010206060a05062d070305040302010e1f0e040f0c0e010f0c050c09090f060103081909030812180607 80
    0x4d8200070083c440745100b141455600d0040544031404520614801d210443d0702502424221500610128001241296241c11510818020b0703a480d0804002000241c4d0507004250050070103a0003000785141c60150800741500c404402003c0011403806050001e12070400c583d500c0c03001c2c03815140d1201001c0400c03601684144211805409440300151013440d18103000c1c0212100548082d24043c0141041d02d50b407452079659007090344440070040da045222501500000740f0070b071185076903076095000160064914044961062081403e02000b07240d000300120000117841c1030403003c1d01500d40014000d480e1040c0c07440303011454404170b1821564015510071005c0c00c280c03202c0310045003109040f280d000d100c0d18060903d52060b10309084c00c0c01d0031600207501036404401e94140d030844036401410410282d100740c0c0c1824000c9600c0744115a412200b40b001089418011043c0b4034543d00c061040c015a240745100c9000d035400902c10040c1d0440302c0d5a0800c2a0042d22043d14000320054010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 814258633 1250 814257383 814257397
    0x20d0f05061906080703050307240c0503060f061305041805010515010905190b07030905060711011407030c080a180f030302011a060d0c0302130905180a0b0a020a030908040b 76
    0x19030300741000013074003130380c04603561081d02d4011024628240c0e460312004034010f008890380018074411196a481800c0e82d208500d00140b0300e0b99000c0e07a9080c800100402c04450440f002d02c60f6004200d0b404542d1181c00c0f449003250410380b404505042071203055280d01c0a0048054003550030a81003001442c0005200c6c050014245c840054560b1608140302c004240303080503818908c0c0341407007484102080400381c844e07d882072a00c494510f1700d500c0810302ca500b02e07071400c0760648d500817103810a560304816451010001c072050725041007010b40740209a1b4100b0203010344041c0001689442c2030340710302d850420350b400180d244040266101d4183c840d0414503c81034005500e07015429032003041503482040c40c0c007802005981460400060800100f00c1c4260030f10a055007000054030f04000324410400614050b4000241e500c0d110102055510201d1130b41070558202001003c009000c07080c8090b0403041e0b03c80010703220442600c05030014035031480d0103400c0d1000802c0002c0c047d00000c00034404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 814259883 1250 814258633 814258681
    0x1505030105160516020a0302180603010c0f0c080904110406121401060e131b050408010605030309012a0f080c1e0309060a170c040e01060e010804020d0f0506 69
    0xd95502c8410194102426401400907008101e550481a034048189540c0c900042c24003c038103a8a0380000d11503110059800e1a00c0c030445c0401005290138442c45080d60301906200365920460280144000324250005207844000f043c140c0490700c1d1036021145014600c01d20640e16501d8a0002e0048540d0b0000d0700c070124103202c0c24940140b003881c00b40e07040705d8460f01e5241548401601f0859041c861246141305541e81e6103058078446040041060380001c1d07038541c103980d40e0611003000d00390380c503503040540243d0080190003090399001100014005d41e20200001314070448602d1001c00502aa000d00001030701d54465040c8402040140400c0c1500c0040301d80400c03070544603d9800d00c050500d529640c0082c0400426401c0402c010301100c140c0f413800f4a4043c040600c40240342d83c0c02e82c0c1016240801080510030811260030090140c1064100455042c40c98000280a07090041000380940d00075800c5401300030788040e01904aa50210a8440a18186455640a04003040e40d115 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 814261133 1250 814259883 814259891
    0x3100212071d0616200f0312030609090a061b0801120c030204240e06100206010b1c29090a02160b1f24030513030c0203030d15050301 59
    0x4240500b0000d030720031905007030040d00c2d498580104100c6401581000d02455400000c0c1c44c0050345440242c00038410b02021805010640410b00074582107640525000743c2c881c0010f243c5055014090302d5010300c040f12030b0303e4103560f40700d0054100605840e0040007141003442d660250003106040c40e8005440d561820901d81ea030b91076038480076008060140c8003180740d000520250910380c1192400c05103040c058011680c6d400720350324600b00c0c15441003058030070b82010300417546040360002c2e5503c00c0078801000079504050184d0f0080c420364140c03448120040308066103064040d08a2103252a03c6481100142c0d048000d8000c000c0c2075103480c601c20450140016800782240c400d844141840810398806200b2a9880824081c006029030002c080c0d001d8000d100c159440480340003901061040c1284605011851460300309481146020306080004000105042e8609032840c10f0f058542703400342e42e1450001c01d003584942c01103040302904144c0c3e65500171b070080f00e11204450069000f00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 814262383 1250 814261133 814261141
    0x80303150406180b0a0b0406030f1d0d0c0c03170304050c0910060c0c17100507080609040f1a010f05011101150b07060b030105101401110d11010b03100212 68
    0x1c01c075030580c000c2c90f980e98600740c0140100b00741c561107606003400250110f98055200c441c0e01169400c694030020009465541f00540d5050601610b0091001202c01c2c0007140344065140e80c403a50054008820031100c41e4403001481010640d031001507420030440c40c00e04c446402d0800c4c3da684200c4064031240700729a002c3d1250f0401c1040580300300161110000082d007803070341c01c498100b04500181d61510070000d0100718000c2807032185100858081c004c0880e0381a0707910440c01e883d0014401d4080c01014000c006040c2c0b940130300706520990000c005807202040c1c0c684050f4542441d0304a00481350500008111000039078030140550714242c841400e08100c281503903080c0e44020203956400c0940c01003c100c00710040d0003400500e0703c0ba840200300440d0400c0882d0840e00200c4100200610203d02000700340c1c8981011482e4441c2842d0108404c00c001c004281e9030600080707401c040040500c41b40422103002c6d80204000000181980d441c260005865806500054079550f01315240c00045 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 814263633 1250 814262383 814262389
    0x60f071a01031209060207151701060819110901030203040501180b1b0301080309120a0f08070204060602010e0a2904050a120908250308030f07020105070c0302030706050c0c0708030315 81
    0x44d811510168010001d00e800c1440344c030a0110f401c81c2c03900030710961600d0301e04d03050f9016074114041c1c105503840b8440c074540b00710700400f0846c05102c44249145051400e4580070810021107200620a00700940e50381c0746d918000e0700601064049459800e681400b9904020000c0070090140440c0d48503040da101191b100c0815901c020310800781c20754010400ca41082c140300c2900c2c0825007640007904d9814800c1d48a0303690000d545001200c0c54500007501104514041c820072001d07185a100802c4030704100d80e0000d60b142c1300501c002d4500449000600c4031200c0c580340b00a22120a03494020795070400303280440c0e0711f41c00c8080c00c8444030b503084040c90308144150354060880302c6034801428000c04580344d0580d030581510141c608883c004030080042042140118051081041048101c1c41e0a4034020300312074014201c00100248c282d281400701c0e5001094034041d54002500091903241d400e5100118800c58240b103105004107940055418008000356200d0701d80c4451021808158401b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 814264883 1250 814263633 814263647
    0x3090513060f030b040206041710060b040608070e0f04060603140105150304060e01110711010f020105151e1215071b03120f0f02090a0504090b010302060f071a010312 73
    0x144001c403030b1140400c1022401071a900c0da040350014007044c0c03520391100001c126503680c4c443c0c0c2e000c0c1750784500c0840381c1c3c1c64030600c00c0a0007041820480ba06140c103142004140c80400340441080100079441480d02d9510700ba0380042103c0300603c2001307181c0d6130710000380c05005500d64400c0f85020450001500707040054131000b1030711414106c1d9285580783d41d0780f00000c0102d482502c4040d941c4968048016400300001c04070305004400340d90100d440c000004040610b00554039003164100000c1c00f40d44414209000700845013151204941012115450036519080000300e0307110325800407011030718070301003290307142003015428000e081c3d514013034182d034410807100e444100008542e0001c00070034820034a58654a04004002c500220495102c0b01950f803c070041c8680c403540040c250400341740070020324004180a80f024460f001082d15000c010341e00510010b03000718000140c1100c4803c0b400100d03480f003980400d50802c0b003034619450a040310400d0008403850003290301c0e04080c05020380c46c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 814266133 1250 814264883 814264889
    0x301030b0736050909010c050d020702011232160c0303090209040308091513060209031e01020a030e0102120a110714010e25030b0606040e040309051306 67
    0xa4460015264410100ea850460480a040ca5a42c202c260300c0020300040c96030034400821880c03071000324184420404040310280c102440c42e17140c004c3c084081500101591a4a0459880140c4a031114001030710420725484c4840c200e54504203038440500e0003c3c1c004138100002e5003515a40710710031244c141500000384c0c3e500440a42c0035811402441c800c441484503244649030110f491000e6501003810b1500694085022030700003c00c005e10f9880c2005240b0401c0500c991020341420100c00540c00d05141d8403029104940010300c000712074404211140918011f03104580540c84440d090f14000d4100341c6440e80004c1c10144000541901402a5400302945299103600c0f41c8036000802e0040c03003400c2100c904110709000f440f0224146a00c43d10303094009800104001c0039102c807450805001070a80094100540a0a60f0b1003111251a0040c0c95000d0141c16070740e11100c002410a01070755004031103c1065104000800d030740304210302d0450300d003516441c004800694070801070b036a00340 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 814267383 1250 814266133 814266143
    0x2030f091c0e090c0c0607021b030d0c021207050901030f050d141c0b120c040c090b030103031206090c02160b03061507141c09060f12020307020c030d0f090b030103 72
    0x380c82c0c8116480e146103125086225202c40e00c1ca42030001030b40a00b480340c2155514056003042d50b01c03644a80c0700b03004070f450341c81741203010708464040000c0103450f0807180e07807010780240300c10b13070390700d105003000f00025809000004d024501d0f0751780d01e240c0071140c50350540d0b00f11811b0058445216040c1d001e00c012100380001440c017141858440440a2041052854200300c51521082c681007151074500c03d0f206042d0081e40500140955101440140ea804a0400e000c004244600b0407041508a0569064035071501d0000c60030079000e460000900506d03042503034241e14002e15441001d40010704014252507007054603155695415240041c3d000465966403c20b2402c1c081c0e24261003560000c00c0a64807030740d42c040c20b401200c0354591a105900c20007610700880c8030031141c0c41b80d400030050001020686040c1c480e0502c070913170082601d82030807282e800c01500480800c84942c000d01500002400242c02c07140c0044000d0f2004107901203886a84000c120012804249a08200c0491341030f65040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 814268633 1250 814267383 814267397
    0xa030213091704030b0105030d0c020607260d0c0c05190204200301060206243102030601030605180105010c080c01060605030a0f022a030d02030f091c 66
    0x19024003030400829408111080d0707452404400050500020140b40d07070038050155100e60031881c092403820b106820491081d80f0075140507401030350001008090715810380310203884500718500384800500c3c001c28444a1032540300c82e6410444010f014000e03400d00340301c090001d040031050607618402004000340c020f4004440385e10100b004051400d065510243c8006038040303c01240c2420542026401105041c00000403c4425810440c541d041b510800301008000302981040c08081011192640100c1d1301f0101d0034408000d44070303125200702d01c4202c0300d10000c851103980c000a500440b11580424a0b2200100d21401c10700003015107001c4035640c03404c0c2070f405e000041d103040d156100216809802004441e05181003030081e100103003010b8a43c9916401c1c9516001c1c1a1000610700340c00061060040112104500034120414400d42402000d012003d44080c0d0451060b190000209130002003444500d580c0e504c0e000d84a85503540a4071030304a4000c1d40300e0700815031942d1020000e064 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 814269883 1250 814268633 814268639
    0x4090207152a1803080405040b010807080a050a0207060e1006170714040902180f07030b030d080c0d56060d090305070b0603030a2a02030a14010f0203060a 68
    0x120500812051401c0d0070140d02c1c000c0d62145400b00a00f46800480b0804c2000c82d080043c6d040c540a4402102000d007003241542c584104010f1048400524103a002a101d202203001041250304907540f00340c1103002800000b20000143c2c2e911124109101510b614226001925840e072401b401d0003098040c0142114600e0444405d007030401c0d4030712040e40142d6640410300180e4620755081210910b20205003600e203007403580555070311402030454090504001100c0c0c0c40765400f040001c0c0d82e105a0504030043d40b1800c0241069004031070400c420589050354101ea01d08505e4605203003140c11142071350300d947c2c03607071075102c1001c611030880c1181007030007502c11650342d005c5400a9401c1402420580c1010342c44403100d8180c451071401a400b20304005400010b2080c43e0440b654851403c2d401546404041840242500040b51200d08607041602c01440a10080d0041c03081e05a001000c0b21103c40541c1441c3c2100c50036001c40c4001c562a0017128450510140241c0e4406c0320011b048044081c9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 814271133 1250 814269883 814269941
    0x50c180a12020f1801030c06020d020d090608270c0a1e0611030c0d0809010507090e060409030324080d030603020f060a111b0102070609050a140607080409020715 71
    0x4680c044180e400416001c120001c101c0104e0341c41d0085005036080840303a86482406820002a6803602046402030380100c00c0340b07174008500d541283e1090ad0864240e40e201c51816242242a40c444000804070043e00005103000050402410404444450f10a07076a8010b00c4541c0310540e481400b04003403050200a01c0780607850040c004440c120a8925208515041c01c0c104201c40c542a004100700c10184401010240b2899074171003a14241070910724105501d2401e0200010810303031259440750401410184a5040a5030a0109180c003500310000c00e80e0307080a081080c0100c40443c440c0c0f04a8001c0d0b00e200b070082d6001c4a801501034003d421046052103d10b80c006280e00382800f998091181e181c280421000b2200c49084000714500700c02c010009040c240c0e15481070003000401e01003401243d40e00e0350031038225920040b854000c00102c1c000300d00b25004540014000a00110f8002a801121340092480d6071103040b052118040903810281100c003901d0340018a10202001e07a10140 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 814272383 1250 814271133 814271149
    0x14130b030403050408150106032708090102010902040609090201020c09040809060a1b05010e0f0a0b18012301050a09060b0d0b03010f0c0c051011250204050c180a1202 73
    0x30b000380f60091801d62075494407032030f04051444404813a0502c00042000b2513241c0308110f5540c90040c1d000c0c46401142a1500c4025a001c1000d4035200c40003410b440c580c1e001f540a00710b801e0340500140507a603501c86901004140b1000c041c3d001d4000d1030001c4016281a603203191003240c1c401c0ca40d81c10080040c00344041c58024103464010b121071056030f003601d00000364408016510950008c5541100d4824031400d01d04148800115a441480c50200192920450a5002c444004043c1d4507004400195000d4054007005407020028a141e01c1c240049152107141601d60580d03004000030b9580034a90216903092150392081c05040c002c8942c002400c1d0014480c0100080002c80d842d40925005800c82c0c00c1e00c080100400c60103220881040014403248400184441d81044401403441071201540302d003050603000c480300308000c487c81800b030000700518980c015000f00400c0c1b9081d04802020390100e000c0e0f4500e50000c0000a0240c07406441140c01c1d2540321120480900d6035500f484050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 814273633 1250 814272383 814272391
    0x160b07080f0301030b040c0e0c0409050405031e0301080606010f0f180f0b070b06040515061e040f0303020f0105010302030d1b080a20060c03040f05010b0a080d14130b03 74
    0x211081010880207a181c001a50185010310411085801e142c0340c031102c0320740994864079003a211103042003481c98a1400361412074402c0304011407242d903549001400c41c13250b002e1580140b000440d4a0050a20010146040e1900070b001c882060300c07001c0c01500c840c008162580001014100300d41c0c3c415100380a4152031038094240707040701c283c8030240e0320740d200040d070010b01050074041140c40c180040e492010703070012420f8904000b5810700300c640c00440b40300300c400c141c01114001500110407001c540064200001000c645440c1e40d01c0d08042d004540d8107200550051244c110200080b81041c0f145504907035004004080000c4002800d507142c0302924800394102c0340e45440440403c071540c9c0101500c41041c0ea5160b030b0800f807803002400745134440303030704021030b50240c401c1140100c68442125001178214402c00420803070351425074098040a000c0c40c0d001000c42c0000290307403100040d0b031284904551641c1c0c40642c1c0410b003500150040000e14074050340c11715810094508814011500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 814274883 1250 814273633 814273643
    0x30f070e0c0a020f0d020c0f0405060a0e040503120f040c05040e07090f02040305032a060405060a18061404120509031c0207080706050c070e09030702130612030809010608160b07 78
    0x2003920131030b46904100003004800b01507089103886007070318074188403c40e08150040303404000604054011400010741806400103032000c01000c2000d002e810010340d4020088401c860030580380040308404115020740301100c0402d08007a01103041e24181c064420042c082c0401000301602d061198000f800380000301544240d820403002c004180148014000c80030107817211603052a101105c8a0007154500c40300c22141c0141d028440020008102c0381d403c82d440141c00304034809032000448010007400390007054249040002c080b00388074401494441c90044070803154899030800706071124411112440c2d8140c10a5a924490613000400f0040c001003a2040352181c64170380303051a15107072a640241c40070510100e002000c03002d003000558080e00083c2c010152504189540c03c1e5039000d6120003c2c41a03005511a20301c0c49441d42c00326000703044c40304480703000c0c0190b4100603200c0481a61840925400c00c84040382000000a00144450440c49041c442602d00308168865030041082150 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 814276133 1250 814274883 814274893
    0x6030a1b1704111f11070609050303160804050915090903030907051309060501230a060504090203310615030f02010c080f030403031d0607050412050307061109030f070e0c0a02 77
    0x310980300210307a110040429103038120400c0407410310601e0035101d41c0c0311f4420032036404c409006685000c002c1d117241e040c00c402c0740018140c0310301c0d100c5d00d5400349402c41c0790403046020400006400341449180603c0090b00c3e4100e0030380b64080c04a8032484110341e020703042d43c041c44c0b040046051403810100b80c004403920001e0412150395680054603c2a841000c4200d0416001e42c078403041c00440802c0e0607012254102024076010f0060098021449240340c0d40713601000040307071042c03c02003d54101801d03070100f64100144100b0140c1036009036030280c4070300345130030315901e078400000c0d210308c080e25000090600b2083d81503004462604894400300d5a0410034400c602034190003401841c01184aa2004140002c41c1880740c90031400720403204040c1c0d880001848000c07900802103a00391280f00e0100b00c04c107003141c281f49255102d0400000c020318540102a21110700010250420700c40840c00c1c1c5280c120980d0445994550074080c6070102c540b040c020403e1401840d004203a070802a0060311 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 814277383 1250 814276133 814276159
    0x302031207051905010903020601060c0507180f050103030f0e0405060a0506030c27151603032f0409110a05090f150c011a03030f07020405070e06030a1b170411 70
    0x2001c2040542c421215691203071228010150140658ac2c05081a4904104000019280d05030340d1a401c0c0300b20141902c20311342c0d10502c0300a07904000c5d00d10340207404c18002e42d40d40b8640242090076100102c030004043d251042d005240c1401341300d00480c401070a28041c40d08005c1003050302e40c03029083c81c04102d400c100d0303d007410a662154402014245160143c290f400710144034408880810a4110640403c01c1c00c1c40c00c1040882d01002a07014030340003035030540d5110314904500c1414008480d80c40a414030700b80100790640280309603651510b05101c00103c90800c40000c2c0100d1510318040780c018480340c011400d01c1b54001d804200c0081104c00c40100c010104540c43d4411104908507035103a030781c040105540d00c58008d51000302900214034011105200c285607004207040240301d691140c0c0490842c03881000f241d040048010082e5a407404c0003030200c40105400b45032159081085240c0c22002c60080e07030300303061080709110b00007696a03c81e40c03440301c0004000c0c2400c1c4c0c0900300701421 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 814278633 1250 814277383 814277413
    0xb06190c140601240c1101090812031602060403023d090209160c03031d010c110c0307030c03061e020a05091809030708031312031e06030203120705 65
    0x2001c0454001400740c555541401500503800700d00000f8140114240c5041e05001d562000451409580042c4038006400704840104d40038a00c6500111103403059010300000740030000c000f1400b80d590881c0780501142007480680c0ca42c6001c5070003801503000030030050154110000c601215000b440f508611002241140c0d0842c5070108040b01056981c07440c15104604098610503002001032000303d900d04841d51001b802500003440050800d074a41203220502e080d00c091000e14041514001d03c086020ba01c001054110b072903107400c0140c86011600e6807030b400c2c0800d045055075009900c0441c80d03420354a54802512400f081c3c9180c0f0f0219490034414505d061003c0d03c00440d0075900c560b03454111100b04610113a2800300b00e0b5145030001c00b8800e00355000811108126801000309481e82c1e984035184581d1103a8440240c01d0b18030318100c1d80031056140d800041c1210f200c1182d2940021121280b00c2211030f1408001d41552242210f410b80032240400741141030b114204891340e0741801d02c84 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 814279883 1250 814278633 814278653
    0xc09080111033d060e1219030e03060117060115050a03020f160312140613150803040e04030306230f130e03090a0e100302040911030607020601050102060a0b06190c 72
    0xc003a83d02007109205100b0386500ca9152020014112201400e2140304d15519894101e80c03920300145451b401c0b0240d0405014814101d100380b002415581690703520700f810001440083da100c00319001e070600200e541070304498000400c1016a84503070401441540c154003d40c800d42d0302040302501402244900000c0e402da05020f18429500c1403a80c040e40030b8540141c0300c482e202041e0b1080807104102d49622800350380026091054004a200d4601002102c0c15259540203200580400030b4003242041d11000410b00991095a0812141b627885050041c2251001d261101e403c45071400c40d00c0c5450b00c50054441042c0c0207014047c0144110061021120a900c06001036000400c40c5001442d00201c51401005000c2c490b907198503001d0310712811488a8000244119569456a81440805d649042d040b02c2c002c0c0c225907160130102e0000e5500ca20034400c45005110b802c2c009800c504031030003aa01008805011103082140300032107602d806042c03111102c1000b2400700800c0103d801d8041c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 814281133 1250 814279883 814279981
    0xe060a062a0b07020c030f07050f0904110d030809150402032a03010c09080c0406030c0909031b03200705061c09022e0302040f33030c0908011103 64
    0xc0c24901c454201b030500b00502501c11010680064008010588515900601800044400d811039640303520f405002510752486071034000080c201c0a0080540010300079010b483c19100f00c07121680004581c007103207081140c00a4058000f06000005440c1c0c0300032690011030201284a04141c0d00e4004c2821209804d4528001585001040200c40d4041c440024248401c2e24180035150940d1200ea6481d202c0c0c2c450000980d507118030400501d0321a4401110840c82c980300d20f640013411f42801803620040503032458080356064200304502c00d002a0000446001815007410108805070701615044c4016042c62500e0b1074041d40c070f005a848502000801001c2070091007800d40d04211400704482c2c507004802030520410040c003010500e0940369003201c4900c1040382062040703003602c030b2241c00c07180240203207580650116400c282e09a00102c17042805503403860b2016076980c0a1501380d03940c0b41c481401d010b5040010a4240640b203079040c170340d50108642401042030a01c45030100400c841 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 814282383 1250 814281133 814281137
    0x140702210d0909020427180f022e0302180a0f03030210060311040e010b0409060b042901270305030901120902100e01090803070b010e060a062a0b07 65
    0x10060700e59960001a010003400010324114103141c203050310000d140c070580103000100004182c212805201d59003140021420707c108842100e581894080714500c08448206e10a03840c0c80c0c0d409480210842100b040450000c143c060f000a84030001d90003035000075980c1440240781120902c0c0d580314800361000030600c103600051900d15505000b400d151100c0840e012081c1000400c03c0420000d84072485101022031380090301d0040d44045c00e004109c030f250082d41081c1000030030002c1c0b003a140e2092804610548040c4030041e000c410f01d41e03500407011180040000e4003810610306500c0b40c219580030004071400700c0c28031090707900210703000c0a41ea8000c844990000402000550744401c01d0040c6848035041403108001075400207400100090a0900f08607124180c150141c6c81440200c000b004400141c0c0ea685000d401c00c240d03a10702c02d024401d4119440d00c04905d070741c01d1502480301280d289035100d07001c84602d036003800120b002c04006e1843c103504084400340815108504103000c1c600c02c2d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 814283633 1250 814282383 814282393
    0x2090405090609070501141218010c09051302091302090103090203060421110a030e04020f0a030506040b0603091005061f0e103609050705040609080303040314070221 73
    0x30304010301e444981c1c0c001d06c4c1006060040e2800411010b82540c050142c2078030035100640e50643e481da01d803c01256061195130034403801c00501a001004c020a0342c41c241d40c4c2200d020203004d0100160700c149040d07940c100303040c80e0bc00d01d040e01701c5a000c0e00c00c24105141c0481e01c100c45400003803030314006480903180140308113484440c007034043d4030170000441c2a0400b00c40000040420544070001018007400740221a0014080f96550303604540419010f00d8419480e1048000c00900528003100d080d4019407401407000400d15043c0d0542c0d210340c007100d0040001c1c548001c0ca400c054000030b8080ea40291640c02c8089180d1122805441c000c0d1666907500c41d07103103a01040090000d035072909041841600c840d0260800a403918540c0c4490a0341d5034214050320b188620681381c50f82e0f620010303900c0d01e00414041120751010041c81218061707600c650f5180e840d148159203c1c841524000d0100f80182c640e03942103068400503010076400241040020049140429108175008040304a039400c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 814284883 1250 814283633 814283641
    0x6010308040f0f05062203050f15100302030c1e091510030e031e19020115060518010c03030b120609300702150d091203090308011404020904050906 65
    0x807000310b03001445510056003c851414000c22218400c14a03100070041c4040c0b44020800c1c0000c041c00001c40d400340c1101c00104401b13260580b696186604c00e0125070f514804036000003d503800d40c030240e0360000d014201c5806503008005080034000072094001124650a00440d0340300b00e00580301d43c04540c010303170550001004218070302850044140c281441d100000300c0141c2d0000c11b4841307101400c070840000030029829401b6500075600c0c59802e07480e116042c9900d455040d0420410050505000c07414a51600c406403924024401130b24414041d8483d9403040d0b40c4504101c41d036180c000c0c100042c080c5120b2012070581d0712002100c1585a000707500b403001d003001c100720390340e10301c0e00a401e954509003080c1a8206420503a540d50b012148001c1440d4056585104d010700c000d810252005036120f00703d58582003c0e00200c5410350f51515107045081e800c2d4040c0c004c00156652659a20304a40e00700702c44121591b000300c8145802960074800d03810240c0302c80c491a809a507403000203006c2854 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 814286133 1250 814284883 814284899
    0x40308040e01080d080103110d02130609060503151501030e010212040c12050a0b0408090a15080f0f061e06160b090102040503060a240b0a090609050f040b030703050601030804 77
    0x10706a0110031180d200390300c648503540d40007103880c6c1520b51026801e1100c8051800140a500c80c00ca4041d510040e420013140340c039105540b000c005c4940070b14082c40116902c004140c0c5801c84400d4078030403005d41200088000e0100c0180200e4010705050004103080041007090890300040e404140702039820044c001031200d03441d034034070050100d5281c5804035100d640e035060701c8070a614801030a500c40000410208501a400d480310488003411003250256200140d03100d04d98071b644214041140e85001c5941040c89000c0e0600c40ca4a14142c1046901c1d80803c2c418400702070f04060005000100031442031303560350341c024100741c3c00050380c11101e17410900b418000e83c000500300c2812070384100802c06c40d980300030454a9100d40d0350138000400d41180280c02114040c0c1c140010b243c0c050501e008507540b1445009001001a11359503152403544032481965000b4081c050303594000044072402150b072606400c07601e424000681501d0001d035490340d803640341c01000e0300120341400c0045001e00c4050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 814287383 1250 814286133 814286159
    0xa1d1504120b09070503030f0f04030b160806090c03011707150905041505030a08160204050403030c080709051e150307020c011101050c0d2a030b040f0b0307120c080304030804 77
    0x8030fa02c0d0151003020300e0f04000903500c0c1f28100910302880c0000c02d2040c1ca02d00f20790151002150448000441c03441c1900003140715490702c840c01c0c008642240041510b0341070003c2030505c07078541c13451094a9a420500040c20143c0201c182406510400c000880c0380c840003504100c00c401e940d11242c50203801d20b001c0005407228107908440c0d1081005003008035690010350000801d40010a0940d1800642c0c038210f04000d4400000e50031604000c244010035a159021078003542043d502c20500f5282d40d01c00f112940d84038440d407a4001c1c0c1640c80b581070440c100382305108110008111041d1902c01003606900ca82007250010096086449003a6480d41c21210f012205040b14008100500c2c0606603800603001d0100422844c075a01c0c3c103401d400c44850411644e1070140b1540242444040c188010003a00700d071412540503e00380710000c201e42100340101e070b40e0b29100801a119036801d10030450a90900d480302039039030340310001000544860a1004001841c051010031340d03200d0902600180031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 814288633 1250 814287383 814287391
    0x110c100c02190203070e070203190914120703080f1b070f081203010b0d0f1802130b0306061507120e010f050406081b090a0f050a0603020a1d1504120b 66
    0x82d003441075002e001a600899403105031012289504401e440d40d04080b840d50003070b00324542000450507140f100e6203401450440850b14480c040709010070510091010f6070403101a90211035024003020700025019074060070428032190701c110b04000e050900b1640401d0a000001ea0582001c1d1040c00b02080c0c3c1030100000d002580010503511110308555004d9201c14070841c0440b91001c42c80394030700d0699410642140e003a084080c440d4905961002c248840c4000040b03101d1803222000c0c1c61441500e009038102c050005001d80705d640e0310801480010003588001201e0072608011030000200380240340c0842c2c00455031552003e5030054005030490404502040900c1418803040100d81d074401180b80d880398612000030a40350b05141a1310080c02a0001035910001b402d00100f0181502c403144130444030101e0b13203500183d588071402c1c0c04178801c0c40042000034070b030700031091195003035400013a40c403240103040107100c41c203502900740c0280c00c00e40220030482c0a10b0340300000d024044180c44c3d04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 814289883 1250 814288633 814288663
    0x11090301050c070c09110d05010806060306180d080a021b031b01021905090d06110c07050a0b0a18150e010210060e011215020301091409070e010504110c100c02 70
    0x5410034648407401c0403101c511541c101c080e11004010403e2210340300b515007007c43c1180c280300c5540c40d17548858645404039032481c007030b200b1900080c0d082c3c2ca5136403020b1300b0107000702c01420356441c8000c003c440a040c0100094030150b02040008070400c50300b50025450325002c4080d580341e0107010440c000076110380d18460f404c1e038018801250070f01c1c88004040c07614140750514a03514607050700070540d28030425170041d0405203011051040060803200070311011002405681e0119110010000c86071494021210950018081d19440b0741c0540d05a640c5095414840c2c503c1581d9115003403a82442000d480001031072101d0040d080c0d58041102004030306841409006413402d00841c110001c00501c240c444085d5181c0f408814007008440422100e40e83c24015513584da180c030802c001070410181101d03494410100012400709010035010b00343c40c11002c240c2d2150340b801e41000b028140d03407070025603005410052410b100500300b114000200d040700000c82c0342d03000034501074280b86203059a00c00b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 814291133 1250 814289883 814289887
    0xd060b0a02070303181805060f090a0b0a0504060e060616080c0d2c0108061c0b090f0f0705060d021c060e09010c02060c071e06050405010612051009031211090301050c 73
    0x401c560401401d0400800031b4002000d5907040c0020b4000400d1009013a006413004003406044103203138008010342c40095070902b03000c607500c800b03101c1241e4062007403040c404030203004102940380207001072204681148501c0038155041d22402941d5001c1c3c280007000350311101003466103030741112400e190b0710080c24100801caa206180b2a8541d90100046030400001c3c4000500c00d9444401c02c4080581290703c1d00325825061510b40442c2609440035903031482002d03180c0040840004c1c01c0c170691040341c13015015862501c0b090103203e40003050741a0303400b60280500301c800079040107249400c4580c400040380c25444e085220011980260000c1581d0b41000000c0320f40e1f83c3c0000703400d1b402204010b038040d0b803078840d404c08a08025400001c044021301c603041490500220750411030049014800802c95150b40d801e91006a6a03074035001401d03908030151112800b10580d20519040b8041d05045040694106400085904030032480700c99001c042008038075030500f441110703130009010801d14 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 814292383 1250 814291133 814291139
    0xf070f081e0423240408030f25050a11010c06020d0b0a0512121c0e060907090501030308070c0c090513050c0f012106080604030905120a170d060b0a0207030318 70
    0x84c0e4505024511220001118031148444050342e000301d800514440060f07035100d0031480803100c00341d400054005030350300c0d1071480b0441032104400620841d40e401001008606841c0c1d5031078210a141d10212418411040440383c0425610b00050420700e00c61040000d000d62a142045040300e100e81145018540300c00081f0000d15000400304001c150a1242c503465400c0240f4180040369002c59400060707082c09021001440001540d40c01101d60764262201e4940b40d454820840e40c01748009000600b01c0c4022071070b2507000d00c01c0400494010703130350010420344401e81c0b24140d41d8155443c064054403c0c0d03040c01032200c28000204c16600480c2c04d407660000100c0000d00000302c2c0b01141843c07000014070801c500509501006c0240742c080d081c3c034400d29041c20098421626445614050038000711000200440810302d00d101c5d03944215554130302d4803210141c0c50b0700c0c0c0140c550044e4280d65801d01041010f0540040c12407403546500518900d400e51400810100e0810f500381e014000380383e014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 814293633 1250 814292383 814292389
    0x40605061315211d01090b24192102130f020d0e06060406060207141011060a091703040f080a0c08040f031406010b0f03040f0b0423030f070f081e0423 66
    0x7e03504889084040c0c01d241306c80300c038081c043d0305900020b540d010740340943c02c4142001030302420040350ba81c060040100d60003007250b240440300380b510081d03200480000080c800202035000e00d2105101031001030501c81c04001c00400c65500408144140d40560100502458980194005400b1a2020b00041d40c6840b40506030458002d00140c4a407883c201c80313040044c0300700c4840c0c1940404400711101e07030406802490041100460565000040c071000403411542241200e00030399000300c030140c40c944203469011864014000e03803000c210754842c0d1407022803441c0b009007003c0d05001d00361032142c0f403841c600307800f0350541c82480b40000c0e008100104000200b01080c1c1d22001c160b640d0072540c980d07891a154070001c040900081c9074504620502c828000211040b000143d1401d132410001070080140715528060180443d010076020086440000c1c03030074480c0d400b02e600c15102e00b0f080c503149800202c480750303814880d00c003001c0000c80c0c100321040d03012654007000218808980c0c0f045041c0d03808 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 814294883 1250 814293633 814293653
    0x2070813080f1b1003140c0307020705102f01060e0a0b0301060509010b0c1e010c0801050301051306150803070305030403020d0504050607030818011109040605061315211d0109 77
    0x460711a40c014130400300007a0107074003c21440f040950004403603280508070150140c100f611104010300c1041008a003034100b04044080ca03000c42e4684d40904210b82e503044502140c2090841100045190141c00e0301009010300400391080303013104000b924121502104884144c81624070a0303051801c100f0054444030384590655290100c13550341c8402201800745401c005280100d500e0101140c02000d20b01d0640c080e40e0070100e1651545861317640c4104240c00c0c0c98050b0ba104060038100860840000c09a601014603070588403d099011980c034241a03040d40c0142d81c0c240e0208400004000c00c040c7e0600c19001480d0007418400d041a0924002c54101e00444200400740140200840c0069a0344d00f23050407290341c8000280000c080a40c0748880341d400c01a001e0b801681414000b007082e28106095520945080c080c7d024441d2409030f20807401254900d4550502080391524420345400c100d4004140102c2240441c0103030b04004007047c002c3c1c568842d00c143d6450310613180009204010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 814296133 1250 814294883 814294933
    0x60904020a050d06091b03140f0c0f150a0c020a1706060603090120040911071703131401051806060d021009050d0b10120c1802070813080f 61
    0x194111416003e454060b00900401030041c02900080e0407102001d0064000d80080d42d2207010f403122440610791186680700a170080d002c03081c0d004510350340b01504010000c4080c0500003031140c0310050400b41c0c001c00d1948078a0004000800c40702d040c4042d0b08241c43c1100052041c454154007080d0103031201512204064000c61140d0000404038208030300c00d402c081c6403280407401442a017070490780d40d4509030384244280240d80303041508010410302c9544c16200d030305421200c540c04428102003402d035180d0009003a04000b1003040d1607800800d0780d102c007003141407040600000d030904101c02032505280c00d840c010086580130740100681a02d40c6546a003001e0741c195442e01090001c1582130701c038142160441380d045945c1c1d2120b4000d010f07044450501a12032640e0303002016031a00040280c210740d001e0302404030107056008001e40d544660f400549100901030060034030f000da5440c000d1640c0405000c40400e14001c1041c462024280200c0d942c07e2003507002001710005042c080703007401a4602d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 814297383 1250 814296133 814296139
    0xc0717030a0c0f02060c0a060f0e070e0711070b0a08010f05011b1410090c06080702121806161109060d061e020a170604050106080c0304140706020a0b060904020a05 72
    0x5520400c040212000f007140d5008010546600225100a50b41c1001c00c00c00d440b45420706490010300e41c00c40c400d2905d00807a550140881702d007071080100c0031140c06051502048080c02c80d009154a052004801034400718048940e510202d9200400c40a4181c2205421214485080010760782100030010002c01c550012050810703a8185080e084040c00300100071402481100c04200741c0c150b00840c2c1c01c0340305603811501c0c2038a94100f10303131103803003180c134203000d03034460800c101d03404000c1d802278003423070300c405900038020380049001c00c2c043c1e009240e01c06060b0600c5c036414400c00c10040d015100240d01540c04455600c0c020b4002040040c4803a03028294030341d681032441c480321010310300400c0380101100c151f594440184004104038100140780079a0300d10680030070920700e40707402464122891039031128082d88408609e80c000f5071000c1e10890700781c882044c041c40340d0300b02402010014500381d0043c1c1581e49603424201441e00d8000e14052251209004100061f501c56480009491050b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 814298633 1250 814297383 814297397
    0x9090b0603150d0606060c170a0e1c0203030f0301140306090d0e01050f031f0801050405060a0e0a0c06020609010b06090a1509080307080a0e3709050c0c0717030a 71
    0x40300800d45a8050103000b138482e5040001c042016600700f110040501c1c49400041d84901d82c01d00034221a0081340c43d0700000a40511004c1443c0c54034000c44a036801030a01102c4801c409a800245994030140e1990004100800104a0503528501240d0b800c0e0301a809400c9910340f0021403529401d41e1000c81091240e680c000ba2001e91050702501c0b8001c9140701c040e96281044140544200b03807079403d00d562001c00c031034003064140341030084a0007070f5409402410152905111000589141c48691410f03100300302844e004507c000001e4001016260003900e02030070024261400d503100e02c15102d000350010410060303d52a40c0ca500021115a4414940460803428088800110541c00070302240b00c00b182290601002c04020b102c030307001645484124440c80001d01103600301c0302c4156402020030004441c2c521882d84598100044084c50322400030740c458280004903141aa004040c3d041c001c00d131105c5000c410031498010b400d420560040881c600c04030305a5901c0b0310350000c0200640 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 814299883 1250 814298633 814298671
    0x120d03020f090a03140f151b0909040f170a0210050601090f080c0117010e070e030f0a03031b1404060f021009080d0f0e070e1305061609090b0603 64
    0x400d0059819420000300421070082c2e50381084001003c0d802c4035105c0342c0c06051035030039130070704006001080c2a2844c0e070314002c6c80d6510788108407002d03050f5000c4010b10305d00304030f900c0403962190120ba100c0c61003680345a034581054200040c400c09a403811110313100d400c100b9083d0702600002c00d40c49001c1e840301d01243c0307a52503500480c4c01003120380c01410107844d00c10340801d000700042202010320001381d0315010540c8400a01c0c2842000a10400202c00030b41000b080145100e0310009016080150849640d1082480c82c54548040310b0020f40000b43ea0381c05040c0803065840c10120030401c986040b140c602c580da204600e0078480d6100d4407092080c80c4400c142c445002b40000707012000303104000c2011080300d0400341800c2d8000c06ca900c600c00c0c035290f410107201e006485151aa004500000c1c03d0290601d80b614003845009080b0300d20507592140c0c40e000180d07003001b071135105120025010000045e18900a0940d60090304000001c3d420118040074541324002920383c851502440392030b070070032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 814301133 1250 814299883 814299907
    0x70506091c1e140c0316030b0a09021903050f0105060913050f160e0601030c02071802190309021804052119081e010b0307030b0a1809020906120d0302 66
    0xc0814424501448221010910000e490001095143d100580d180101460109502c560708110043c030b03078010f02081070004c603020800d0240c0c00380c285840041c41c58269000203528440d00866803100203c20402407003000000d0000d074014840c8617000f8405401d12000052800400504900c039440109000500b8864100300d801c140292517402c0e543d00c03007040c425840c10180c1602641109405c20400b0460b076520a00c46e0b5450f494285d40a400001d0600794a003001c0400e500b034540116409200fa110020103c02a1f98925540350f02d000910160510501907940c0c10b02c60741121880480042102080b030204001c0b5240f11442c840a45007100da41180c0c3e2140038049220117000281050041110b03007180d4010f01401d00da4440c0322740000c50f030f030003c0b40c0c0b000e09005131802400140082030203c0e000b40c0100f0700d0070500030a070404041d2100315694289000c00384141016841d40000810f41c2010780c80d10303402c50340c181c0304040c202c2400d1a080d507490715841e000c042015400a40c00340004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 814302383 1250 814301133 814301153
    0x807230d020607051c02010c030507050a090e1f1212111203130b0907030b09070b0d0906020f2221021009090c0203040305011401050a03110105040e0f09070506091c 72
    0x160441c0020307421171003010b10090007040840403110100b0302c2d200118150600940a90b080800d1543d109488141086010b600180000d4541400305d21040f0400303021441c94016078000d4170701c1c407140f42c05049103800d006070084180e18150050010b120906080000003258614001107450340702552500d07600c003020050402081c004e0600c10b03000c2c2c02c0c484c02c65400318210701201c0c061464001280c0f40c1c4420346448480510070b003100c4c40810041524200901e800422016000e010010f0403e481101a0721550307001044240d80d80703e060b44802000e5460f030b101c0700c002e00914441c102d012a40b01c0003c0c480040c40311400380c46845100c030300a565900c5003081d40080e020008080c07100010b424806945d0360847c1c0400c0b00c1550a0440307c1025040552089048440007080e50649a140d5101c0009100010f81ca19040010130030000c82c00341c400c40c114500800082d29056801d1800c4502c02d81010307015048541714000411407401d20782c0c2c540900e01c4400f02d02e114600030342c000c180382c880820 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 814303633 1250 814302383 814302403
    0x50901120b0c1b010f0e03031509060a03122d080f190c030c1d150c01060807120218010501020318040e0a08220501051e0c01060807230d02060705 64
    0x58400e00d0354422a2071064208014204000000b402601c14016500382c1fa80011103030a0a1400c2e00000c0041500d425401503170045006003901c40c01a0312511000a664448406480401d262952460140362802d01d25442107031002c0885013100e0911381d00600340350018010001a80d030358404189911080c2c200c80c401c9a6840000b0001054031043c081c02a00f00007050001141800044000d140720080903505c491030000c0c20342000d00c00300101c1808a4024400003085036585480c00b00b40c4c0c041c00c0020304013400440c0b409507403040701441000803200c54256101840c18030040100803603600002582c84141c0c07201c2e84c0e452244007010118000b8280e03000c40083c2c034070641140105001e155002041512003174110390703041d07104548507984841c800b0310450780044c42c200000e07035028440706c982801c24401c000341140317042c3c2444402402d49170a50045078564010000811408038070300c1548007507070036001e04101000c0c42140040c0d104043e28a019008140015811080082c144902d41070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 814304883 1250 814303633 814303657
    0x15090303080603190506011409010f0b160605010306060302090916090b041e0504060b060a08070c030923131e020a030b0324010617150f2107050901120b0c 68
    0x2d0072a1a0505c6662040c3c280700304020011040b00241d4541402c01c0064141d9003d0403584c00002d240003c911035030361058403107004000340340070110300140d601c0c0074080c002c0d4001e0f8008101903042d4010040c11043c0513000e481c40d5440f00d42001c0010041c0c1d9051022180c55820000f498150f100100f0040d001c1c00254104c2519000c12480c43c910031940614041c1c0d0084904010a0084800740802403003190603c3c1c0101c0c610b040001c51252003035500718161842440c08006441d566040c91401014011241c140b40d1618000d928207400d040390540b2040540f0a02070100340d400d4075041d00740440c0d00e0450511207130001000021540a074110007403091010f0110784241502101c0c10107214103240708100f850740c0007000000d1040c492010100b5030000d881854403175484080c00d804100c0d0001603850b070030851180c264000d5039164003e400803900c0d9402120450080d61000340d042c98547e400071403040040d00014000c103081d0480d05040c1d2988454264040d4842440550140c0030b07050000340 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 814306133 1250 814304883 814304923
    0x90604060512010b040501020a1b0b03090c041103130f0812011211040b01080f1003080a020a03120608060402060715060311190506090409030c050f0d080115090303080603 75
    0x600d450303101c0024042c0c4051054800010703601c0f68140c040034030031071003824010b911407013100000c14998600c0203908282010124001035a50342000d40d6504111840311050308840d00710100c50419020742e01d039011301c41c0151803030352605180308101c070300c1d071000040d1a0111014006c1c2c2001821021160712082480b5641342540c0d441103a0410500520004c03219428400088880c83c04d050003506007110058490040075a00d03808091782d25400113105841d1280b002a000001c90711800c0144800030319507000e0544906a800c01401c113403420801604003901d084410003038954040340c110f4101c0e41c111070715591007440d81080c544074841041c44590061500700000100421002030703d903d0b90042d51100c451091926410007803d00904c96103400590402814006107815031100482d07510900f00034800001c3c644a00e840c120482c5100780042e4088241011116001840c084c0101204101008420081400100250814440107081c07080f100081203495800380b20702460034140390000d070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 814307383 1250 814306133 814306139
    0x302032509020d140115110601030c0e040303020915041707030b0601140403050105090c01030c030b09010b160803040f05070b0c370b0708130c031e14010e06061e0d020105090604 78
    0x1c6ca0b060740d82c05100d002c02d20b141000340380c0720300c0421654101c07900248506141441c0030014001400010000c8040550800c00b00c1000d980b01c820004503103002400301520396080c000346030010b41034545000351035403004604000050704906801da0000342842c149120006e62102c1c40101d02858000130165401d1204004030200009480c0440781000d90b42404040c0b210358040d41100c400c41310850708211220300622502c4494030050003414040069441507403a1601d65041c15002580c0440c1c03200c00301050101840010407070000900040609030385404040c644880d51048903440140705000d003036a14142008030701150080038078104146075103d600d549040e03989600200e402c140400c0103d4040351890107a010000ca10b1070388071488000f4542181c445c02092482e141e200901d0301e817001c000c0d00c009100307803444101c051011400400c12164881940d030916000504c580e000341c0107110043d00040304840c00000d8141e0540d82e00d038003c0e0301400100c1d03480c4507001069030412030000d000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 814308633 1250 814307383 814307399
    0x31a1504051324051f140d020d06080c03190602070b0415050a1e020c030f0c241e040f02060a090512030f0406050307020304050d0c0302032509020d1401 67
    0x1c03145100451141004000c0c40566070f07010010103008040d0130036040000010700403c0b0b00200761060007581002c0da60450828402401a0711401004036855008201c0c00d00e03850550260001500d01007005d058140c80c40404a56107161070988000c2e45958008100706004181d4101d605080e041020f5000514003818441003890b441211700101601e08800102d44201511508002c0380108060b81c4001840320b0110b40a5006083d01c0c0034a40000c0042c1e4806030080030017015120300640140510b0b000824030001c034070a24016071101c075507900c003c00c40301c400e000f040940c00381e8050407425a15103490924950b5000078a034025005640060151601600060341108985040310300940318000d00880544034041c4500d42080314509100500c0a1405400030f590700c100c032072040b40d00b00340c2d590b0002080c0d41d01d03105007640c1c41c0024a20034419810144104c2c006403021040d040703a4801c0e100b20301c0504d80c2c01c43c4034009400340c0c040b400195490b03098020301c0c0c0c40c14000a941010756103c0e214 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 814309883 1250 814308633 814308641
    0x6130b0c0f160c140d080a1404121110020303130f06090506010b1306030908180111031317030a0f110312010305060703060602060c090d0212100b10031a15040513 71
    0x32800500c4d0f41c111040041d18140c9101000654098512418455401c4084c2d500e4640918417130000c0c2400e01000c039150156840d6400894060b45511155000340c0040c01000300c000b203c0801150420001c014140110260f0b240840303a00041e07811131440541080e10040c0120761005105d8000c1c07000001d483c1070203001600e04092581a00300940381c4e90303401903044500c2010010070303c02045c480d0900e02d06088005825100041c1029203628200c0260303103085038800c0800449075008203005100c034071250068000ea5030202d070025494000f6101014111400420200042044100c0d0743c81d042242442510340d020b071082c4002615507103d140264544d4012030390000000e2804400140781880082c989014091400b2038a140c00100001c0c02201140c07614240d03003040340c010001c480d01c00c00f00308200001c805008009107545070355080040c0d503114660b504d010542420781400c91002440381c5043e601e00300300c888034410703088042101400d000325881b45a000c007008230711444408076170300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 814311133 1250 814309883 814309889
    0xa0f050a0c11070501080a050603010902030709090318060c24090f0203120403080d020307230702092a0c0106170304080c0118062102160506130b0c0f160c 68
    0x181c0c07002e200003401c0c1c034941d03d0030140308542c0022007a6010820140301588455000800500040707503a0f2101c0d00400d192400b1a401071004660720003000c0e060641c094800702d031b0010000006c200181c03034444000d10345140744101a107400040800c444090300c9911112079140c0d0b40b80c1c4240f00001c12410031440700ea9400754240e01a0180401000f08070040e0300844081c1e2307500001e030742e060800010f45c0d40002c0d00014403071400c2c080c81c80c44140114048003840e49007132151041c40399880d41d05205225249101900c6804034006800b040000102c101c44450107000d545000310742c9841d01c86244030301400d580c0d8404010801100503900c5ca202010005001b515804401c45040c0c400315001101c0c403464060800c0150300300d0000074007482d4800c03003542d22210088805014440c0d01c070184903007241e000c0c246110071620b0a01000041210a10103e0b90005807100d1614200f5190f40300d22000800080100350f0714040018641032207040300742070f00c15140321403045481c901320f42d150503864980140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 814312383 1250 814311133 814311137
    0x9012004031a0c161a0f090d0c0809040c0c0213150e0c0a050c0a150e0106050103020309060f0603070b030106120f0b0d06020d0603050312041109010303090506030a0f050a0c 76
    0x20410366152110140700c1c0740125030b00039035945440c8401584808803003044d4000c0302d06403811400c09a5580d07040407642d0160784140f840071035604024564900d0715503003010000a00c01300d504000b000c5044c0c0b00035200100410b46000c101c5e901c005070b003142c4d200c0440800940c41600100b0700e11110300b0070307448401911301ca09412140c039606c0301105c00e0f5020341150804a13041c41081080251407051000e041002c142204551422009030740d00ca03215502c5201c0394107010781e200c0c05040222802d0051800904080c201149103050014119031120402021501d400c42e6100c0031910350745080185000502181901c95140c0d40c44003001045109072035035800206040001d48200480c003885038a0340000010010024000d81d545c0d124042d40145542700c1580b50303142c0c0c000010460600041ca0f050210407a1089140b07403034036141d903c5082c1001054050b01501005200098000e807001040d2002180c0050703c81c0c1d05c1680c0c0c0d0001d42a862081e000c464140824072039500480d07084041404603503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 814313633 1250 814312383 814312403
    0xb0c151302030f1603260706090506010b270307120602034507050d060f060609050d08030a1805060709050301020a0906051c0203091605040219080901200403 69
    0x7611483c1d0355681108030407015090725130820000070f205c110500080d00d0068542e40c3c80c903010300c040044690006c25091b544e09860300ea0400c01c1000500c07000d8050084c031500c0a09001d26482122003281d0190b04c0c0305803140258050800d5603404105000c014280e20340282c0008100d407a000001e034109481160001038030401c0410644105504101841031001460400c124007510700e11a0503281d501a900c517000e404d101081584031060301001d010300400d40468040040645101160f805038003010401040c2e2105000075524240c10349070f03258010800d80c0c0c82c0c0d180c44580000a04030090250300302c2e00c4810401080010208006101d074030307551141e1481c0359445060500341d100d0480c20100140c4004d00c20f11051b4000d5001d81a41d001d1034000c401d261640b204600e040380d200303480e800010380c00300d540c03225400d0260040da00a08420b440c2503060001064114210102c007031f0b04402072212450004001d624250700c00c002c1d40542524140b52010304d4508214240d01034007043e078080900d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 814314883 1250 814313633 814313653
    0x3100207030903110901050f010305070311190914030d120f29090402061b070b040b04170304060c083702100203100303230a1206140102070b0c15130203 67
    0xb01e15001c6c120303a0301400e40107040040d00011401403400401ca9418180d694020070440500c1341c024010750024140e5111682c42040d1001d860f92039254030945400d520600410300303948004c00c0011035480141004000032000071500f001400c1485000079080d0301c0d1051214804030707900b964894100a5110794182d1403007080070b121b8104021113002c5e4100130104801c0d0010442c3d00c2c01c41800c1010700341607604468480c0007070952503100358000e413040e14021500307010016039505190490811100214503241c138002c80901446000c4101400c3c1740c0e4041080b81400c4042c001994240c8420301c00384c40781011881907100d61f80032034440000148520b100b51104e00700c1900c02c0300d00540034030000c0c0e0007a621359a400c0b11009250341c0c110440d0340704488030180c0c101020010301407085580d1a00704002e2004140101220707400c0e40b00810024036080e1002039a40c0104500c03086c3d403074a0401030750700d400c1d1004403480e1100002d099540e0b15041010400361000d880701541c2c42a2085050706e0070f00c09 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 814316133 1250 814314883 814314889
    0x1903020a03080609060d021903060f020301030b0906160e01032301030308060105040b12090307020d03090515030c0d0507051c06051504240e09190e21090310020703090311 75
    0x4503036140d04200707051b80040c05490710300782c03200c80000320744a90034a41e6200e81e00c104c20ba0b0703140c00c85100071341d030003000510400104801040d03101030180700420361803519221046241940394510790030b00c08280c40d8810030713911a812480c0403035044200020211101300a02144480911013980001c403c103000c01c100b58842c40403502142c0c07172011f460b400d011001c1c010012200c00a003e10481c0e220803c002001a110f154001c4103050080d01c4d1510041e140006004082c0b807a1004038844200400420000711000c0040ea14108110345001555580785403041d07649100e005d50b2501c060002e0081c81141c20500d802140036284d0650f110041c40080e00d0781143c06000354001c00b184049030560700410158500c5002014103020710b001107c40c08480c000c10302d080c400b515100d8602601503140383d11903d2a01071010b00119100040c6070043c82c2100c0d00c00303a200200341300141c001c400221001d003690204509501c4542885d82190707a2803042c0f501410404003403004450718141e0a03040380c4185 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 814317383 1250 814316133 814316149
    0x30503070506070e01050d0e0106031b150c0305030a0c090e09100b060406050403031409100504050108241306080f1e0114011202041407120b0f0f01111903020a030806 73
    0x14040e1601c605002087c1d40038405048004000c0c000380d076880c400040030655007125924600003280394049045c1c100b506200d14002806560402d01c1000401c0d800001e521108907a07000780959000150300410040403200c4003a180d1000391000c50b13140c00e01801d8000803400800e0340c880707031a00b0441d400703c0005000450045201d83c0010030400d100030004240a11252050030445420007890420a01c0c00216100700c1076410000161021809012a58100c6c1000e40c110b503103000914100101083c90081c4000f00d495003074081c0441084180440d20140c1050015002c081c003610340b4440044c1e08190b44085008000c1d845000e036090310542d420303040c45506201c000c40c520140e1981c0c00c0c00c0c28007100010941080380c00969881c20540401500c0c407107a40189441d80d103008990911100c09801c0e0703010840c1d00c40c41105d5040f502660340d40c614032820000070007801c108918104c800c4905007420341000054003d12041582101015404250f0f07102d02442a12400d100e41c59103401d00078a0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 814318633 1250 814317383 814317407
    0xb150f0f060d1d0102040e010302041d072709121b03020d0f050c060f01031b050d120c02030a03090e010f4203020c1b06070b060406050a03050307050607 67
    0x1407002c210705842100240c1221009036180d0544020b81680e40e15400d08983c400d074052a10008400014411031406000d411442d03c555044800f1030262001351a031141d080780708400c05041d96848c071665035162142950352142d4600c000300911403407418107016a08203505075400003000d4001c0c202c810815850015010354040e80180030400c540d41e000d0301c8512656410310103211052201e01c2480508101452092006501004c2d80394510718004490b0521402c032980d10400c692428050b907120001052420368000402101800180606035880d41043c540607400d40107000d00c01081c10780140c0a00120745500055207103030782c0d0f101602d038881c01150050120b0022540011480da5454990344413003141c010131142050070880000101c00c0f101c1c030700c280000c00e0300410001e0340c0c0d01d824000566854440d64280d0180c208050005030f0034450054014018084080421a1138035075500042c05044082e00210f40541c6034104141c0d260400300e812612449100009400305200c0c240f21020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 814319883 1250 814318633 814318639
    0x10b0d08030a090f12110609120a08041502040f0e09210c010608010f1a0609210102160312230c280306030c060206010506030f06010c0b150f0f 63
    0x7141c079000303211005009054810348919141d00386030008991060703154000d60505032901d44014482030415410580000c3ca00001504400600441818458200d07903d100140c034000f001555546030105100021248444409102050200381100c44001c101e003a6041c031403204000d41d5071402100d0761002c0c22600380c0209100d1a181941011041303000d000800100320012072010b840e48a100d01716441c0469514015071240005c41c20054035008119042405440152407d2a05800310b448201c010404164504003400542e1044a0a5041d20320150b82f015081c5981c00b1f00c0c2c10000c0012045800c0e203038545141459101c072070010f88504035141000303000b00f8440c40c1d40310b44180d00c2c0d640000380191000440207034818940218078401010f40d48030b9880c0001e01ca41182000e402802044c0c0250342998000b41c0180107599600d002d89510071001d1a90003030b29076800300104c0f004c001803907006091258040510100018410f200749c04440e041d200a039510308060100704101100700a41e81e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 814321133 1250 814319883 814319887
    0x17061f0807090b06280f0c0c150908070801020414030607120f0f0908041e060203090409030e06030a050610020a11090a060b0f1c0902030319121d010b0d08 68
    0x2011116400ca9407020500904945c2000c101c6201c00c40340c0d400e144000301c44d08100442440d0400c0e0094003480c822200b42c035007400301d0103040d07585201700101c600070b6901e004e00c3c014828462071700c9140c0c07000c003500900e0b060b00c01c45540e44010714080d4000c6d02031542c91154108d0071500c10309000609600c103580b40d0783c5010300440381200314001054013103c00300c88951a40181c8258180038000c034040302c4e20640e45240c5d51454101900e07140c44605450b10310100240808121203036000040e50f15806007100c0000b11b9a0031440c0030b643d4201244035460f001000401082030200403a402148070b600241c6640800000401c0708a0b21075500b0a00185640d4000c9140790a600f81250425803150542c0c0d0000340241c1c84084103c1c46402c04180905000000581c1c02d13444200d80000340c607890182401804a00702c02da002940303034054004c41080d501b0019402c1d80505224039120207581145071010000b00c40400309140d20a0441c6400072125030034080741c04994100244032540c86134000a450b4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 814322383 1250 814321133 814321139
    0x12082b051806130c2c0618150105250311070602071a0d181407030f06020d1d010c0809061e2d0105090721020a050417061f0807 56
    0x14000a00d0f000043c1c400002d1079902080000051001e85407102c146075904085519802e007601114a0041400c0e0107181521043c1c00440f003000d100740d4101c3c4d050f0303510041c559a0326004907100c3c098800e0702d520302903c000d20f02c082c0c403202000204004d0f009a50340300c860480ca18489617249030314410f034401a8400d52040209401c1104003110b100b000250b1a8600031860810200742c42d0940c1c0013241002554440c042004034403080304103d46020800b41c80320b5441c58503011480d0b40625030140c0304580000b07042040348421f52103100c0743e40b941300384104100c06102810f07000f403943c1003041d00403a141d1400f2845954000901503c141c40f03070380001c80900c180340c81601440201510303050502c0d0f82c040c0710000e0141a03003807080e10403d540714401203640c9081d0030402d030404090b182c14244100c0041040c56400e10500101c5178420b40140565180d1004604441900c5242c4c45070740c0368010307210802840400800c15900a1001c4c5208014500c14100001000010f502c14040e01d40e010200c10 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 814323633 1250 814322383 814322401
    0x220b09360405210313031205360709050a150e0601120b240708030118050c120c0903070b0324100215190207050a050714060412082b051806 61
    0x1044944280f400840d901c0c00744071a18180c8006403103500c80540a400301e174082c0c441140c1c07e008503034100c227116450701089104207901d40c2e40340d0182c01040385d19000042c0b0038036001d401502c003000109404440c1d00c0e81d20000c0180f40501900c02c0c0c1d00042410024459041481c05031801c0e07420000c1c1300203503202410140c00c243c503807040308581c9820b1080c405a070105184c503000d1802018040500d008110b11004034008440f80113117082d9032000c0600a200d4035030790402c1c0340c65024603049000c542d034040160004e46440c1c0580c3c010001c02500101f04840000c2c07504110500c00b10700c402036100203030823000304010081c072088002c0040e03200c03600c02014181d81060007504405444a20300e0030b6400c0c0c6071000182d0344102025125540f01007a5182000000c0201e80000d009030f040c00000305081d400000c0711403080f4440d4409a400e45400c0c2c1c2c0a2041e48000c490b41014040c1c080300070312800120a00c075004111208040191600d4005000e0b14000d07405121103c0b110005814196900540 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 814324883 1250 814323633 814323661
    0x1603030806120a0c060e01140f0909150d0305090307060207080607080a020d09080912010b01050f030a020f070c0e1003080f0a02120f220b093604052103 67
    0x2c1a4194464003140d40080307055540102c014003007907079910064240c010009400c8040d810040c1c01108402c000c90f60409602c14152800800308564242c11900c901004042180d082812141d00490101004c402c05401030b004144020007a4255041d6690f0f441d000d07600da500d148150400c64101d080043e114074842c3c900c1c0303544215501c2d00141020b00d0030300950b0880d0a010012200c1d03040005000d2018030b041d6440b080002104002401304481480000748503018048078007c4041e000b1005c00c0c0e0b45400c0303030103070780e240c3c0300384000c8580390000381c280440700c480b5912130b001e42c64404502040350340307d850407104152601f00c6c250914001200340382100d65807040000104500841e05540b041e04107040c0104101c0082c804295111400840512030300112040d40030020324603000d0402400588001391030000400711061041b02441c032303480396185c05800081d440021210060720030303400d6511500178011030040084400d56443c8132480140303070f45a5540000d121000b8000140b040a030204 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 814326133 1250 814324883 814324909
    0x11060f01030807080c1b030f120a030b030c0310380f0f031f0b0603060d0b041506180608030304150b01050d050c0301081603080406030b010504080a030206091603030806 74
    0x1828914003000340f05d4090501518459200154062030f4030b0075070701d140c100180340004907448090405003d21003103181161103003001d101c041c907854042d6a0010b5800f4040d2007507601024056a00c001540d0382000020300741d40f00f866540b02c3c1303050000c0b84048034460b14000006800c1c100c81c0c0b46140d00c0701c1003102c01550480c070030b0340c0322078003084040c2103480034000c16011741c40d414240300c90900c030980340009840700a841503018071070030b10400c40030390395002741c45c49003036000704481c0100c1d142c1e82800e94120203c0c4800b0f80d0321078200b000010302901e03c01e00881c1c4290440070200800e0307484108141e140e00c0705480c06414804540d1305035484001d50b9000c13403e400b4050403c01c0c034000c40403c12006a81080f43e440ea0054000b000400c41c601091107240283d220050000c9800d0b800d603075032000d1a00490041804240e510a0030103000c0c0d00400458010307014280403a0400d5801d450000e40d03603a000c40c0c054001e030141c23220f0108201314140280c401c1e40e074513498141450f0f6841c414040000b201113 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 814327383 1250 814326133 814326143
    0xd0209151e031012061d0f0601050402180619030b010512310f0210050901140c0705040f0203060118080c040207050a080a0c1407240917070611060f01030807 69
    0x1400580142c600804c001107500c1340001280d9480340302c060451024100c40d140d100c0d41c00100c2c540d40e041d040410154150781d07088030010f171500301d41140b058241903400c5013b904803200080400100d42040d85071b20004c142e0340d034280a1b916603800110740b9400b546842030521600c0c8808101c2c0c40c0101001c0150140001a145042c3c5e880b079a01c00191020713504003542c0b5200c442c1400415410101480905204141840c0b40b078030441ca40001c124041030580303029114800300300c8401502c0c0c14804600100002002400800840400032000303500c01e81c0c0380c60224105900622030000015170810031284d40c080500030b1001d8138410f001c042d40c401c9100316114003401c2d06150000300c0c1000a00310b109984d94540100c188146000c0248a040ba901a130366680b14182c1084502013080414048074042540c048418050b072400ba00e2a40c881d4111801c405c180d00c0100c0340b00240003e0784001c032025551945140e008050000d82c503010141c91454003440c03040c0052020401c500b00401c0d06034814 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 814328633 1250 814327383 814327411
    0x6040b0d060f1e020c0d2d0512071d1917210c3c0c0f010c120305040f0b100504050f130201081b0d0209151e03 49
    0x55450400720360700c96071000c8029039520048040800071000300c2042c0d40c83e400046161a07890034449644554040c80700c4100a4010081c61030302e00c8400908038040d5600030b8601800c0c190020103441500030b15a60b40d031084103240011001e61056003400281c2d00c1441a4040b8030130070406100c2d01c8100d52200c41040310300120001035120b55008210759100303089000d00212180040f80111000b9844003201000c80180700106911001203280104e1040001114482e0a10301c01856044060302039500d1103403451010b401642c05010600440700c10301103810030025117961006442d0211507100240924a440e420710188034002e078850307a0454040e035034206c04036580356030300320001e0003c070303002c540c140a1030004000c64200b0b07000300c83c0c1104200c0603054051510100c10f48003403082c65400790410080b0004a80314400d505810303122259040607241c4e6540316090998003070760041c465513020703104188044440b200d001050f15122642804800c244e01030300d000d40510b9400140401000801c0307 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 814329883 1250 814328633 814328659
    0x10c0b01090e07170304060e0612130606120c08010c0216090b06040807140102011404020f1026010e06030f030a0e06040e0403030f151a0708160506040c15050306040b 73
    0x1050038110071104c00c040150368450500c60000c000010701c064081c000ca070240b00d24a480a5000342c20390b0720a018800070301800045007015805070016501480446488105210512081c00c072500143e0f80c10038000d0011b42e6800008a80c0e41180c0c0341c0100c1d03400301600d42480304580c00d4103c0c28003208024a039a0030562220b8040342000d01503030006d0b1802060341465200b550b028010603c2d62403544203c01e07035a00d49900450031070b1841c24101c5110b440c00841e681c0030300703000d0a5580c80b400c604008003034185850305002143c1036000e00961606c0c10b21500050388500c3c2c006441d00e01c07059a00e0145080c0403011506881d440740306600300781d00000a1002060a0040d10300003071003240296400320341500c403035804004030384240d8200410443c070150140989440040014016504481003d0f600c1105041c0078000b4021080201041581aa02344041c420b0004190340a03e01a04a1041c01c1da038608010041d101086400d0011034000c3c000111145419400f2045900000d071440801d509 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 814331133 1250 814329883 814329899
    0xe010e0301060807060807270e07020703081b0708030c071203090509040605150a03080313031223100e060607050a140d0f030204050d020d0203100501061706010c0b01090e07 76
    0x741900414000340c6c00c14100818a6449204000c4202c9805001c09449200210b2043c003064903009002d210030855011901c654030030820040259009001d8030780350100060700340e440d07032501c2c82010224841c01c400410071000c003000301c03111740c6002c80048c02e00c1031800c80f4091003800c20710416002c0c440c0d0300000050a4941e02c00307540c4901c7c8546e40010f00751400504040d0164000f04030b0600a041450302400000c0003001107a0704030b0b000d0440d51550141c00d280031101003913a081d0044155040c903000715a80404000241030352011901c1004a0341e40702070503081e080806204101c1c10008800201300107003042c000604501d07000c1c100f81c628800c4951100c17000a003104120070080c2d0310400402951070340c02001c000c4140114030341580b4141c98940000d5030401750140c064892110b10154030115a01040305030b01201400105202c42c1da9216800390000040f003c0c1031076040e50040008400303600c030b580501c09140d0300240e45d400e02c2c1d00300107141d001040c0c3c0c841c1d0080d083c8541000414650 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 814332383 1250 814331133 814331143
    0x90e0f010507020d351b041206110705060f0403120c0825210204030c080114060d030c12020f0a0803011815060e0d02040c0309120801060e010e03010608 67
    0x1c0c65a0000c0140313950f50500249622012440442511404520302c00010807030301c242941440603560002c20f80c0c5810314a800c40d0001001500c42c48040041c0c00603080c10850032510070f190140c01d00b0000201500901c2d11a4850110000e10b15040718000680b0503601c810032a800074000c0c6004c400e196180c12000f812581d241880c21f000ca4030810404c100500468001c41d2a000e2000c411084000b010744042c01012684c90b1020840ac002d074820841944607a049d40c00564002184120711503982800e43c0c001d01c00c0042808252080d0b200182c01410521451100c00364180e48000705120b0342e0303d960b000801c6500000003107000e42d00b66020f480004101d80b14802c1e01807115140c0da54034101020790441114641c140d841400d1002100c01d03d2075203d200e90031256141030041a440c0e1180001d102c0d03080c0c80341b000354007a00e400014814a94590320094055110305030002e6010350410701910490350900c00c4200086203401989481d5210348149191080050700100d01c96850313041c418100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 814333633 1250 814332383 814332391
    0x150203040f080f0705030d0525020607080d05070e0d0204050612010e031803160b0f0c070e0601020f0c060a03020c0a06020703180e090703031409031209040c0513090e0f0105 76
    0xa0b40c4043e444a00082e0306020900040208030000d2146202101000e071030b50288400c0090320142a2000400403981184c100c0c1e9403036070080c18aa541d5680c0d1070a29120307000a0100d00c4082e00c1c2c5400685400d008004819422400900036540704d5400e03820000580001010b0b0341e0004600300324401e600ca8240074003032400c0031181c05580c444401c1321844500d1108160700c41c4c4a41d014843d45c5482603131800c480b034281da000b188010f54030070301078402c13068a200795041c0003c10320550348001050003c4088490054801764250303181c4005000905503508090002964815000c22440c1074150084d401880e21541a2003a10042c03500364a64004907080303828280c020400b04071900069102c11035900d0b020b0641c5000c2e5201c18100804a6070b619021030000505100c030a00320a030021441c03030191000c2503c014101c8001801d01742c03000840e50040760740e00d07000c1da00340403050304002d01070b00590b43c5104441410103001840d0140c50f501030440d00c0c08564140c0600700445001041c2070181a1003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 814334883 1250 814333633 814333649
    0x2031b0601080d0e09061c1a071e020616020f243702041e06020106150e060d0605060a1e03020a02060a05090708030c062509150203040f 60
    0x480d890031940030306103d8070305048820030020018003a4250744000c099034200030300b030f100c002020f003000030210700c1000c5000018292100e4600e0f40c0600e803c00d400c21030b11030940b035501c0030080d0140182d0b122080d102c2c10074900c0507800410016240d5108507003003042c01d4009104842d032007540d02c41b130700b4100340c0300301302c0d99424200c594071540560b000002c8960700074a026180c009204544819001644c4a00c0b242540401d1040c02123983c100f6541c0669000c0c000c2e0b0421200100c0c0034082001880d00d8a1040c8400740d400c0200025429240c01c1ca024140906500c50780e04069010041003010b6003c502d1110070982e580002013859191a40035090810345e5403650010074031084165804030102045240402d40100b200d821400d501207100c9410400604001c2080c0d26000111070400d08241c10a04485c4004185510017050004c0c2450007010505d06c521002030949840c50100780f580210540860044007040024551100310024168440e205272800e280d02c4410420100c85180d2202d64 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 814336133 1250 814334883 814334893
    0x507120c090e070e1612021812010b100c06110a021e030f0729240907020a0b100f23041e1503050d0201050702060108060106050d02030702031b 63
    0x1107202a00c10029104400b41c01010281c0c50031044140050006000690a0000c00d1090892500408070240003002c46d02080d519480e154002000c20048017544e5849419610001c1e003566a044c800c0080c0f0384401307009110000c44149043d260751201c41011150590740e203080250452a18003c1c6c020071030107034043e00c1c23113846410002d09403960001d80743c61581c004200741c28100ca050004c0395041a8080388d003600981070303072880d02c0075120144489032400b02801c0c104011504080700b1f05981990a00811107101c1c40c2c1000d0100140e001ca4103100964800f0101001184503e020300b680070580d4415080511784a11a102440042c2d600c407a5000d82c0c00034610304025000c0c402c8034481e4800340c0d400c04c90b110a1a03000e004200155111f02069503440580c03140101100011902542d001b01c01c83d00ca42c140c1c0d2030020300900d4201c4114006024540c004a2104800700c0c03d54100e44407692503130306068502c84039000944c0050101015440108034161801140d68101e501d1403401401400d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 814337383 1250 814336133 814336139
    0x1030b1816170702072714010f0b0c2e140612011515171014030d2c030d03090b0106020d0912050c0a030f030e0d030203070f0507120c 59
    0x190280d0340364205488202c08620410400320741c000b0340c0700111043c1165075000f80c424803501c0b40c1d809500f241840b00b9517003450b003042c07450458503030128100c50784d4012480c034281e554410410240185079030518183c11208505216007039035070b06840c0c19000c682e22402502c00c0d6409000c04c88406113805208405801c08114041c6000c0d00c0d5008040f020318001e100404442d1a0390151710140e00a4080b0418248240c5000030300c03803c500302d9030100c1444440e1040c20b224039040c58445152240158404400d86100d1270b0382004110004a02c0641e03d0720307400c000ea00560f40c1100c07510415900642880c48010300c206640400103990206000d071400035000c81e090401c1104000141c02c00e0066502070789a1000c0c4c035a014034107804980c0c454400c82410802464410b0138030740d040d00c40e140c1c03003004044044144040c100c8144a003504c252078040c5c21040c41c3d020322240c50218480900035800078098040070900f0642c1003800d051154051740d51140d140d080000020008032015280035005c86803c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 814338633 1250 814337383 814337387
    0x1170703090b06010306080a0f0305040f0602060a0605010e09040b04112e030501051005130801111c090201050f032707050f0a0503030a05131511062401030b1816 71
    0x160700b0940a05c0d043c0300050800003410754074042e421000b0482c038840d00c54001490700c5041a207001c0e091041410000c196103400003503950405403107000340300d40741c6400018250700401c20281211406070030031700f80c0c3d41c81d0344411508060080c02650f0804500c000000c003951020202101e400440020408040400105440b180700b0103000b2000c1c90300d840c005000315600c2c03003510950700d4560701d08550740f16a0001807a4a8121a9000407120342c2451003420b29203001d10050080e03900c030340d1006061545812880401e4481d13014004c0e021950030080f040d880e003456001558094854000c0510398070504000010500b2a004619191b802042c010301192610243d081001c00007283e03102103072414040007075140c3c03142106240a111001940680d4000207a0000300100451a40c40362010305215002d4600800c50075600b03468011400081d5005c45460909030040d0728641c1001c0c1076a45243c015002000014641540581d5007003c2814911030ba44a43d440740ba5500d2881c10405120040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 814339883 1250 814338633 814338653
    0x603020304140d021b0609040c05030619060e012703060e161d06030708070303020607030c2c0105160c060809030c03070f020f091f1d0609060117070309 67
    0x2014060340000640f00040c640c006060540e407004d80c411400721003039410014006106903083c1a4200e07080082d0100ba003030300440a144181825660391035800918400201e541034140502000702d1786600d0181c0c400c3d48101100000c00030000c090070300c14112030008a54100e069170084407581d031200504c5540744000d21500c490180e50a80440c00d060400c40905091522210f07522403000c0e40c9000a903040c1c0e0100510001070a058040d151025240c0c14002d45404048900c140424100318030100480e01c40d10300264491040b40b08100d0003840741120f211101004406941082814005002003203420b03500c24084511a40c61070009038542000034044030001004c03854981c1060000c0c0003202d03c00b0046540031644005d48001002d401d20000342c10360300c4d1200c0f9507040441c0004005204041d403c84c02680004002442c510ba9a40c3c0243d21806920f22080000e1186502c0032074401d0030440b40064000c2014109803025000508882e4000c2c070044901e40e001a4980306200c0900c030b19905 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 814341133 1250 814339883 814339913
    0x10608030403080913090b0103122307030c06020d0c03061805010f1202042706050f191e0e0313060305060a0b030a090b090d0905060c0c090705090303040603020304 72
    0x102460901d451615550898015030b035243d8010007996900369002c0b00d899200800c0f01d544540d040038956141e0404a0000b8800904000071840b06610000d000343d900000300600049807958502c0e1850b1a41c08a545580860040703a8007502072003441071145260090052801c5513545c0001c401c0e00c2c0070403020340160040144c03828075240000501042a110b03a0000070345107141d10b01e0f50140b00358800b0600812150780c10b20f220b4550042103446054200807080b0030b9030300502c1d007030205446106108204c0b51f0192510f0219107048252010100a950000d0500e00c01c1552200c0496000404c4e031400d48010165201054000040410010429002c281d004d0455440c0c02c1202d032529034003103200020940502500080c0110004030b420460b40c01201486611801d9510795052003403280b03554048400590021800700480440d190410b601640c0381a18860004c024070312454040c04040ca0000e410001040020400d441083d20100028001410075541c01603480c585418054010000f402c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 814342383 1250 814341133 814341149
    0x160b0c070b0c0a12090305010c052205030c1c080703210c09141309050c120c0f10140c150a09030c0623010e060118030b010e0c040e090f0106 62
    0x845810101c4000207003401626600110134650030003035550941e00d4000c1039100501030b6007070411994045a0050191407024550628403a100444d07034440222503009000b19605540200c50003c07881c40c00a107100e103010301a0031950310003002c0c2d8940e00c0c0c4682c0402c80c2a03010a80310414811805040184090821030b0403d08100c2403031501c80c02850705140b489900200300e0220100021650f0300e00780728140740f894400801184c056407501a40f1450b001c00850310440c02c140c0c009c8142a40840c0501381164000c1818944030300d000100140c0781c00c280f0302a4100400756100005107509c8500030054604980d0007080100302d103210100380d00d80010100030415090400c03c0c030029401445506440b1350040020a0b00306800801c8454a0200d154010805e990a000004c1c20102c40500034080c04082c0d0740d40c540c11400040f4140d01d100d00b407100411300558074004014403210382d11095008070310381e07400b545010f60302c40503a120703064151072240d00c030b0304042e01001c2c1b201000d2162000501d605 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 814343633 1250 814342383 814342387
    0x3010e220503030c0a0e09040c0f0605071106180d0b090c120a0b0a15030308010305061f030308150a090c0e1f051b0a200f0904060e160b0c070b 63
    0x50780d80c0715100c0c0005404a09040383c085100d00515005005800b200d0401a003403050615090800500d48030302c0e88100310100c0041000400d001340301c0d01c11998010b812214078100b103805881405520b9016410f20381e2001540b07a0030301c0550707550451041100d0b0080b180520241042c041e0303a4104100100c200c0d205048100124414240c04503d1304c101d160040314848642e9545014007002d041d0000407041003010780c91000c0101038010101a046c0ea004030201c44042d87c4110021400c4403034018002c200e000040700c2040000d00c15079001d5030100f00c498401440050500102d460400f10b50455400151561810040d2035405100340c01800c03003c80300c0038421010070401c10b20841050040741d0400800041a0001451413407040710880b4102c4115075521a26041400802000059988240151114014a62905041400d500ca000038907164aa031266a00c1c44010904203540c11740f140990400d600c20100d07c0c010081c01045650107065444001d001d0480c281031080d008000c2044c42 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 814344883 1250 814343633 814343701
    0x411010807141809091b0303030103080906032809030e1e010f0e060a0207060f020d05090409140a0b01141c0308130501020d0603060b09090a1b0b03010e 67
    0x222046102e98000c402c2e407040d0b40c400c2100c0300110200c502d520029000416281803001102d8001040289442011440300800700c100040540340e110a201c060701e1604184025807007407034003000950f080505200980158001201000000094003035051021952042404141070300409850039004045a40160798040a00d011400c0601d4208481c1006079003051101e5040c0106208120305400505c10707510365030454802942c491090068100143c01c02d10300d5686203000080c4203c00c01c046071101400c1503246014407006011900702a541070902c0c2000400461050100484490041440ea0140e60400001c2c120705910281100d01519007080300c104040c8822070341c42005549458040600c0d110007501c0000091a0180946035500c001419915030005074020400c6900c80d803410300202d0000001c1080011b821100c0002c507800c01d94000b80041d1601078a00707c08a034402181c091940c071030010344115003090304040c1c0c4480d000006d015204070082071a5041c403486015004001d60 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 814346133 1250 814344883 814344887
    0x507051902011407051e09150706150b04080601270f090302060105191811030a0605090f0403020c010f11070e1015090b18040e1015060203090f1807080411010807 71
    0xfa200b01440d5100c01c0c0490907e40b0790b901d02e12880b80400e2451405911003115040407001840e00c0c01e000c0d551413400e00c0000561552800547e011982c4202c00740034141e28200e580d030809800c5180300c110b1440345070004103080c401441128612800c140001482ca41c1d00e15029140c058183c104600c6500c83c6102c6800d0200d40e280203005441d01d40307902103454504d52403a00c000d007400d014409c04111000c010055280103640c0001d0468000301c52f90440b81e102c1100d01c80c503a0700d064030040c0042c0c000755002200c0e0b5005503a00324090510b4074054543c8514500101d0400500c1e411802c9445060001c0c080c4443e410480743c8050284100d0303000c0351002c80500680b00246a1242ca91429801300769819803101115020f03107134150251090210401000f1903a8030b8a03210450009841d15000045003083c21400c40401941d01c1a0000e40c03400480c0002c0150056100503541d603c1203002d9200f43e170201c40003010500800f010707166070056003041e14248007101034516219040001034020428078503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 814347383 1250 814346133 814346167
    0xa1805011a040315020f070b0403020d0503060a05010e0a091514060c0a15020d050709090c02060601080112052a011d01090506090301150303121d07030204050705190201140705 77
    0x2a91045101084d11310000c1d04401038000c540e400d51440070081070701c0c400d1011000e8014821440b0380d09a90442038501000c4da0180001d540381e680105201034148100d5001d03d42140e401c081c000c028080e620b0f43c4403017034000e03106400407a101c1004404e6041050344200e152610729208c00f10b581c9030422600782c014035910306076504040d001c4511240304880d1003019504550b07a60300914414407040c0307007410001c1e003408106e21601c1e80c02440c090b00b500000c0e1020500c00c0c05910165200c808c02d0746040301e810040b000e01c440503207c6019450302d000f050030b0440c150081d82221008010282c80c018030025107201ca0074814266800c3e02d00d406003030103a074848000f00940e00f088a0342038841a4000200380185004980344a00914001c00402456040300300d0002c0202c280b5000c6c001030031100c0c00100945144003150315294040d09085c0010b107000d82140303612680070704e4420f042c02900c85021245139442c01102025075501d880c0010704000c1240815400b445605105107170006000280d2050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 814348633 1250 814347383 814347389
    0x31d071208090a0911130e090709110f071208010e090c040507051b060a050c0c07090b0117010b030703051006050a0e04021608030a0e2103070309020a1805011a04 71
    0x2600000704540641d540d00c0c5031102510010f2402c0005240001400106606c0060005200f1b861904000f03000e000303030f06106206070702c001e010b445e082e4078100503040500f40401a102c2c620380d041c00607401c00c07045d10001d4110240980e5526840c03040901001e4040c01041c0c103c03009000381c0c42c08002da001400100690060429140022255244001100c25004400c1114401c501c90396a4800365a80018154018615014100226210652034146074400c08860384801e8022600801c0b000756030764001c04582d134060404e0034410414180d10192641c007608201607040d404018881400c0d40762090503806098500d40806660030b005000d440b50280385810400c0080700d803528201a1110b4054410400400c99104018007081c070740348031540c1040318100b140070b2030503c1c1c0322080d00c0c00140543c503c030b0080341c4d0540c0c200440d280d1003205902c000e1114040c161203d24001c0161100780c80c0000610301d14020196085651041d0b0064804c10703032184101c04069405442c1038144c00c400ca40031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 814349883 1250 814348633 814348643
    0x60203011a0c0d0c330e07080a02060d1d1e0109030e0f0406080d0e0102100c0e01081f03060209090a06050a05040903090801060303110d02010203040b18100c031d0712 73
    0x700900318075040044040c410009000600a070b180c50317009100d8002c1d1002c110800074800e0001c9200c42100c20765034501c41c46619644c0d845501070102500f00349001f00b2030346001c42404103514058086005802c0e030304a500e00003552150481940612940500c1200105844000e003c2850707203440c000c20300403400c0740c800e20603042c00b00840421f59842d4080d2000309060000d440d0740340786848002d0308500820490310b001d40038004180f8280243c61084501c000078a403650000c20030194011a9605d10042290913010160548031040307030001e1a901000714411900503039a00702c4841400042c04c1c002c2c0038110b503141060b00c117119075614813100d4000c2e1a0180c0380040c11106500b421907071400e01e6400200203528050020043c15400480010b0b80c1108104881c0f00e100082000c80c202d100031200908440d0307414001c141c5248c1c225851000c0a00d021f002c40d49030884001010044445503150507010070750700c074090032030204a803580f860031203508030103400b00b24500114a80d94020038000101 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 814351133 1250 814349883 814349897
    0x507051315032405040c260706032c07240804020111070e0c0306100f0203070303020a17100302030106050604140d0f0f050f07090605010e130f09060203011a0c0d 71
    0x1103d10040454842d01590300b04080c0224241800c000300703401810f000e244403010b401284e0710060304c0302503440c3e01e40405100007440c40903e400c03802c40050002c8140a4143c082c1e41041c40d0b00c0800d204100074004000038047c0a80754985209103001405003080d9420400e101020045441e8005800369406602802d145004500002402d42400116040440c1246800083c00098910107001c0c42c450138040d122000e40c01c43c4880261030000850201d02c005034070030403640000a10a03005020512064100b00070038070000880c140b2801c82c120703011250114281810001d626090148200414080e60040c0c5410708080842c420b110140396074502490044000004002103440c6010019810100d0f4060458042c0b40050701c480d440d041807100380c03089050100d000d090038420741044403c140c5170992264035031028841c50b401d103d0341070705040b95110310b904100e080310f00070310799541c4c8241401a036a60500607101400700129000680c086414401c0962440340042d2000f034941c82824808 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 814352383 1250 814351133 814351163
    0x19030603121d030a03020618060402030a120903080307030b031b0f0d0c0e0903340308100905090c1c0803061306091e051602070611070305010207050705131503 70
    0x2d03080c1c00741d9066690309807207001d10107000c0c554045180750180107071803458041a1200700c2a595a80c0c030641e8060b5254002c3d002c2100003d0703090740440c1ea0981c0e241010b498003596a1039401282d00101c0e55074022a8407a4620004d900d01409101603a1803031715851265107541e5404502c3c04403002c03c8950250440f07801e00c50030301510440e40d80040c0840031080318140f92007007015850741c010301b003c00c2c0b07003103054016002451075008605017a0390404061030844c2d042500e04172481c2001802415080122413004158014103018040c49482006c000b040702161101c00e01602d4010a02c201c1074000c9a080c0361800641c1d600300f26900300c00c0031204800a16203140b9032500605c2c1543c0700c8006d685c54012001ea0320610025001d0300c5980b90b01c07040120f9610350086111450707044007620b0040e0002c107803e1050a00614140008144250450790110340700d941d041d00320b911030300095030715610515081020385000c20701d15066a000610500c49110a00c88640f9588101d0000a2550003200602 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 814353633 1250 814352383 814352417
    0x5190e06040e0304120501090215030c070201200a03020d12060803042912041203020a200a0506010801090b061e0108060f04090c05030d050c0606090402190b1903060312 74
    0x113100a05248101912403405502d030650003804040070490081128152904030130b107203401564820444805010324010b4594011906180e4401050100411100c5088201e1204011000c0440c0c401e400801e00e0144034140600368030143c1c60100215400c044051000400100c240c80c00c50344011180801e19417104100103581c21311504610f07000c1c0000c1f510802d100500207031a0b005500802910300c4551401d1011002da100b01d4040703d001c192b8000d5804008100031741c0c06400b103004074060b603011f005a1780d103a608105081e0f108407416911035410500b4072401c0208250032010450b02101d4400c1400e019480b541d070580c9006044c44500300006078170b074898210030325a015000300304104016062800c180c85880c1e9000321030080c0314142d420794245005000f150285040c80c0001c10701035071a00c08000941c0c000034000c13038001c2c114a500d05256841c007107000e40030f00501d01400382c40d0010404110f170412000405601010309148040010464000c81c0e1800554240780081602580a0701 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 814354883 1250 814353633 814353637
    0x1020a0b0601110d0f090b0c190c09090f0501050f01060f111c120608060c0403060e01020d0903052110031511040b0a03050c190804030c06021305190e06040e03 70
    0x24600c40fa0058102c1ca80c40d10354070000e841d4110129855903031006445914003202c901078070381103030110f43c40301070010b094240d101011241684250044e041940c1c8820031802135807801407080303801c0d119402d040010400c0a000b070551004c03000f04038041e25890003800a22102d00e89044030705001070400c0c6814108070900400301c216070246005c100529280380010180e488030348a00b0040c5c3c0c6419030101d4000e0f404610745014507049110f0905060654640200034040901410358941d803c000913048443e05014030541240641c407029283c0881554403030000c0901a01c2d129003464a00030480311300303c404001c0c0140c9400c40381104640c0000b883c1c84000740700c4e1600c000d0039420f010400281d600100300081503601c00603a404c0c001503c1c7c21418a02501880f681109104c0d030744460400c410348a0585658024083c2c5406251a9003545a00782240c0c0030007100c5400d23059070b4000b84203d003410740b00e0007190100c005600841c02c0c540b0104100840e00500190710480d1110340d12980d044040003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 814356133 1250 814354883 814354907
    0xb0315090705031f0f180e150f011409040f031b0b1e012d09290d030c020f0609060315150c0c061612020a0b10030201020a0b0601 57
    0x403500c44142003000c00a08550021a015042c141d00802804002d00020985608032516070784011a11420180d006201c4000030360411200d03540c03511303800d2005070100801411800c00400c8010642025517080315218416042400c0e44500081041455201d4103400c0fa07026070804000d0320b800d044c40c0740882c1c4aa60710001003081c81c4503200003c0a00c40a0090207004081d100038100041c459250105a400341c00d224030f10000e100e901d00d011840001e001d0300410b0b0b84500c0b080d10326607615111840102d40a1b500000000c0c84020100d80c1d21030000d00c0c0e2405580812a2490701c01d05c0f0b00d0b50014005050300304007c1c0684201c07600880c0c0358546c0c0b0155556000e00804050b128640710300010310448610380e0103441644c2ca04025145004110101e8190302440780182c4058455042031006a038414800721261800c00c403482d0300032850786450005006456400340040c00c419040c00840a03078040c0010080346140001000107030380000c4c1100c14140d10844100142e942c40c0c0050b01c0380d103c1c03c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 814357383 1250 814356133 814356139
    0xe0607020709020f2701030e01090b040206030709050a030c060221091905030f010e12030403080c030606070c06030e070506160b180313030506100620100f0f050f06030303010b0315 79
    0x404820b8164000c811030340045c0b40280e030200240e4a8101046090720031040026003184168404913016007007200c0215482401800c10211031552034010410354800d642c01030f540c000b40b03c9014400560b060200502040c000d00300e074680c000465602c0700303080c4140600700d849120000c14a0814012040340704005002c020251865496100241d5018103490302c1403108a0040e001c48900c02350503902542e004d01d4040e558101142c0d601d15400600f948041c10f82070344000e00f4001c2e00c0000340820f800501900c080e0345c0104120002c1c111961829519030000d6100c1c410601a4200c440403006400e004a600b0810144243d25040b00d00da80740000d180d0000d005020000d040c41c64a49a42d0103002201e100d0400c907480d580d100c9401440b9001103015840000301c00104005101d071400a0403c01014103500b50b80740f0340c40e0106081e00301c0341950000f458040c0c44581842040c2c105109065005c2c450307141d800e2061070003c000a44a200500031910708200110114a03000703404018000546405 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 814358633 1250 814357383 814357417
    0x180111010b03191b031a07020106030b0408040806090a02060d020d0b060c011b08060d0609050c1905011211041a0c030d0605041b141b060c0d0e0607020709020f 70
    0xc00f020b500c0402150000b40c440c203954109590a00540c8038003082280c1e0008516184411b41c05968507402d1005041d000440d0740f202c2022000c078020b4007481d805a40700f44002c540e00c1d03242100e4941403101c0104480d01c190041094000581c0312131049541400c070340c440040c2c0c2c0b100b030b413110f00005010300600c41c0d402403008115601c1c05141541710710f001d803c0490700f14818414240c01200c0301c1070121803840e0010301e10701d148000501d517500407130042c0d48104241c91054084c0350100706508012040d0b280d201004c3c410070041540c2109030942c04900181c0244559003a9500300b041610503845500c0c07040b458a0503070f00ca040c15030010340d0740d40c10600c01582d95491340301d5030034809440e407801014411071500102103c42ca0440300d81d14800c0c2d149850358a2083c3d02d04c900d00640303800c814114103841d045040c40240e02203040c0500791007607290003100e507240c0030509590b00441e103191410042c4d541c4010107100c8070700d80000d034500803140600009070740c0d108098414801401013029000c0a0194 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 814359883 1250 814358633 814358653
    0x1e0c0f0c030903010513110d0c050603040b010915030c18090c06030504060606030501241107080f0c060c1905121603140306010e092a030714180111010b03 68
    0x1c0300900165000718003d202a45409040d000c03c100d400d20010030303480b11700702100014101000841c1c2c0c150301400c03100c83c985030b44101292450f44102d0381240c01452500051083d01070b1403094100201000030004400c03403e41da00d040242c0d6aa000d0351884119050395850f100359503422101c0031941c0000101c650903900c401c060050310080d030f8119005400c200b40451241c0c800c0c40360358100c0d1007419203450900c01402040d042103003103240840c01c018a880046518580c1000114020441e4a000b840d60030000502d20341041e5001c4226845004104105d0102d44400a401e140180529541003400d02207490000c1c5450b00607100c0b03403c0d04901007039200c80705d00400444401c49000c2d881e03000c15119540551032075403100310389043c00305560100501c4c0341d0500d041c041d076000320490a0311f00c01081600c5086845031401d00f060742441c00c000308102c00c09501081d041c00f580c2404004070b09040395220401c00701c0040d5076295042106513120a03100c018250446503a5031805026034608400b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 814361133 1250 814359883 814359907
    0xb0705060708061905040b0d210212090d03140d06090606021917090f04090c061b030c0b0c190801090b03031602041104080f01231e0c0f 60
    0x80d045407128041192034000a03120700300a414010f4007035103030800003ca10f00384402c1000429541d8055078029004000020000303816a860501620009119549078082d00b03000034540209461362402400303040c0040119500c8600c400382d1155810304211100e205082c540745071030300a101070480281e00702100003c030b0509660002382608d60582c2a039480700d524400800b0581401d482c024244c10a201c0760030b00350403845000c2d03c0310000c003d00c4051440f0641c070000d01662004a016240220784001c10001540c02c42c100420000140c400d40c0a20b01441c2c4020b001005030300c2e400b80001c50b0f0f1900142003000020b00700e9201603040007040654810000000b88000e0090003a80c0000d85040700c3d0020707030f10f000000d9851182240041450710a801d600740409018244c10030b2440c0b0105000c00f281d502800e002d00f44141c2126000065540811100c500c5103260b188030810008030644144680461404000340046601d514400e000d9119107000e11010710460204d10342001000c070f41c00c80008 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 814362383 1250 814361133 814361143
    0x60c0a0f110a050f03071a09031f051f030308190c0f020d021f0e0307080a050a090e090303130c0807060e090906060307060c02011205070c061104080309010c06060b0705 74
    0x1d1000d54698a030b05450302c0502494055121495a0590249004020119840d405035080303c103034442542c1813001002c0807928024805506142100d60044030b410b150605118041c0d104480d40001c0e48074006007da499501c0a0301c0c0400340030132034000001340d03050f5010807414544120400e801c03c581d01c600c400c01858031511130354210060140440400c04e2610010b4030545420070010341c50034200d200752042c2c0003042140c41a08041c0014040030010444c1c40300074140510b441e842d215940c11440d1402032900c0440d8124000022021040c8203080c000001581d51015002440010721001d50620a00d01400c55000d04000e204d18000410503075030204500740907050554818803103071180e01940c1e41315442210702c513415078801035040229034404d5032800b007030328010704001c41a500d02e50214000d550084075804041783c4000c4200c010000c0611402c01ea14141d05840c0e0305081c1040500d9407a8494003002a04220f0421624000d01490340d0000004241d486452541c072489403411540311 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 814363633 1250 814362383 814362413
    0xc03170621010b01170c040509100b07080d060b0a05041e0b0a11060f070c1b081518070f09021e031303090905060a05010f02012009030d050f09060c0a0f 67
    0x280d00c0780c400603001020205e9590003041c505000742d0401d0304040601c410080b0003821204044908500010b401014031300402c3d8603030207003001d165a03103ca40840410340e1101d600952034240c0410481c21540e61140650382580c06242c1c3c1c00700c031407600030700304000b00350140c22548038120005030100341d00e50428004411850005c082d0f5000e9aa24503100d00c06400403a0f0b00c0c0701050060002800041da0380c04000034581402041c900c00603103401c0a0b40c07800c1e061803c5141c001903588284001d41014004100241d003200008043e400c0c1400143d0307401c07040d00d03c03585e200b19402140d24590800d0002400c005a050100300c030340c4a25010106400c4050742410680105210350300210300c4503028001d05104810107045400360601d01401100e81c1c10000c01080119503072035034040301078541ca03116014044c9200b0316840d00caa41d90307800c01d810f000324200b850082c00410081d82c10b000b01e000c800c0e90740d1004200c4103944c441d90114070890802c440c1d40b10052813012a10b0030902000b024001855170 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 814364883 1250 814363633 814363637
    0x5071403010f06030c030303020309100f0c1103070515090c041104030b010f150e04090f0c0314031c0c110d03021c060b1206041e1b0c03170621010b01 66
    0x5120100c400c0b0480d84140005000011020014070200740660000c5802000703000c103c403080002442080c00f120f803418034500843d074136010400581c2d0341c80400c4c3c1d130141101c40050361400b84181d580700e668134860364030a9a80103454002521009050110380c00030b080141c0300780108283c0d400c0202ca964001e0104603102d6000400109118400394040010740c2c600c10404403062647c0e0900380d5178042ca003901711b90710903280c0345104000b824103040800b40328490b8000588079800c6241000442d688200c000d2020752050090320b05400803010150020603400500062062481e40200c458046e2101c0c00c41c1c0341e02ca13a07000740799500d81c5980140030034942c0d44600511203a400d01040c041e5003451190401c00003060240f080051407070042c4030380203030f0002c00020b240015452401200140c840e0106030150b40c81d111203203401d40500e03401d0303103204452a20840446d5580d801400445800b424000030b0150382000030515118000c00007103209031000341c407045a5103c09014040c1000d2202980 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 814366133 1250 814364883 814364891
    0x60d1d070f08010e0c0d260712031409071a04030803090a031202090901091508010c020a0606090e030f03070905040527010510090906020405061b0f0c030d030c05070507140301 77
    0xc003030b89002c561002d02820082030a00c0c0c2410640702d04445015002803500c806041c1818807c1c1c414a407030003803000520402d613064000201103000f408445c0030b034143c0a00e43c0700b00760801ca0b05c0007001c1003403c16070304002c00c0211410040c0746e440000340a250030080082c04000103021003101c00051415000d4401d43d10140c401e14a60794540907401800555600705101c00011b000c011004e8005070600700066514055540d078515401c0d0035103002100d0040560841e041d030314140569401034202903c02d030310003840200504030100e540c900c034180a507a14200003002181403640306032540001403070024020f00517400c0905040080e4140d40d0390706100c41c03100c5080c00707250030b0040c015103219101c0d881c0040705540c940600840a0800c4076812100f00307600304004a43c59686001404205904000310940c0e00f0b8440c04291402c07191407100381d140d5112000321030b440d87d400280e1411a00031881c02241c500040300050780d01d8000d100000304240501c040c003003070001ca00040385a141303a044000380 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 814367383 1250 814366133 814366151
    0xb0c1207140709060803041a132d0b040b13030b07050d1d07060f090e01090b0a0803030c03062421070e01170402060f0705030c07090b060d1d070f0801 66
    0x50132203800d8815807480390024441000700300d0f0159509074095525500d00d625042c2d0706c9000c1d211b41191a0040003403203100b59441c850014007040340e4001101c0305041691014208203a1107514022441000248000000c1c1d01040b80c402400c0c42000b164010880c10300360800c0d0002a011703800649005201c1864010b00040c054281c2c40760300d8031404070300082c00c036075424007000719001108541c88505000d002c034400211591840d56050080c18170010015400302264100504078010b5405101181d0040c402c0c004c3c69520034045907005402102c5492204440e07880c0a6032240500303900070341095001ca042c82004003810840d1034500c101502c0b01102e0b55600e24252840d01180440c940021140340441c410801051106038000d0b00042c002421b00c030000000740582e43c4070540407503142c0c00110b4001003d100411860014154841d8144900c0348048007003a064010b03400c400c1e00c0c140e00d40d10038410b41000304ca40810b01503255002d48880a0f210110220212a144030300e4489618000c011 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 814368633 1250 814367383 814367399
    0xf050a051902010c030e04200d06050301020a02100f0f0603080901082a0c030f0a170a140402061308030f0408070503060c031810090c060e040908040b0c12071407 71
    0x4800307100c0c0d05071240200c200840c1c0f003c6404060305d0300d81c5a0855501d810070356203514400490000070440c0542c3d6640c0f0803803604107405450490748120700a86c01408050305044d00450046a00a682c0b02d0004451003036407034203009170810300102541c1e6445c14102100744445030004140350b02c021b80740e40361710742c0b07a07010841c840341c26040080140451003000d4003000713010900186100404c1d0303800c0f64181204070241090a070300c21901c01c8003154604088106038411002255800700d440c1108109444100b0700b00484c0d9400180020b1041c40d00181084201c1c000c2c0c1c4d80403000d4070034002200d44803800341c604516194000d000705034081c42074020000302450005038042c4111b13074482384c0350b055460351004000251009020340095025035406424811490f02c90a50150b003e03900b10b583d00c2d884c0c903202510003c4080b4195000d80d04020814022450715021201154800200343c0d544a0031900c400c2d00740480018101c03042900017035400d0501415074503205541d4545000e94070764a50303031644 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 814369883 1250 814368633 814368673
    0x103140405070b0a022104080f0609061302190306061d3c0a150602030304031707050906070b060a050303070515041103060a140109020a05040e070c0f050a05 69
    0x80403a840403405002010f6072002514400d0b03443d004540103101c05008094043c9000c03032804100001c0441c0c100f0044500b00f0050000420442c0030380501d0500c180c2c115241c02e801450313040ca0f4814035404c070003151100c44012660300b100034071042d0303180d07142c0c41e02801518aa21440e03401105005d6403058644191240314000c654108000341caa403c03000031406040c01c0c80f2003842c41150b5a0400308503214401051600c12420003a00040d003200c1c2c07440806681442d600000e046500c14010440002d030040003000500d080000110103c0d5141101120740c1d104008606030000b101003000001c11401110560040c0c3c8210f840c1110317541c031a018150b49001d205805040c0d6407000c500c240503002d4840d0b8a98000c2d010303038036909540a001001ca85071100949007401400c7d901c0159260b08400d200302e403400f4000040c000c0d03141400d82d2100030213502841c0100c0c00c2c15081940030410480c000c0038603074000e0341d208680111a886d00e003412515034072110011307100d0f4080c0d4040d10404400c0b40c1c038 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 814371133 1250 814369883 814369891
    0x4080601090f02040f08030706230714040902040602030711090c0d27140114190f02070c0806011d01031a090c04020c0c030c03031e0703210506010314 66
    0x1402140e1800703504101038600e40d00034040e656800c1002150410010001c00040c0005000031030352100c0c90702d00b14085495003041c11602351410341161280c03100045600d904400140b400804200f1001e603030f444135104580c00f00d100307988002400a1250b4003c8050042107000b5185440c0390720014041c403000340000c591521401c6010803103070b10540b5980e03204c00b214002d01444800d0712803107040c443e8011540c60300c00f40c4917202d002c0740c112034072102409003201403400242010386500b000310302d0310560040301c4640340005803520f100b841d21981c1a13054881842e000b0b150040010b0f6640203464403540c00707020381084000b0480e03440b1020403007928264100c0b41e000d08205690400c1c8600036a80c460050041507160103440d8401a054ad01c0d80007519600c20560054201812180e04042c0303000a80565240242c00034014888a581c87c108c00c4081d04007046411f542d2400c032403400312100303a0160b1400c8100840c4015003001240907078461880b0b50401c1e02c04010b18ae800001c1a040100212 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 814372383 1250 814371133 814371149
    0xe0901020a09170c030a0c090b10050a03020c0c060d0203180606150c1e1014241c0c060806031c0e01050702040e011406090912130806090604020102010f0204 69
    0xc80b04005032140c20b0070781d554030450319003900c1005000c440041d0502100c1441a00c4240ca034103424001c0e10018464210a140222500ba40525402c1c7d005030103030080e18200401d1690101e4200c0d104c54060140000130340c0000e205a0303a5840c0060104025001030b00e0018400190700d035442d04088001030300c140180d000410f240300081648000024550103030030a07507281e000d800c00b482c0840c0b05140000c1c4003400500090803041d01041041411140e9081c1010729408100e0248090903103800380e51440344103220248070a411880c00480e2f4400c51400080040c0d0490700840301c20b010004000a003520480d035201c003800d8560b2410103a40e44103900c01440f61440800c8659030650148513401c01c07505044c1001428600160000f500305c40741c0880c40b0704165154210114180c5a240d01d06510000c1200d03c00c2032400e080361029a21041c01140c65024400015099281c81000000f18002c00e0764004441e0305142645e240c0e80c5908c3c05071022030142d030070003840c0018030010340262404c2d94420 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 814373633 1250 814372383 814372397
    0x3060e21031f0918200604050d030302040816030b0705070206031501031e051f18020a0c0b0106020d080a02190813020910030b01050f090c030901240e0901020a 70
    0x300c284006074080503801c0c2c0a08441090002401100070700458150070340720044c1c21143c07080c40c01c101044d6614055404124026103040c40d0050340d4410985048c2e9400745c414041141c00b07444c05070024413075900403a40d0352003511a4000a480d2441701308003540c3c810076042031580c441c4002642e05004912000707501c410140000380481661045c0300704040790501d07001c1100c6100c00c110301c0300d0031810001030130904d40300d604220030707040c03082d0708103140c0c2c0f0a4070010b000440c0341441220701d82040104014800b500002c0b104c3c1e003248103903510303407416400020300461541c1d6040003a40d115044201440800c0140e00006c504121078400d840512207202d800007240c40c01c1c03074011101103000500340540b040390a81d6140150321005203440c8920400180c43e048641581404515504141d01c520302c0352060988810441d15461030b120340001c0034400c01074903515004840e90140500310180c1609108134032201c4402e05944e0741d543d044498020300e9240a498412a89081c0e01c1001d030a14007043c10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 814374883 1250 814373633 814373641
    0x18050d050f0306090402031c02070603150b071e1e051e0d2303040507080f0a030c230d030b0415030c03080703050c0d0f17100b090a03050703060e2103 66
    0x21143c0568006e20060a8800d02e800e840c1e040300c017141c0c4081045005038003a004c2030000382d4051161542a103095455100c0180c54542500d01502c510076006014a000a9040d038281100c40040301d005940501d01d2075240c0348620310080d003868030301d20580d09845044400c0c1048840800e00545020510340a041440000c0c0402e076440c0200c043d07003010b41103080031144a64500707400554052031007000604207082c80c02480703a02d0280c0c108020b560503000b001200b00040d070440a20b00d60a54030011200c102000301c042843e807a10390341c140c500e640c000c09120601d0b89034154450000810300300c46c00c2200b90308110640d110f800703482c00300414075086008240013140680018221303551291405a142084a03c00b00e41000102c0304140003040841d200d00d02440d4100007603d25a00845000c800d85281039040e1400090326071040844142d40050321944903214942c03c0f1019682100c01c0f10740da1a505d1400c00b00504003004001d54078000c011000394080e40006a06110140c02d144060554035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 814376133 1250 814374883 814374889
    0x9030905041a04150314010903021e0d030f021b070e07030b0f060702040b0a060c051002030c12100503030a0503040209010f050a03110607020d11120303070504121518050d050f0306 79
    0x402c90940e0000d50f138a1000c0000010180e0f0540c40151361050008540184603241c0039103807028031030400104082e07403001e90055040002c4c640d0f80104051402040d2048902c2541c0e000740305120104403440003040c12074480c6c22000070120211030140d407110740560343d0001c080b81120b20041c17032580d10991603c004040e91502e000a01007443c001131002a400907140001a049242c980c04400481c4400218500340081071055000b40c5a000d28250301d54a4000b000c1a2144201c029031501132a0500c0440d0060140000e281d0142502508880e500d5017048809000c581088500324070800c00040007040d40d0b0009128007007210000317051611007a0565030f607096034050151460782c0108043c084800941c3d074525062007840d0181034554101c060342001d20070054001c00000c62a58010002c0c001c4c461b034800b048a084a0300034181c40080000e516080007502070460101042c0d40c20049030104554a201040740c00920a0045810350000d4490540341405900140b83e241d400030b000140d8241 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 814377383 1250 814376133 814376141
    0xd15091517030a1d040501120302060a0b09010e13080c1b15120408090904030c0515070f2105150a090606021e0a020301060b0a021015030f170d09030905041a04 70
    0x1807004104c2e6201d92100841c00300c5900340d10603290070310b01001180a164041c010380d50403950804c014404891540007107100b8031810300c180441d060160000601811400b031400c000300c0d5021410740d030740c1c0c41d68000161f41c0d0203440681c02904290310b000800e0926004604111121600085504044100100141d6044010020703500d0384010005800c0701e40d00d96040511483c03003510754510b04006402c0c41171524400c8207156a1444094007400300854005030342011022481c6000410451549040d841102e100403880c90700504120034019000e0303c0d11504007529405442c4e500400740e0340c0ba1580c0644030240318510140e0401c1d29803410410043c1d204640b0221100200c80182080d070f40800d00315050342d807103d044890081082e908042c0c2c14400c0e007010340190101489103060082e000d4803892483d120003803403061541151810405100c40c0d4000c00c8091900030b644821007080880c002d4201e01e0302c221b000440082010813a40342c50710403d100c0101c805c400401c44034848041c80014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 814378633 1250 814377383 814377407
    0x36061203130e0907082505010302180405130b091b031b041107021003050709081f05070c050714101b0f02120109080c0601120302060703020d15091517030a 68
    0x138050160049250082080f11032030326003481d004078003410740e440100348041105d80c0250341054010414481c14911407c00f0b6180b22a049030001007603222040d24a1840d0003070313040213000d0224041041400358003c500641e010580c60340800e4001004070400d0b0b03c5000c1001c54911448125002e0b542504143d403021030140c002005047c0381c4803440d00001d440c00c40450b00c0b4400241c5640410440503803200e154002041005c0042a0880801800340c082c02ca8089010725581c0c0e41c0c0300092401449011b0680d0040d40200c15582070030f071103001e4454468201d00345140100044540f0b401c410380f00b280c2120f109c0c85074151211800360790303075100b4022500e1003900703030380c03040110103010840c0b034080c03044c048524480da519075902ca180c00c50f11130900a05a224140440d40c8141400103e41c001c115070b98043e6641c40d00590342d41d44c1e2810322005040003c42c0540c040d2410202080038803d80d80707c081840404d40b90051990780e606c1000c60000c100c1840032200350418000410070900074602c0e0091 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 814379883 1250 814378633 814378651
    0x5091305060d20030c01030605060a080606070606061205090303010e19140114030106050f03070501140720030606040e0d03090809120d081003030c0236061203130e 72
    0x803008043e11a5544800000c3c07403806840d03880300c10400b4525040060510500003800c060106516220009219001c0e026180052051003000a03400380d54005c01c48001030f6000e0002c01c2602c1d141c0c1801010309110b24a405445840c01c004203100030400401d07681240c078107000d048a42e50390602150754800f9901c4031b0303404107500c680e841d451040c04036400394040d0007c00e84424250364040c2c10503003500d030968042070142c00f0321a640f03d5aa00c0c00310700754096072402e082c110500014041c1d41c0b00d052052140190150404a4044182d00d030141d109103d03c0004408598840c0c40c4c0c0700402080790f8842020300501c0e0700500c0c1e03605040b8000c5d0000100280540900390400500c02c0c089009840703a0f404983c0c1d140c010390441c069a039000103159400842c00284035640600b540e40c00741c141041d0000203403051854955442d400919070010079542c848000d04032408416060380f80328946010759a582c03140e03070707220402c0c201c5003800000d0f01c25101092100000c987c2c90000b0b8a24480c2000e44038281d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 814381133 1250 814379883 814379899
    0x803031305010f05010e16050c0c0603060d0606140406090b130b01030f1802100f0228081303140c0603151c080307030f0506030307060c05091507120509130506 70
    0x124040c0f00d40306440c020320072564851000c0c034106070034818401621240c1750922809000c1440b0071030b000034201c80b409030300b61840b03580c0b526800d0014001c1340030790000500075800d1200100d10b1290080ca02c0410500503070f400d0086c1516004000c007910310100e030302c41c0c000f64403118202c00c2c2222500b00c20400e0381c0c10304000524076400e908010541f000341d0134142c1c038583c002d0138000450400814161103800d051800e0308690451240c001d459282c8000c544145040d1000060030b209400325034800096071183ca559580e036401400404680241d10047d40d45611008413180021404a0904403001c0002d1030380345140e07906c8140c000030030810140c00b40c20402c598400c0700601d07560b00e100c1c035140780180c60070354a07071070700940c002c09440c000c003241c08a007800e0205124840d10004151740f609503000f24003182c881d0661030304a0b040c1c0208111290b0000341180c0108400203094010540d050050150b0b8854818030342d81644c051140d22002900031301e540140c02d04000c07603039114541000c07000385040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 814382383 1250 814381133 814381151
    0x12030b01050c010c090e0c2b06171e0601080a0602031f0b030a05130f030c0510020a0c030206061509131806060e090d0906031e090501090203070609080303130501 71
    0x7401c580c5210402c10201c1c207201001d000918400090560069406403058a01610305000005d00c40c0803c0a2a02441450305d42440f23152a6030002d402810140d601d86103005060b4aa0720b0303440c2c80c101c3d1180481e074606803440c02021030105446050b43c5480004100f040c0155030740307c00a5000600308048200144200c8140409045c2210002c0c4662406240c4a060050a220440e030014201d4082d5648851130200001c10182c07111643e142c150516034112207030b509201d4144080da20580300c4040c8001000043d403a0072165201041e8021b034229020780d074034202445103a52040c00c8840c0001c009101603115480e00303a4030b01c0c190400c035550110b021201320003040b00d102100703001201ca4071f8a40505010141c0340300c42c0203070f1200c0000b00030220042c0301140076100d41a01c2c02070030101901c03903c0440b900e007001c0c24074003c034104500d810441d40303189042090003080e44070340c100e200740035182002030707a944540311440517204031401440c59511400701c3c00c203400000d80300440d07030f0b035403104107178 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 814383633 1250 814382383 814382407
    0xe010210060803043201140702030f061009062d091a0f0402030f041112030c15060d11060a09050d0b040203100c1d031207060e070501050712030b0105 66
    0x2010051042200442d203071030174650380c3e001d51203001d011107411400c803010342426456004400c02c0408428284100390710340107040480f07580301d20040a50184100e08015001d000009041440f40c4109600d0090f890744450448007034038000c0c403554020800f1503200701c0442c0240303594480718848081c1c0c2404048d039620b690360255450a41610801038404118211504004510010a400480c1c08619516000700444440403021b44040d0a0000c03480c034800702d6031113285102811285034400c0300d844200099845659142210040c00c001c00614045150350134840016000554441144003005c0c1c03400043c01040e8010321855810400400030004407902c44003442d101b400c1c040c12102d1241d00d040c0c018546440103440080c04c0c1c5a140c80c101c0c0c0f00f8a0f51000d07210304c4025440c0d00207440b2803503100c0001e1501048107803c0c2c403480c0000075180300f0030440e903116000401000041c1d901c1550f41d00c00541d010300504401030300140c0c00303444040341d5901c00e52190744502014100305040c2040c40a40b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 814384883 1250 814383633 814383641
    0xf0d0506071107050105120a2d021b0f060403180e07050706050c0a0e040504060b1206100821030901060b0f0d05100b1b030706140115020106060806010e010210 70
    0x8000c000c200e00e21041e20149070240420f0001c3c200a0030802c0ca0001100b00f1040c01100040100e0742855880c00c000e0140300c090403001000c9a80840d0260b01c01d00410f452500951022a00c0c0000849000042ea54480c0101c2e204054403080000b80c07903a03503a9600e094171070030059043e0404240044034041070006024500c02e010350340c16a600364480d0070924003002150001b400c0c00c0740000d800d0054901c4c0aa10040d80c85d440482600c002c5150b07292482c2c07403000f9184128045a01c506001e56141d0181c200040344e610401000600080081d59401d80f11b40f1000f4400d030540c1801c090789200943c03000c0c110000d42e040004034000045841d507400f4008074603089030852030140c5a0002c0d0407542c0b21818000c03d5000340e201c0d400c1021031071800402c5006842a03c030803150751134002c00c549903609005e02c2914540d94100d001804070712a0300428019813174003401007481300b10301c60718504046841482650242e501c81e4550b2017898031100010b554061940c4940b03811403248612400490031240a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 814386133 1250 814384883 814384891
    0x90307020904080c0a120f171909151e05060d0f030c1703090120093c0108090a050606012a06020a03051e04020f0103020c0a0b01181a0f0d0506 63
    0x117064030741d06101d000c1c000c004091424401081150101d001c800c6508c0318401a904238107030009150603800450040c1000c2c1c0040c3c400a41400c4020200b0020031001d074000c0010043c1c44030702c0896403000d0124040c1111006d4880542107100d14030000700044403c58901102400307800c00382000520b0380d5802d10b0003e402040800140381c04000d01074408000d008034602c031910900c0f00c40c5007d600703101100c1a1701514500030710030003644c20981000b80c00303030a00c402040c0036034808501483d0361030380b21006070702481901d5000446910010b80c154001140c0404510fa00c0400b924564440310011100d012241d100c007120a000703013010050010000000c000c0091041d04090b03240c1c40f8861014040300d5004118040c0000c00412142800315000341d20399200341e04440c1e0030040001003004a0081c09501482c102e68410144000148102c100801d070482d6041001000005640b00180050703403213020200c500601000c140c0c0007903180a0650703168822018024403120445511074600d4150199 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 814387383 1250 814386133 814386143
    0x8071104050411090106021222050907020a051002040b070f231b010206040506040b1302120a021e03030409021b0303070f120203041a040c0f0f0e010806090307020904080c0a 76
    0x310343c07440c80b4144100440d00410140c0087c0c035100d0403a000812042c070403580280400d02d8080c4201d2150030391040c1500240c5030241c4425102c0c601610041c1d40c0340f49009059580384645c1c00c2c200a07000280c0211000e8404d50005d19080441960780c40400b4840107100301d8032002200912100d1601818647c88441780200003401d1b0b00340394624200010b221581c0c114115005a41004042480050603a801c298402c9003585a07546a600450380210f8510000b980070500031308580c0145000201c6099a0b030080f1141e11071020b10320142080e09a030100304a4254100f400300308003c3c00181d000e484401022600201e44c03081c920700d080d003076610841d40b490200300b01580e0802c0d495440003950f0040150320608610f1400c09841780e0f4040d50000c040818000f80c000001810480004880b000401040100030070081e12141a1342d80d1a11a004140e42c10002200020310244000b503154003805e9543e002d18075044094080c04490b400041c016210315400b00b1512100e01010805000c07810701032 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 814388489 1106 814387383 814387403
    0x70b09070810090519112809050f07020d08060907110708030a0219020901050613080708010b01120c20100608071d090307080711040504 60
    0x350018952802002000b0400611582101d40b25600c103409441d003100c0e903c1550f030340f01c450a04024200c00d80f500a0410b19003032002c60040800940442450b009600c803803049100c4845034824031400350381d201088185034a8001d04c980040c2180b010b0007054840c1c40000708540005000d6078424040500803c050b07c0c0079800701a4041040c60075100710550341c0c80350300d443c0e40040c2d21980240c010040d220105101c400703407004030540d000704100c1c0b031b03a400d103c20b2241980201c540e010b101c42035600c01240c454000c1241c800180782010012940b04e40f40800103107002ca508807000e00341030912683c045156001400f540c40344214900824070240440386031f030310780306501c0b0100501a00e0101d0101c1c103641c0c00300c0c090040e07031902c04c601c40045141c2c110821700c18500300d80c0b49403030360414401c4c0070016403c0790050510300c1c050300d01c02c507011804a0004086032400e5604640180755 = true := by decide +kernel

theorem cover : BRFrame.Cov 814208633 814388489 := by
  have h0 := BRFrame.cov_init 814208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 814208633 ≤ n) (h2 : n < 814388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
