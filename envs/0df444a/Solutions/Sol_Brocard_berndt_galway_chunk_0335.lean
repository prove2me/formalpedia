-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0335
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:16:48.679568+00:00
-- url     : https://prove2.me/submissions/6c1f6fdb-7775-4bc9-9464-75939179f674

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 60071945 ≤ n < 60251801 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 60073195 1250 60071945 60071953
    0xe100224090705120d0807090302090f0403030f020a051602060708030903090a0909030c060c02031b0105091006030201080a02030a090816050c0402041a03130c08240609060105070c090204080d030b03 87
    0x42c4e5000795560b00d10b50401703081132158000005032192300811010000710740160a100305898811080c24020008640840100745040180c4d2642c04240c420b0b00c0d0400c1c201d407a0586448606030260342d0420016500301e91140d0108490400150345501441c0510000c400031a145c40d803040800c0340483c4181c0001085030720f440d00c0305010991003141e5400392604014001120a00c0307400403803e6210703642890886880c2020900d02c03003801548101d100f1088041a101d19081418400d8143c402600c0083e000421f00b1004c030f140035400740e00039a004000c8242c00684659180d40c3e40f24643c002c11110316201c0030411031841440000d120a01c00020300f2201145003505100c41484045c00c1005010750a9a0200c00142404002c00c04c0d148400e40280c1180030241d50388000e2a501c0c01a00c403c03c1c20329594802d82c504500701080c0c0f0707a00031140140076240c43d07659040111082d03001000705840541040c80006420311441c40240090b00d0b03041c2c0541000e4222000142c16036800309100c50103980 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 60074445 1250 60073195 60073219
    0x506030615060c0c100509010314060102061906050a030309060e010c080a21060f080d08250e09070e12060402030601030303090201023c0d0e100224090705 68
    0x441d0303078240740a41c001101e1250b1203001d441803592801c1036200c0c000e81c1042c10581140000ba40120107841c1e1940c090f64140403400c1003481c2e5000807501528464050b030710403c040b80ca0101079459803c1c500364051000280c0c1c51355030300080c0c020900380c0c0c4150040703101107409022655001d017103030008010030b003058910802c5503600d1000e00d115503008482084080d0707080403e04041c804134101c7d955101e410074414141c89280a4049010922072030000d0711480100708689800380d03104510400c40301da08007183c0301d400600c2d1501e2401a9900c0700030014840c00c114003960340c8868a5002e10300607903030402030389480c806104d200c0003486007407000c0350300000070440140d03000618981580d506260114110402c0c1c40141c0c64241040d03400325215501c044590000020071310042d25240030302130f141c40c50034400c802441d21024008101c90018030340307007080100c40c2440c24400402204900c129880c42900c4a141e20b414014200700c1c1c0b0303000101b10240410342d40c0801c40c00c00545411151401244 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 60075695 1250 60074445 60074461
    0xf0f09050421031104030803071b0503250203010f0510050402040315020a050705030c0c0102060a0203040506070806192601060b1806070206030c030a0c08060d0308180a030203040905060306 83
    0xb08600744034100758407a50054040b0070321941210268011032001d1903240e0740c407494000669081202e0303000020300c55441010402000074115184140c00c81d002e145000078811f03801d00075100d011113008031800354040701401610309100e00c0b02131006c0c01320700080780c0c207100f100c14100703549079480306120f24010711040c40810070103010052001194500181c2da0b01c20000c05a80e24000e40001501500012410f0803d4070320200300380c18190f8007603094441581d40ca03214034080b400152009086944070701d00241016001f501c150390850001041019001b19000e5000c400101c660490801000011240e11000c80340b0f650502d500b2031441c2c002c6c8400ca0a203140b00c43c0d540184c1e140340781c91844011103148a511920101c2e155030b60040c1c11a6560310300808021680d82c0151006105a40b400f00756008161140e801503000780801000b950080203603407001c60b4040743c06000d000c400041c40403031006141e8104000407500d4800e4015544a0346010001012504024000e034003039001402040564 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 60076945 1250 60075695 60075713
    0x2010b0603012303010e030408030c10062103021f0c121a360403080603010b030601170304080a12120c12020703030216060e0106140f010f1403010f0f090504 69
    0x144640f00191100d80c98440b002a0151000300d00d404414040043c1c049130554010000b8004698003004880d010100041c90724111891445007030854044089407195420181030040311450003031044403541402804492020001c0e420300f1007540313980f81c0c01c400c0b149821210310705a09001d041c08000d54003284030301d03107500a03003120503a11400c2d0083e40701100305030b418804040b03441082e8a00055101c3c2240d0302c40c4103617007502c1c01d030080b500107400640c0c24641402101d8080c50050050a96a4600307070004059030380ca1101200350307010900c804200c0785400c0200d4003069004400501c060354200d0409009082c1ca5015101568246504000010b07000010710540c41104c8000690742c09260800710020700030106040002111800e055040c409e86811103004240350f00c000b0461980e4884842c030014154954031a08480781445d501c10382d6014020720112000c4508151200c1c101907892850790368000d80054448e06140301c0e043c01080700b00074080c406040d00d220200040d0401ea1a03285031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 60078195 1250 60076945 60076979
    0x13050a0b010c2d0f060c03050105030a12050a05070212030702040506061321080d0533040b0d0c1203030c0e01021009150905010b150405130c020a0209070c0302010b060301 75
    0x40c064501c10300000989030b507410400810f13000007004403000102d203014800351070814407010000c0e040030008180751134040b0f91a00076a81c131421529201c00e0744035090361950841d0284c00148a410700c240c0015840b441b480e20075030b140e918003665403000f40b441008120385001d0b02541c041c00042c0a510382c850004680e56050310400e0000385070100300d4441c1e0321410740c1308001c01800311102103200c28a10f04182c004030302a03100c840080d25440071040f080e085107014845203081e034014030f00082c040340c01c0983c8a03c2c03400c2e001406030786008407140c4541000030000d0303200e0003070040d04035044810f1603414415000111020701c1c00700c0300d401c50322000035030b10707017000c4986401d03903980750400010845038039a900780003450300300d080c40001c0090608034000c0401c0c0160314045d10611041011745000102100e0a4500080181d1a0101010b010700028803a203000607056216004030400503030b5841801e6031188200d582c81842c140d00a141c001e081d0341d101d1106902a5209000611840c4a10045040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 60079445 1250 60078195 60078233
    0x11a040e0402031903020c01080c190c0606030206160b090105010b0d1814030a02010e01020a02030327011103150a060e010f02010603140706081003080702060c030913050a0b010c 78
    0x1264940b030000070704040041c600c007464a00c15200200405402080d400c9001809803110070300c40d075440c01d058030b01d03110354031049551507a8014080c032024052100c1c0e030384550107800700040b8903417a81c4c007090441d4014002e0b1203902840e199410208000362583c44c1e44449010020f102552501e5500911405500c09920046481d000c0480502c01150003001895030410008542c20300344120f05500c0343c3c0008003050042d401c0c10300340c00100105008840184045600851450b074507404111403900d805aa420f44110141c004d440305c0d0f0400b40101d030300152030382c1151540c1c0e0400541140c00842c0464490b4003526101360704000b001d4001d50000890542800c0503103210364848000c034010b2000341c00c0142203250b00d07219140407041c006045002e8904a8440c1405a00c0d0884400d43e907035000d10005101100422008005040240141188000e00c4007140d0420b040580080c200e43c030b5000071002007950741c00400180072014020414069001e003401c407400e04603604c80e03070311900389080509 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 60080695 1250 60079445 60079469
    0x906141005070b270a0c0503010f06030c03030e0109081002091215010902031003020d08030403030b030a0b04020409110405090a050c10090b030601050f0a0201020406080f0610080c0906040b0c06011a04 88
    0x1a080943d0005565945250352045d11080452881c207400b01000a000c3c243c025860040c81e40a503070082d10800c016281c00040403844640703160341c2240d11140100f8031170b04001c140c441c0010380c040304218030319001e07288940c096140d0b0408020b1100340f031003a10f0411125807000704144680301440340414191200e0a0025940760b85465812485016a510003500311190704881014001d40d02c0256001e1486035909000840c894405c0603503c040000003e095010204040340051829a100e110301d107100f1540511091030020016041719412a2061305c40c0e04443c0c0300a00700003040c407506481a00c00c640c50301c1e080010690007020303e00306001d2100760301c0001005c110355038001c00a6a803d052a92881a503074000749a00a0103500944101c0c8041038110010403400c0025001c514071608000d000180400c0143c18203d8000f000030b0f2030b80c00e0104c400c020606441d1141001080a42042a40e00f59035103420341c041490300c01705901045010b401c0391940020f0005140864046614480d040303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 60081945 1250 60080695 60080731
    0x1704031e090b040e041707081827040501050a1a04020d0f09080c01150b070602070c0e01080a0302120a0903032604060629090d03090906141005070b 65
    0x1076404050640100280d86408103001440e480240a044c2c4101e03c01d10300c18640b55440c40f4507074100d0090b0340c00189030400c20b0003245041c0620001d80312038254018000c522244280b0700050720505402d00101c2103102a104100c20f10a00f4002c5981101901c3e10810840601d000341200d03c08001c80464030658000440800b0011103400c0f402000e0840318040204a4807071500101c00c0e40540341110041d4240760702801c0071300c07405107048110380700780080314541541a039401c0c0080d400014200d5010700c000e0008500250b41c4551140070707045035801042295028100a03207440c55000b80f102c00c4480c10000541c02e142c1c01250201201d5140c200011001c050600c40d00700901304c0540c502e804210a4208800e11101d500030700121074440e0902881031200c03418003400035800c01d03129011b0784410032255140c0d040000b050404c0500a00d480645240c4440c411000d40320030380d1102d00102141481c107521440d210100301400891810030900e0034606a681e043c040e50010207100c4090b4000c565 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 60083195 1250 60081945 60081947
    0x5100e0301020c070b071704060e27010303020d020114010506040333020a030b0618190308030406090507050102150106030c0926010b0f06030406020903010b090103050606011704031e 80
    0x19190f941034840c003a98069622840310710129040706200741c40851031106400185030000040310180c407869a08c1d50210b2110800b07010040100f501c003070781590710382c0190411403510030600c14040d6210b68098952452078500003030035204401d119094115070100100520342d030701c0b01120304481c2c1c084000c56001c0c900030320344841c0003410900c154910001104e180c020f0103041d07006140090050f102000750118a1080c084140510000d91140f007441080c0d09849142c40b2401890640400e480316514640f41e5440c0300c01c40d0000d4808540c0b198a0380c401d002002005c0c03201c0409881c0a10090402600c0300002c50244070041c810041419550440540c0d80e0b84102a140042c1180c0210540007010120708050340d402c1c1408040d03090b520b4104000002d240c000529552a80c004050b5801c5407100c2d2601c0d00203501c404a11a4150740e00d6200001c0c50314dc614201d030003540214003400c5c551800e140050300d40300740344952144140e02d5100b007200080d040340c064085412024440314116039030841c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 60084445 1250 60083195 60083197
    0xc010e090603071d040c172e0606050c0609011e0903020c150310150f08062404060305070203070c030b0910060902090307050402040b1e041505070506090705100e030102 74
    0x1c040c4d00202d4844942c00e0a18514540220310072198100c04954500d0311512503500400383c9000c5420881040200b0000210041d40c580c01d10500714207109000c00d24034007100c2c001da0000001c03c90200f0710001c0c004080c4034042d84a0103c000a01144000b2200f0803030f0a00d1640524041590f18002d500c1403610800400c81c4241c4060054001e40740c0102810700e19410454140c01c0011180101154407030750018003031901201602c8852040c58911015100d0f2a030040c1b01c1c3c1d4000c03101132107803c4a01070702d401d10707480303003070100802e594036414114014150740c0300800c04415584108882400036802404c0c4004994110f07031340d103000351038120b211801c1500d070384008040701d802e100004c912503909900604c0c0d8110214100c0b5602da640d041444140d018901c1500a81a014803030718016070312036880907404000c1070340d40c140380503242c081c01450385c40080300340800240040382203020044e007002803a410407105001000d030300b031900b400100e400f01d9410a40c020050001c60340281520250 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 60085695 1250 60084445 60084449
    0xa03050f0702041e0f0605150c030c0106060c1a10090b04020d09030503010504140105091f18020909060108090604030323160e1009051c06090615080c010e09060307 72
    0x38414030850018600300101007120b405110104e0f89480145032039400c4600c98030381100d00c040c280d1a211f21522a10340483e4001011480c030a00040086c1151100c0070301c182c002400d065200c289425845050100c00310004003058103a4040030014401100141900c8030300b01d803220000442c8150605010501034001c1e1a090b200c05401d01c42c01000301170b0000c0144d8140c0b1000d0f1410444540080541d4100c003000b0711078550003103041d2011031400c103421170b030880c00c00c140414240780d99527407284010b250b04040da0602c00c010b0b40c08680600189420000b07203403c03a5007481d10494a05100890135140d5801510090505580d40502c104000d1a0390030102500c411709034880d100c0c944803e0350307159410b030800d600300000d180b802c0042d1140b0345500308100d4184a41d850000c80c43c2440e0910001c80520040d03000030030041c0e00c0300c0c0005403443c0100e44000d48180307008516003407800818070515100343c0280140d5040308403020060399221040c2d046641c4125a65006a02c9800101e41040455 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 60086945 1250 60085695 60085699
    0x50a050403060b130f0608100614210a030203030f0a050613050403031e060806010e04050a0b0403020a020402030a0212070221090a0e09030c1002070c051207151d030f0a03050f0702 79
    0x504a56421140750381b00324212003512054807918260304d520007003244c0042c001c0c81c038840484440003086007003054401d84a04440010a12120301e8650381d00d103000404501100180e100208108401000444140d009075000d0001d0019007000c1c80090301000360440e941e41d0a90b40c420000f820715200383c101c226003e84054480e0700350411070042d80c0182c003983c05640084e01c1400000100081d0940c0c90354420740e04440900000850b1380e94912804802400550440c4201c16605000d43c0e124802140184c0301c01a0059880603055a107141e00e58004000c1d00030f54000180c040303184040151640c0d580e01040c47c5159a070310300c41b00000c000350410b802c15002c0c50880001c0106e450800001049a40c02a50480d1440741d84004c1200c00d0b44111a4001c0292400d00710400950078549000c104204428040d04d034407030f8940302c0f03002c496005030440034006603404101000d03900480c140e04642d43c20540251250300004802903690b0351075848020108140000da6114000814050303c40701a40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 60088195 1250 60086945 60086951
    0x130504020d02070203010b060432150309061e0106050d020c030705030310090203040c030201080604021605010b010e01020f03160305040f080a0312051303030b0d06050f0f0106050a050403060b13 85
    0x4560203070003504805800c90082d1b1911044031624a400000d68085070710980014042d058441d0400e950182c042041081d2244000c41c2d0484907a05d10703c400800c0d42083d01121345070316200002e2403070184040c088a5484803034114110414800f10101e03410750300d003418407031b59505074848188001d00c50034100e40501d00010860408001307000c8011800b400c2c60040e1880c44549903840c8004910013035a0082014800e8001040154080c4140c5548950001c000505112485e4204112922503c800f1500340e552040700441d40d40c1c01c451031340350b803807000e2006128446164120550340c2c800c15216018480c0700715480300030180315000f00c601800c0260700c94034206644602043da240b06594003200031480380300101d041d0003100d11030540700b1242500b81142844164400798014074400c21400c1d0804804034582c40400c81501606000340c0c9d9146001c2010320702081c2221001c4010b81010b01003103004c000290351150b103c13040e40c2c00e40703400884c00240c503035403500010b20040d264101a13039a241 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 60089445 1250 60088195 60088207
    0x6120a050312090601050102120a0804020414090d030c1b0609050a12080703060911031603110a050403060e06090619090606090b030c090105010921020d120e0d03050a0513050402 78
    0x340c01c1d2149000b00240401c590950f46c88a005a8464000c104c40d0320743d5800500c045c920a51040070301580150000d04005903924100d940c2c5084000100c0c0e4201e10741d40300140c681c40c441d074103101d49424000c2c00c0c0b505101910b00f181c2840700302d20b212000038021540300e841c003205104041c4040a007096001c1140c881030014007002a11b2a8001c4540401003071030560009402003250082e90316000029001c0781c40c5582d1345050805d445054070801c4201503542c4120a07103803001100070305003480c0d5612a030340c8445c82c41c034140702034070000300c66911160410070511a90340c00c0050205e0700200400d0807144808145841c0030001c21600801620140c100040010a25030fa98401106070b90180c0903204851000d50910007685028450305000400005081244030740410010006034100441d01c0d42c00c0866030001020300400c884199403803200881c0c030080c01500081002000c4009661070a002c00c02c948015059000b104090401d010f00020481c82442c110313601e94002d080018002c5403124 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 60090695 1250 60089445 60089467
    0x3010609120809040e0a03030501050a1508070c23070f05030706081801050a05061009060f050901051603020313080706020c01050702040b2110020f070602090d0609150b060304030806120a0503 84
    0x210003203051f00801c2c50f00c00081031a0070318188002c1501c2c0424980100902e40703200456007084000d00c580e042141c405001e01c0020728141032005109950304407000900b1018040c18109030890380b1640c00151104402c101940b000700d000e404841171400d00d003a450b91910700b06500e0070101d01a24003207528102c100044c100f80c035030110780103401c140c1c1e00b0080e016030310f14180d40c03240d441d0040c8000304422030980c1c04014440c3c0020500b8160615240c4d08108000b50b2141c0a22284c1100314050f0f0000715030400010f00b100c1e0014001c2c00150004e241d01860000d000c0e442e14003094a050401c03c1c0083c92350107544450b001108020809441a62010911219500024509002c00010303000e2002c00903010400d50003034955404500c60498a81009640da1000a6002945c1c503a0008007819039100072450910603071440311702a00484074100c142440043c210303020141070a110b4103061050102090344842c240da4032030401d5581c03110000440d0300a0b45042c003000300003071243c4000a04003140c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 60091945 1250 60090695 60090703
    0x3040201111e01381908011a0d020901030611070501090c0512030403080f07060b09100303020d0c0c0e0703150902030603070e1314030906040305010b0a060906080a090809040e010c110303010609120809040e 90
    0x44101a41620008080d08e040100d03600189070043c0d40400b0752401440440d0382075101015074407180700707014500000c03550741c1409d5035404042600d045140702c00403c12070618032710301100b44640030091490716003142e8034040107003c6e40d0150300000a020a0707200402c50a5844070300283c200400000e21072826000c214903070340550004600501400c55085401406041c41000440e401013544000c94100781e05d1520024005004c6402c05407074120b01800301180240c01005020b4501025a40c0e213441d605045c03420026038403035150200d540007044640c8007038140514002c0e0b070007241d0200c40002030000ea450760256007000b90f40407400180002c200441540710704d00540080e074131516031940e650411368800b91140714040101d25084009282e81c016540f04144c0180b1404280d41054100d20104044602202501131140c3d51840f0740713a5941d03004680020035950b2503004525560504600400d05030041c4070741400b040c568a80d9204000c2a50181c4240c000043d10400c0a051480e01c02c940d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 60093195 1250 60091945 60091961
    0x9040612020f0402031e130f1407060801061205090111030907030303060506040308091203041505041e050a1710050709150c1703040201111e0138190801 67
    0x4101060324503a42c89040c180296071250342064203c90181508400052006c2c00c02440d880b010b240c022070b040d001501c024190007240d03002d041304203881d1030b2a0f82d08501d41809a005a4103001061004201d03280d800610740c002044132850205881e2102c40c000381c09420b447c100d41c1c0c2030510200c02c0110f44240010007504480c000d035020301282d60b8500520680e403003a8040038107240ca041181e025181070264030301c6003404826085900d4a41e41c0c020028205040242d8000000c1c00090204a07803584c0c40115a0a1070421400481c403619001c009410701c0c800c1d10a07603401014040e03200415010074801c079407020078288020f000c2403808000040140a10f4081c100405c803a2190700556148544d03500d50b03060b540250548005924121500c1c51604010f02c103d04001e400c903030080d882c11040c000344080b49580308138440e80b80c17480c02c1d10342c1c29140c0c4501d007040c4c0501028591800b108a0700048204000031081006510001c800450024400c503000d165803c0060440014074500c15803000c51 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 60094445 1250 60093195 60093199
    0x90102010b01110303040204021c050c12180a030f0201140f06030715090608130602070317150102070e1015020d021005040305030610030e010f021801090302010507060b060904061202 80
    0x301c0011810700549204445800041460340284005001030030242e0003402c001082000c44804031441100c2941551022034590380701c450701081d191010711801c0140e40d0060f0b010450307810310130510302055603954201c0074040c04004120b0841180c40b0300070360050601c000140c0c50000e1502c0e0800d103020092000340c5a0307501070300c07d80200103550b00020504642d200669510f0028051a000c4103e441c0381c00030b00440240e092892074070700022094401003000301e101c0d4680349920415101105800c5d040185000c2d820740110344030b0001c980e80400c0d1f40041d078400e4180002c5585411621041d91540d80d0052510f40702e03600c0001c941513030002408250310318568200c9010450b00c2c00214155541a00d001700030070803c4c0045001403400c2e00850001e82c80a14001800c0042c0c0e0a9090a41d0760010b0500641640040c1c4000400444071900505505c2800d02100945c13859000801c80d20800e003024080d183c0d101a407103420f5441030708684c0142c100030310620007107407580500d01045502c160124 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 60095695 1250 60094445 60094451
    0xc0307020328030c170d0b03160b030c03041a0901051005041a01080405070503010c050309100b0a0603020a23180d0308070c11061c0b09100501110c180103031205270c030a0302010209010201 83
    0x8c0f500010710f589c80d00603a0b42080940e4199142e8010014041e08050b00072030f07840c040000d044040302c555000c4684244113100011907079080c07030300d01d0880c0c42205401ca01d005500300350607410422100c440200b40c4000a20701f616096070703035041c05030400003039405c8a5030550a00f04891034541d88500a18087c0c1c000c1402d4072014801d8003c01002c43e1509044590000d00805c42002081c1c080c1d40a4a21900c1a05001500c8242d0303001c0304e0880c13414110300d00044040402c180381e04100c000e06030410f001090314880e103500d4550301c000d03010030700c005d04a10420000e201b04104010007185a02c61080e8050503003602c84100742c10740c64aa5043c190f000721218a8808103e140303240048607030303024a0040c42080c05a9081100450b0b110003002c1d0000300b284200090701a907501c420400c50b0450182e0486c4bc1120b5065140040511100d00180310701c041c245070a0102d4450310f08221208502038070090100541c420500904082d1381030304050741405612001414180c041d0000c10555809038020 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 60096945 1250 60095695 60095713
    0x507060e0a03033201051302070b07020706020708030301030521040f0605030a0e150c0c031309020703183005060f0405010510060804170f0c0307020328030c170d0b03 73
    0x624560b4000c06200071302644d02c001004503040220030b642030110761980c09841c05160f41c6503110481d4040e1062401684100400c2014650600c02200506031400c040d40c40c55155464440d0f40e82400c485140741c281c40c2542d02c81c03035090040100e40c020700c0c00241e91031750f0720713611003000c5c1003a00210b681940490400902c1640c1c4d0f8004240c3d00340200b1050b020303040c240c880c00e80c12451500205c1a90060344001c2000014119030412404020400c112016a0300d4070145402040201c2c4100305404444008805000800780e0075021078000300e15550303122010390915000140b1301841c44000d40b06004110500c46548110070501d845280a0ba009001684450190344203000b4070f44034020024a2600104001070861206252100200c140303c43c00e1420b041020720380c0350301c02420501180e100280010442c02c00348465400d088140700c00311014142240d050400e4480058000c04021400c80c50104118544111100c2d900080c06455213030b80c4a0b03070b114001840c9c60481c4602c24860b040300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 60098195 1250 60096945 60097001
    0x3020307060e1908060403030c1814130203010803040314160605220602100203090a05070602060103050f01091a040201031401080708060c0a020304260d0503190e0705010507060e0a0303 81
    0x3d03410884508400800b625584c030b4600b2002440c11018580800c0000a8081c0c000d42a02030004044e00401070b12641e12221102006a03042002e84020300c580e0041c070040000722808400e0341d0440c3c1d0010a800071900e00354200c141800030724160480203090301403020401541c4440030f0510740a680740c4800c1ca0a0981c2c207041400040f6106000043c1c1c40800c40e04581541138003c0e54024051208803904000290303200b41c1400110380000e00103034050401001807103800c0200c03680c2d00c0c002d100200603003c901d440d8510304003c5c030600245c1d4a84200c021908691081d03102d02c4488038402e40c04211540c40785842a210306051040458522441c07001c281143e03c03203012145a80b80c10b800851425160100e4102c07a0303c40c1d030a41580080704076505a07140c070b805001c4040c0703098096481a66030302d4443c40c000b40264440c1000070300f05282c6a50300707040440001c5e400c0706883d0242469034580700c082c40c2400141403004035414440c01600d06a030304068143c1c1000d500b4070b10b4810300c00720403240011 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 60099445 1250 60098195 60098239
    0x1c0903020124050409050a02090901090201090609060507033c0f02030306060d0504050f010507050a030c050a020d080a1e0501030201080c031509070e1206011403070b030a020901050403020307060e 86
    0x4000742c0a01020001001a46001d034072901d55103105009407100c1d909903030000b4594100468009a0b44e035103805a030300856038401592005403900e400e0890805007002c3c00144503020f0054024240400c50400c8014205034079580300a1340d00305400c18480c0700340300006403000c0d4003a00f0070f0400305800385404400c41d40080241c0c2c2c4194005041c484c18072541c05e000c10080c1002420503140c80c09448003d02c2012170a001d928801c0c41c96441d0641d454030b88000040448002da0440d03010414103000c0c80d018075034082109141707450640b8002c030003030310350101100040400c00e03690014464402e50131038001c8080e80226048034001d0322180d034142e842480341401840121130969407841c944000700254501703020400d4011400f4501b41103038041c1c020202c0c0651406e1200300b10150310540c010009890807042013400c2400070350152615070f103028100d00c040d01020b0070707118509130003251000b06644182c06331402160018101c60300e00b50344950180c50280300c03561007402904d0b1800c1c0c03484d120089007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 60100695 1250 60099445 60099491
    0x706050408030f070c0f03210e010815041104060306030501060501020c0a090905030409020f0c011d1024030c090605030118110d020901080f0f010b01020a020d03051c09030201 77
    0x15500d4900881071a1030f9a80c0a070b00d0031105032418000c0400c0c82136814229102039441120b128241d0708512010746e9100010401d0b0b00300300101640c4103485641d00500c4140c11501d01a055850302d403552000801800328407403084070312100424000b42d403e906402140490340220000c00c0929112001280c90368a552441c0350041004071081040b12680d900503203245010750103480c1886e03200d002110a03603000c6560248065800301d00c1c182c0120080c801c0c0d8130190340d0101c0228241d551790306807035128442c803031a40e0031407503480d10101a2100c4554501518056540c1044003154403407400c5114050180121084a0700d842000725240c2030500c22030a203105988600d01d80c1210680d01c504100496180407a001600c000c0c00720300503212620a980a0310804000c2d00c403660401d06a98907189a01071600e10aa040084402150340c0110300300020340c0d0140c0303200385d1420880c2016100b81c4a441100c0900410700000215421110340c4103d503110702c81da00070f201401c0c0c2980501d0a01c8440 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 60101945 1250 60100695 60100709
    0x3050105030d0c030804050c0d080405090907030c050f060403140d08090f0a322107020a090e0307080a0801050a050103050f0f0901140a060f0b0a0e010c02040207060e07050307060504 80
    0x3c0205100424011000d80c0d40c450b10600481e241c40f8003d50100342e034000c228008036960080458280103c0c038040c81c800e03500909000c01402064510341300c07a030106c03000e0710600d400742e41800b8482c21140c0314501140c01440e0072500100580546d40f40071659110780d0955a80056115800b0503444c7c04082601170040f618030004206450150715182c501e454028820090080141c28442203203d050268000800108004d002c0d8070710080c100155240a900c0f20405814041140700c0040c1e44199481b41602d1118400090000540030880e1441c466200d003c1c12070b400200f07206000036400100181601ea0a5031a480d030690744000540950b202511724040400c0480005801803403124103c50b40004a0000424580c00031980f80b400b40609072214902c0ca0748500381030204034081581c01c00101002003030640f4003084144020f00301c00d56400214104011710008405544e110380540d5042e603003058040000c8011864400e030f842002d842001e01038061400d0005190380030b203041d10211112 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 60103195 1250 60101945 60101957
    0x20d08070f031b02010c02100207080d05090106030c09200c030a0c02061606050109050c090a0b0a05040302180403080f1317041508091b01140304171903050105030d 72
    0x16448240c68112080321101d04142e0303a007000707118845120060a20050407034000086c80c881c500c0009042c00040c0200782101c500400c4400005070411049440c0403111240c002465114910707498090f016561010700b040c2e40e00303040840d0340000d0754084c591600c00c1e1100302c00f10003085201c8400c035004205210300e81ea0001d0040c00290fa0062561703042d1107200800c140e107003900c912040c1034030381c40180d02075503c1030307136080180b01c8a00c0034400c05400010f2046030350300f480c400380d0004540000c240a285401080407548409541c000c10503103000e96030042c209c000b01d001412510300301e210212406c0e40060002d1010545465480c003d860140183e580f980d0b46801007030f01e540d181c080ba01105085001d008100c00107a4001142c6c050410903100e40da07840380c07805d21406a61070705c04031400340d00c8103c0343c08100201907a001407056a150201081c6213840395502e003845400d1001c5140103810035000010510504110b9051164000591703032030802c1a6622030007403550b0b40d0000d404507404109 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 60104445 1250 60103195 60103201
    0x304090b181302030f030307030204260717070b0d0209030c040e06060d080c0d03060303020d080c04060c060b041e0609060b0f0306060c12130803120705090a030501110c060106020d08 80
    0x242031840c2e0351001d0001e01181d10500c1e598914520f19881140c2c031400190b40407030103000055441c110450102d1004910715181030381441255103920709486084040c00e07003903075542400300302440118000d050382e643c0c00b80c5484110a48102943c80045818803a00401036244c25034a031034418040c00c41900002042542d0302c62017882803a8045038025159094103104015408008220740c0055890556000c90b1440c9549000781c40c0405c200324110070302c96040308010101c1007402c00e9400301c406030701d003000040510b420320100401005855a40003401c001200c0300f402480c0100c15880911110f080094581c2c40c81281304550840c0105007040c8810440d20a8005208010b035801910040c8081c2c5071042c0c4002c02403800d036042411920804021805400801c2c0e2149660010584d0070040d620340241002d02c044048001070606041c01004510b0b40d400c1e45481d180c3c81c01460b4080007c101e0a01035440d940c5054112005c074140300e1045000200e8458030100704115140c0103500e5000c1e8580f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 60105695 1250 60104445 60104461
    0x41a0411090702120c0c01020609060c1204020a0528080a08040306020a0e030a050601060315081f060b0f040503010f0207080406030b040f1a0108090c0f04050a0f06080304090b18 78
    0x20328050049403c600c1020820181072003108010058481c0c03110042c05454034000c0003a003072040c0180000010f8000604004c86402d800d0110ba0000b0702c00a07840082d0b80d5a031001030813210702d0381c0020341c001209201045c07a03400c81029040800c10803803105550f03c1e68405019a80300c2c0b520a000303103202000d0104100080c05034000d001980842e040540e400c402150100345410280170050322564815001000b0140e094410800005080130050300d4413418820480d0342d071400c7c03201c0402c1c60900c10b050f012104409512110180c5052241c40d9920fa441e0f0780c0384d1445820500510f44654613280c646440085240300711801c0d9a4881403440c1040c0c03400ad4158024900c44580d560420f1311240341d00384800b990302c00c001581021070030f80b81218041800041000000610003491540000c2c0010a103986420040e042c0003011200814513640d01800100540401c0702024400790a284012030000408006402074940721001040440303d040704000d4410800030715001405102c00200d1010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 60106945 1250 60105695 60105709
    0xa0201081005151e0a020a060f050f010e0a0b1c020109120c060c0303060b0406260118020a1e0c05060f07080601030902180a1b0305160509180103050303041a0411 71
    0x1400140c6141e010707503c50540490817a4410926000141c0110501004002140c800d00e080c18240c118100b12620340f88141240d80c030418050409200001e50002e15101d24580140340380c4207002d41000c0182e041c800c1550b00013880710f07604a0219070b113010045041168226907880706500020503c03070303071071920005458000070b40e1403c0d0f00701900d036034010170902c60a074000c000900f02640c030f0001c8101d00c009003000342000842d4810310540440d00411030b80c3c680d00b000c94160102c540340181e944070540b50550340c032a10641940c20100e40c094045040c030340c11141441c0d4250013401981c1d80c6988640741c040d5030807001c41d00705003c284d125000c5203c1b540300358000e0b4940c41c8040e0405202c0b202d01c00303619848071000c82e080007215444a0a80c0041d1002c0c500c060103042ca01c0c101402181481c0d00c40a05041182848400b04000400c8500050340c1b200001503010120920941d12541c490030000d8803640100e40996800c072503840c0045504505568291040c0d400050070304141012a042160b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 60108195 1250 60106945 60106957
    0x703030e10020a2307032c030703081209030c1f0e03030f090f010b06030109020d0605060c03030402010f21241202030d0309020108040b0402010512090a020108100515 73
    0x9403060100d98009405188000d10011a158540382c0265010700440c072046665604c0903c0080024003421000a810007414019100c000319100b0b1440c07038410f4003a1806c0014031509030300d48a403550005c10701183d40010101c0000c1000c2041150307035101b214650368440ca448903410b51348045248003040c03142384a40c001c80515075101003072a01d0a80d1015280d5002910080c2e0715800680c14852071040400c0a449503050380c400a2008070200b40005005002c1482035500c1c0580018040b103500e0a03e6029401502004003a19203440d2100a010340d660012141280401d42180d0889081802100769640e081100086010b440c1c3c80300d10700d030000d08051416003241c903920070461984800401c000f44027800e42c000141c6003406070713401014030b0140c2c101c3c035140c1458035115003070016076444540e4030b0f4440d40100c6005000d40300c620049501d44181500c4503400201503040c080e8451003c134200c1d40d05d038002da0ba004203544075107129010a824030310a0550010703002c4290791204a042020b440c0c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 60109445 1250 60108195 60108221
    0xf0f010b0f031b030106030e061630020a02060a060e0f01030303152103090f0b03010510020a060606110c0103060509060d1e03080702070603060602070e060d060912090515070303 78
    0x20706103104000c66407580081c1c20040107c1d0702e41c54032980899081005d1a4000d40e00404000c0040b01d5140240101404801c0f01501107000541c944110603d41d4901e044403030001c00440d07842140050003510340380280c400d0b00b50541020ba00040765040310300c5881c0074200c0802e2200545c1d203596001c2e0003c04d10004680b0203d4008800041c1d4544901c800140c2401184540c2104200c507250043c00602550850290341a0076072080c001a40e000c0306681c10349600b41d0b1215195035504200340e00c2c00c102172030028007860030480301040d5030341d10a0f500d00c4000800022103c0410002006400780c9070b07980a850340103c44100040c0852a041c040103a0310742c000c05000070013082070302c0706132443d8210444c1a4040343c086c0701400112581000a0f8008003010310f420001c0c103060500007515241c00b486600f1000303001201160303103544c1e10540c001f401f5521002c10031205410f45040c5000480360007003440071406283c1e00080f1810408080c0b080303a40c03c038070414540f0440c0da0f401e60007030031140201302d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 60110695 1250 60109445 60109471
    0x201080604050601110a080a0e0105070c0312020708030a02160806150f0609030118030e0909030304030302030406020f0304060c141615181103010b100203070b06040e10050f0f010b0f03 81
    0x81e44005c42440000c400034000d810304d036560081050047d083d544101d00042c1008010404070b0f000c107201c401070600b0b80764001e000145107000b0b41412460000306401c840700034040004c1088009800140e8400605041c51a419403180c0d00d0900c00e17204c040840d4200d1410f100702c1f520101e2850308000e55000203600070100e5007020002c001081c00c442e407480d4850403805a4480142c14140c0080a20b0f0008a0880e490030051500014160301d9000c0a0030007018141c010002c0740410602c0c0d01660903900811390f255441c4e152504119000d80000c2c0c0d9020049040092445000ea4840081f40ca21011810a24024554940d21401000c02c0c2d4614414469070394001d00d201c040ea49009000d900c3d0090544800c1c083c0d8103002c050031503c81e200e41c1841401520651044c182d0003106a07940c00b50010b45200040d5510000700f00500b41c0e00010044500640000b680320304000c4d0b00c850300503415a07c5640b4940e84002800301c103520b081c000e908580806018005414002d00000d6a00c18000140c131 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 60111945 1250 60110695 60110717
    0x310218210f0c0a050306070c0809040612030e0901090e07050d050106030c030b01180209010e0f180c0c060a020703051615090602090f0415051504050303130f0f030201080604050601 79
    0x2141007014108240c1800c0d00a00c100016601e072180000001d000c0c03c4014210317038103211a01419250340d21100801081c40400c3c5943d241c0d0300c030380c0084018101540c0c121042c4840703240003000302c3c400d034107010b20583c3c210001140c4144c02d4070941c82d018071400d0040c10090f04007003c0041209100000322200d64903900c001c00000d0345648100000c612038084800310354108040c0c072000107140e09104048510503c9032020b103a9004900a40c4440180c910810a044040108010b1284030016101502f48a42072000e1106408020480a2b075064151041521109040c0e01a031180150160000350700380f0000180d10058904180078500c0b030002d6003140162200f41300280ca6440201b60390596010031007104a0410707851041504c1c0c0201d030100010b1444400c0d10000350302d6809540e0280b8034007284410380000040c100ca0281800074200ca44600b26180d00315001c004500400005441480b4000762074214447e049066a505840d00c6c88070f43d0f01c04061100800c40200103a0402180c60b440d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 60113195 1250 60111945 60112009
    0x20a18060305070f060f02060601020c010e03010f050421080103050c04020a1205040c03030e03010b0a03140a05030c010c0e0d0c0635091902091b09310218 68
    0x100100802c022600b440c13480b0b1a003500641180300f880e03000300075504241c040016680e030205100200720406d080802200c04020080303401041403a0611501901d0101804280a401d8818080361a92a850308100c80031106084400d00000c3c44000c1c00d50b4031035040820140f40c280c015100e01460f0f0324000d520111021108000e880c401d40d01a50602c502c55001c1c000d15500c0702c525046039200764003e0003855016408203600f42080d00c0082d00142250702e2000e02203005005041040360494112602c800304100618001e007201d6080002090000c0b80002032800c02c10248800c0682040c02e0340d084600e003800036540c5101d8020103041c070300103c09004400c0a22000e003c00307a844c8036400704030240342c152101441c004d00280c00b0120000320f26601001070b91001d14807680800c0c4200401b1100c18030909074401401001142e640c0300d200a01c0f00c501307901032103100c50601e000f14041124148107415041d001c134403c1c2000402c0859404c2d15241290600c054119210faa801000181184034654 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 60114445 1250 60113195 60113203
    0xf0b0d030804020405100b0912030c15100602060105091812040605030a050901020c0304050d0206160812010923070c02060a090e0a150e0403050c0a03031413020a18060305 75
    0x1808401203020300c028041941418444c0d681d1000385105105c0310641482000c035180d004440324184100203185100008810500942f0b100d011208125540816004d0905506110845415148a0a10b000020054800215141218400b0380610301035200d510407110042050319800c44070303200710014003a0b010240001080140010707a500c1e80c807405c02000a6080d03810250403014582c0c0184600c46100e6030220480301201d8045400010086071403020810601070014034006072a1410080b100f4409460020110420084204046070b03803141e5030901110040800003c110000c110143d2a5558107004950413180e5800c00410020070303640059042e9101880ba1030014000d041c00b0440c606030350501c0c54022060314810300044001e22250020312050744030741c0016a1004c001324003418084d40403206480800020b07070b4100c00c41c0d401e000d030107001168900d001c902c01c80d50002e0b40c034120075480070303d0955008014595940c5012400059660720b60403001440356140d00010004901708 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 60115695 1250 60114445 60114469
    0xf0712080609090a03090b1c060801060806130b0604050a02090d080c010b0105030f0426040f150302130b0c1603050114010e0907181b080103020a08150a0f0b 69
    0x95100903952600d10180904488040c210700f1407584110700700d01c000ba8010200700151800400096150441299039080c0440341580000c0014070b050340100d0300c60810341103031003603e04503000c68400e40c441800d075145180c000038000d04956407070300101b0030b285420703085242c01100c0050058100781d40700f0002802c520b40c841c4216013159000130200b00441e420302402c01600824240542540780843c0407204071326008200405002d446d000c030011750001811030400103204140e5264640b502c444c0850b48044160040b04540044a8001c51140e03100740202c940d480603100d041030049260a40b070003059086211008440d004441d0f52807010ba0314000c41100460084d400031401440803200501443c8040c3c0104581c8030090040240041e80000c40108442020034941100002e85c1001802030010303001400141c0782e44044105155030000009060701e000302d405409e429034401340b032642c603044020070b100329100500024130101c01941c0a11680d00341d003900802c024468400280c01440c0300c2c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 60116945 1250 60115695 60115697
    0x90f10030911041a09040c0b030709030606050d050c0d030302160b0a0501060f0c0b0c090405070e090a0c0c0b061201060312080604090f23010f0b010210140c0f0712 72
    0x10312800341402012008502e20042c191010444981a030581810080192042502448410700031504001c1d0400407a401031048042c903607104d00327040364000c1021242d40b01c01c4c0c4000317003480000300f00d52801c500c0c14010250320000601e008190902886001c961690702681410750a0060754034600a055115540e107205e030811420341e2400c51052012542d042e0800c50400003448220400a0340007042d03c85100d40048150540b42d46101d14007882c0e1144c4201d654002d4204010301c506140c2091000c16560811035038910300b9610110702c8401c8070005102c9a0029100a4460f00450000a12180c1111010f80b040c010012030084182c01d44a07207a000300c5184110b03406005400340d000d406103030065001c580c18009007005846001c2026005000035000b40c21783e038030140985403e138200e1251991051300034840c68929820001c0140890302c03074603016000b1450301c841c8082c0c9501c01c01c00d030504040c15031181c640b0359140d0080c0e02d2b0003c0b051070b1901c403802c021140100d86a42d64103803014041d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 60118195 1250 60116945 60116951
    0x20915040509100f0603170c0106050429012d0306031407050a06030203040c170a020301050901050714041805090304030f26030f0601030f0209120a03031b080a02090f1003 75
    0x50f2035010411503850350081800e4900c1d0000500018404085002100103e004815120051000154010169640300325486440d02c0342000010000361011a01040d0f600014403006020000540c0d0328841613244c190745080d21410100d0428072910008280041440d00040584d141d650302c8449040550007015a640301240400091800c148880040c1c00e0f140750542c2141002c3d034034001210722a004405001c4942420111525001c000341041d80b50014003d01140c1490455207000b020262401c00008220000315002e41c0380150485003150522013001c2c4600469502c1d1340300500d005030203030000d40000c010000100d4045010500700394001c94026900c0d807441401d00e00c0e0002041211099404148200701c229600702f82038980c010400e0034089040e1882080303460003441006052903210002400b202000c000001d604080c0910a8608008615880c0c01c2c000c1c40701d1001c4810300000704a4030000300c01594a4028003000e2001520b00a04070394040c0005549402c00301c51080001c1d9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 60119445 1250 60118195 60118213
    0x13050421230d05060a030519020d24060504020a09030b1e0c03070207050406080c22110702030d08060901060f030f020c061b0307020a021e1f1701050d020915040509 72
    0x40c40d12820b40c00c030808444c03030b40e501403450341c1fa2600c45196031903050705940800c1421095490741043e1004c0300f54460320070083c0e03101d2006000d2450b824107240d8562036260810102e0203007400e208803806000070351900d11800d855666111040c5100504000c2800d243c00d03a111103904120612a0007408079102d041d4982c900030030300a240442d40d034800792185081080400c240c103004255005400b00540b1064503404c2e06c1d00c01c040307070044481c0707000c181c0d02d14008050760f0341100d400181c11a13900c2142035a403841404070742150501300c25100d00b07601064440c010052207024408a080e02c0c8042c2c2400b08640522085840481e00894103907512600203500304482140d1481070010b80d42c1a10030300c03908504000400a64529035840f000340506a2180210020800c4202400355044028040c0a00040040b980b0386a01c1c85031000002040040d00c3d8616032241915140b4140c45d8003400c040c45c6c8207403d030204920034201900d038142c01c0424006004668449009192051704144020300d02c0da0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 60120695 1250 60119445 60119467
    0x10c02100506010203090108010b03060406050a06030f0f090b060607060b060301030c050306060103110f09030309030a030c14030406020c0d03030e0a03180b030c1e19030b1305042123 80
    0x748000749414115002000300256a80e08282a5815601d82452141d101d59400000ca4000c1040b900096881283c4000c005941c56050304a00c5007071501030420301107101800014410380317800450042080c1080400500c00341000005030007490b0090724080780d110810400b0500da40e0003a001500d06d049060024845030804122143c0c0021003807070304205a6003803420390340e50341c0500c007030300b00184000241008490341c081060300c5940e04003d0030740d0b52200352840c02a0614240031300c00c803071000c0716550001c0c1d44800801035500b20760742a00940440c4402d0000c002400e41424401c41c245a0307690b0860003541c808000c0171100b944291030304401c07104e40c2c46581b003c4d5900350388100c4041c8010400c0014104403803050360a460b070f00c003244400c280443d142d10002c0d070288442060350765404985e6029180d9060704181d0000c0401d0781c1d4800d0008555040390162081150013614886603500b00703c481050301948903505010919084641e48064940070907071702e498410b114845800420240305036 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 60121945 1250 60120695 60120701
    0x70204050906150f0a030203060c03060301060b0f1207090803030f090c0406060e0d021503090307170c0c12071502010e0c03010b031c02010b0405070f02060105040203010b2505010c0210 81
    0x8034040c000d0045103040100068118082400d080c0504c100f603940d00c0440d10b88004480c00b031540242a41c1403850008902840b980049070003a219600b40b01000400700065001c403902c120300e20000a14204040b0202040c0a03c044c014004001c11340340300090050b41480554012440880680b034607040040d110f51420080e40380981c8203e18015042014035003154420034078000580f44588103e560340009040390b0752590409041c150000b0811a201c200440204400307485107402d1403965a00501003e16400741d082e42c2451607000742120041031402011810303003000002c0407144041d40710f0f100c01500c080d04d10030090160703443d0303811011500801d20811400071401d5001b0006514820300003030b501c1c403850301c2207003282002c0d46409510500c01e402c03060040e4170140c400d00a134248480c000340045000a5080c005004650011903075140600840c1d0403203110104160034065203400e4181e1b114110354200d10018510840d0100041c820b000b0088040810303005404200c00d40580c0c2c10030303 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 60123195 1250 60121945 60121951
    0x120a0b130609050405010f050c07060506030a0c060804031b0b01050904020f0a08070302040506030c0108060108090102160b16030608030406050f12070918091509030215010801020a0906030524130509010207020405 93
    0x10003800c223000c2040800b80c0c541511151a081100030800d5119240400d040c881c05a501411905000c04c1c0400e109130010a420b029602ca070f41d482100200c20000340743c456242e40001440070798000010072440c0ba0a070070385074120703000916020102841100041a16040794000306058100d043c0800541c64544580b1340c0c071104c20788c058240c0b480c10750002440c201d0f00911090600c030124001c5100c4010075030569240d070100c441000c0c0040c126060200d51a00120b4003a400a2180c0c05104002c6120740500001c03501c40d140218101400d103401503c103604401541040340c41c0a126200d190488810305500038a80c030380b500c1d0180d50414030400301d114010308032140e5081c20048051b001448072541c555107020400f200292440071803504a0400c203801550701d03100c40c03038a00086600041035000381055549030b00c0f505201c6584a0058052760b800705c80400b8030007000b0703240060b0038070081a80f850318500180f80c03a80944080400104803581607030210030aa50108211085017424401d05030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 60124445 1250 60123195 60123221
    0x1f08070f0e0907050a090f270b0d08030c0f040906060314040503070f0204020408030a120606020c03150a060503030c0304060f09180903020f030c010905060c120a0b13060905040501 79
    0x6035001d4039101140c42804064a22420401d0014042c4904c0f80300d644008050100702c2012210076030790364002c01040409411441000b040d01c841d01a0f41c00081c402c40004050180a40128040c5034644003101d4000030030700d00c0b03a140c0c10441d840e040c107114401003011341808400001c4090424600130100d86003401c043c12402e1045c010310001c2034001042d10511940f020360000403112900c00315000c1d0145034056035840c48041000c2e0f18081d00490a45008109040108201555400d08903030750354400f4104d0760140c0144c1b240682c103948170500c290b4080020302001c10526607500220f4a1584101c00710a800c0d000841c05004c140d80c030511021080c3c0e031601c0c00d0300885040525400d11100200708001c0801d940b00306000401d030013444984115454001942e03118080c5088032070181c20002c074104c806004030000104c600000c0e4042c1c820003489902548025075452852100a00d200e42840364822215804d0f0f00344072485003c0c80d405405042004501420b1a140090a50345540c03c911 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 60125695 1250 60124445 60124457
    0x1050d0e0717070803190306090203010e0a05061009090b19030803011d010e0105060c0c0613081c080c03090703081303031205041203020d020f0c070f080a020d111f08070f 75
    0x40034180000c05d0320105145420316101d00d09144001f5002050503920007180b0038004800011030043e8078143e203118603101c20f4184969512074080140c50b150051507900070460004040c040341c1015440859074000c050802c000b03151410760340813942c1c038543c2e1040b10808000001407011280301c03184403519440c0044200c07669414902c605045041c1409001d00030000442c0302806500100400960748401810103591a41616400c0248a80340d0140100d507110349101c0c000074045540c1d844951042c0703591441081e441d02c40101d01c0e15400a00341c1c401900c146080400410002e0004254118801029084861a40c903004d010808250104084645004104800314245a030b21440c0c501c03291038010381c3c400d04e0300b00700c0000f400741c8031880c0b030501c2c408645c50340880c41c00100e410640d04460b414401603642c072552140c0d10380000c000250460b6100c0c030040000307840d03821100340421008000c115045c2d12240315441021404c0d5100001903514001e1009480d00029040e580c41d00500d800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 60126945 1250 60125695 60125699
    0x30f03070b0103030c08070606060908010b0a0803040303080402030312011401030e0109120315210203010608030f0702061605030d0c0e0f0102120309010204030f0605010504110408061501050d0e071707 88
    0x4580818814031001d424446903580c1602000504400c40d03800030787c8000208606602c1302b000600520312805200002d44c6000c15001c442e10708142003104561039000254070701030659030101e8410300d020303108913003600c002d016401c0008c0120b0301e0f25010b00103008260308140c2d1014001000c0d5001510b0ba225244d00d40202007022803941920030b54204000c5c01c000c20101100c0c40402c156034600c2c1e00c02c021903080060031040080305080140c280c180210000e01c582500c0d018030544a10461003421204034007080780c800141803030000350064445016401c2031004464071014207550080c1f0449600d04c3e919102c110741e4580000700d40940d804285c1c0c480c0c00e580c01c0200080c2d0b035000d004200320304854022001695101d82501154080d56114005a110b61028603000000c1d18080c000c40c2e00c5182042902020305140314107840c21a0042e0009010940340d600301190265102c00c03c060400008014610580d07415000e13210341e42c80341c540200350355031800d013503243c43c9000403030110ba0340c6d0494281 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 60128195 1250 60126945 60126953
    0xa02160603020d140c160213090807020a1d0a090c05090c280c0f02042408120306060a030e0c090c0a120c020705120709140a15030201080112080f07060605030f0307 72
    0x3601c0c0003012860700303040035261500018007212090316600f280e08d801c20500404001301d01d0081d00c2c24910940d207944040c0d03210321a401c00c1080000303010141d2170032000041c407640706c107810071b00390107025000114410362600089801741d8801c440c4030301e04002c0042d41020b01030a40000745054031150f4502481d5038240300008000e5a21000c01406090007203c03010300359503d503845160300701d01c1044c5800800400c0b80488a44540d24071690070107020b5003803440d9090920720f045900c90200103001c0d40c582040300e074048c5e0042c0002000958a846110b40c903218a880b03c04440c0d008a000080d030799110a060140140041c0c250864000e403582410041e003003030b5800007480410b40f00e0803203218402401d01005a89441555440450b810b403c008c469510151410002d50007190b40d082c060252032400100092007003505d00c4024001001c10004000001c40c000c100d51300a4454080c1c2d80c1307001d00d9014041c04c1a007010b00107545180d55000c041207079160400158800d03151101c040d5040c400541c032 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 60129445 1250 60128195 60128197
    0x219030503030604090c0801060306050907060c1110020c0a1e050307050a05040c110607090302040c05131802071a010806100b0f072f010806030a11060a02160603020d140c 75
    0xc083d0161744c4a5041000300684c090740400505410f10080142c690340b8280040581810380f0258414000c1c084041045071280c041e000121303821011200400f02c0c440b06200300d208546121a003180608425507080c0d40c0d54040c5200103168014442c2220f82c5000071550076000d40e940074510a602003a400c214545513001040c044803403c5038000303062541608155104465036031009064040d900c1000034050f00030745000c00340e038000c1d10708204440d14404103485600c244549201c11000702d074810820804c000000c00c1d50300d41200e80c05800c04082d0740c3d8204480d0500c10740080d0010044c0011f000b80007003041495884264419240c2980d4500503c1c22000c2c842c0d0000c1180c1c88000080100c2441100c60b00c0e070310481c10241d80c45246c0d65403e42d080e00076225001050380015016000b10b4068a0001f0b2610480ca81010329043d02240c0d1070104004d82d0f1001d001041076009815890ba0403030401e81c620030041c405038401603500c0c61080000811a03844000065000c43c00400b8010704c40e0f0102c1c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 60130695 1250 60129445 60129451
    0x220501021204050a170a02090112060b0d030e040c18080106080d03020313140309120c0102010c020f0312040f0602030103030f0909020708121008030c01020403050c030106033203031003021903050303 87
    0x32405088004000e440386d003080e00340580a034100b8a1000006040300d4040c1d40002c040780602410031101055004000500c0e110b818060001520b01c041030303009240650050400c015a42889508607050754984003801c6802e50080c40665036582003080b0ae03040c00e0000c00700c40e0a85140451452a10594074803090b2032429021b0001465099050303003500042046420401c0020504183ca0090b180007507a19001d048140c2c2c015401c103003d0075001400012030100043c10365000e903041c101410400001450010025240c6070864100000450f40318801140614007079a1018959800445e0144c2440d180e44c0c80282450700c10089840070a14900558044004644084050351032709140c249610983e50440681c5020000301c0600810056004001f141c0c400c0003511060390b2040c1c01c0500f20713800307403001920200600c4008d1030303500582900a40c0e50b046010080200b241c402900e1859034000301c03903102c640c4809002c203000350314240900c88032480c00320034400c500b64159030301d840d100d000203 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 60131945 1250 60130695 60130709
    0x60b040605011e050f03010909031101050c09041e02030705030f090604050615060903070f090605040b03100504050f0d0c02090a05100e150303070b1e04030c1502220501021204050a 79
    0x210303d4404a0714801c0040380d00480e05d003003003d83c0720358607801008000d1004940450214404682c0001c91000600a89202e207580b101c805040915034400e000c0070f4651040c1010103035001d050b00c200640301d203201960085026030b0701d0941302d1070404581d0f0f01c03900e0040c00a140e140d000401300000034a0001d00300354820340001001580101010106403e0702403000301682c90f0007422004503059818600440868019030010302401d980d49092000712038025210710b800d5006520404003603141c0b03030003039074001c0e1042c002c07181004605400e03107081440790111000000c1c0300c130411006600d45880321907003050707410300200101d0504442000c6004001d1003040034144c100f10000e40e20704030030340040414000140540741d07100041c2c43e14151942040340e03240b03030f410742000070303000c0c424100e6058034031603a4140c8503201144929228004200403115074000025002c0041808000d2074541440502003080307100d400070b5003817000281c01c00948480c4d040a2130760510040001d41d5812400c00c0803a600 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 60133195 1250 60131945 60131987
    0xc03050613201c0318140303070602130e040501020a0f08060d0b060a121a090d0503040b04020604091a03250b130305010507081005040507051b07031e060b04060501 72
    0x96840841c88002503c0d0003914000a01401c0d0810b15402c8840d2055180c103503440011407540b07a81e104000280e0042000f134240d4010301c134150005071694000c02c04114040e1014031015a1401c8080700c807001240d01b214140d4001c941c42c44140c1d00078000d414049121705211aa61070080c0100c0c000c0d68100e50003600c903603105400308190743c030b801d041c3d00c0160000038550686844a42040c01a0100a1103240842d0020600040401e480400d0400c154511640c41c6459500c69440e00020800060801d90b8003a1301040001100c5a0703520030504d412202c1146043c00002c404101030504044020800ca5004030002c2000c4202c080c0c12420291102c4500c02c40e00d601003103d664403c1582134000920382d6103801d007848511600710072002c0c401d00c0540c0404803c1e40e211828002034030001d40342d59000c201c042c4400700300c0480d40748100000441c1141101c0300b44d40d0b41c0d107802c03010589169444401d0b19036590140140312880c00b64481d244c40984d800d22905282c640000c042c4444049400c0035815 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 60134445 1250 60133195 60133253
    0x7050708071a0a0b01020f060402030717250e0a06030803070507060b0a0305010506030709020a091502030903100f0b031603241506110f060415020c0106030c03050613 73
    0x104070010400685802420882c9840e240c0814002003514060050161190042d40080d020002440510480d80a005007507150329000310023a5540c010440003040d4021240d002c006c03104005e46103043c221180310600480c49c5880842407041d1400b1f0a44000e0030300b001030904c0852100c1003100d40040040c58000d030360350001e081050040041607045940640f000c00d0001c1031040540050303000e90b01c11015a2111640c400c00e03c000c81c400d562a60001c2111600200203444403074880071601e100e2070041e01e15201c1a00000303400c01c001c2020b04140281d440b014404a481d41d803165000e050801d6004001021040e030070b42a502995100c0140310240d0800c40400015001c526050040b424070000c0c00211031810507070082034010700a10001560410304030081c803100141e0340d080d000404015003026112a01c40c400300b02c6204103000c02d00c0b80c003040082195002486140011070050404040756801c5107030140c1400d801515212060300d0440c443c01c00300d10381c4091140b58503010051034500b0300c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 60135695 1250 60134445 60134453
    0x2100f0c06090605070809030304030806040b01050c060f090c01020c010206011203030207140114060109050f010806031c0306030c060905010207090207021504030501090203010615051605101b0e0303030705070807 93
    0x20100c000010a00d5080540040030040701c0d400a501a00850b16040c0085d520844455942d010464000e80001e40040100300342d4103241c0e01c04081040706143c4030340703402c500e48040c2f45080015106110044060030070400150130a220030380351042e0034030280000c40741100000756220070601442d055a4200811142018020f5044541ca140d111804140110307140383e94030300801890000b4003690b5414000199950703c2140a241a01c1e001032080c5101c0424000440d08201c005003281d401d8819520740e8440c00410036955080b903106650041a264150b2034401c640580691120040c014581c2d800e20407680c010231164295218071400603102e554500000c1e002d900c01c1d0095100820300050007005001c419045050298020b9000f481a280ccc5e038105c0207140c001c1000303d100001d9050004c5c0201541d48650f2504d0310b4080c108a0319001400c20303841c012200310610703c03070003201c4040512000c40c1c1c200c03103456010301c07085014605514102c1005062446081c40080161400140c040d00300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 60136945 1250 60135695 60135707
    0x60e0307150503040b06090f04080a0c0b090a020a09060e06060f07020d060c180807061b120503180c031b010507051f06080303160c1a0403020304031104050402100f 72
    0x100465069a40944071200c07001d0041c0c2d100703441c20745005800e8400078000307003000c1969500940240c1d91174105903070740d0745900c8005e070000614071382003260780507502c0c01145000c083ea41c000c076100f5020705a81c480e280304000d0040000c1e0300c4200b80310b0034032808205100170301d0800ca500603c240e0740165900704e912801c024600c16100c00940c05404581c140b1b05006a07070303201040102d51034031152080380d1303901482d070a07181441c41101072075442104c082c0701e40c41c030030350743c0708010012414040f07241400740d0b6070200d03030605034000c0e07038001100401000302051104907416107214148018140010a0001007510f481a40145c00e6414001905031a0780b0b9103e0402c507080e1075000429900e403200c04000380458071450003541000c4c1410880c000c60b4642d004070442c1c0c09081a0001d43c01c00d6a041e0000f40d905640841040d00c03411011090203841c44404141548243c1c429805580e5a60440c5001e4101c071195a20040c0a10701d48410400103031290312410050404504040d00203999000702200e00c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 60138195 1250 60136945 60136949
    0x30204051902030f01061d030c040b0402090402040b25030f080c0f130504061a07060e0102190c030810121b12051b0108040209010b1c0e060402030c0609010207060e0307 74
    0x1400b40b00004206442d00a1003d04c1e06940d05035661a841c1c03450f0340c940307a41c04400610810342c160407641c40c10000d85019440110300402c081c0000d814005131400040c01c9801540c030000e0300c85000211710703c91140c5c4081004417001c04403c0e41e0206822034900030422200c01c074404051007034590105502c07416510648601c0d03800b0341c0450b640c4100c01d0150a2803448a8414207000d1414048007155a81000c8144a112180f03000400d00b001e06a031146c4010344410040c424181d5402c1018100c403411a00780b8826010803911411030000d024680200140002001e07102c1d0245c1d440700621007000311145500e4900c0c0c10180c1410180381001100c1c50418940e4841c81413500c2c0419030004201c00460300c03040036008a02401e420b105030000541d9802000c0b20003c0d032000c00d200060010b400d0310400b420280074001d00500c08041140c1001003103413240201c881d40d540c0948200401c5103400c1041e01034070b034025250b80c0d040113048000070f0f68405280c0100014442c12400c9604c05840410810340 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 60139445 1250 60138195 60138241
    0x190807020901080a020f0402190e0d141b09010b0301030f0311070f0e01080f030306011206150e033a02190c0f060e030a1e0b01031202010b040b090103020405 69
    0x1540c0d181003c03039403040a10300c200d010340800148103c1c14a814401e80b22000b0805038a0103402284032801c840000480540c10b40c015140314070070011403150440401051000c0000340007006408410400d03100a50954620510b607100046c05001d050000340e9044036404101d0b500c2d401081e16040e11209000b10044d101e52042081c0050891118203401003151003040210000c0d988461415440f002c00740700703065107039000304041940c0d544655074112400b081c401c0d00090480c1c440c680001900e680030b8141d00044c13200900000c107032409011031800c043c00c5056801d0300060000c035801c85040520a0681202490794480d09024001e21000000c046203160105080d40940f6003030764100f03164000c543c44c070f03601c200e00454100d028080703002100720000c00070b00c0250159940d0800110204141081c00310038056400c0020f280a03400501843c454640e0345516003241000030300f12001480124440c60403d848900251185805c00f41540d4042c3c1e00030070650354604020080c400072900c40a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 60140695 1250 60139445 60139459
    0x1080622080306060d0c1d01020a0b010302060c0a06020d1a0102150415060315090501140f0a020315060d0c020f0a08070f17030a0e0105072606040615020c13050919080702 75
    0x600c5c41d83e1f00c40982c4106041c0c1032031001d00551002c0049075903041d000320007440303041103100500141c9001c01c09018101c4c5180200e0f4205942a5901010b81e0010b103002103641d0344400c14440c5c0000c0c03112404c03031191001c0c0f00810020946021424040c4401f0344003405410f49845905880c400039002030b00555000301031441d403000090b10820003403889501c19103803940303084018240403810300d03d176a00407a41108544410b032075180054000b9032000c1d010085034a2808a02030352911008040c0c12542410a0002420119a040a420650030400404072900200701103400680d44000303842c01d56401501c0d142000d15185000340d1480540b0030792a070040d84c003004026507a80a50080c90b0120f085000900c91b41c1c50f0050709459020b200726140713403640f6000c0b0314013900c41e22040f0b4a9900c0321004102088030303581c50700400b6001101c0092034005070811820582e541c1005008070085c0b07111100204441e140c071001e090b403500303050080e1003a0403001040b80800d20620206072241260020b10907 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 60141945 1250 60140695 60140711
    0x1090c1707050f0408060402090a050f1506070b0112060507050406050a18080a0c031b03030f0f03090c08010f0b030a03050a0507050106050411040305010b03060702030901030b0a030b04030801080622080306060d 92
    0x5c80d0f5210f8040310124490f04425002178000c2041e80100380c01843c003007019907007a131030700200a01800911241c558003c84240805408540d92801144c000c00e10800354039811b11040c00e0013819a44000c201505002080008000080e401001c0315140005440e0100940e040b288400c094088698001265485016001000c1c000c0c81655681142d2244580c0d130061300086100d205e40311118800900031442c425201c0e41101c5c0038880c600c590081510b000628020980d070750428880341900160f840e61756030402c1c101d02c01c1a5200d0050140011002003030f41032441d9500902d2840b419424004104001c640d40007004000d400c4034010f004000c005126014814003c030f00e1507041703803109442c0e66080c510401500e06006c90001d000e400150301961074036075200c0040d03001e070516207820f079080b0009240003c080307610800c20740d006500c0382da0303101e41d55403410740c807580741c4000a00841240140c1000c044209610500308000c40e542c03003481141c503030f550b68000400c0c1d8007034000d500c15074034101005 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 60143195 1250 60141945 60141959
    0xc0e0711070522063303090210050c010b10050c0f060405060c0c03040e04050a0b010b090a05040e10021303140319031503051b10030204030b040204110906180901090c1707050f04 78
    0x490a0b00c842c511701c0052449800e0b0071015142c2c0707500d0180d0407807151040501102d2154001b8030300a03100c6000807070040302d118086070750078036100307000340c000380700841c00c509555000e00038114511442d0004001909090712455101c001c00b40c1096100c18000850070a811002e209560007000502c0351090a0320b02070420340e4654a1114044031240b540f00008207285201d0360a54602003c050104200c25081a0a000c0149040f20080c901485400c0e000f0040003144d00040c08403d4021011054403443c5140200c02e14103d00400004c98009001c503141e10240d9490030500302d50305180c0071444644103a031110003810542c101a03d21300032280980150513506404d4001da06065660400840079100110103c1c01280401442c140b1400d0204002d4030703140d003000c410074840c032205a19001440d00014456444444030000003400d614811605242512246004002c02e12090210403190311000b00550903004c400404400c602011441c0300b8801c1c0d05651883c105a403e8598990f2034007a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 60144445 1250 60143195 60143249
    0x20901180f05091e0a09020604090603030306080105010501020c01080a0203070c0c1211120a0311160f0905070f0c1b030203060c040f080106080d08040f0c0e071107052206 75
    0x34903000e00550b5001c104001ea00d000f007500e10b40141810b04c200c9440302800f5402400d00284140da22920511000c111600240f29000c001c40c800d40340000d0701c5107031548550a5401c164801410354004002ea564142d80008205a0000c41407100580d6555051000d031030320000380300302a107060540c80c030105401c402925841c100a024050000d2a510580100009002d1064810a00b50420100b0100007805504904d000c1c0011009a134140c0300110501001c0c64590350082100180105003003142d41001d10560740c001002e8644840f000041c0d400107420f092800700010200000c3d13001c400a540c148000140146030300806a038100e0502c054007003117581080c081c2c403613124005140040c0040c4140f0428045505400c09800412030100c019100b5460051090310150305100740e4100040b0100040f8001d4004141c00d110681030900c07004002160348080b0315619400402d0600050b52030241000c100c0410390710090980081d00e1081e00a0000b5a000c4414000c0f041002c855100c5228 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 60145695 1250 60144445 60144449
    0x90203070c11090c0a050f04080607090e070f08010e130b180106080f0a032012040f050f0f040b042c0c060711100c05030c0a02040609060f09020901180f 67
    0xe811110042c2d0309820031403580c0e0b05503070f50109680100b102101c1700303000b40c016184445002e101d013428150f44a4400c0d00300310003254103400082c5c06010500c551303056400107507040006880d110001a0031000050000312040c0210388942001a0001d103038005440c0c142000d03190b00c12042c1c0e2480c1031450480c903444503031040c0300120f5428580c01142c2038000158542c490b41c8010020420344000391019540c5c400c201592410380f8120418248082c001003221040322a2030130320965a5502d059201400b050322034021501c5600082011245030741c40341800039600d14202c0d40003030000c8051000400404d111290913190700c407500702c092102005611401c20807500300090b0794101288400b00495485004001071055105c24400c07007150410102144100c5083c2c01d1500100d040794895910b10b8105501510307640d40081c081008600b003500800009120380f90007400003d0819044030403e500e540108140703035501040e0543e1583c495a85d03890b103450700d50740c04d5800300d0f01d4004444103c5818 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 60146945 1250 60145695 60145703
    0x120a0318050105070302060406200a050403050d08070509010807050904060b09090f040b0403080c0913020910030b030703030c1112060403170103021c03020a0b0c09040b0909030403020910090203070c 87
    0x25180c00101540501c0c01c95040750340c16070241c0759542e0703155100c0b0300506200c500045240c40070380b204050001020020480c814464407207907161440c5151162500408101c80c40801140c001404155a00f0002381d8040e0307003003400c2001440d42c0308542147c0c0c134060320080c00d03407241c1000c1000504205150040082860039215005c5942c0d03012803a10b4034400c00d42c0c0040644400c03500103004603100311503081c0c00502da165060b280243c80c10006030a6101480805400b6500090b0341c2d650303140c9034001c81c41d9048682801e1100d421290000794840c070007444041d00f881004034809003042558008128916002003200c403504080320700442c0d031082c0444088011a40c1c103000080c500e500071000310304030ba41c000d01c42000d00c5100c040b00400f032804407008400354407a0190440008800c1d07101d0341c0c4185110144503880301c02c42e20810042d035000131207442c000c4107000c4c1030004c400800300440b8207480e015107010303495441c2d52100c103440ca00142d10040c0541d1012040c40301c090f5000140701d13165806 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 60148195 1250 60146945 60146987
    0x90c0206090102040609030f0f050a060204050111060103030807050d020f07080406020d030207150f020d060806070f080903030c070311011401030c050423090109170a080f010b03070c02120a03 84
    0x3419210328204c0c0704a010340c40200e10051030400c00030b038500d522064854803c1d440c00c2581040d0760b481910303000d0658411524140c01080034010365030f2058080c059000c10000170411940346440150141d000581380d0000c102e400a00c5040748225601110b8006c0f01400031141d8400342400e14101c070f40c115024070b80c018014980c1c004a0030b44a8020303103c9407a040b01d540d50180030005c504600400300b02c0c0400c08480d80911000f0220380440c45600010300c0004060300031440d000600070300d8241d400c0003d0b02800b8a00d01840461400002565403181c0301e900d00c25550482c505040d6038504400240460642c00d00414207180c07500a04000c0c1260710a0510a81003a1500100400c0d2990030078801c510700140302001807581c8002109940090052000084041264440c07440725043c503040c50001e403800007038207181c10754000541c50b4803003542d008401c0194140300342d020541c400a4103041c00c2025404c1240d040d50388081601c008101c40030f04455660380c192401504402d02004107001d640a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 60149445 1250 60148195 60148201
    0x10030506090601080312070909050a060303140c1b0d0503030a0605010f110d0804060605031608060601031b05070309170607090509010f1a1e0310050d02090f0403031104090c0206 78
    0x1002074824140c49031080614144500c020440c03806c000001e100e542080311208000482403040d10031a8007440042e0408221030f1f0039410013401e040f0240101100d94030302004404402000800d10303a030654848800c0c2455415150f0004801040c08980a00240030010612203510318540c00032003191400c0c1c9991125429199040d950003002e140c6e9600182c11810003451114810414a60300c00d00c034440000d41c058a480101e0705d00f800808282400c1481314205010613281004010ba0110007440d0034050a0b04111060041c6104620b00406024000c40c2d54410580600c403020054019018184001058803210681c1c40005551000c0482c11050b004a5a403e240081c58162804400810700840c41d21603c0e035143c00c103081040c0000c07901480415101102c0c405003d41e86074151022135204d0038209c10fa10800c2641794400ca204000c0071500c080161150340c000740c0e000c01d481b28030804c19a03c6003401e40c06064980015446154001008a00390b11660b02c40700704048150b00310360b8296 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 60150695 1250 60149445 60149461
    0x120c0d09120f0b060111030f0901080c03010302060910141305010e010306080c061809090a0311060112020427080417010e1c110d0804060b030a02100806030a02060310030506 76
    0x940500c07070250410911000000120b0400142c960300000c040c508946922401049142940c1028140c0e100425000500c03802540e0b000810f250450710210340d091442d407450340041d1040c444e601038207000d0040c08901c3d00c0100e01840c0070000300c06204020035a00c0110000d10480f50005018085c04550000c80400184d48030b48102000d941507000100350140700e190801500707070812248480703001604031408110391102c020050044464070b0040100041c0742c98040d01c218440d01d241035880c0d1241e07004001c2400041c00a501c4180c0590700055194607c0800200c51a900710782503014404d0003078000e082241d008021b00c1155100e003180b49121280c0c8048500b82ca200303803028600f03035000340c19800c200e40d13200c496900000c1749420b0401306000042103441c2840c00800524001c100c100c410002404a1400340410003607085011b0120300380e4540c00140c25081c0c03c40030300100101c4030002006500d04101810055070010401501c0c0d10b009044003409146500003269030b40110004601a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 60151945 1250 60150695 60150719
    0x306180601080a15050402180a06020a0804051504030f0308010503120a090e0c07140703150908030f1f09021b01050403080115050906040801090b2d040203120c0d09 72
    0x1558140e4a803031958490601080203461480003201d42007405080002d0139546e20b00c024090012444c0c02c88800c0e042590400c456500030360300030702c195007000310680000380d540380840b016076908903115030b440c3c1030440701d0b5519401141c0005112034060343c5080149500504064101da034220120382c1001c030060080c900340d000c1c406403e00070a0010340240400104542141ea000381451021410548280c40d080c031075424240070240c007030304031038400d009210342140c800303e50f0740d520442841071441030344c0e0b501c606205c005d0400c0d50070039109010401e80c8003544980340c0c0800c1c18603002203407152154072080003035100388a5500800200c102040c9801c02c18055684101e4050315070f03100a0b0b00c0e05101d086100c0e041519501001410030446a40c0d5480001902c00703407a0f13001c000101d141c0c140c544000f51810191210344240070910000c80a605100d280501021191102450382c4e1928408a8075000907000701c07210b03580c13022482e0414101c0c0021110300b908140e07a42c200500365104610040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 60153195 1250 60151945 60151951
    0xc0506090a0603050406020d14010f0605040e060603060301060b030717010e01080303040807032a0201081506030a180507091b050a120504290a0608070503071418040503030618 77
    0x209000c1e440030800305000c1d901c81c5911500503c0e0141c5402074807401c21048031520103124060fa03003898018000c40c00c10744114400f4181908265181c68206007040c5032070040141524810070340000000c45984080d0886c3c1c0050411009454480c14900005010302006203114400010f05030000144031403c00c104504803100c40c00610b285480f00e0701d030207800307520400d001c4c6e05101c03038007403440e24007580101daa40080b0720f5a258005220303818400100700c41d201621003500c43d2901552080c85aa840003100d0b08003031604c6002a202c40c400104848003100424007a0850090b11000101c507516508000729940296486802081e6007043c00e03500d41c000c043d0440b000820441c1e014032170440c981e12030ba401070300035160b00c1040c603e03100001c0d0a039550034882105c20403843d010300c80c2428180c0101d1020301404805088020300303000100c4d507100c3c00c84c03042c030642500c0c1e90100801c541355807006510411a00807130928a00e0f06051445e52a8400e40c3c91501680e0030b10700c42d4410710000e10340540 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 60154445 1250 60153195 60153199
    0x60e040f0b09070c031b0b0a0f050f150102010e19120206070c1106070f060b040e12030c0703050f07140c0105090105070b07030b1e040b0303040605071203060302060a020105040c050609 81
    0x340549841c41c08444510038403d048084c080da4280361003a0040311020304407010b1146580c01c7d01494800d00349010f070303184c0c990500c0718982840300713002400408200d40c0340d03c603c9803a070b201750304030800004078098014425074a4441c09640d03091304410108032130004109001ea61601814500c8810403a50303002d04071078030400910905010070000e40003085600585000904607410f0040c60f8803580850102840f00300d1b05c00d6601c0c42198007a041c64002c03110341c26030b11405005a01ca001c8a03848a80c070006054184c0040d0019460041501071015249a140e076252104c1e1510140e180594061440410207102d80c0b180c80c801540c15031051b07085581c50a41a0b41e003508021070fa541c0c040b0f10241c0a4045000d143d06c4269000054860003c0e80004511240d030442031165000107100844042480c124001d400800003804140c0d00002150701c4d640e84584135210482645208400500c40c80d04002d41c40710703000843c401c60710790540003140200d009508020041d0f685004000d424440c10152036 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 60155695 1250 60154445 60154459
    0x61701081c0e18070f080108070f05040b1c05070306050a02190c02030c030607030b0f061603050705070302091e0a06030525030b010801090c06080c04030b060105070c060e040f0b 78
    0x4a616842692140606030025140ca042015000b80f07006038401e08a44071000901c5120b07070400802e500c411146d00401d10900030703298181c05c00800c0846c1400303902606001d503440300071098480d11210f41109243d604410102d901140318640300ea01e1b0f0f405403105481c1a030422011a43d10300503482120188080c0d04c02c54200c1070040d000c01c0d1140170102005a0b410f00401c010b02d0b0854a0a000b0342e0301c100829a000201d45103640201300c00b0005071500c0d1030140000b030101040c80b9002c6c280d90310a840e01800d05980b99407907031808038501000e03900002e40100148003817101205021042040034903004c900f0030b606a890b1507000c0f084441c6807201416036405140c11581841c100303d00d603445020317003940c800182902e03a203d4100200003030303000141aa66030240c04044c00002421500a840b0a01c3c0040c01400c01e52144451402a40005403100c6240c00c0070602d103030f014408441c8241c2c0e100c071802200555a00000c0c080e0403015078103500590a0503091745000d00c40e44580201120018145 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 60156945 1250 60155695 60155743
    0x50303160302131203031d03040626040303051009090b0402040e01140402040c0908030408030a02010e06010f030b1513050403080601020d12050c04030206120a0b0409050c1003021306170108 83
    0x2c1c0048a00005017030b802e141e5240013080f110b070b01404900c108064540021903555240c10310040582101c0306402c03181e15200c0c02d2001d006200c2c041c4c66904280c0500d40864151941010343c030b41c64000e58410b0446a00c1c1030508410082c0308018944203074000c5a0400c181c20200d00e0046c207a816401c3c0c1c00b2001803158000030300601c1d242c1d021003100125490800e0301540c0f06d0708024507542c4981c019120700d5101103031001c400c40e0f090207001d0340b0040e10000b600403540b6003015040d1414840c000102105540c1002940d150b00c103410705d503d4648010503110310054084c120400a0000f590f041c0c00041c0c0d42c01c0000d2846d400090300000c11140c0380c0e1a000403400b01110007004080141c00c60404ac8070402002001da55403001401d50b861060028440034144034000c00111401e40c40014020ba041c528410003103480410800c0f0b844000fa100c0c00d00c0b503050403200b24000c0c401c1c441c080c1d001c40140d660218101b030788003102d101090552004800f040c3d8858007825900d50b400c0b101c58501c2c81481c041 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 60158195 1250 60156945 60156959
    0x10f0e0f0f0405010e070b04080706030e100b03010b060f0306030f0304120308130507260d0e0609040f0608010c0e0303030f01060f02030403020303070b0906070903030806191205030316030213 84
    0xc681d8010f00034000001d002c0c4140060908200075075200d443d054502250031320a060f010b200c400010b00c000c0c20708004039600c0c00000307a10b5030803030b1000b54030103076a400e006011901c0030f400501200000502c3ca80d511301401003484042e40096903614000d20425a1130509142e000080b5010340f0608d200351200400e0542d01200e14950041c080020841559800c1c800140c0800480000d00307d49000426260b401001c0d00d40c0d002152405813031194400140403031002c0d0840d101540c164020b0343c46ca0358511306e4802150160280520b00e0480500c0d01d8000500024198416a1042c205a1b03030082249001000c02d992030006558030b0307189120340303c01004031a025920076009180680141e9050035500c0d00001d04540104409407176440b8842c0400035120301c14000300c0e070701c0152424020389050075610020808040185072500801e0340c00304803200e031105404a4001082d01c019540310f9250740703280140c2c5079002030782c1c40c0104503494420203180070f01078000d0745c1ca058000c0a40c94000b80c41e00c0c01c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 60159445 1250 60158195 60158221
    0x215150d05010608060a0c021b090c030a0b09010603020c0114010315020a142a0a0b070e0f04060f0503010b0901080303060405061f021b04060305060c0307051b06010f0e0f 75
    0x801c4441d990b90300d03000510813005210003846586030702c00014901d0524500030b130605e80130390910652140140f00d0107849640325444107800107020404180c50f551a580351500070b14082c040142e20501c120300024032140c1c59002090701c0c5203400c00900000042048042d541103081c00000c0800d004c00420018a1205134081d1a80d40921300e41224000d48010031202660f10200604481c0f00c8100302610900703464040792a000c0703035520010503545c681c0c0d17141c00003a00710140200e01001a444c0c04490303242d841d50190014002d0080003080203035520342104031061010300c00c00b8000d50030082036002386d152040d540750480340a100610f185175500002c11005003030082006900040071200c0104100171100d4440144c40107130020198920724120100d2100b0030107900c10310942c188001400060380101d90b441e0085a2810007a40300d480d540d106031042e0086040a0086000b520221001c1c0310300090014100d0b81c81d2054084030940781c110401300440b04132030b040101003e03400480d842c0d000608c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 60160695 1250 60159445 60159469
    0xa1401060f0b0409050c03010b0702040903030608030a1106060f010906030c050403060f021308031918080604051f0b010507030c0c0510200a0c05010c03181203021515 73
    0x40000361040d00d444004851007065080350354100030205060007240c0b1944a0140c102d4000101d1740e04661401029a08512500000074011a201c0649904041c02a00010083c200c51015039441c0c0940c540024170000c0b504454440d070f03104500100307100c0e00300012190139403401a901c0e10301190401130190040c09400d98038200b041401c01000000c41c001d031048210000d086a00580c0c1c0c4c0c084003610900c048101d400c0000c107504100898000000031610b10036000c803480c10002c0d5000710106c2407082d901c2160381302d02c503140902420001040000300d091205000c250303d443ca1044103926100d03044a00d40120140812400c01104000c00d0090b400202410300c00c040a519250f1108041101031030744561410105a10075003004540c0718104c40038a8044220005001c44441030303e0303900154003203201d454188102c500f510000d2600c140054240c110f84d509000c040c840d601c980388120b500d03d40100303800500883ca075002200740703c0c040c1540281a00809070304603400240c10820404144 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 60161945 1250 60160695 60160733
    0x201050a0512160806090708011703070602030a05040506070e060f0d020903010c08010503100905070b0702010c060207030216120c090b0a0302120703030320120a0605040e1c030e0a 79
    0xe0100150b032108480702c19104003041c640d040e2503030280640c094a0214050070311072203078190f60200081c0b5640146041c2c110713100d0710100c040039032410f9005410340c490404094030301030000040080603001608a14000d52041d812030341507a66a110417034070303602081405076210340c04200c400181404880507158107c281c000040c40e04005400207808c466100510b070010646500c0104140c1c03609002650071078100c01c0c03051054680c0c41e91841d460703010030f0250741c010302004129203056910403500003c0c8650320441c21075680c001e0342400396403800810710703c070300340500c0340e001065010f00790203a8555243c2c402c00705010607051151500141003c0f8407015000842e0400010250f45c03103440c0600300c00020805061410300303505005003904d4100840f000000113180319800e807201e50300100ca15003102daa0805d982500c96100003005440c0c00c1e03202c0d80c0d2103401d052603903562000102c2c04942c00e0354007000c8400d030700040e000e0640580c0c00c54111040c10303400080820300410704224003200d02402c0c1c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 60163195 1250 60161945 60161947
    0x110309010c030e091608220807060b060d02070b070c05060402011103090a0b0d1a0105070f030302190206070e120712050a05161a0403150b04060510030207050105100803070201050a05 80
    0x2800e01113010a4400c0b90340f82503503000c00c2000040c1581020300150803501528903a00e04000140b2055905000c04000400c4210b00140351400c3c4600c0740d1104001030801070510756661900a4a04065042402c054424480354404604054013480c950380d03071940d0141c0580165034498006407010503264400b07071881d00040003010710540d64820050b01400c500c0c0360003601c48541d100700c0811180ba01c08040f899150415030302072680e230008140c03414581d11407803445a5a10740e140c201c01a0054004809a10b1001d0015804068010508900c00c1c1a0b0b9a46c001020000d50300300302c1d1440001420101e0f1380c000640a01c00e040e0004511000d0381d014030100c032403126250f62100e00d8403440754001124842d2001d814420100c4508107030342484010b40c0814101400c544a82a100180d10dc020064940c0c5624038000c81d111904004000c0c0f40041c600c005040c54040081e01035801031702d0031211765213004009918a8880c0440c0c1c000d448100c4010340c2400120f41c01500e250b0310521301c00080c014 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 60164445 1250 60163195 60163217
    0x1090b03250203210f2205011104060305070e060315030a0203030d050417120601030b040f1406010e03030c070302090c13060e041a13020f070b01030c05030d110309010c03 75
    0xa101c08070407040c1125a0300031075031010307082071942c090800703003403204850000c02042c07152110f10900482e4024016035020000f80e2002c014400c000108200001d081c0d50030240d4941003212005d024108481203a24148a1a520010110340c0c3c04a0610207583c440c0c418008640c0c4644000311949030f40d20050102c6540d00c03210f8000034a5078110703040700603140d40c5401c20017007000500464950940d81180d5040d003080c1d0848c0c0d0000d5261001000c19041540e22681850503986036040440c840300c20031301c00c01160b0380c03510118510401c101c4115000c0b40a03011008081e00703000040b100400b6481015100031070540e8204405004098040e1008140074030035014503400112420340100741545680a1102d0035005000c02c0c2c03402100084140010280030800c5034441441c072000510b0a59030040c1d50f00d00c8208502014010001e02401403010b400011041029243d002015135108030101c45640000300c80440c0e41c0c03960703503180521541050000350350039401b0f404041c450610034140614515 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 60165695 1250 60164445 60164491
    0x207170d06030609060f06051207051c0803040c080d0219020d080c030408010204090b0108070e0909010615050c0f0727090b041209050406081f0f0501030c030c0501020601030201090b03 81
    0xfa000c00c800355a0246ea856030900c0503211442140007d1030181ca080c0d550081294082e40c54001900c2254050701884802c00c1d4045a0020306142c029840900300d5224103113414408801d5000c0d001d020b03550710409042e015440d0000940041d88400c60607041c11011442c0d0030b00c0181400d004080354244428054881c00380410700242c006012070800050301c8502d45000002695510401e850601c5000001e01081c01d921101400c907440342503803400401c0d221070508500400c80d585c04a400070f2403040516020030341c88001007200184000c111000480d043d6031042e280c00751441201c22100c592052102460307044400e1501c580720454001034003052a480b050128202141c0458107103190002e00314070150440c2d00c1c480604000da804014003820001940e03a0398090500d4451000090212502c080d001e5400818801800b54030501065940e403030040740450306800201d5007080510301c04903c9500c0096194100c030f40581d60001c20300e00c1c101404140d940050140c02c40c040702d00c00320345044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 60166945 1250 60165695 60165701
    0x406050f07081902120f03010303050915030709030308060306091e010b0306070504170c0918031b06060102060906060d0201050d150e100603050c03060108061c0501020d050601030207170d060306 85
    0x60101c00c80e9525a6514000342045d41c400b8900f07544c0c00e000d01454103150301c0c5400396415240e041c2491079540c0c40302c0d400501d04420401d0082c4c11a0800402c010100d68001c01c04412a8072076100c8034001c0e2502020543c07516800c031038200496101c61880c0c040304881c40c081d1419040c0c09000000c005401c90082810402d04030b075401d0218400260401c507072400141401400708501c0d001d032925441120000307100c0103018003003002e044802e004c20000d50301e06200b201c81142d1003621a0520031250b56900780c0f00c510841d0a0780c00f602403040019403405003c545c03144142c10091082c80d03c1030303195005481a401034050f100002d59503100c0e61820404520200d4003a0204003403101c50b0340740680d030310700301b482d05600034104041c00c000900800340b00360300541e9081082400e20042a60301ca1021030750102c0844160440f00d0522440e1509120040d4002c00010403c070030140030540c0c0d80c4005406a1242040003004482400c642644903004e1501506020308141008034040d6034a0b11105c1c19 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 60168195 1250 60166945 60166957
    0xb22060507090512070b0a0e03070e0105090c030103030c080d1e0b040b010201090b0a090206070203240a0b06070f150e07090c2303060d020d030e030705010806060406050f0708 77
    0x5550390024800d2054104080c1401030008480715401c01c031105126070b03103542480c443c0b404070610104100b600e150080c01340b0003407210083c1c200c1d102d26958048840100e142841030300d0140c06454007242405d00d408045a06803601520380d8040c20015540320300302c40c1c0c08150251304070340e61095807051403001145100c0030300f1060300300812020304c02801c00c004c40748003a0b4294151fa240c4840c403800500d00c41001d651105140e100005c24404a0000c1803143c41885002035060160803824403042c00f80000b00c241d03441042d0320084903a6a0030040d801105c0c0302d035107401e502070760901078900082c01520710320001622a401d0030b41d0080b244180da80a4a0400c891210030340c01c0410140501c210710b106461300c0b007843d844d2412004040390114649000418a140c41050740080000c843d500c50500300820b43e40c0c05040452101c000c0c0c10010110803021007014405d014004001802e58071410045000701c00003081c0a180901e00182510310b54000918171300f0005003441060301045010000c0e0503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 60169445 1250 60168195 60168203
    0x210c12080403080a0512070309120503100506070203031605100b03030a090302060d0609060b07140c011e170703090506060a030b1801061e0f0803031506070201020115080c040e01090f0b22 82
    0x14500480d803030803000c5c00502039581010898140104020203c00cdc142800840380140c071001c0d80d440141c000300b410b61061003204030410200141010030010000b035aa0100300105000700000700c140c0003019124441c80150000041c8544e8090016182c0300c0000c0284034400307200010410340d03d00e01c08c3c0c29192207910524242e20041140c8042c01120844050111001000342807920701180010b81024440e00401002100904114580c1c5025000341851120280c00b101628603250300d00a001c0e01c60301404541a0150502007282030400d405410309517030703120168505070742c0c820002e11170018905444103010340d01d9000020b42c45100c07410103058402a140c2000d2000d0801411601010296000b603c440d407040042219042090700c00e00424032044542c142d13207480e01c0c00101c0c058030301455942081e4000d04000a188600003071844a018030540b420700900742c0105049003202e0010f131014100c00307450031031000003c41c2c1c00d8035254410014504046130a40039100c40d1854a02c03194126 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 60170695 1250 60169445 60169451
    0x803090102010e0115030f020105130806040201030e06131502070f0b0a0b03070311041509020d060305010e0706080604050606070807030305060102070e010b07030f020106210c12080403080a05120703 87
    0x9445580c280655401030340842c0003841041c00c420451040e1944034072020f0051100c0b40c40c11000c5a125204485032004c088080700111a181e0b19155220101502c04a0100307203401010030f400384022500d948900f030800c24560709102d45480d1000000c0c1641c00c0c800100340e00f08400030029004d000c1c000b020354018141c494481c901480142c041781e269141d40c41c4298800007081001031078a10408030300e4481a2800310b03a5124024a0402c00e601580244100600101e03130780d6403640c503039484a01103901030402071100442100602d0380302d80080c0100300005980000048990a25400440d0460b6025148a02c0d040d15600e440e0115005210102c0009031608203000c5130f90382c1000b58030043c0400c0322020bc00c0b035140c0080c0051074032a00000500307001e52040d4040c40d046c001c4d0b2000c802040b2640c1c04c45904600c03080c14040720240c1c7d420481d0380e140300c020b0100302e075024200c070f0022050307001d07800700d20381425a25156a03e82001a0081c00c010080006920324133040c0361560048141d52808 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 60171945 1250 60170695 60170707
    0x1602150c15060d02030601030f031206060e031002091c0c030c0e010305060c09090412030603171b01090809011803170304060c020d0509040c050909150102060a0b030a021c0b010803 79
    0xe01650381d8060499480750f00c400e2031080142e0360120703a20341100c1d484841400e042d046881d05690001c4001c2130f07035100501e420000200c441d001000c02c02281c1045094546840284140200320300a80140c213030003004100507040aa0390f002d038100281c50048030484081d039604d688a2050420507009400c841855400400800004001140d0001c0e83c5442103410503031400041852490020006401142c100030507450447c0030750702c81406150049891101864070a8502d800ca50200b18866142441c2d81d043e02c09944042c4290921141d12000740c51502c1580001161196071001d0f400304400b0541e540000052071f01503034140d6981030440341c0d903107a140c03504020040342c500b4400d07841550001c020011005074040100c40ca40c3c01c00301c0c0c00050b801d15082040310076000b010903082d006000507060011032030040107a1098040240c0c01c03544681e4500c00e02c401584c170898000f81c2c05900c809020b80062416180030b0443c4070040c142d4502d100015143e01050074030aa001c1c403810f030030000d20 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 60173195 1250 60171945 60171973
    0xf0605040f0f030519140607082a220b16030807031a040c02011409070503061e19020c010218030c01051303021203072a0e010b1602150c 60
    0x1004008002d020b01604241e03145454042d21886011640311052000c0c44c0c2820400800004403080c01c126070040f100c0510303182c4005008920107031003c0045804c21b2900c1c414081e905443e2411100c01c000c10300c1c0c10040e6401c9020820011402050302265044001003000c076410000ba114040c0b80c03080c4040c83e200d090a0181001c04054282030406003080c2a40c40c80e00c0d00020040c21801d010754000440e1150010124014400c0d02c444481401448e014050300c9040010305405840040b8244c0390f26032100b104030844200360340b401d5070300c03c0c12200c001840221618802e40b4142c44a0a01501e0b10742081405401c81c0c0c00005800f080e440f0311550ba00480c1402c000129580e6001e00f030030303403402c1000c8076904200140e0f403100034440c007407050746d0802500c2c05000341c5115507800080000454442030070040003080d104004060340c0d02c0c02c48005480481040141c7c100e52541882620b800c43c0b0b50042900c40c1440b250990700404610100d03203070764034450300401c4c12549120180c030b048080c80c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 60174445 1250 60173195 60173219
    0x30304050418021915050903030a12020f0703090302100206060907030504020d020a0e0f01060305060d0813120b07020111072001020c0a0f05030f0d02072603030106090504050a050106140c03040f060504 88
    0x905175013048010b0006107150f86000007250701e403095500b082a40298031000710b070040c0c841c0e0314103055400b001040c10002c0540000e1043c0549100b00d40c1b004060b0391019089070340f52030480700b02d0ba00114250200300c1c00760185c1c0c03045802c0360014165030099403a0340c000c030703545014903441070844500c0d06e02045600b600b8800e41a02500e424581805076080220000d901020680e0000c0c041c01c400140d04070104034502511001401190205040d80f400c0c1d090014010b001164000095401c09507204001e030641003c0b9004507a2200108083c0c500012120088880078859681503220726504a0202d40c2c40d141c4120080078072080440107a4105400c0c18100301c5100f041d407815500c2488942103507500403070b410090300c04101481c00801a082030000b014820040814898000000086401a8041c1c07003a07064403002d4074107216903100d252425040301c000f449020005404030b02a09000c2181d9002407060f0700083d41104d0505484540300300c1850116801032011910014081249407400f00d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 60175695 1250 60174445 60174479
    0x1140913020a050120060106020102090108010b03061302070303020705060423070b040b0c030d090b0a05070c0b221a040b1308040b07170a12060902090303040504180219 74
    0x11140c0103180c046540801e016220701c0c05814140000b0001400603095107041c018581c00d0080c0494405580d543c00183c003e5000f002018001221100081041170440d070449000d00f00c041c10340d1032805170301e0700c1010094000640032000c054081148401140701003003a140201c0c000d802547d40044241039030740c01607100341078410044d00080420030020171282c0981d41160704441c004d540d10075240900c1411403251810410001d03240c409a030307040c0441c00e5030840c0720798003401d410090341d1100c003030949010140042c020074010b0340e800084c503c02000c1c0f102c0351100c1e040e080d40c140158002d54640c40500041c180c001e8465885800300000d02c400c01440c51307008040c02121f000c40c10b05a49549007944514040c0e14101c0f600020107100300698040201c500c0d10780e442e1740903200c60707821078006c040300c0d2000600088075040ca40042040101c610840d003492000600841ca402d01d4072003400050141d401503200c400141c40c0d00c08016859006889a590040744000c3c0d0340d441c105401e140d0208240 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 60176945 1250 60175695 60175711
    0x30a141b0303071d0312090402090409150c08010e040519080409090b15040902090109050405030405100f020105060f0d03031107050312040515010302011b140d030f0612020307031415011409 83
    0x1c00007510804800100f01d031f0108030305039800350340d503003c1e10301040c007601e903a000c02040320903141c0e00d221050f0005d0b80f100c3c1c1000340704e40c1c6103e4180d81e02d8107800d52407807041e01d015080783c000425101140f642da00781498030510540190f400c265840c0d1510040700d210000c1583c510f8200b03410080010b005550420420034120750410a104068010501580050041402c680e942d4030100301031040420a440003820300404003050560080d0005100c24290020200036600f840c0105000b49801c1e101c210080d04042d01303082c0c5000458608a000d002c00c0316200500c00c00420000c00411030520003080381c0340c420340c50915182458074202e8034104403032a85542c046080e100500050b0703800560149180b031204180c0c1e03000803441c20f00203210365954101a002c1e1040035106210070b13403d40c0116443d04c683c16001c000151740c86850050041d10050000d52642180c0001c0c00010608041201480d10f240102c0b41e11501c000c0340780b15414001c3c6c000c40314001c81d05110390454a02106d94550041700 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 60178195 1250 60176945 60176953
    0xc030e01090f0227070507060c170c0a0c0204060605090a0f0e01030f030219050c240a030c12060905040b06040903120b030c0a0e04060509030a141b0303071d03 70
    0x45a12031100b811201c02c8028400c0048601d860514440c107009200c10310100f009010b074a041107000a816603014480440703440c0c0c10b040c428031206020340c07085800251090482482e5a0f05c00d0740080d041e510540702c003014030800821010241e10703144a150017800c00c0340c4400303584500c28420814034641e02d074082c4400070304800041c4402142d0280c0141140d1f0f0102151b2500989450280e00703000c16100c0c90f481d0301c5c80e000d00540500c20001103203001e014054881c88e50300d5840b0001080d206541d54683c060603081000440c407014403950180420f4021864940d5112440c041850181d801c80da01c858190b60b21242400f060062010f00030b600403408990070000d49482d40d4010b070006000c032120070a510313030340e01940382292000c1c80340c00c2d10b4000c002c00780c130304540d141c3c0d984140740c10081c3c909070f075a90b241600003401c0903000021201c0c8a45e558171450041404403807074202d6540601c00003c001a041210022100400c1028500620742d940320365041483c2c20100040303044c69105000c1c80390b40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 60179445 1250 60178195 60178211
    0x80102040e100305121e0c150c0702180402010905030f1f06060e0411040803040303080114040501061403040c0e01060c02010e0103020a1d0607020904080711040506130207060e060a0c030e01 83
    0x40005200170700d00d1041107038140c841c60088450078001c070300004090186000010900304881d800301d0385282d0114801c500d1005500c4410700c842e164007491074004d401a481c003580310b064000100d9040d034420300c14500540c103c1d864802080c03d18000f00820740e0b40740e200310298960880072512400c041d080c80941000110310f0407500404020001c10a907004581c1d409042e41000d80840c01c50340a45005021a540e590b1740e8540142040000d118880d81011020151700320340c609801260304070703049980d907900700c844034054038101c50b40080d01c216171804002d5400110512111401402840a80c40702c0000903030a0002404107400310541a041500c1041703034003d040d030888c2c44c03101c054034100a031440b62200380c03021a405d8031074800c0c06544946240d040000700103000c801088014880d40c2d4070200000d50205001c183c510541e0784a0b070104140c8034814440c107883d0b000c0c100031400f604002c07450a41c04a2900d050280c16146c100f4502c6c0c03107424521400d0f800d40034481011682c41f0007042041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 60180695 1250 60179445 60179453
    0x50114070c060c0c20030c09040c03020907030b0310061403010e1c0207030b0411130e0a030804051005010b0901030e07180b01120f060509010602010b0102120d110301080102040e1003 80
    0xd1101100104010340d0f0304000341490f4400c071114540c03142d1205004091083c410b031440000b11188904074800e20400c0e81d80261820003480f80ca0085034840c0801400c0350540d4200304485400800c090101599050000420703601013000550008190300000b503824100002c030003042c80b1009480303010782e041ca02d4440c01d4090000d08030b0000311036840c00a0804000c040101e0500c20070b5400685900c0361002840207014040540400c0350a084071104000000565580142e40d07944101c085207810001d1a00042802215200c0d40031303105400303480c0254545645c2c0021074070300380c010001c45540890380450a503018410310410304402802007081514103002e0485e141080321200814907100d4148a54503409807070422002111004240b01454448004500522440c85450311802e5078400000700b107801840f03030f55034000d01a4040c10300350b030795400440d40c1c3d40d0184103040342c9681d482031881ca144a8100142d03000c0c02000c0009a40c031840d240b41842d2a100190242e0310140749884104006 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 60181945 1250 60180695 60180707
    0x2240406140708071b0c090203070207170a020d03030b030307140607110c060c07031e12031107030c02060408030a020f010605090c0a0c050304050915010f210902210a05011407 77
    0x110001e0700d0b2000700300400d600d8640600d00c10b088014208201d01b000030a02c0c401d550007a62040320107500322081d0903038407000d9285010b074410405080d45c00403e508005800c1500805459500a04010845800c1040803034a1640300c404199414841007480c051961428014560446220718002c503500b95540495521102840c840b14410f11f4000f8020030040b0081c8208801076400c40a08540300b0380f56442c940c1c08481c5800700702e890303500c030182001d9018040d20490892030901c0c0e2207241086921b64080d90001c86c1c2c0003042c2d034002000e220008050208100925610300240e015101210143c19424256403242d00700610a05070003041200c0018120143c601c02d28044c5061080e000d418100a030451245070401c3d500050480b082052a100160004503000c42c00c0c3e0f038480c4104034010b800c480114003000c98049003901c1c0200c9040072091504826141030009011180804040c1d51208410301c40000002d5035411080d089401e001080c4940c00c50070340ca03c061001140382504000b080 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 60183195 1250 60181945 60181951
    0x9080c0906040e010c170a060b03010909141b090f04030819060305190201081621020c0a0309050a12120503090a02030f07080d0201021c09020102240406140708 70
    0x40e0305200009141ca41c2c550300142d140781240f600800c04014000e10051a0100200070f5030305240148000c500e00c20700c0d13482580200c0b0440441d042c2140d0078020b4602c00f070803420b1800e6441485507501c9100045090000003c480c01010300702c4404030340c5005101c0290402030070130804000100070880803a0b0468001503001c1e06a444c001d5662240c040b524004000070340000e0814422400160f252a68451042c1c4080d0f001344c8404199070303207500f242c00701603880790040400200c1d0501440000340d038603407420880c910020070150500b0108a0410b18241d0b03100c406a00080070b09208010a08103400745c0006000801e4903941c40201c2c0d51680c2c102c00394207451000801c2000800114449824828a1070290340201500c1c10300d00d0718074109540d901240140c0100340507191030100d10500503c2296041031009040e0003804440b1100480140130403242079042d4020511602d442030034203100f1300c111103101021102c85003090308001089401a4600004d03002c103400512140580084001d54 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 60184445 1250 60183195 60183199
    0x3160b0601050f0c0706110c030a02090712050c0a0e0a0b04030b04080702060c1e07030506010b0a11060a231905040c120503041a0a17060102121206010e0109080c 71
    0x219034545100484403031040142d00c0050640206a440c0390000110342c001c2103803815542d03d00700c283d0902405880300809400241d0550000ca561401824000c116650069050900d022490b00717410301c0e6025200201d031205600f50002850f01da4054102200c1000c1c110180e42200505091040d01d000510581c000030341101d02c9100060100142802240c2560b43c3c0908030035280d101c140d81c0507039510041483c1c01003c403080c05a1114402000412400b2241c000b401426140d1074034442c016140e00c015030002c06c10284004c0c00c0c0e0005000c01c4594091441c000d00000d042114031100c801c6109000080c50180c041d400074000407031103c1d07601d0035000d10342410008098445152501d00c4030a1340d80009900c0d1522900b840504c90040041c0c41254500c1d44802d01c16071056258804601c1460000000b0030800398064821400da543c10545c4108103004a8010700c51202200080f030f0030807084903540212050400c0b8555a100703282a1080b1402e003010300101d81013100c003984820892480c82c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 60185695 1250 60184445 60184463
    0x1050403051e0405060408010f1116060e0a1e03020105150901150306030501051e0606030606190c020306011203121e020901030b0d0b040507060c080a0c141515030316 73
    0x41c8824002e80102c0d0028440108401c0d80c0310750b9203062502904d4050714a20f00c9500c1c0c40801901c600b08c05084441c000b0b2b5071031054482c585a07503190710061200c0185403010b441000ca10400089907528003c41e491411000b03018540141d2070000c4c00c3d0742c0002d02c11b10024070141840310150700c4207103140341510700881d481c0903442e031840003c40c010201a030024250350300306030500003034144c01d0903540100c21100c404810156035002c2413000601c415101c482d0404003c00010f5001c00c50107400904a039003504c0c00c0c1c982d056542c2c001030301d042007c5c0c00030b000440510007403804141d00040d540e000c00c0d07585070050121441903c81990070310754588a4100d03aa80025885206070310aa02c0024000c000500580c070035505401c1c01e100992085030110f0303d5100e0b018001c1010b038090300110340b500741e010700c0703a5240070f001b4182100c050014100481d005112004800c12403c0300b80b11405444401d0b00c819002894250b0f4624108803104a40d14000d03001004119003170400400b0180240740c001c1408 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 60186945 1250 60185695 60185737
    0x1101020319030213080f030702060903070905071706040c0f030e0114040c0626042607030305040b010b0909040b1005060a030203060a06030501080c012a0308040c080105040305 77
    0x503400c5205000e03819820711014030a9100c000c1d0554040e003805038104502c1c50310107403950426650b4034801031205d41c50b075100b0f2124000501e0668014001c01d83c026040e01d0300c003a65605108103450301965460041048400c2c1641485141c0f110709502c070078221000d10000c400c2d903502a2040365070340010320402d6200c504492100c0703001d400074040d60b80022181c440301d180501345101c0d40821805010009010440090039940341109140403000b10480c4800c01c0381c80d150340d49417201041d07229140114218072000781604a024000c1c00146000e61804030b00c41c80d0a00d040f02100300141c00141d02c4c1c8a09201c02c0c7d0203601e45850180d0301c140c0c071a00400e148c2e00c950442e5058000b45620180e80250005840c0f2600c6605801650190308140c600d0f007a443e88911b01501035403000d00401c1c00c00c0e8001c6007124015032046294007042c0107102c80a41c001c2d41207084c00b100e241d40300f600c16000304041205200400025210103c002c15030700000304540d0900d070390000c21600c54007181c40b804503400b2801e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 60188195 1250 60186945 60186947
    0x2060a121a0d03350108060c03010602071419090203090705220e210c010605040b1f031d1608011401030b10080601030b090c0d030504060c1a0a0522020a031101 70
    0x1c81364407540204540c02e4915008202d40401609009009850180c507001c1500700c80214145c905896468001d07000450420641c0c03090a548100c60561000ca200030b850a20369132010f070031018180c00c00c40941d0764904100890710f4884103500003030042075180c4099640a28200303015814000b0414007041d003210084402d40b0b4155a400c8006081e040d40c416019294007010041200f001d424000740310b5280d0304c01c1000103c5032000302c1250004e4240c00c4d81c10102e50040c103140291030050400040c8946803160030080d507134041341d04004a80c4103003820700381808442d09103801010760750001e2040ca0201c4031060b80390320040c400108540c40500125032003000184108015181840881306550f9480c1172242c81041c060711440b81c40c2c00b502810304a6800c042d0380381c3e885250561500c2d071816103002c3c012038100600b80026600090703404480c41503d10003519182c0612060304010990b0f05008041111551165695011000e00d81545400584407018840c1c11283c024101615440300400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 60189445 1250 60188195 60188237
    0xe0603150106021e0102090a06170f0103051e010f0f0c03060503070302060403060b0a030b070c120203030915070e06070f170705060406021b030307021c020102040b1204030201020702060a121a0d03 86
    0x1000d00e48c4100406000709205030b009012141486103186404061340b61581100500c2c80d003804080c0003a0448840d4005403400720318160440700d0340d10000201c2502003100d0724125980c0b08144480c1030784404141c4085a81401400090402200a07043d840c2c07031540003400ca40308a1000500345a00c0d171005880c80e030307a0b10745040300031038006d214a00c0324a04800e0060803241d170303040115022003210300713002c0900d480002504c0c4180c00711002800b11251a11000c02c030b00100808130020800c2c0c10120400076180d00000d00b01c082d10444049108a156141c1414203441c0d071800c40c6029201488030340c020035800105a90801e41044006a44013218000c502070f48060006080e0700c0c0c17000105100c401c075400903640c00c2d0740b000c03c400103800c0504280220b080c1d00c2207100c3d91402042c01c0c001251b102d00700c0e03002d2a80052103400010f1404c0c84980c04608076401020711a404161284102c01d0548858040d55131103203580c02109105480700030028001c0441120060200a4510b0161400400d484 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 60190695 1250 60189445 60189457
    0x12040608060d0204090f0309030b1605090906241c0509120f04051c020406090b1311040801060b040f12030503040807021305090c031204080c06070c0f0e0603150106021e0102 76
    0x3c5004080046e1400e014110403040e120460b520304010340010711594503071180c0d03c000407103a6201841c1074140f10811140140c0a8801a440a050503980a0b01190141d50004a0140d40f07101e07500c6d03a0fa000600051003c000705140a894100303c1085074402c0041200032030381500502107511046082842c0d1040c1c000e41e04200c2d007001d84402139451802c80100c417141c2c03243c400c136014400310380c030f900130042511402e865468000c50f207010006810806500901070841c031003085030b810a03a4514080b4291181940101c0341c800000a00340044540c2d1003800004e00098442d50310200443c1c0e41c0145640b00045c0060981600454034000319655660720054171801c4840c180304908000025584070324242481512903c60001c403000350a100d081a5021100c1c4d610240c2540410f0360709210455012040c1141c2402c41e0340d1000c248031b40600c10100142107884a11006860300106040c500303d00e41c0380c414554000e060041246541c00214007014001d40316481d162450f00a47d041c0c0a40222 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 60191945 1250 60190695 60190703
    0x40e0d11070b0417011802010509061e070804030b010b0306012f0703050309030118020306010b09031222090213060e01020f011a09010509040b0a05060d0501050f0912040608060d020409 81
    0x200000c5403034513001c0c0c1c0e05031021203200800841c03a003201c0340061100f078031100a01141c01409040580c2c030b881400b62030364034203146420800d02410501d00a4540c0200c0c0c0484140714080b90620070b100406140501410300078500b42d2a41c1086c1001810343c4000b540d4014403010003940ba0180e50487c03004001000010310201c6450700d031289012501d98000345d0105000e5072030b064514040d80c01d99076034207054517005009407a02d40d0a08855000c207a10080480b034040c8030307044008960608100007088040940005100400481c41074184240c00310b80c0090456401405801000c0c0000c0340110700b2a201424100309078004000180c0c00c1c400a00c004e0302e915441c003411b07003502910b40c4ea000035046001720391817620707a0b80301d608000901078280e80240c66014180001110703144160f02a035000100100301c6a0742e056143d1314142581c0f01100c401c0900c2e0603100500440c4241003344140d0f00801c5441c1c00c0c14a03003080001000a81d004180d603200e0211544414155203503580040101c60b00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 60193195 1250 60191945 60191947
    0x12020a0e0907120c021204050405071404080309031b0f010c03020705040e03040531020d1b020a0b0601020d020a020d080c030c03041805010e0a0504020f0301020a0c02030c040e0d11070b 81
    0x1282e00098041024181d41140e254140703034150103140d00c00729840003000591480c1504250070720b014840201001403201d820b000021907122252003030040035100030002e9500440c1e5845c20350040c14242a5041200303009074406a00040e20b542d564400091003010a1815021003141800c003246814000d40c042904146440342c0001c0b4580c02100070401d6400903100c009050b201e005001c01000f005140d003030803c1038a00c003440c080f03120540090a80542050000c9030100302d156400c1c4108901c0e00d43c62000d1703400304918a08006540c050780d540301400340060701e40ca000340e08000e500c5a440b858000d214000c0b040d514010000d4036015981c0c1220703032404683e21281d0701482c0e60350325442800390035054040c0c0c0c01d111440e43c07042c0c004c142c180e440002c0321806540350001c50300c01405000d44204d80c403c2201e00d030900561000d101910f0000b0340c23a034603211342c281c59005141c1003242584616000e2414820041036030000020322440e180c40c28a0b020190707c0301c5050250801e0405d8002802101c8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 60194445 1250 60193195 60193201
    0x507020c09070201060302150906221805160e1f05120f0402011709030a030903051e0301050f090c030f040201020708070303020303060a150c021009030506010e0414030a12020a0e09 79
    0xd41503200c5c0b410b40e1710a03a83c4e001000340c840552240d50003120740090788510708000c02034041e10101c400d480011000d80d42c8440581c0c56800603034404134040b241012160707889042084650015109046005003420074081092100380801c0300c00c000a40000700c2d020300c154400002511481c02c4500e0b2280340040c819060500040040c0c0c000030948007a030000380a00c0c0070300100d10104d00c10710b000c1e0314450003e504d0303c68071003001c0d0060011900182c0600c00188032201c0f003070340011510306003101c0c2105440c2d60b80d81440104500b03a0b03002d1122714000d0041d00204051418403004590f003040c02d20250550380d5455100403403411000b9008041203000b00c2000008154002000d940a08422234008454507110310b80310b81070a0344015610300207240f107004dc03c050b04103008210b903a41154584082d9558580d21080c0c41d001307081c1d00c50560040300000300821b2240340d020301c00f25a5041e40c081c618010089c800203201c3d025650b05d10408680c0080c00c82c1d14070f8062048011000000340a242c0b8601d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 60195695 1250 60194445 60194447
    0x50d240504022218050702030a02030301120f0209070201050601031a0109030204020313020a1403010b061908092a0a06170f0c0d050108030705060a1e02030c0904020714010b060a0804060507020c0907 87
    0x103104c039112103070754280720106204900120035aa41304403294011030641c1c0c60401c2400c212304400c0300a40781c61105008040c09030325000302451054005800214541c10050001000c03903045205200300e07a10bc0d6201002941e81c4200003200b01ca030120303005038407074036a00c0c5650308001020900a5100f001c0c80c0c800510000703e04054002020100e00800c01c40c243c00007880000e01c901311101d00400c0c0a0b8086013655401242c01541201d1000b04031514044d514042c0c1450491103003c05004c244440d08545a500c1c101c1071140140806141c0b910040b0580342c410280e500002d40b168018075400c00002e5464034888080d0341c07000d40014018041540d5850000c0c1d10b07540a100140d4140c05048001a21010680a115000f0740e00034084620030488008140c001c0d00701901c2c0c000c4c09a0308108031852941d031400585902e6018842040078500d00c640d000703003129488044a409141c05010540e445900880b402e80d00940140f404070342559080c00803803c0104070005160b0104814092040039 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 60196945 1250 60195695 60195719
    0x406021e1e1b010c0c0318052b02040507180b210a0f06030b0a050a0911040b04020903010e06060a080105090a080912070e0a0b010302030903031303020f0a03050d2405040222 76
    0x303940240c4034a80b501c84c040d800141f20450b1030180503001101130010344881504241d0380002050201c40703803021614503500040030344034240c990788005042c401520700590480440300d001059034011141c508600c0401856000c0605018000b0800c5d12400083c0c2e044119004100e0388082c4c080c1c1005150344074601042c0c0c0da1802e44600405a00d400c00054100031140302d19000703150068031384091404600c2c00c00c03000c2c0008142c0701d0340007030702070008641d540c80034040d01000c05414000380c05c1d04e15001c000c8c8038494040c3c0d400700e03d00345e0515007800024a4045100300000b50403070341403a03840e80c646010491001f1149100e4032148140400000c482c01400e131206c4c051041101d05105054560004600f680401e4030508119001000854617444110100340e0b00a48203006a03400000500c035650700f005160042030b00415400100b01c0b038540c50f00d2203240c41d11118860300c80302c03800a100e090342e0706c0c80c000d004150089038002280e400750001c880308401006d0000e0356020006c2d4427050460302d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 60198195 1250 60196945 60196967
    0xc0f050723010309050c04050c1b03070308090a1106090d0b09010504110102030c0c0603090109050304080a02100908030a080a0605060703091e030f1104020409050406021e1e1b010c 79
    0x7002003501c80d20041980b0030b015614201c2d81140c000c080821b4000c040000404000c0c00c1c41084031400c008191140c1504040303500305000c964051038507200c0c0c0d4100500a000300804106040c1c004415250009110302a00000484203882240c0c82d140001d020070622483c6074409040c03c4010f008000c00c0324815081144554480c40c0c40d010701030b503000700580c0e80e4000d03800c0f10906604004580c04060400001441e0702c000782d00000702d448459915001c0c1180e00540002c4902c0d00042880029801e05d0566007610408918200781c1951a182d2010385a0140c08045010080b4010225400c1e42e901d8100388003600b00180942e9858060340b601804500c0280304480d51807285e0005440d0208068061200710790b00a0102e1200800700c3e079411200084004c1141d03485542440081101c50062248600c00c0d442010b005a84100110360309241c1e03500002e802c4240c00d0300300301142c92121140c4002c40e10952030180b01d901d41c448114030101158100030901d00070761a15881401c441d5202c18070002d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 60199445 1250 60198195 60198239
    0x10b011407030e012606130e0705010813020604150e0303040f0e040507032909010b09180708010207033b041505030a06150807030c05010c0807020a080303010f05061305010c0f0507 79
    0x94134a0080b2003a010348d085244c1824082d040103d0402c050350240c50025480300c40740c0300780030000d40e4940c0045c8481c1c10541041d44000300b4500300ca201140c1010140006200c110002d60401c0d107450030b01031034492203000d2001e040c9e6120b8040b404202c3c003004414041c6500013443c00110110600851340300040c154079500000071030011613a1000c042c0710f001e10b00c150203819880a0ba649002c0c050303100c00004401c034100c1c858030100080e010000c1c40a80340c124480da1341e50810034031400138010610702a4101e180c55030410800c45100e480a610f48072038488003910040b403404a18400320100c3d40300d0798002c0350907000c3c40e26413000b001580d0384003003030030422500c03005444c9444603150344d9104002d003c01801e080c1150414030a070740c003461103401c0303661050f10000d207082c14507808200d01c00f10076842003441b0340c07020005001c00d003048044000509029100b407810440186405810070300d80780b180b04c1c1130201c2a0081e01c2404400381d083e056043d00581116549540d9001c0301a020310701840b84a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 60200695 1250 60199445 60199459
    0x30f0f020d0f050f13140d020607030c030524040207020303071101020f0601031e1e14010b040b06031f03050a11190305030703030c18060302030405010b011407030e012606 75
    0x2c10103280a1150b10301031803042c5132901e00340e60340c0301c0c1049400c1401201074405a0f01850703226002c0c1c0003000205000c4419a015190364105114050700b074800d009402824103040130104110070303410945503441099201c030080001415079000c60001e10804c2e1001e901800000b400c2c60a0160003a802070f003280d42a421100b203072207002c0007951205c2003030000070102c28140428005945107002010301c0240165501e208044180780444800d822186080700e110b60707029142003840d00c081c030540740e81082c20b0358140552024200010507622000b0565525a05a06048134052203c80440405507078044110366440c6007070301b0019030b4039003003c0c0e005204580c5140005c010706c03180040da00031654004000c504040c516901a4084c1100380001030400c0a10340b81c18005000030342e1800300401541e2030050741c0781010700f40a4251610000001e042c00b0030308031040306c840c4d016021624050380500d0840c40e04100400100c5034a0f407071750710300d1a0100340c1e81a00204007070052052405220111008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 60201945 1250 60200695 60200711
    0x111070e2401080a0c0207050d0302060a150b1e040e27070b0d020306030114010906140d080702100302040915060f0206090d0c030504091103240916030f0f020d 70
    0x4441c81505031100300d002801050224110b010913030094100d40c042c50060700d1505442d50085034951094207800c0e40164045070512203034802505c94050884a103c0d0080003031400d14010303100d50320a1030100c860614500c40b80402c007030096001e84014180d4a03841080070300b842c0c04421031421302210010b00b1410800c40341c1440b1180007900c9000c4a0007614154140340340c201c1158001c0d040100040d4055485182001c2060005101c0c68060541800d0014456003000c40000c034605001d101d1600030100400d806011a410030152400c1c2c076411102d108406070714100480103809283e1110b00114204902c102940200c12000e4090710f0300ea6656503050321502400300c1c0c0d214802c0c0d503002d140360806031881e007135030748210070484001d0b0007420414070f055a01c40d09030080ba106c50708501d4a0780004130900958003007100c2140d4140c0c104081420451070340c03c0000d1121503015114805566042c0002d926040c0070b600010002075225404020b4446140c0151010307601000440c500d0503c2c010007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 60203195 1250 60201945 60201991
    0xf070210020405090604050a090203010c21050103110415090c0903150c08010905090703080c01060303020d050c07060f032406201c051b01060503070b040806150111070e 74
    0x2e0364110707140200040e9254440c5010f100017007001500407600ca548a8070f044015031824001d4507500b1030595165142507254200c1e00452000407041000c10078144001000400c24840791104104c0c02100c0000d101200203407105031700c45040c1d101c0c6a40c1820314280d1418160092124800c50303002e100c580d0040d0003c800203204a50594030a003000c1200b00005000c0c1aa10360300043d4040440000c4035041d58803500c50300620f800c1690120b03441d0391220020b0080617410700c0380540ea001c0ea801d1540c20324484180b50f50b250010340c000c0500b04801c41d0b0290300e05034032130b0700460001d101d4003090084002030450140d001054070700030580031071565024a03080880030b1500e01c80100025021380b002da0300011060206120141655007085428401c02c00a58441140503c4004d400000060b040d0f103880f042c10704000300396010176100c0500784001c02c00303088080b07060742d8003a0200701d41d03030642e400c1c001c01615888025000048248250103001c29044041512903006030300011860200c40a0040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 60204445 1250 60203195 60203197
    0xf0609060c1f230414010b1503061302090907050c01060b120f0108030a050d0b0607020613030507080105070e0d031106091006052407060b0301050c120a060e010b0a020709050f07021002 81
    0x14080064154403c001400700da91003492401e03030346035a00003195203110000010341c0000b01c05507459622200205200c094074185105c4050f0300500801541006207000004070b008800a16581c00e1101c009200006a0b800f940540003601102202c00e80343d0300a86090220400121049403c10620344004107000c4000402e03100e583d040c6954461410031408200006820380c0504a43c0102080c01860016a202006001101070340c41010030644d15508016152860b6a84001400d9161009002c0e401c0e900c2601c5210504007a50f500e03050400c00c2c81d088540d28540031000c0c035103001b11010700104180110302d1303000111001c400bd0103602c0d00c81d810405014815150b481052440e0243d001ca1256000003030401d185c0101d1001900c0b5503400c02080c01c1d00c4c403c860051068a0005020042a514103d9540c01c00c809002c03c001e02400c0400c00403214006014006d1200c00214180194510070400800641042c002c14002420500d50b040340c1080151a0f2130054094025200f0600038244 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 60205695 1250 60204445 60204491
    0x5040218010e030f0601122402130e060609040c020c04150503010b121b031009080403030327080f160f030e01050a0f0e2d01080105040b0f0609060c1f 66
    0x30000e4000b5907e01160034060f02e001c030108490100c0881c4100440341e2800861800400c640c139800342c0c0c0c55541d6560307a0008201c035088080d030122044184156a243c02044c2c0b504003009135070000d4070300100c0308268030300003164075400da00500b4a07030910880c03240c0c5034076001119001d500034004044c08400300891810752424251190748840703103e204c510061110303030301e4807800901072f600368a854500c10800d64650030303000c0c1c8800b6030001e820410568184503803c034051140c03000009510342c00b0800f0000e4104044080c000000102d8070303005c007201100440c0c44214051148041d25142480c1c08200c203c4604c9056012401ca2080114254000c0d0201d448164465442c0640109240015501c1d15070352405543c201c0c0031030010361080d10180a039505640f00440b500760354400c0880c0010025001600710070700407400e240750341c2c01d580c550710110b00c4004000c85140780c640c6558004540a07011f80d5540c070384244101c0054203000b004403404180d04003000003090000c078001e0080303156042c1d186 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 60206945 1250 60205695 60205723
    0x50402090112020a09030203030301240507030c0605061507150c020c0303030711030904060602010f0608010e0d0c060212040c090c0e100809010e030406050901090504091101081005040218010e03 85
    0x155001102c010703a401043c50480c0e6007848201c03151a40c000c0391854001b40c005603420780903402007000300a1050780000c00d0a0151a1043c68801640c0e03000b0644043c0e5100200513075250340114001d40c6c0c030f000883e02e50400c502c41c010b4480456042c19401161a40000c0c02d0035481c0c806c4420405102164800038542c01500030b51654840190856076840010402800d40c001484894516a214050840244425070000c02d0740010850500100ca0113035101380352580c50000d65152584020603041c0902e4140e0401000da4401411301802034403030b00f2402d2054045001c00c00c03040181026406080c3d4500c0ca200f0800300c40008025265009510b103c2c070b505c040c840c21000103280c490080240e00c102d54400104400f06001da1051558110f60051070119801140c80507140d613002c00c014009043c103c1d8248a0300b00580c4940d00015020b1040904020a41000a001010641c1250300500020304110340d191181c4038442420400c4052080c0041d500e501c025809140008298010002c2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 60208195 1250 60206945 60206957
    0x1d0f0106050a0906120b090a020d0609050118030f030e0a0501240905010e15030c2e02060c040905061f030603060e030304020109230307030b0403090602070602030901050702010504030519020a0504020901 89
    0x410745a941d0311450041191102d84107200b123500c01030700c1d40d10105484500c61071000c07660000c507241490030344617040600381c0084511940000401e5000c07003490031a140d1360500107418065000c0603402d044038004050950740c00c1244540080c0b0900001d01c205070710100c0f14402190b02c910400707003921020311071a003001d100c11001c00d0078404800056619080005c0840b030035070040c0000710f0100b4103007131001036413851804c17040c4204440788001500b8140c05803010b03111514040c0c245d030b6494051406500d42142da1080010301e180c4900102c2d00c2c0511007100781c41c2c12440c928200170007503c024003003143d900b41803080759144004008140da0050358142c5803030051509001c5403151035580c15848020406c41c40c0d52030040354405000c000055800303110b42c030110f45418103019204940c00d5020004550043c03400308140e40e80403042d81c0326280700b442c01c10380c3e0302c800b400121103d0150b07820190640c091100c88512042c1d0248896850305d1094541714001c683d1071080104070700400c400d040c0401d117 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 60209445 1250 60208195 60208229
    0x60307030e19060501060915300903031a010206040f110d050102042301052b0207061b020607090e091005090a0201020114010803070201030f110304050d091e05041d0f0106050a0906 79
    0x1004031446028030104015909c0008038400c0411a8268084210440607a9410000c401c2c145e060181c004000c86207106144c1d0100600d0000759500da000b0000341c408440700c0150000c02c200111034400717400000b480d85000351120f0420034000e42c403d00c2419140f1010035031007040a840405004031440d01610b81c9405c101520440c981e214050f180c03000c60b2481102d00042d076a08882c40540781480c01a000001c3d01454915143e55210090440c0005d6510540070403000740d602c04008400da0b520041201e1710342d00c515103010320300001e0b0038811070110f0901c0c041020460380042c0c852540b9000b6030081c026141014201200c200c42130040a406170410040b0710059402074211410032100c8640c0003400b00c07003050020307601c1d1700150390455190b0490411107010030790002d2a180541440d031000c0c440d20390b14003010b0355121814801da600440c0c4420700380a1080c2030020819901000d03400380e84901102c8801e1500030800c500520740320300360840c008100c0042520400701038400360700034901034403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 60210695 1250 60209445 60209447
    0xf090a0314030604090507140f0f061c0b0a1203170103050303061002030412030917060c070210020a060606050a02010f0b130e071e09050115080402060307030e19060501060915 77
    0x42d2000740610b40183c0c40d401164002141003010703000400007007070030740304400340700b01007140070141c0c1007016100381095030500a03c1e650300c6c1c08a60340c60002000618080d84030900d400003409075a0f9000764801102000000c0381d00710612512400c2d40b19036a60710181c854095240354400082c0000b8000e54400d0001a805041110740c139a00581e450040340d0500f0356890759001d201d610480110001442e4202c00c000b0110226810007005102a02030401c510700318140300d1075030254a20192080a0304258000060b001740010040789810000034000152600e4001d0f00b6584a440d40b4001986803900c840b031040f1040c03003180ba10040c01000c03442c0d29900c0759602c1d8041c00c500c09180703106001b4410002505c84580807800100401c0e8134091180307525291200b4115581603001140d07200d01c11501361915035202c81c00710f40c455411900b5645a40781d00b603045000380004500c0058030711030800070104005000f00f0f000f0304944148028845e6a0700c0d040115101d0444d442183c0400d10003081e840041 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 60211945 1250 60210695 60210697
    0x60801140103030e1309050c010801170d03090201110307050a02030c0103020703020a02060906040b0a030b0109060309020105160501110d0212060109060206011203120903050703020d0201050709120c0504050c030f090a0314 97
    0x18807801000c1c2d6011030f200445d0002100c03000c000072030f000d51000a0100342035800c01d0344c081c010160700d6824030003541040c025a4580c903105540a040640d620307203000848e0300480c034030b100d14441d10702280e44803c3c1c1413500139038940d4401d805920a1081c80000c50841d8881d000700e071603060b4943d010340310084581d030074840306402140f007503a8008010300c030100c2c52200700000b13003645c002169004212081e0f110005821429150030040405041003a2200542d810108458104010350405c180314005803c2150043c40160b0311041107a20015200f1a252090b070050540070a500007001d03040d889182c015102081c45200b00d0000d13811070f0004100d0b030900c0c04006155180a82030080c901c06a000e02c6104880c040309044000c0384011030f14506040c1c0c100840045c00e809400200014204410083c00050b074910846a005105800100410031140750360002000050400c1c4181d040c4424502020303007045a003600d0f034036000300019403805000101038400a0309501c1d0140040c0700c141d40c0c80c642d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 60213195 1250 60211945 60211967
    0xc06020d02010b0f0a0e180d08071e051206010e0303040f0603060509010e040308070c0501050c03041506051302090301060305010204060e1c08030c0922061401050403050c060310091b0306080114010303 88
    0x20002e06512004d0032414048006000b040396240d8080f0324000074041c5c01e0f022100e55aa09507142d282c0303041e40081d0030330212800615032500d003d0269441c400125881e5030340c1100e05400d0700010400250001581280009807441e584003404410b448005200303404209109070040a103d150102d0301190007503009581050241c07802040246990712441d0940300c050f540207603402e0b030001c00c01081c80500c410781e180480780f8840a1000c2880d010004090b40021555110b40990002d000d0310140c0c2d0942c440c0000b998010001c2d9100e036034650001d029000c5825034075008445000110b07210041d072026242c41194040e001074116203075031581c007210790015040d0b190411315102c1070008802001c3c5030700712907141c0c0c17001c0032400e64100884514100003200c2068103212050205000055000c05c141c1c03905001610b0090b1295a100202d500ba1981c0d5400455a40e2418010403505011613000c480180c1864406101c1aa901c2500b00e08032090740910400760010304c0d006100080c4030701c4034100c0e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 60214445 1250 60213195 60213211
    0x504050705070807150b01020105060d0b0901060305190c1d071409220b01020d0e040e01060e1609120b190e030a05090906090c0703030c020102070c06020d02010b0f0a0e 74
    0x41481c4860f80c3d10042c59008280903035400700c4a942e801c0e0408600e0082c01e442c20380a200901c424101a0080344c420560700b000100320042c0d840000d08480c034258030000085400c0380c100c42d102c1e0040f101c4100c41d040c5024040c0d50200b14240046a0100d984690400011200c0b20442c210313620b81404441ca84444010000c0700b070010405000d0366078514410345440c3c3c0118045102c0c24a0003500d110440c0c1c10020303428103541244a4071506541c0000000c02c110001750740c00f140c02100d1040090041c04035800c1500311100c11800e00800074030b040d42024a90029448a00a140e00d500c8410200c51000348001d04e0204084001000d14920240031040032032040008270b0514101e070280d40c155000000400d00045020030f206070140b82ca94011a0044130548807110300c1c0c24010301944052040135000380505407a01c01103900c1d2031003581150542d9410411803811345880e04002503c40109500b19001582071081101d82458404064030308a00f004180c1804a440e00c04e90300700d942c81c0186092 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 60215695 1250 60214445 60214447
    0x102090402040303030f20040b13030605040b07110622050a0203060109020c01050c040302210708120316020610060e04140a0506030601140607170d0603030302041404090b010504050705 81
    0x1410303445500191002d14400d84010558910741c400d4101241d80c403030440c0e0782e00840c940d25850f420f0190803c45055440369000640c0c0c52184269503944032902c0c0d40010011481e00e020001032081004c4068092822662070007181441744141a507148402e61710b5410105a102800142010b90042c40410921803c10385481c1c016540010381481c1c0241e21030403040743c0002e40c00301440c0c400e21500344d0101c0151030807810039055801091030710b20301100880c070201d0500c0c484038901c4000c0000d24001d010105c122034104e4110040000550800da84000d41c0020000007484898004608240b28404440c40ca0400624003201121212141d40c1c0d1140c2040d602d10398550070803118a201489180181008030341803e0010500d0f14211050b4403885c0c44114840c0c142c04d0a541300e9003100c4000360420b0641c3c0416176000204415846450501c08a292520500004050f0560083c000301c0d40c2f110841c140030f170282024001650703000302004141449940050103a49002c1e400b294020750186001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 60216945 1250 60215695 60215707
    0xa1a09120a0c0b1602070501080c0909040203150c0d1a0d03081807080304080d090f0902030604020d090b0106020601080a030933050301030b01060915080c0c0a0c21031d030102 77
    0x4070900d100645002c40c09429007492411381da0780400c2001e000b004286801c603018034148000518a000300714600303100b401c100b400325041d96010083c0f074100c0d042034507888171f01d4200101c07081d50f01e50014940955650034003c4041075131f40b41040c8496020707409403015104501e00da400f110180001011802e550407180100b401c84c4504102680282c000e8a000716078441c14a60710602d003108501e1440304015030040140890b20800c5400740840341c8410025840e5240d01000402078000c6000410006141081d00000d1003503100c1039904841e1281c00f5200c43c1d9032241401501c4090036080640401c80c110700400194541011006251200c4000041d900c0e041d5010900000502030041e40000c80c080014814082c0f81c03c1c049005182c01e00300110701e07601c3c10960440c441d0020070b0107421b200b1210001900b0740c502108640c10000b80c40b00b42c403c0c0c09141c1c40d102010169600a1080c0304150200e241107185004860040880d055190203000304001000084410005002150555024020 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 60218195 1250 60216945 60216953
    0x3091912080408010e0105011a18100518040c0203070201080a0603020603090304030605010905010f120203100f0609060b030907051207030510060e0603010b060a050d1103090a1a09120a0c 82
    0x111036005100300714469446160103c06420340c0e030300f0761110031540d2506004012501c2c040c0c11004840b040d80e11107a8071240e0b021000420f0112038a4125000034140341400d029541c804005d1002c044200ca0103080c1e00c02d0342040c00100c82ca10252603002d680100140713400341d8000c6503d29441b0700b0400703000c91030700d4883d1302056982d0400d403445102d030350022900b4400c00006005032230241c16204004c00280d0f141c2095030944581074411842500405142901503444c14440351844040303d8506203d0030301c1c2c1c0b14001000b00724a100d898551407a160007c66040e00320300490740a0983c00e0000c111050900c03040021030840092020450b11441c500040050b00c18001180c140052000005100b45008a000050f12006000c2442649006119040c555524080d9810152545001a00c5252034002d820040418211072180710368040100640050b000800f911118401d01840748030902000c0002c1c110441a55032075410740007202d080c6412001c07200030300098075003441c00840c0207100f0b483d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 60219445 1250 60218195 60218219
    0x5070206190c1203110702090423030c070f18020f04091b110a0c06050f040302060705010605100503040f020402090d06050412020601120c050d1a1e010f08030919 71
    0x6070820209021410400c20300c044042c100c034100c0c3c030506042c00000003040c0c00b01040e10401400074466031912022800703000034024081c610094143d0008640800343c0c00d05d640d02e80148041c0e4a662165000c046500c045201d04c80048449018013130910036444d0a5190194112711040b00c03124200b40030004088120b806000c0b80a440405000c00000c0201c0c002811000d180005503004e0780104100310000340190003500c2200e0135450a42d8580c0714090045c2d40b41c0c41030381e001035408000441d0030342c00d010040d40280219001115a0f105500178020252418007048170050800041181c2e8440981010780040000d42c41c02080c496080b040c0795102402c5490558069850f20f01c002c141948a41d0100305660141511110307040031019241d0b0b03480c800301840d00880f40203184582c0b1820412095034100d800813902d40b840d40103a4a001511442111003400200055000110000803406d007a80d020750140c80f1008051032401c07040030309202045c450780d1803181940c0741d025000180102465 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 60220695 1250 60219445 60219487
    0x330e03030a051801050301210204180302070e0a05040201020304030609061e0b01030501060e030a030c02030f0d0503161b03030506010c0204060906090e0601050120030c0d030603020102100e0d05070206 88
    0x915081e403140350440141a44011583c0000d051080410051110391680e0000d10100302c1c10702440c000c12111440818003a0154917244038041440f402e031201010f8001c02d50000b070380e07031b02c207107600c500d0356144515019a0320548010f80503070001c0009102180580d0040741040c0c1c05400c0100703141085400c050004558401300560480c3c0e600101070441d079045c02440e00501c1c1d0351070180e811b00074040009858450b28000202800801d42c83c4a08544083c004d007000103181c2070549004030350100d400351599101312184121074090306c00c400105030184800480c004400b524030040100303280c2d001d40090101074034103414000c10442810059440c2c1c05414040d0503540004202c15203800d180c00c06850b91003241d500c4039003048005000c03a981c081d2001e5852902d00100311000e6208204641c154483c003a020f16003801015540608940c00d6003020040728402e07821504d0845c0da809500045070801207644040342c004070881c400d000c1c440c80103002031070300040409240c41c03105070705420b200b5610 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 60221945 1250 60220695 60220697
    0x4030306230301180305030c0a09030f0f0c0602060903040614070c0605090a0b0702030d030506010c050726010207050601090b060f040e010e0f010f120804050301051f330e03030a 78
    0x100406a907a0030300b0700130031080c18503050008a600e5001da4018041e804001c0c030504d040c0c00f0100345090a54804c2c2e125100542d01324541c1c01d560760350750515040c05214000d080e19055542440020500d100240395485100400091420715050440885005d0710301d04800041450500450010410344440b00d0b00400361500e55a90b0b8030300e044184541429298412420154240010030142e140440c4101c80c005440c035000496942d0800140e03528801108054040d1068840c08211503d20070202c1050300f154031010102c201e45084490309030322031040300422035003200380108018019500b0004c4100e0006080da03040007014a14190f00360003680c40501d143c8081f50040014010b030518054010302008607a041c2581442e11590128031284204140000e03410120000d01c4200c406a4020300b000030000c0c006400c054214a8040c1400c20b929050310701004d600044080e43c060b1a03420005803074080302d42d4601c2084880000380100341710301040c40602d140d0060f095805000171700880b089 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 60223195 1250 60221945 60221999
    0x3050f0a0303150f050909150c030402090a0912030e120705071e0e19020f03010602031b01060807060c02040f0606090f05090601090302040f0905030c030a110a0f030804030306 77
    0x900700101610f45a441a401c030200d6088140220001e500c10502030303d1007612018003549030003841e989001d02041c280441440840c0030320402e00c003048001c3d40114000c545105554a03806583d02c1200c0610700020400032180e04104065400f070f0304007140050140c01690410034880c3c242da0200c0e406204111820b40040704203000600348040f05c40c2a0740c0d070321600501511300b81801500b2141c0042e0001d41d00603a900b5400c42444d030302c0e80440d089540000c0590b0789959503003001a5903078205100e00e204054034101d98012a21052003004115481070700102111841e0400950f1480310110040ea0000d8691001c01807501c150700548004060541c0c802c00d18a152617019100502180c01407032040045500b03004550ba401051a4152030301210700041d0210302401700d500410040d00010454000455104030189010000c1c105100a54890701c1c48036101c9500341e40c0720304040c0d50040c10010b00c1a007500100e880703101665401440f0f8200010010b4039020341c034480c090480c0d21081003001c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 60224445 1250 60223195 60223213
    0xf130c020d02070f0305120309010207080a030209031e0d0509040905030304030f0801080f100b01020c04050a0c170103080403030507031101050103080301051008130809011803110306220308040c03050f 88
    0x54100149002401400102c00c01c1340c1c11540c607a0345604442608004005000c008500c480e0021350407600c615a1000071195507840700c5d580a800394000c1007025200b40100e0300d215810184e10400d00880d030000d800501801401b022081d02c00360002c10350940c00c20b41d0303036590400003141040114000e038001c0d112540c0c50900340ca40249001d105800041c0c03290071144102c0d220820000b402c0c0e0b004c81c1e4100010610082c50f00040b440c1842004a25521605050038042e102c9082d40c4000c406c90b45646e200102c508401410b025504001c3c40000c0c0180d40030001040401c0c400d2014098440c80f0380b41003c0000b900180342c80c251002130b04195240b4000200403c031503d480507204040403c5410000e07000e1900c140f4001000000b100b025007034032400113000070340b6032045040d0030400e584051080c89aa499042c0100c801c0600e41c02ca80c000d101392000306070750000d103601000c5611001d201d04481c0816994080750720340340c003130300c2103548151b5108040300107042441007102818550700140fa2111b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 60225695 1250 60224445 60224447
    0x9060807170604230607030f0b03070b09040b0a0f060f0e040b010f0c03020f01020a0206100b1c09020f0402030f060109060f02120c10021c0c0516020f130c020d 70
    0x11a19070300101d01c1907410191241d1140700821203075841904683c03800d030050300e078980a022034886494150014016003080090031601903100041138429080c0c2000384010800a050f66901a4000c5032600c40041c802c0842a261680141e5401c4030083c0601c6d2006070b869810354401c4490f03803c01d10126101c50080303440c4a074008195444a8000c5405003c1c1c40c44250020f0181a2925414010400300040903000e0500800103560080b10482c001c56513400282c10003529001d0551360206894092000001c0d46091030051790f50881d031030700e06035041c242d00c01045001480c000c80101d0700200c6100482815079100c0c8040c521440c80040003e0192070b1a800042c083d60081d0055010b024540380d041074411b90000740700c8148000901e07080e940351060400c20703281258078180c0350485400080e010350405003900c180d09100c68014400d00c840010100250f0310b03805a004551180c21803c0e01031800340c80c1400218140c5900079040031000300d41004008107454030700c181c0f5400369100d00210201b207 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 60226945 1250 60225695 60225703
    0xf03021006030b010302100e03071202010e0303030c030f090705040f09020418030807120b1504150203040605031b070507060908070e091905071d0a0f050402100503090102090a090608 80
    0x2034002100070480a8259580e07550f46840602020f8040c0702c1003100034211a0180607004882200107045500170f541d91540c11080c0d45004900320300044003010009000d007400001d803400b618030066204d0071a44c40a0241184900040c18075442e0700c10301e14006015152481038200b074030913481d404036003805e01e4014002580c0e03440c6100083c01145102600c0826404141950000e402d45801006001214102d0002c1e00039105440c0d80051030000310608014054000d10448901e81910781040c0078042c400c1e605c90060b88141c0002c6001000051201c243c540720329100d9449000038141407441c1c1d61115451b256090700100082409640144042c0904220b000000e02100006024070b2521392429a210016581102180c001c0004003104000e810321148001d400010038101c042164200b0b452080b0701c1c140c401401051900c01c42490700320150040c0c51041d07030041d1411500000701700088600d60301c000c0840201d035500f03001510190707454404080080465003000b1800302d040060302c0d820 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 60228195 1250 60226945 60226963
    0x1a130b030f061804060c0302040305150f060a0f0b07080403080d06140a06020a110307051003090201080a0c17100b041d01060203030103020d060c090b070609030206010503030418021c090f0302 84
    0x31a07000351102c044460003d8502c43d81c001d0b44010081404a0340d020250003034016070300000c0250203802c0c0b03103d90041816a2452080645009121803901c0303190a01072a20301c903000b040030b2502500801d0210070020001040004c0c45603042e5460a5a2a01d4a0350302c1d401840d00c2084682e00ea450030003420038084485082c0f0030044800410091030900081d682e80900d10000300709101d07080302e0f2510340e501440031000a0101810f090806130301e03858018001e00f0658000c0340800d2000b00462200d94683c0324a800b501d0a41c3c503a0300c2d105460080b02181c049000b8030018440244010210f1544001e8004e0b0004044814401c036540da118103040c1140c0c501604905c003194414801040075981e860814031007150041400207280d1641802140c0b4941160480c0c04158400035070744d010400c80d54031100010b13010f6402d40e41580d0301c55040507183d00c0307030740b080990004050601d0000440b0590003010454541c0040704c4003c7c10001451054404d03196040c0c840046003c0c441c81850740500440034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 60229445 1250 60228195 60228199
    0x9020a0e070e01140403050102070b0a0e240603010603020a06020d200a120e06070f12030605010e06130510020718050103031e120e0304060e01050309071a130b030f06 73
    0x4030390701d48801e004101026601c002c1d410072407001c0c03e44401c043e4500c210b801440d003020080d9650b0206080500f0b070f0300e03010f0342d10304a0140381c00c04550401c040828808600c843c90f81c0c08502540810021414160780540303641d505543c0c82e04000010382d1480d600384020180c5802401041400460140540d280d04c80c550900020703000d8643c0124402056020300c203a0302286030b01d0380020748107040b1111464481d09503080140040c012040c0040c94880c000014441c4001000b640c1c080380c4118160f500702d220745030100f04080d10881c0da074a8420080d20081651043c0c0c05050303556080007a42007607150030444050303001f090040c06012200c82c0b00d4844c0c3e440c0b017142440a5491075400404a5a40064610340307205505c423020202c5201d010340c00b02d0103602040a0021000c48007000b40c80394070a10901001c5980044154080c2d4083c2e01130702e00c00d6071864041d100c10b41c034220300803150010151045002b0700003002040541680704003000058003007d005a41c80b071405944509440c2c0020705414 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 60230695 1250 60229445 60229469
    0x60306030601030f08220504060506120106080a09020a0909110a0308030c0304142d070308120406020f0f0306040b0d023109030806030606010306030f0803071404060309020a 76
    0x21a85000a805045035401404400804014100344486025000403809a03e458804000540b044070422000b628401c0703404001e05a41e038001c0004501c11103000710a0720f510540100a818004e262807940005148008200b485660303000814228064001c11492560f81c64800103000007400d00b45520035007543c0440005082d51115400e60100a24480d007442c8000005010000040d05640c60340c09c00000300d41340a003030758004110394072500e185403510100c2d50074a01003c442c00100320b4100c0742c00020301460100b01e0700c030740000068020410788a2a8080044c2c1c07010303142681c01812034a46d10098a9264103043e81004240c80003000c00703c3c403a04d03140c8203105c05aa1852510440400c4200c0d415000c400051145c1001c40601c502c15a01c07a494651080b05040d0441c20700e80c807031034044050f1040c1d9640e2500540845034a0702001d4031480740c0030902000901c1c0c4500071604100c980c2410b003c42400134000f02c8039a4031507000ba0000030f40764101c800841c01c00505e442e0240c81c5a030310807 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 60231945 1250 60230695 60230701
    0x1e0d0e06101502030d05090a0b090601060c030c021f17010602150a09020f0907050a081605071217100503060601141e040503010914160b0403021e04150501020c0603 72
    0x3403005149140595140c0080e0504640b111900030012506007100d000c1d401d101e00d02c0c04800b0355444413050082076400e0548880081c8c80500081003541c1a41c0300c3d03441d100c0781d140c07058404840da21103d2404a070400e43d0380301140c925280c002800080f5440540d5130891038211440c0200001c00183d0212040d50311403065030040184d1615a40c0e40017912220018039007401e0300014500801c85443c40b5000300c500c0c01841a070035072150041030b1b0010b154403640b038551911004042c1513841166031900280040c0003034000075105004010700042c85141035040707141c058040101e4600191080d41c031174500c0e20b8080005040a000c06940542d007420900144141144800014494414a429001750000c55034032481045020350700601f4014000700b007091420300e001c28603441425145000c0d4814118110b64203c000d43c090345c1941c2031400c10703d0900e840c6600303011014000c0141d00c0041192049130080e281c4442c030074100c5040000120f139440d1403902001a050422039840a805800e0070010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 60233195 1250 60231945 60231961
    0x1e0f010501030b0f09030702040608010e01060e1306090804081209040c05030f06061606090f020f0901030302120d0603050a03090504060506090306060d03030207020d0b011a0301080607080901021e0d0e06 89
    0x9000d82c4100c00d511102c04c0381d42d5044c0c1c00e90440c0f0940000070f500501d041d101081d4150b05600c5999002c5042c4000c1204a403118030026900c1c004880b02525600c1b202c0d101d2000501e1500f00d0400301e407159002e82c0c2810b464414030b0342403083c13084d440b200d000310100c0c80141c5440d203806134200159050070400c4c598180801d0900341818000e0946029583c001220252086401842c4603080d4000000308107641240ca000350007044d000ba801d0744034043c0401c40d50460320386008a14104d0798590028504421070207900b030b456400c03c0d61400010303580c07250004040341042c486414507920a5803110f80c0c9a081c1000c01c4200c4050b40c0009008600c1070008080d030380c800295a0340c00200498480129810a1800320040d02c940207000350040b0700740e411041002085140d03541610001c01200106000321403018502d40401d1064400c55480000802c060b18041c41c0a103401c000c0d56000589000c07034000c0b080e402031611407a92100b003030001030152400b000318480e1340b0040600318090181810803500d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 60234445 1250 60233195 60233213
    0x3030c0e010f0c05160f030b010602030a08041511030412090902040f05040506040603140a030e03060c030a1e0501140f100206070503100510031d010b1e03010e1e0f01050103 76
    0x501d400c2440f085140c0e00c410311400300000041e814110102e05a983d40360720300c0014040041c881142d6070403400001040b0300740040b003030b1044003590741e80300b080075540c60701c51903900d2401c0075500d580565289910420314404000444c0316a004d0000a03100f086525001050352449920620300c00e44180700502c4400a600a5001110000c80e000310742a21464001001000320f030780021b0941c282200d001d001c245010682c507080d24081d40700c410b40c40744244103146d1107907030884e41d40000c00310410020382c00e0b2005034800084082c00c100301e6400c40140120b0725044600a801102c0c011003090540c039690f00d03180304014803414007503484400313418078108069070754080900070300c06010011001a680f10b024402d0348008080084c04070070b48203600c400290081541a2007030218045591481040d24014000c0c1d280c800700c00b900b02000030300044240100f03150a02d82c819403554076034149800e444003c00080da40d02000c005d81d0b203145420408180d20304500080401102d034101070040012981c410 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 60235695 1250 60234445 60234467
    0x60c070b0a0b03100f0608010203090a02010f03050f13060209040f0501150207051003050c0c19020f010e09010605090301090f051b030d14181c030917030306060705030c061303030c0e01 81
    0x146005c00c081e071038248071070090103454001501a40c808010011000000151502c080b8003c1c0c0710020030020003a0210180c0f841122940310181042c004118040c0840b0b18091000c0d00400d401410603625500007002d4441c401c003a01c0341e0588600040c0180ca0080800d40c00401640c002008002d14040108000c40001d0701840c00f4155642c00182010082c541122103800700d00d0700380d880c8118040f01c83c26042082e000241d010324641708400300c2c82e501801407080080310003068410241e00e016002c45503a4082301072250555221032458002407441c90440d403030188640f0280011603c0f400000d0031000d4145140c522a03484a8140402c690300b118041c10325080089260366a643d2094010030b4003a044559a80c00c242c0c0f07070000d01034010a80b008030500f18441d80d11000600d80e0b0749280c060884c5c40f1103003003909070010000308500c2d10b041c0c801041254810301c1543d061130500c070009801c100049400b003e085110310019000c15a25120f88995800c503814a41004201c00000030b1890301c0c45 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 60236945 1250 60235695 60235723
    0xf0f1b050d0b040b0702070806010303030614010311160201031d0303010905060d02180c070f03020312090102041d042108090105071b0809010c05011104060210020702060f1803060c070b0a0b03 84
    0x6804208117610910800740071b05600700442da01969a40b40003001000180300f86a0340b0143e500c0c20050b03641c824001e03008094002005a820808840766041e8002200c0b04101d040c5581d0f198240d45803c45c0e40c0c6081c203901d03031090140d900c0391f24060040c0191000141010320a0100600381001660b998410401840340300c10824459074907c440200c5511030210301404001c1700c04e8040041650010042c640c00320350f1044d40480e0b484600003942070340a14002d89004442c45c140308482001549042c1e5809409543c1d0040c90b00c034000c41d40141c9040ca81d013080006081c280820070780c00d2003401981d401c00641d03e001e07070707482840d401800c0c80c4240010004180710360010f040302c040d80c419504132003501d82000081041d00c031021000800c5501510490025015a61410109100078825100a290081d10170351030040402662900c583c0400d1802040d100d64403694941c07074504111507031003003180489840e650240307400c01d8408084010000041c40c0c0c14135003a0703606a02c012400c5a00341140c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 60238195 1250 60236945 60236963
    0x102070c0b07062903010e0a02060418020f0c0102071a040203120702130501060f090506180d02060c07080105010306050109020705151806090717070602030906070f0f1b050d0b04 78
    0xb8070314210300581000c1400820040c4000f100b0100200c0c030120b65070f80080110020404541c882c01075903190119910013035880f540a0000f040509045400c803800d00d1000d40f401481d04880c9a0074900c50380060407004102e139408921042040300e4517400e1020501100300361401807034140c0c0080c2d5580200311080014a401190000854503500d0f2001341030100020300340080d60f11008002c0000008181c84d2000400c2c1c0351340001e050034808200d40c40c4100c0481900e0190480005102d50b00c23180c6003089801c100c08008402204d8010b110000280044400106481d4514100302c1d09649061304003401c0d00348100304000c0018400074600f03401e03811000e24500b032959084070212003025101520b0f6243d028200030440d6500e000724000c429542e039101400f01856440a540f030fa9503602c1e000c1c4c040541c0c810000550545010000f07050301070b110780003e180f03064460751038003a5020030f0700d811180840b0307060503a03a27801d025045220103044191812080b1a0f8a602d07204020301d4098806482015 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 60239445 1250 60238195 60238207
    0x30f031e0904050f040309060c03080a0b01050f0301030b0609010f0b0d1104050406090509010c030b01211b0309020f09090a030c050a0203030a020d081e01030b073e0102070c0b 77
    0xc0540140e40c01a140140b0402c21490a680622100101101c085002820014010440c0c0e402034401c181548d030940d8990050303940305208040181002e8138014140700040c02080c0040c1043c5c00294041d61080c0c0c1f240d401405d1801c01c0c49034514044e00b01007140c0710490001c0c0842c0302d802090740d444c000c4070360000c110000003080581c2036114540005400c45c0c10201c000c034080c513103904580e0050130603100800404058060440031a020780001c1800122a001c11202c5d8030480140d1505401c0032100c0080c0d003c00c0482d036809071040080691700465160000e100642c40c043c9001840c3c110140c80d200954a001325800d52540d0520346c00500b400300440304482404020800c0d883c01e55406011699074071041e02d0041e40c1d0301802a035443c00110104000303004000030010380191260020361403101a42581d441040340b01005014104000110400800a10305010344039102d08031041251900e00e211910640848998550408240e00405c05c442c001041001d0f10001c441008440540703e807 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 60240695 1250 60239445 60239497
    0x50405060307210c020102070302120c0309010f0311070b01170105010305120a031107030504050a0f030f06020901050c0a030f02010608010608070611211b010b0d1b05030f06010303020c030f03 84
    0x44445030f14018500d0701008860b030a030150f00508440d80030780c0031642481d0002d0490310b003500c180011004142c00900008141c0d500500310141040614200810041480e800c0900c0f00d40040609071052400c51004201c2c1c0b0a9020b880640c00818000a21540d030458030750369030b0355415074521840040e000a600000170b11139800030a4003004000b50760b41d03408007402c006009800501816104001d15103001814070011132420048030780c42496a0f54031951a02c0e040020b40010070014180003041004c8080d0310b406018401005100b622178042c00d045a001c0213086850580000741d0aa26000341030000800c0000e100c400c03030b500341c6880b10342e4440800d4080e00385060074110444020a11030710080305202c11003c0d003000d4a0518020721000c40c0407207102d00761510ba0f940241c009426000390b001080c0301120030004d00c40c1c0b0640c0d0180d403960f9180806e01d00b10702103400d111140c11000040c0101541031150003d9420704800611181107103c02654592280c0c00c2e2440d900840d440141c1d001c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 60241945 1250 60240695 60240737
    0xc111b010e130f050105030a03020c04050424140703060f0506070317010902030105030c0603070c030809010209130504051c170a1104060c060506030714041104080604050a050d050405060307 83
    0x1104000c1c1ca900d406070301802c5150007034224580c940340c2042c1400004212414005920011a90103500515990300c0b050309102c0140009030043d60b07180d00308104405600c100c103d2140712208400340000d803d85e03880d000346001041c0500124101070400c20700b081000d03040031898043c1c0c0c80841d0466501da80c01c4c0360030b827030200c14981c420241003642d5000041000c00c07580a1812640240d044d0740d03650440000b0030803103100455144022913494070a20000c68420752103a40e10920310b40c001858540081e00140c1c58421030a2143e03e856180e608102c1007100030700c405180c512031100400c001c6036918002a00d41d1541c82c28160201c071100c0001100c00700160056505150240d400781d595581b64034000300260002101500c2c20f030b0a00303000c9501ca08000410f00110750a600c003000b0010341c00c0341040064056940a180c4201d0103120104289005211017401a0711a6006040503000c0d072401508144016a001c424420f00b13110800240e2103075400c40b40d02c00300a03d46000c2c02a22250b0300401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 60243195 1250 60241945 60241967
    0xa020706110718140f011509060f0513050a120c0801020a0c140a0c030c0e0f01050604090207060915090b0907050f010e04180602130b0906040e09030f030408070201030c111b01 77
    0x1140b441401710018501c00d04505aa2282c1c03080041000780c100b06450126240c46500002000a854500da5510a9010382000300e100072603900060343ea0340000352007021a1304490798864418003000704004078012108008e15003140250f041000c1c00c00c01500c0380000303400140074190075245401406205001611500d940115120b05050b101d080c5110016850700485d0503841054000c0340c1c2c0146c0b00003020707049600c01007841c1d1402d030a054191006e508801030845690303072214000b4002070f1080c8207040b81603444180000744607602d410640d80c03245002d4441d000300d0300140014017680c2c40d81c103881c0007501428200700780c0b50022040810300800da9010308040b2102e01d5a0603004201041d001001e010110956030f9113881d44400c0921910300c0355601465008104100800c60601420f00c120744c84405801130b207040072209810641103030700841d000c030f40e0720a00084440c115038140c454003c6100291410580c0b42d116845060342d01e031020343e03509038044000d12240c40c40d68030a41600030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 60244445 1250 60243195 60243221
    0x80a020609060d0c05120a0207170c100e0f070605130501031d0d03090b070e0102060412090f08010b03070b0306060306041509020d0e0f0307080301140f0604030302030a020706110718 80
    0x29111300c50000404036008018408001114500071500303401c5a4001d540070190400740d00c000c0800c2d0240c0e0a03c4c15404042c102e0080d018485107451071035034900c200313408051000c1c058614080c0000349582006680d07009401405000d01003030010103850210081604d84c01c1c20000381000c079041d51810390950750000042188200c40c03541710120f601d07800880d401840750700d00c03000c0ca1322748800c15a10610030f55801c3d401a031081c0d0000300801c4804942000645541c00d009042c5602e900151070354518036000100c141c0e454655400c19401c04100c03420081c0f485000d01429800e00ca8000b503102e00c00641014070442e2500042c284581c6400b044000800c03028030115591900e01000c0f80251003440780194540c001d2010001c80340c0404011201d2045d44406103501c0d503030034010f490301c0c1082042081e40c0c004040c562540ca090700c50b4002030001e1070094000310380f0389502101c024581000c580140080200783c24440b9420500010350100f030382d003d02e424101d0740810780c0d40d5800414007080d041e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 60245695 1250 60244445 60244451
    0x203070606180b041b0c060e0717150c07110111190203010f0c0e0d060b180103111f050a0516080406090e0c070b060102100906060602010b0109080a020609060d 70
    0x144420070801c0078420310003942e40074401c0f800d800f410001211404510030550700007000355294a10b00c25185881b41c2c2e48103120005000321601045440c140c4160003100f842d03072a0354041c01c010002040340000300d4a0004c03140400b07142c0511066541d0068200003040c14103000d140383d00c541e02451507000d08440382c104481240485204c070b2080c5900c2c000c2c06902952a00d00e50058202c040e003d65480c44080340c45100500c21014280003005c01020000e41e495565001c07001c01680c3c4006103d10400c0c44000d00f0b86095045060134020300b001000c6040c42105a42d200080c42d80c1100400081c05199003045512030320f010000303031040e01c13800c0c2d10340c8118403421b41e03842d0400003401e002d0010340710729607103003201e8680790b110044401304251400d00360705034140015000550400340da290300110600c10740e00484142d000600a903144810304854003500d40c1c6003481600d50900c41d144903c0c4007460700085c800c0c6412080368540d13000c1003010b07024a00000d80da280035120082115441c43c1c0e001010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 60246945 1250 60245695 60245699
    0x6140702210102031e100b090d0605010b03040c06020606010f11010b0a0305030406030b10080406090218090a0b0606070201140c1e0601060806040b2d03010c0c0c0e0412030504030203070606 83
    0x190013580116515800e080940940c00a00c40e40307481528490315a0301191002941010551201c603080446150340c0020031081181c0010254000c46008101c601a500d072a400d081c036002113030141d02c1d04454119800101004003a83e4000007500505026017010542c0441076a241400740840800c1d898021962407000000c102d40003000344110340e41540c0400c2038800981c2049a0700d0b040b41c428400042103040400c012030302c241e2020034280d100804440c00041003100448151408503200b2046070849124002031010500e406a444001241c00c00d1502540e80d0005e400c1c0c1003111070510407041d01041090704030714101b241108800313482c0d2500080d031603031100c8107642c2c6109000e80000144240045041c605040c00f60554116004103c802e600c41001301070281800e252400d40301140a4941c04c042586003031140c5c1060741021342d00c0261562487c100103600c60003561120107500c0068080001050150303c80f590201c481c0d140106068035681012840d600403484042c2503d450701c200 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 60248195 1250 60246945 60247009
    0x2090612040201110a1104050906010e0408090109030209040303020315030f0a290103050f0f03090f010e190b0403050f060601020d140d0c0302030a0f060b0301060509150d05010509090706140702 85
    0x41b0303e11800102c805100e02d0b900e0542d030a464000038440c40011552440100b0005600b010140102c01411303d4541e003402c0d565000159468419102a808254000180281e42103080c061240311603060b40242101c80021002550310410a040500403d1038616038030540414a40c113803040e03001c0a244050b8950f1a410f106880341002001c280c0d071441207003040c1070003a0010060380c5103408014004880820810015545a0210140d4541c0000e18201b603070100150046040042c1c030118a01c1e5450703608509e07086141805500c031918003a0311070020810b46a0f400114110314060300d14000d840501c100100d40160f00900303261440c620b0800103030406440d4980e000d90700c5815026000e21030103204200e481c0817200c20380a0751240a00c10801480450b010344010000c0300b001414075884400c4800b14400310750040c0c0105800c850302d0310010031540c030341180768941210034a40a030041700d01e0000e000d04102103507440401c111801099400c2550b51b001e04441011108a107149079407040c5880c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 60249445 1250 60248195 60248213
    0x4061b12020313080a0c050405250e0f0402040b0712020a14060a18020108010311010e04150510110a0b0a1103090c1f020705090405011b0206060108060402090612040201110a 76
    0x3d01c1044241d055000141d03a02e8002a040c04054106000041e80c504020901c00a0403000b08a000c6000b500d030044a1084801c8249000320142a03880300d202480000c200702201021406082c4514014001881000003800c00c9070050356014180400ca41140407099080c06103200010700311130340c0c986000a800c100400d000b40b2070000500e0030008000c1801c0303244c9503000843c0b8007900103030242c001800041d0a41a451800c0181410320303803510000c1074002010381c3c101200c01255142c8030300d020080d6007040c4d801c0b20055402400c2c420384400014040985c0c4415821000d8400501d180200d02204100d501541d880c141080c200783e56450f0036103030684d551024091080c007031111201d20280714007070603110151916155000d81000c0345010100a0281c1008d00b050700d07507550b00c2e40c4110700940500c540d11035924040d00680360616000001500d1a180141042e0090f401044070b14040c2d0303075032011544011400002d086a82d112400102c0304002156900400c501c03488800e0024440c03408 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 60250695 1250 60249445 60249457
    0x3040902030f010b040303052a1f05060108130f02010c02060c031306020d0f111219090902120402010f0306050a0b180a0305120a1202030f090c04060b04061b120203 72
    0xc0d00400c8690740d8010214880c40b176032002134009031041c0a01041c17461f084086c0881d80b40e06400d0350000c602e0306000f2609202c11681a403225881448600e00303107032024020180d002100342420115481c04005a1a103030000c2107000381400c0c5104030782011a03018480f040700680d005002c2c0e40d12016003004e160750303a40c890b442800c480342208800050340c520010321040c20056980c0ca140c480c40c003001c0156681c240c0f28680344401c1c0500e501310000b0004130030140102a010150b02a40e8400c40e41c40988a1000c1d5040842d621340100042d8010907007400c01d05811550a00e05000023459180084000340300340e400c0306074400e042180004ea0810760001500c5103628001100a1725106c4004021002d20980f0000301a0303081140e100054050002c05011b94a504d0300304070003070498003c40e0408070303030044405400100c560000d001d00640704004d1841e4100c0d0039107013080028181980d10030140140c0c4550b0381003200603800c03085140a0044182d09841d4000d44032420341c1c0ca4580d02035102c0d0445 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 60251801 1106 60250695 60250711
    0x180b030712030201020306240403120516050d021002091005031e0103060501060f02030a120b13050903071428020406031e0501110a0914120304090203 66
    0xe070004621a200c0d500050b92490300000300101038206070740c80d0300c23005034000010b20200c100e14100c030b00f6281c10130004c0c0002511803404451a00c81e40740c0302201c00d40da2020620420500040c5040e181e0310030340a4482400d680c0d070001080380180042c4a62006004a902e00c0301c501540046800c0b95641e4091484d0b0540391040007041c04003a4012160303160b0750001005626441101d21a07c148948061840c3c1180380100418050084104118a5030390310720052040da42d10b00014084110b90718140300740d1400501c60b41d03c940000c0f0050360b41d903140c60309040d0144004a8640c1a00c1c0026402030350702107010240c41900400481d0482c2c1261341e48001002080840b5801c3c040c0340d0300d807022010318460501d003503402d40303002640c119000d601c140f10111185400101d090141c4a00c4c01542254034400e00001d00149001e002261603400f00083c00300301007826070000d40c810564 = true := by decide +kernel

theorem cover : BRFrame.Cov 60071945 60251801 := by
  have h0 := BRFrame.cov_init 60071945
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60071945 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 60071945 ≤ n) (h2 : n < 60251801) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
