-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3733
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:31:27.548013+00:00
-- url     : https://prove2.me/submissions/f5b70015-031e-455c-8013-628173e7f0a4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 671223021 ≤ n < 671402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 671224271 1250 671223021 671223041
    0x30927011e09090804030f020a1a0c0601080a02010c1e050604080304021f02120f0705070e04151e05190e0607180503061b0d0f140903030708060f030a060e01 69
    0x186072010000c0c101d40c9034410140300e164003a16591800e4915100d1841c0d5801a01041e684031284060002e080c1310300060020741a0702810f421134844400d0341201e824094144d0080d603445d00020440310050380e010480444a980c0034541d0a501c00c4100c5882070b0312030704200024014400d020034407060245a4000c0c43c4103c0c42180d8a6024258818001e0307940d850b40049000580c0c04808185901d210010240185000b520005800d000880d1600e52810006a110180c41e004070f0082c04180842069072000140300b078081486400241d01496606c004c1300c80d103441030b40d551480480d488001441c0f501d01580380f202c6043c40440c11045e1451b071909810764101c400f140d03d4141e0000c242d541880140c0803200e0003005410160f42d141010005012803e070344001015040240111100c0d0341d00c5800340c240800800007900b03004125125030603a20140040350740313900038420071a141e680860456440300b4103a80084108041c40c000c24a4070040c620004e1001d41402110b2200b000154001c80c414 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 671225521 1250 671224271 671224319
    0x825050319180603050603010b0405101d010f0513021b07060806040e1018050f070812160f0203010f0c0507110402040303080a020c1207141b010203092701 68
    0x103640000c400b59a04074a840d6481c14040c0700b42820442d140c0a40d016039405030300900045011010346001408440d0704860b4440c1c4251441d40038000c5007000344c3c42d902c032603502d00c41c0e00e051541045000b900420051142511030040d00d65103944118264042d01d0403011030a60954500145c0440c05489103a2400342d00c2c0050052400100b00b80303800c0c0100380281500001509030b564107284c0c0c036409040b04101c0803c40904503140b120004404000d5100000020005024075078101440c0b241415481602030003420010b01c01041202e000a240303115181d803044030714030200c90520100c0c0c05412a988a6120b0514280072803074019045801070a2a621403101855400300c3d180400c41280118007010b0b000a0074100040d2280001d42e00902c000c850100807244607241d0341084541315403101108841002006e07800c110315060400002c0c4100d1111210750382c0182c040c2d0300003590380c0102480d01c0e202c1d03c420501d483c810080c0e0381c0e014075a492000c101007410b6840d440c00b444250711180c0101c1203 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 671226771 1250 671225521 671225557
    0x2607081b0102040f060309060b0603011d0f04020906010f020106032111121e0f070602190201110d0f02090604080c030d020105040c15110a211b08250503 67
    0x8090010b1007242d0507128141d414003802400c0c40c1e02140100700d40c0b030003100e4956986508414070b940d40c0c00030318000c0500e455080380c00140030b00c1c1012008409094000440720b620103200050365080003c0e81d00c070b1001e1824111164005004070f025085030b50000d0901c8800c40d81d81d00c50220000c0c01810f08880e107032121028490340740b0049950b04403244001940c2d240a0051403c45050341e00f0749000130040b1055542040b0022440c00c0d01c640c03001108441c04d0342d0004082000e001c030302c4103012038010b050000b08001085000110314900c1079000c1030741442d6480e545481d00106542c19950b00b0080682003e441e0b135210070149075140201c0102c10310030310070081e007a83d0301e038030500416209651040c10b1340d01d8607150200740c940402c2c040d0103401c140300c0c4a50341c40c12070990801040240601504884034058011a001d5030107000c08103c2c0420001c00c020108043c3c2119825902180d50040c4065603074412246405103041d05c003010804100c0702080784805200000003d498001c48005141d58 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 671228021 1250 671226771 671226817
    0xd0f0c0e0a1d160c060e010207021e0306060910031415090d0c0813230f0f06070807020f1309060c0503010815191503121704260708 58
    0x12840000b222854140046000040d65600c12000d05064030102c90426401ca0780c04c07030780d9038000c5e0b800e00c440d04003480e035001c5000d000394039003041a001040c80200584c0d410703141c9a07001c00c0e25540000c040724040c6c10001c0100301c114101603482c20041d60014000240b0722902d00c8000c3e1540116095a408c100e03003800410258480403a889060900c02c2c1ca4618211900da070718441243c00111505815140703c400c0002d103400000001c9080ca21110042d100c07001e20702c000c00032541c00e00c1c0300e980e015031211100e0605030385508003240e20780d0b1380100d0030948981403403000445900022403040c0e000003140000d1981c0303010540065a80314070030b143c00d0200c0c00e000c0d281100c22f40002d203d8040035900091015001a81c0c40c02d1454101d030070f402140175150049075800064070f80402c9078114015400c00c0810a025070360001100301215407500302112100d0720300e081c608001c007070805094007450030701a16161854070380c0f000785e59041d8800304c1d46a04041c2810042c81e0800c1c0101c40c1b94000c000c581503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 671229271 1250 671228021 671228039
    0xc050105060423040c1a070309060203090a03080304080c0f060a0609090b070309030e150c0106050a03030507080c0309040513051905100f1d060403320d0f0c0e0a 71
    0xb0108440322494241003032075007008240780c2e034000b0b0000d803172501d00c0c4900032402400d801c089030308216514a4a5550b90b425180043c200700d07450344a0030854105011882c07540c1d64405165040783c0d009580140c4a442e54102401d0302d01c02d12070382038060300c00d100419550110128510f44521031203041003183c2e1b0f43c1e461601c000d44551060041a8081c1c1e1000240e03000e001e58011030145029143c8444110707507075008541403840c141913601004001050318010030100f40100c001404040e03c100031002e1442d9800b4000307000b140030003400341801040c54540c030682081981c99503000140248040e0800d101c0714008000801420b94150240401c800403100344041c6404040d0341c00340041140c01e0034611854001c08004990754051500c0300764440642d84607030900710f10019108050440d1742001c0c0350140c004007112544480c518085840450004400100c00c0b0f500f4803410300a0741e40b200c84d551804001c01e21400319500540c81d0005084403150320505054034440182c80241059460719049 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 671230521 1250 671229271 671229281
    0xc0602123402060703090614270f0d0c15060b0409050702010504050c10021221070c050304060c0c03060f091202030c0303010909020d020907081005011106270a030c0501050604 77
    0x40581d10078004168020305ca9403028803101d0244500140029000700c803004541c0c070507210102d00c04e80110550b28421403129140350a020345400074101480d50341991307a110541400401c0c28001c0c1142078105014484195040b051010030f41040450b0f103822009001c0e810a01801c40c1141c41d000029400134014459a805550010001c0168013140c0f4100801c42d4080d40750a03045000d050b4420181002c20700142c08528864007000a40540d00c030402000d082c8000c0c008020060742110f80e0700401c6002c03007150191403c510300004c1c491450b0912880b102c8803503100911051811114600d5610107901c46610103202c1d0601c00c10346482000100d980c3c2c0078008590b086500704100410010720298800c07032000b4809405010442110340018910070400c490400224542030f00b041a9064880006005407009081400b00810809005681c5480080c05032a40710341c40030504545030116030003071902951860407250524100e203002002411180740c222281d6003050041034051811340aa = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 671231771 1250 671230521 671230621
    0x10c09080606042c1c170103030305070302040e091605040b1810050d0507060305101203080a0e0106060e09150303070209040f0816021002010501150c060212 69
    0x14070890312114200801040d1803100614501080702100125202044041c0f61107044034026100740a03400c2c182c4201e80c281d410740c610810103130032410200010350b41c84060540b900b40c0350004440e0340d04042a002486176402c2008078903030280800400b1000003c0640c05015031031084110f89988800b80310a0310304064084d58080899041c480040c10341c0b1804e1a8480003085140350416562004680c4455688009481640002405100054050040a8010452000d94080d440c50100d56125000d01c825006040100401c04100003458a810a03142003030800020400d02d59a8480980503661498003607004a5031140041d14a0340390036049005001c02402940c0b401d40070307038200080c00100078001c4440060300154000461181c6000e84034000644846100c0d0402900400500d2a00c0102c0c0c07508680c100001803003c0e04440665018400046c20035030f81c0c11210b03181c00c501030300580104440c400c611400b005521400003110030100d100380d4031060344114004000400d0041a404 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 671233021 1250 671231771 671231773
    0xf0c03030f02060702120a18290a0212070302011b121409211209030307110105060109230301020f0a08060312040605090d02130c0815010905060c120f0309010c0908 72
    0x4e000e50210300c0c60040101101740e2418621a00190101c40d103a45010342003026910a0801d00245503120052440304d0302080fa000e6602b4140d41d294029500c00805007074610b114404201c810806000b5041713000720303c00c640f910707200390401040020300c00090f03078106800303190402c844601419810310919011750340e00001342c41d542d60a00031406409524035501c20006204104047c0b14602c641d995601401086020710b0345c034104031000400d80c46210f000c0c61800d92401381840144c0c1e8102e980142240d00212090740607602d000da9020500d9405d0303040c16015400003c400c074504114000801d00041c641d140c20505450b46001d01d9030700c44c1644089248000c08102c240815405140504582c1078001c0c402c48550403d13034045101108107940404000d501c906090040c00d402c405507950160040c200d41e0f4142202c0800200722142d01c0c81a240220f0300003a02c40c080317000c184203944074001100200355a401d50400c800107294000c03112109076510381010028561b114482c1c600485060030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 671234271 1250 671233021 671233033
    0xc0a0f0602030306091e07090302040c03110702100201020f130e16020d0e040b04060b07030306211103010e0109030c0317010f14180705040f0905010b03040807030203070f0c03030f02060702 83
    0x9400d01c085c41401910082d01841c181e02807100c02d140d0022860302c520386960b034500c9998a9071040c4420365005030035000506040ca241c3c1100041600196880c4a4040b1400c003061004c07544280d00920400303850100f1082d000420400d4104a4540304040704c0388004510b0701640d60030040c010085041c2245401608411003d240b0544203c440c81000d0b903000340300062140c078850000d4201d40160380202c1c415080413a00c0828107406100c0c0e24020075820000f0654000310720003e0114042c06c0340000c05865040d4036411503920300f54071000c19039039107500801810045060260801841c0301d4100d0018101c0128080c0020700c80c0c1820741290120510340990f107051a02410900d40b9030308110750803c07103070402c0c400c0365010417141350300500941c0ca03032580e21820040e0308108029203820126100b8100b00040050410031800c03250301c1500000616202c01d200d1a049003140701d100340141101040e50703000d5041c00404591141103c1c441c1d110000c42c1603c503001640c643c10304803010303070158002c6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 671235521 1250 671234271 671234281
    0x51c090b090103023f0a020415050c15071d10050f0c0a060908040e0108010b0604050405060111010908221503050403050f1827061c0602030916291e0c0c0a0f06020303 73
    0x2900241111212803015640001021201c8030803330301003200d183c400110701c030454030342d108601b1045491003401541c3c11400301c5205e8002815074418062802500c40001941c89418201803020303020703050b40319005025030390aa040500c40c071707041401140358400008000045601052241d05118640a0b050500317040c51b0904000c0117140041129052181d01800024166401e01c10110003a111703c4000e52a1006280100c1c0240414000e001d600d074001c07101449201e01c6100350f956a4252440c0128942d03079246000c03261030181362540e2501031b501040c034041c50401041003007030320981950040510100302550310414407010a0a078002000030004c80d0f031a06042045510081d005100f50343c18803241e56a00d02242e20468070700e0308a410503c00c08030f91041030b8581c00007c01c00e0340402c207081ca0745d2010382c0400030792902d13140c1010700f40001d14045214007850484001040c0b80420741d00d895017003c140d62100f141c100c16610410448001142c040c2400c01705005031003c5600460075a611 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 671236771 1250 671235521 671235527
    0x9010e010f1d01090b03130605070e03150601410403020d020f19030c210b160309020a0b21160c0c05030a051c090b090103023f0a020415 60
    0x11002900c3d040103504031021511000200007507000b40d0200002c24140043c84c01c100e8122500500140100444240010015980011901d03490700801c140104d0985449005850010700f2440c11105c20030300719200b8901000d0009200b0a40c1242c038004041c074403000701641c503e40700d18040250b02604c51b0440c0c0300581082610080c005078058210203d1101c900d19410741e4004581c01120720320581340040c0046141c03004001c22140b950313840d0a0050001e0340d5a1021841d004082c09110344416184148603813198200703001d65038001c3d107042841c0b40c644811846a51203107035401c0c42c2402c000c0d50085418254002d26125241083c0c0401d1551021401160800c110fa1019545c0005000001c183c9039018441170310310038415401000480407291580c0a5528000c0203542408021501003241481036811500a0202481c0c0140e84004e45c004040118804642d2090f4800380d04071541505442001c0200040c0004017034a40c50340c5d60745000d039044c0e1085024000200ca011103900010f540 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 671238021 1250 671236771 671236817
    0xf0a0b0a03060509130203010f020309060708040507090c0801090b0111031c0603060f06150e01020c01260a050114040203010b0a0305040f0803090a0b15031507200309010e010f 77
    0x228514021402d20f40e18800207042c0e142c00d4550761210711090000b40e0451400b48651440343ca80200c096040d85464860030f0f8845000410310303814000500001400c215041c0012000b6100c06c2c1000c000c82018264000c00190003405207100c0e89181600e481005c0d8000da019407140c0b0f041d4402180340c114841480c2c8460861046200c0355551246e00200000305030b804ac00c0342000840c000040c05525103c01c854030402c00041400038814160400b02c01664040381c464041a402c1c04c1841000801e0100384000d40c031048581c03001104204280942d48140d41c10150488910987c0b070f60b1201469000c00003240f00038030407201016810444034100d2806500429070043c002ca03244801c01065444200c0340b81d2003183c255039690002113440301000220604c16170000c0070031444241c40600c1002081d81c030348070821000c181501030400a8511840341e840c00c01d0603a6038401201c04421521009079403908610300c0a8040791041117800712551041c0310b139403d0b800c0543d036050640c0400d103141c40c00e003070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 671239271 1250 671238021 671238037
    0xc0a08090307034106010302041a06030f0403231c020708040b030105181306110c0f07030c06030e100e1203010303120e0d2c0a030f0606050f0a0b 64
    0x40900d00d0b00101181c612034018113104c0d0640d041d1045107010586200c1c3c0719040d054207030300d10500703081c0b43c100484e00010411305681c0d0545000480f004030741901707106080760040b1940c1c0071000104000d100c90319002040e0066100b6144c283e03482c00d01c4101e240d80c43c004180c2011162600b400500b000d0301828001d42201c030210440140b4211b00380c1c80703800841d40941c12461343c5c144000010400ea05007000000d04d10b003520300c8078500c94240160503407482c01010030702603e810b80f1001da048102c0030610858000f610b180e4201d40000c0e1340034141a85035440b520081d80d842507403150000d0628040d019030355007024000302070050b09003100c02e000b00820321240c1070981880750000b614896110800294080d40c02910303a500032802d880c0741d440a4460036a058540c903000041c00070545500808048030006d42c2212940400288648041505442d003094a034040041c280c00002c0c0041301d03612070100c0f4010320040c84a03603190007d102239803013403620780794203c071a0040800ca400d4062018240305 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 671240521 1250 671239271 671239273
    0x3060606161e0302070f080d0522050909010b04050c1303080706020403081602210304180b041109030607090f050d080d0501170c0306040b04080903100c08040201080c0c0a080903 78
    0x5040d125420300389400010b034080340945e0005209100b075070748030242c02009100010060112980c020720090040c06048440071140380b284070511450202d0b1580719000c1c010152048103946040307045580603112030040300c0d014074905004030300509000003c440c074021b072404c08a0f01d014a180d071261000e62284905840c030a50a00c40880007803a440001c1c0b80406e02d01060603100100d40c010805003403c4000ca0f89029421002a0180c904000c41950202d480b4482c00794008029400c8410242c51562040c95101b0b1502c420810301c824444081e100307001060301119400e5440e0b00c0d0a0350702842501503a02132172a4240f081002d0300d01b5200c001d0307405204112032401e000d101e5140c2c0b000d40f423085c1c120f0405498103000a00310388c141004021804e1070120010070b90b41c102502c034070703640520107071010306a504006101d01d8152000c1001002c001c103429420000030700307030400082440300c06980880c000344400c0c02007410169440d0503100d803810010f0182c04009100d41d100c00095000c01100b07505 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 671241771 1250 671240521 671240543
    0x21e010b190b12091c031401060f08010e180105010308040306060524030a06090c0807080a02041a070314070b010e0c2b1b11121c0c02010b04050a020d0b0306060616 72
    0x71880f17245044401c00d00e41500c2c00708452040824520b400c1c04141c0080d030403c003001d40c411244a41c048003c504488400703000384182e8652a5013005210303940f0051199039030a29000200f000243d40040088900404041100c980c0360003c11262004060b5801c9140034861a5850780700311101c01140c10050f0488001103581d90f4800c180305443e004a4441c0c0461412020042510b40240c0c0c41c83c0d218400d12404c51505d414440c05141910f62110603100c101004144502014028904001c0710f01d46031101c551541c059141c25140e501090180c0e00c2140365910106401e400c01c5019540c0305541031003410ac50b40e0f03d042009401154030560300c0c09050300c03a241304066000c4440704005842c03060340c514200c040f00c1c042d46481c080380718480d4040d00c5c4040000c1a42101d6800e40c0000703648a0200c003143d0014092803c07405000000c4045500516000c14000e001c0344641c010a0950702800083c0040c0210b40c0030103846490071115190014003c2003141c1c0c00000010791b0780162449210a030103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 671243021 1250 671241771 671241793
    0x30c050f150a27090222260312010b0d0c0c0b3403090201032901081b1603180b180d0803090106031e0203100b01021e010b190b1209 58
    0x90f0088668820090564000f560081a1048009400010461001c103400305454018107100c4045044181515400b014600308020601807007280ca003213500b60848016561140785c1510190300010540c0042071402a10f409010f014900320340c04a500301c0c040700c005640704a401c41e41d27640c0e004e040b111074007c02d000040240000281000c0c8030301da642c1d80000c0000c582e10024080380c42030405400342040c01c4413002205007a0a0300707902000c0782840e00381800e442d43d20b05440700742c03074403051041c07840302c00700f20510307501a0808210321480c042c2d030390100b0100d4040540c201200d014000c50100c000200111182c25403101400490143d000c2d00c0000098825260300d070700303038100342d90740d4507540d4460b0344c10800d000c1700990603010318402d40c40c41e40303100781d9a5001940d03408860500946081e100d01d40507806030300174810500340100003000b0300106140d280c8214002c1c034814482700e1051a80444034100800800c4a6506035200402d00618241c3c1ca0301d004101003c00a04c501d07854440d07050160 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 671244271 1250 671243021 671243087
    0x60a1401091416050d0e1e030304050606010e19030809090708133e2d04051018050f13030e060306061c0506030c0612040b09030d0204030c050f150a 65
    0x31111801d110003a00341c0ca06072060f114003000b040119888123901c20310a00011810104080303802c12002d08061a04c03100c8880800d003c0e1194109102442104020000920024400900058004540c071100f1990307200010f640b03422082d6800340200040f907480c4000507482c041441011040c0c10607182403d04035210ae03099038481320039416115480460074144d00d0410756a4441002070b109000c501840451040007088500019264405d035291808560102210103240c0060052004001d814011410080025100586502e42d10780d40d4039001420401f00c5041f50008603903d541c4003901c11104004100664002130700b05540701904201407000007403207070100341c2a0700e100300003c903251600408050401414aa90f02c0c0264010000700e142055503554140d40564842c850802c191102c0340410b25600480b03a0b806039091000902006011305411149d08851003107501c10790710700841041c8001c10300405c40700c0d91561401e204050003540241a00c00314810313946c030841031200c8946125 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 671245521 1250 671244271 671244281
    0x4030e01050c0d0923010215040606030f0503031023090a1b09031a01030809040203090f12091c03140a02011811040506040b030d0507020d05060a1401091416050d 71
    0xf9101080300310340c00304001e013001c40d00e403c1409100d20113803104a800c0380010752100c1e0309101829240d283c0c0000034040120741c0d403200c0042c1d50841506c0366918800d02d88641d8a03401070b900c0042c01c846a0304001a9281548e00c030034596099402407000316503a1000b44494070402408106040d03880340300521440c0d03420002c40300580310a66072500e1003850340c20400700e081e00d06040c1046606046005001003140b007011511030703603c01c0e20016a21755511150b20b04200f84c06c007603007402e4010b1408100c40900d2020183c000d800044500c100c0080301801c0007900c54804500003404118050b82e00300a041482018200048241c0000b00d090144224070402080705658101c40300e103698000200c003070070644145680303c40159400c1002c6100400000d0ba112825030046041050004640086445080c500c00529034003000b12001c03401d040d10b020016110140203840c014600000018a0400780d00961745000c0c4041c01c004850b031207014580181c5150303161000284001000b002503503a2041c441c1c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 671246771 1250 671245521 671245543
    0x5060c190503031f1203200718061217070c030b010603090314183a140307120807051b012403050c0f011b0605270604030e01050c 57
    0x2c0c556030320b0010000488502071154114032603e58a405005210305030907680324081d0503081001c0340200c5030a220300d018110b60800c220034001d0140c0003a20103582c02651240c5001d64109002c4282c60f440e00e03172a0703034150300c1c8050200ca90402d004102081e101d002003c0281c021070384d00f02600d40702e03116181001e4080c0e01c1400001e036102c01c000b044c140e10544004000340d4100e0482e02d091822a5164100502d8407090b61054603241001d0105140000021140c0e42c2000c040d040300300070440c001414551682006c1d14a000503003040000448044110380400e584024030300e50255840c4000c40740c40c94000d000c0c4051100422912140786844020341e01c0e0102540c0020801503003003c41140c08a180c001070b007280a06485c010700000d038001c00c14900107501502c60000c1803c012004880c9014003401d04070690700d02130b11407820b1015a804c06803084c2c0b010403a0402c1040070f00c500e1191210001102040d640144000c40e0000384076212000c840d01d0705141c079031304000e500313a1900e081694180c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 671248021 1250 671246771 671246773
    0x80a02222c070603050403020a12030f29010311040b090409060f0f0b0312040e0924010e060108040b06010305060429030705100f0c15050f010e090607020705060c1905 73
    0xd000c4101c1c1d44100009005402c0c5440c007071103c3e0400b942c000e0354400c426107004100c50b51940c401c481e580c0c03096002e0f00c682192418140480f48104148010040084c0c05501c0e440703031070025081e000d5009009050b903461a8011081c07a003403402d1605050ba0703b05103c2c0c642d01a44500184000c554140a50554004000e2001411000041c00401180d025a220034003035003001c035250294410020603a070482d140c1190100d40c40d540c034200d131424205c50190303803889003030180342c0c01d203081c110f04001c00d042e100d4044225186890700c10041d900218121001400035034000c2c0054515440b90b00007a0f00400050404a250f04041401600c09140d06252a1092003c803044859520781000790100a10094178906031400f0580401451440038031010701c11701806000380410401ca1a56002c658041c0303010802c56806e00c042d07681115442841940c01c4004a10f012806000c8080f81543c020700c0190002c4c44107614000c140171a40d040501c10141502a10b00d1528507641600301d501c40c560f102750 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 671249271 1250 671248021 671248091
    0xd05240105091303020303151c0506100e04080405060a021608031c091a06060f0a030606120b011e0903050a0b091504200a08030c010603030306080a0222 67
    0x502482900c0c00020301d4050b8480980c3d480e00003080d004030840307821108200110400c4003950b80403544008404000c44000c86103040c80c0d000340640460024000c401c44001108850755580123010080d0b001d0743c0241460008120030800b0707240400c000c0c03810081c84d0050f61208104000400d1038181c43d0752148840e80c100040c215901c0700f01040441ca09118100c3c1003000c2c0c3c0b01034552048502498240a044140f0000401d4241c0e45400990b4020f4242c0400180c2d12101e03008001d0140005210b8280440c0191a01c0c480412450055522001040c0d444a02c1240d0b09506500a40080403c81060261b01c04000c400f240c400d20040d44054000da12444550a01c04041c43ca0021941151815840ca400c1404001001c907a040e00c80641c425501c068400c544c0c0b80004e0880c0707255800302c5083d100c00960999490f8064000b58102c90094500b0000c2d642c1c0d400c2e04a03100c42c07c81d0300086d44a40c00c1400d00c0300b41c5911040b24040c1c2a85d90740c1c0090f00041a41a81c25000000011022410001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 671250521 1250 671249271 671249279
    0xb1b0d030e16031509030c1b0608250e060c070306090b0a1506030203060303090405090d181409090102070b01080a171804020a020a0506010b04060207230d052401 71
    0x41082c0620b0240441148035403501d0f513203500801ca0603003810040202d4036100075806143c81904108038058000f00ca41c0014151681000c0d14070400d4030a50022440400000d00104410b40f101c00c3c401c03c24140c2e50302100000107086481c1c00800c40003642c040b00a100da005040c07070411040001e544101e0001811344100e003880030780010000c0c10100c10f0b6040c0305500050b19100c0c040001141e41303d040140c1c0300e80301c84002034154060aa4003d0b00180360104228604000191001d60040f15486401c001d22844d42c2043d0409400d000f5200200440744e5100e6103418107800c2261300c819154001820140e6070754401480a2080e44180c1c4594400c0e5846010b0003000c01c403d01360f20b4007184800c1e1030604d0012507140c0900803042c12a01c12035020800212450090114290704c3e40c3c403200341c841030b40e19070414440c5a000760003010010b2040d4040410803d40d4030010804800071010141800d980f0041048000100b0010860b800c0c0100708107c1003020b40c131800c01c1e0750420400e014004940c10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 671251771 1250 671250521 671250523
    0x30c0801062409150c15230c2a01020703020d020f03120a180f06020417030918041703070c1101081006120908120a0506030f070b1b0d030e 61
    0x4403010390400a2044208441860700b00f21168101d81a280002c0340c07a114500c0b0590f44440316000103805e14840c2d10f00211540b10f00e034031601c0c00602c00314510340200260101d81400e290100c6903540040030402070341030042140392070b002c004050126110700003804405243c0c26030b00f002c5800c4000d680510034150440b40c05014450715180c0305401541031107680c428100715500060a010900daa4606000750407c96039915420101d4101403d600c950529142400c02523019101d2109660b01503000c1c807407818404021610302c0c001c028130040c03011507510552140303060080c20840303035a2420140341c900807003c1c101840c410130154460104001050510084020400c4001810810f041e01001070360540d284c0c40348140e038054a085501006035024110040050b100098001c5401103040d2039440010390400e4414800c5035418081c5440b100181951030306070051003091a00246018001e0792800406400030301e82c080204e000c00218114000d0408501c543e2040020f5102c2e8040b11076140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 671253021 1250 671251771 671251799
    0xa140c010608150621150a020903030a0801090606030218040b0118030c1802070308070e13020706150e09030d151203020307020307080d0906180801021209160e070c050106030c080106 80
    0x1a526011817410340c00c0b50005902c44c0108015500907840080c089408000c856055544600010341100d50310319040c403000e00000c00910074110030904103070000c41c81520034001d441c0c031080d000b110390007051409000c010140c00120b611604202888605145044185100000a60142d00c001d4031031428910110b0300221803001444402340100000c40000c2c4c0e001003195400303046842e00b202a100900d00107a07c03011381507003040d60107001045103402d00c0502d40c4001d02c1c80740300c1402031048941d030b8151f01e49009005c03a506516600b09210401d0341d1355a80e0800c1e5240080b0703800a10351a40c441c1d00541054603030000540043e4808a03544046060401c45103000c1c1c800c81e4000c1489280008000700441c4240c05007004100306001c8142c024100303442c1c0e0030060310311f6400035515070700301c1c402080b8100303012900e40c4601d10808504042250040c4240c1c41642c0c10f014400141d9038070707148160740d0000c4c0301804554a660754140040410041e0900704c028100d00390000c5180703458007038031102401e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 671254271 1250 671253021 671253049
    0xb010602120a11121809132112060f061701030209340203070c0e07020c040b031f05090c030c1008190f0b01090b0a140c0106081506 58
    0x54000c1180d90381107418601030310a50400c91a14048450351000e080741040d041295140f241c03100880c00410b580300c0130f000c02820382c0c0c06403080e07032499440740b100703000c29900850003a00e048922103002c49400204080c02030300a805041034441348079203103a00400c0303c026501c03100e80a01590030502c141c075440881d244220001c3c00c06101c42c1c0d41190002125502c010700740494441d5020a0a00d1241e40c444103102503d94200441c0b6000064000194982e0f00c0042c0c00c84440440344000b00c0c240d800502c072540a82034690060091003405407d1000500c0a5000c4c00d0f03047c03081941e00800079940d010260800320480c6808225802c04080d09803034030380c1c1008a64402c1c0c102c98210380e055190358460100698031031400700c0381a1201c5201c6403a400110301400e04007424003005101c074204542105419a07000e03030304c80c00690390343c1400c10b0480c003030406000002848000310401c1109007401524000c80103000010f1010ba540c403559161000704108c01c00c0b80d010120070803d1138503107020250340132 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 671255521 1250 671254271 671254273
    0x30d0b0402030f060105031e1501090e04030f121d160b04030f0f0f1703010501080708010e06121c0c020306070905090f0405070b0c010510051c03050c010b04021201030b010602 77
    0x2508003c1001620381d800209a0780c1000301c003200050042c5c291b00182101d84294401e4030a440c2855115040200d0080070102e0102d000c242c800a4010400460148102d426544d070840203041d00c0400c461a09001c050312801c00c1e1a078003902c0e19121104200c0f03900001d45002071110042e28501c003a00c401e43d07070744110074100d410712040001c205d9024241c52240e5004180711030000b079500d401aa03910504c1030241001401c101a44240400340d0f00640c10f0b948240ca41c0748a9582d10355048a030743d042409200c0070394400c000440c00c40e08022180d520380c0a500c40035140c2c0407644001510050006000e5070002404c02e448140070b41c2400e101a0fa0080e0703180c82d2a84010742801c01142c080000901072100f0140755a0024041c03020900c030b807101428104548030f03594081402c0c02e502a2005580c001030046112070001120326120901a00500403025007166480b4103403801d441c903070020700a86559540b120a0142290344c3d9100500c0c000007940d045550b0b0f0b5055082620b422007050b0441419 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 671256771 1250 671255521 671255527
    0x38130509240a110a020a02091305060103080318010603020a060f111209130207020303040302060c0304050907031b0201090c260f030c0d05070803010312030222150c020901260d02030d0b0402 83
    0x11581c007181201b092501030b20305074059105e83c80c0f07484108440b10009002c6015039400030042141c0b8400560252002403100d00c112600c5140080c00ca0307101e848000e504c003c0748001000003034014280303140048002e0520380621440f110f112070030000c1820001d8802980010040010319000b0b00c804102e02a4510031400d160065010075030307900c654000684690008540746041000c100304650191101130424103042c10040f07005000f601000b2034402040911a58449000788144a2065041c1d0003083c2160072901d885e401c20800503510703500d22251685000400c81e60030003004142030100c0a04001c581c0c51002d1a001d9080200c0451624100401004020045080700d82940d040d241c00c059603600c1d050803081e040e4000d100b141c00d2082c0c0280310040c0f01c0010f82000203440b08407048000c00d440100d9000c9030488220444503402507000c0c54a80040c00080c46040106d501141410b0001ca001c0c82d00005103803812500c0711540c0d0040e4030020f01500745450602490604030b50585040d41 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 671258021 1250 671256771 671256787
    0x3020f10150504110403060615200c0603070512010f090c080712020a050d0c0905040e07060c0b04050708161d0106020a02190938130509240a11 63
    0x40c0c0e01e081031003524450f607220103403125044e4400381140c004690144040014550b94001d10000041341454040828828a82c0100c141c0a001c5044041c00e10301c0013038042c0a4600d0100f0140c1c3d0005003850b0308200c03090191403a501040c46085010382500081c00f4840385c41d1640000a44040d01c1c0f1480030004540107001c001d90300445d00c00d4003c0281900035865079401c2408035941e0107807000b500f11040c20090388082643d0030007007a40555400740d034127010b880314001c50f0750381d551301501c6aa03000070b50700d000d0180811030805909802a00c110281c1c0c98466580a80c0e51400001c11250791280100c0e650402c0103601c008003035000c0c501008620915503160460103034403820600c902901070f40c00518414294451034030208040d115404041010b003800c841e0461103003007003144e2a00c030346162101c2021860f0170508040c5840e0001440084505040c40d0040f0142034058603010403446821625090700300502c860000d012807001c1004042c1c900440c42106596100e2590508003008021541d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 671259271 1250 671258021 671258051
    0x1031106130b0309150c0913050601020a03080603030d02070b070e010e010c0201121d010905010b0f0604050d11043602030d03110405330f0a0f0c0b010303020f10 71
    0x401240c01c00000b80e516965802002d500781100d4003403034808a043d00b410400b18606160241c0302c05c15054610343c1c03002e4003a40403501101c406592090243e40410301c103900091040f001c069001354040d003a2403c00c0c1440d00c412050b0b80103494121500036046c410401c40740c0e80800e201856520910740f6504201090001804600004101a04000c5030984200c0c100c00e03550800500c58010741c019246504007403041d107008080c02d00080707589500700341c100c440b0780c9030032945c1e00c102180003000149000c0ca4102002110b1040c81000c60781c1581d01d0900c1038580c0d550380708401d9110040c80081001c500601106200c400d180c40d030903d402d00e0020390490160301c0c0000d2030074684c07000b41400540800c2c206040d00d0300d80240c2c0e001941c00b07000d014440300000480c207030014029002030b41d0810f119a812010b03026074010038076160062802071010040300f034440e00c1450b001002500302142d0b01c40301c83d1189078144c0000d8100b0740242c0d000209805511008018145000015a00030041c003c1400085 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 671260521 1250 671259271 671259307
    0x90a031113110f03060d0b0c030601091d061014030708270a03030f1d1c08011503020a0509060309011e0c020c0f0a0f090b010909061d0c0405030a080301031106 70
    0x101591003010000030034030b864221400c802c06422004138641f51030140c0c3d04046ea44e20413103902e8009039100b4400181141c9078100500800450900c015060340c510b03060001d9030a81d507102008114509403892a41c2445200a50140c1c40b40da45240340b5151440c410355483c01440441100000304181d200800038010802203200350f03041c900403d050071812002400b400300040b1410246075105500100d02000040703c8103242d00031000083c5942c0304000c191000c8600344502110001c90400702580d0703500c031f54010a012212800d00606204105001c1442c0c0c4e0801c84d10201169034034901c3d1040320b0b1700e41d607100b01e170346006820030b120b100c9840b03000a48807810890003900400074003107200003503520f0090410180012090715100140d41390489000f40000c0340100b808038035070dc03101062148450048000b9940e07851010702c0410101809072304041c900030683c094030001400041200ea0703045c00b880840e6170049902640369411810854804082040340c14801c55080104000ca81051146 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 671261771 1250 671260521 671260537
    0x11040b180303040b0406020609190b0a1e0614010908060106120b1225050f010903030e0411040b0705151b0a0216030c0602060a0e0c1203090a03111311 66
    0x303081160600d0808a80385000700d800c0540b10710404100490001d0740000e0316071281120301c1c2201c1e60003080e01000000f443c4c0100005c1c1200c05094000f80c0c0500782600500c94200d80f000000140049140d000d0303045803040c2c4c000708402e242c0a401801a0346e40018814013400b43d0340003806403540350000152050080003008407103e500c9002c031884a03074502c1000c41d014402401170b5918606d1a0031111608540e041c814100d1a882e44001300f285d051030b00381c0032a148c0040c0c407900e00207419070b01c09030354440140340c2131130340a521019200f13085111076020300014582c807640d594644689d854030314105070042c07060015890b594010003c1500e4842c00d8015104001d1400941e80d04003000c0172070400400c40c20f4a9101c10000d1400002c01408150785000c0300c060340d0940740c03d92030f08100e200550340b0007464041c981d80071092103242441c0116043c0310003001d0300100da151404800105d081c3c02c0c1180d000382c502e07800784543d004e050700b481c4501103a200948001001f2140f078103000e421280c080c080c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 671263021 1250 671261771 671261797
    0x30c11070911120a0603020a060c021302030405010912111e1b0d0b090304030606051806040c05040302040f02030702060705070f03080a0207240f0911060a0c080301061211040b 77
    0x7000d007542032020b4211032000c03d1094800d900c03842c0912040003e4501440100e020f66004500000c00620801c00e0ba940c5542c01048542d903841551b002c50040e400141c015103141d5aa180d000c400142d014202280500803a140c0100411000d003006007498000b01c0706401040701a1413000b520a00499848400d05031100681003c1c08698041841c0003110900104000305490500c000300070000060411607200306800e000b081e44400c240070f0007260034a0410500b03c2c0d085e001c19200d00c1c140d044222480703c03d1170040d003819506d40010b015101c020213002c0c90b003a4008280000580d061100c254404864180545840e4855907140d58441908801a0070407060401148109402d0b404840446400c80100d030a0b0180c0841c040a40301010890300c042c240c64088001d2000320603005401036590840980c203103500e00c080500825a1002e2010340030004048583c10000c2c08a02c00b640c0a428184c1e6000300c2d02960074014402c40d06003200098200e04140401c0191038403920803104458501c403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 671264271 1250 671263021 671263031
    0x2a0c0406081518031306030f11070812060f060a030608060106020c031203070513030803091b0a090b0303130608160801180c09050901080c21030909150a03030c0201030c110709 77
    0x1d00803900b03500a99141d62800d9074484400500183e05401c00800802810b48c10440032021284c0d02c2290312402c04020190141404100c0e80e9100f02010264810000b90601d01500801000a0b0480c4c0c82070300c0407008640e03101c10501880c40d0401096014101c2800100019803000c400207075110704035031002181d9800003001940d40b80c412400e0703580d04280100010301c083e0b1203140070080c40c1c104440303100c680c0c410029090341c4144203140030800c03c0d801900217000a802e05414001400c0001c404903010310040084200ca080c8030600c1074001d00250b40c40d40e040381030805000401070721403040002000300c4c45005101024046038445d031003192220300000c01d84071961080d120030360f50390f0002e58040c804400000c1c0d98280422250704110044803c0306506e0503403141003e03039601c1101410307410b40c070038043d14070141890100703250003078540340240104070341c50310005480b1405070f041100024000c00f103480071960135000300400d070f0485040c1880040c0c2c51200c055620402c500c100004c181d00c607 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 671265521 1250 671264271 671264311
    0x7051212030a06030206030a1a04050606181c060509070914220615050a0602070807031101090807090b1c020f060d02120a0605010e09010308030403052a0c04060815 72
    0x20f07510690003198007500c081d8407480d00c02c01c013100914064600c00d02c42d80000703807807011a03d0144203031441584014621404d15641420105100c86c0c80e4049913004501104200d81d00401c0c0030038560001d100d0031021420785032400e0b40604001903940310000107810215280d03041350380204150744c010320720391140307030381031000000f81d08429040000504000e141015039400c0000b02d0000000352a4291401440242e40718012039691803035100d010500e41100200b8070005800800081c20900145080002c490302c0b013540d507080000b04d41c4140100da0b40d4615000355410410211099003043ca01c82c5114484030b900400c000c940c82d00d10307182c0300750f50000c1c1042240072035505032104414070f10f18105642c54031610301d0004040c5030103a81d01249500ca114070481c90140300b103034180c0c3e83c445c7c02c240c250b4443c0d9809440c00d41210800d150107143c4008404641502c1901e00303a52a83d507040100a190382007428001200c4540d049040e69402c000280b81288081c41c8200d43c01c00c80c03119820201c540d01c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 671266771 1250 671265521 671265541
    0x821070903082b0504050d05120411011e0905030c0a03080306150d0e060603061b2502150d0b060f0403020111010e06090f0d020601050a0504090c091104080705121203 73
    0x80800001d000819071243c440c1c030303144030341c42103115038030038000c0324030b02d5130704c400c00f51010b000b04d440040d503d0b851900080d0000e42160014500860107051401c0d928010008030307000f03082c0080341d201c001059000100315620b810843c1d11980302040e198070749a1401c580b281d10b003d00c002400c030380c010380082c104c01c001400107804803291280f1041041150f003203900100c80e00c4001c1542c10074440d00c038050108000384407040380a10000c0c4421070041c03500a408a000b24038403d03544101c089002c0b148207942c09621800710800e00002e100301d9030340d502c4405403105000c132a0408a6107000d083c00b482a91500c041c0742d0100d806494090910005440140342c50a0144c9080e5054040d1401140305100c0b04200c0060610f003400384040540f07401031103c46003269204801d2050300c0d070108031520100003a0401c0c1e40400e60140c011448034611603142c10350b40040e501410810802580e00050410118405000402c00b50504483c4550703818421160295103920140d0000c1d078090001000c00c040d814 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 671268021 1250 671266771 671266807
    0x513061a040e0a05010f050708011a120f090d0207140d020f041407021c081602030c01050115090603140708090304170115210b09010b060304082107090308 68
    0x900600c1880060b0320500340c1c9480e0a15100125000c0d030a2506100e010a401d000e8144900c801e5918020307075a19142a4108840c00d5490110b402c210412141040c1c100b91950f0504c903540031400f1031a94140101e1003460581d04509910442d0054442840144803404030111604030031120024030060500005207050911140e00340c0c41483d00480d010b04410180c9100d00c80c1c101a029643c0c83c03030b0050348030301001c03020750034240001d60085e0024440384c0c500c880d0442c1840d01c900c101c0c0c1c1840383c29450700d800c450080e0041241030740c00655501e201c550080d100406441c00345400c3c0507032103089400500c8040b01501c02802c2c0170703500000402144082003a00d00420b80b912650020300d5401d4580c80c001e010210408518904400001c6850240d1600c0e442c100508204080d070404607039101d207400300b200a00b0000d41d0f0b5481d40d1200c2d03d29500c03480a140220301901c074183e035450900740b004481c0d40d6405079004042103041c08002e01c142e0000740e084204c0e9040031006941e01494140311041d00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 671269271 1250 671268021 671268071
    0xe0303181c080a0e030c0c0405010e160503040f141c0201020408190f050a06051b18011202040f0e060a1a0409090c050406141914041d06130312051306 66
    0x4440410811500c40001524a24915040d5410002c2c0d9032141c0c42005111000c4cc1da0042c079401d0300005411840c4214000c640c414058a901c0003c542e0340d95560740040c0c03d240c42d0112540c0a40000f90715110885c0071424204240c1c0000c6180c1480d01030711a40f10703052500c40c200c0c48000038401c0410f002c1d0000c0d801881e19884401ea5080a40c0b91401e4002002c0136a00003881c406200e4215614225003400c81d40080f03940c9a0200b810010117004550017200c010140d0705440c0c09000002e0340d054168070460241c14200c2e040c5589240c55000d0140504869100c00c6010384151701c8452110310710030480e41521003050001c20b0480320742c2081d10708210642d1000307401c1494804002001d55035203e440c908440215000c038941c125541050f000d04110740101c0380e28080d20340e444200c4d45004d5005070100844950000c5045082015041c03c10301c1c1110001c5400d000b403c608410568801640342000710321401c20051424034034003001c5141c0c8441e80060000f0b5442c1d045d4441d40303840440d850300c0c0d4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 671270521 1250 671269271 671269273
    0x100b191110150603050a061202090a0603021f0e03150f0c070803071d09010b2508160b0f09030702280308130b1c090c03060e0303181c080a0e 62
    0xa0004404101c6502c024407a1000003807030100800c55240c01e40c010b003003c03640c0c80000490101104e40030040305050180c005d401c440da0b11203000006032142000104059500c52200d07602c2e03c41c1c414054081810005024840d401c01100301d2001581a134003150802403550f080000399070b031400d10100ca0301c54408050442c02c000b10402464075884462030954100440c0e01111407180b400038480058820b000c1c200c8a01400d01c070b52900c4201b0350243c00800400b00c00302e000c080215440382d040300c0d445011403510342000c140745041402860300882e50000e07207400703c1b00d01c6803401c1070341d0303644034010050020b01c910319940401c01d16000c2c1c1000c03194000a8080301d503400304d07035a02d04041643d0210b0f0401018441604000030b4010b044404c0c3c96201000160910495000c800d0070001080b040303130210f90845983e18041b000c602c03c0d02ca403900c2222107100035540c034203050a11803c0c8441c91126140264000004103140c5046800c42c0042034015040c800141e0f11400c50020240c042d00240e0101 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 671271771 1250 671270521 671270531
    0x30e130905010603020f101d0f0a140f030307080706050c0d1505010f02030408030d020906071b05032b0f3c030e190606030c0806100b191110 62
    0x740701065001800712803003103c00c2120404510248030048a0010b4100045000340103181d204a03184541d180c03080200030144440034250b007000500b405181d42110304403d22648510000d402c2c940352003000103004600850034011127a555107540d11900400030500c40c0c5071804260100204003da40c54000d00341010301030301002510030300040505100301030014005500d201c1e8120700100450f02654000f102462a20040c1400440a54454091203030045007c01030400450180b10700150884080c6002c00f000b00e240104251504d00c1c0c601200070491001d000021480300040055140722009040c80301035000340d6141076556000343e420350801d8240e2054500600320940c04a01c0300001900305500c2c1d502c44001d000c80c12101100c20011896001070100343c0006814241c1600b014450600402e8464130390340c070b007417150150b0303400007107194019802e1282171000241c59201400442c2030580c01d050061900760702c1001458440001c0c48450f110050350428240080442d55001d0302003806 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 671273021 1250 671271771 671271773
    0xf0b070609230a38060307170609010c3b0604060e0102160501081f0503030d06030521040504151a1e13141207090e0106060804020d030e1309 62
    0x789074100404211101904c0d90800c0c0100d695030141c5103072941200d046104115146142c03040c11240142400c2d0749442180000501d6411140f6881400341c0c1e40009402641840103590303082d90a038441800501429208031040d10b00b102170600c020b500c00703400c150000c2c0034031001030121983c0e00c1e04807a00500e001801049840e040842d8804200b004c1e400c4840c65441000e91111803005405210700140b031040208076058022501904524040301c02d0200d803581d242c000a1542d0b01c4100b45440035616503d08109010040c030103125280f0464166048100488075091464411b50084512555452541e01e011030000c042c0b11001d03100d640680130b90303d5020320100c07202c2e0b0060303c0309000d08602c0fa034402c0c1241141d4800e8480b80c143c001c507052061410080346034942c08000783e0088e0007005d40105110940c0b010011703c0c00800e03aa49001a038801040e80c142c0c2501d00c2d40d048502844402400c0c04011b03143e0f1410f01081c01e130945050301080140c00002035170300ea5800402c540305424002010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 671274271 1250 671273021 671273023
    0x90c090904050c190b07020d03020f0106030b180d020a020121090605040209160e040902040e0a030c0512131a0906192c010305040510090b100f0b07060923 68
    0x80c50f284011500c99205030b64460701c1202200313550040c078080c000180100c40c01801c0269080030614401d00545401340a010605801c45009600c141c4070003d5000612000c130400c5503180900c601d0840241a1610802e030740603540c0c42c512a4000e0400c50300140d00c0551900c0513143e41481c0c0310040060041300c40f542010000b070720302682e00740d101e81020742c0425207018030f441c1c049018101d25151610b1030743c0004108001420441410ba0b003150b140c0f042030b0080d00b41400185002c41c803d40703032904180c1c1c1074207129140c03070080301c28050856003c000b00e0710078240801e0340f4011901c00128a8284a80c3c081004019002d200610b9800c00c04c041808440e4a540c0d120038030364200566221445841e110300382144201000580c510040d042180c65669548641c10040e4010700403000c03a4904029440c55400300c0d4070100081e184040000c0c00c1c460888800c1c803010001700341e825020310515007000d0386002070744500c0c00004e001c00c0d9182c409a0030814a8103505020422064a420f103907000d01c8051 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 671275521 1250 671274271 671274283
    0x230f061323090115080f0c0108101a0d0f02071a10051203090a08150a0908040e090a170a0809030702090705030a0603121d0411031503011b0f2606090c09090405 70
    0x21800b40200f0070007c031a5441034440324462a03e078030087d042a80307800c0d98258500103403070f0001e44914007003007184000b819a0080d04003c11643d40d0040e80d4800718244000c1001c0c14006260810269805100c60308100e444600c0644008940201c0c00ea540d46d18038514609c01c0070304d0305030081c40b4034500103105100841e19a05071410780d5200c02d6030395640d0018600701e4850300310040920500748018403841e40c050a040ea80000600212201403a00d44c84100c034420f01c00501c50044400010380c0701c8034036400380b616900550b110009500b0050349070f0008015880040c0000c0070030402000042001010fa0807800c010758102c4e03010410007050f0300380242030040301203500b9824408400000f82c241000d2090350029041410314a00703544840a00040300c0e452205455859900c5001c205100408040300d50181141512000c400780045080035000020103043c0d00d0350960003d0861102780602c1d000c06070706c4401252401400d545016111407607000d16072680e03030402e0040c41040100000040c030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 671276771 1250 671275521 671275543
    0x90f07021e2a0108090f07060516020301051f09050f0a0509190b040b0c07050706180506030a0204150503131704080a120201050109090f06230f06132309011508 70
    0x1384010399a03c8075481c580c0c90040140d2242945d0051504005241c4a04050800e00300c2c441c010109011541c0c00003800c1d14001c1d100003410004141c254610700c1804260103009060000003400320389040e01c55a07241000003003500404544030f0000800100f401c0c040720800c0402d0f802c0341c4a0382d140d0b40c06c05145000040f83d0031105c40480d440807510301d010400940c0d5040781d000c1c0081040714140304044a41282031940d02e0340c0c078062100041f601d07a444c50040c40c411001000d00507110b0345450264444400300c10b1404007030242c204180541015541c0c0c4840016030008914441c3c40090068000c882c4195400140d05006e081d1440781000006070005803100031aa000740f04598850860f0000ca86a0120003424000034000010000d05250850b6060002c445c0702c11490401601c1920b14510046a40000280e0114100031306442c02100c00d00795004416400c020446002c05114071617035411160740c41d05210100000d800b00f03400d42110070218804064030240316502c404032943c4030a4154 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 671278021 1250 671276771 671276777
    0x40302030c10050105060a031e1d0d0e131a150a1e0215090106030221012403060f0b04240b0f0441090f07021e2a01 51
    0x9021222032030f0081906031040202043d00e08004640f094005028a040304101442d401c10024886a8503100300343e1612040245442040f41c4c00d0841ca061004424061003484004565600720703407506050790319401046078000580041111074107218607200450035902442100d60003050111b0032024149800d401e4070307032101a01c2c0c03100d4600340d4a42d56820f002d0041c0e12240d5401c5e9404401c69400341c22101c0c21000041e2503031a50040345202402e40b0120120759940707071502030710300c1c0240304014514211042500340780c2d156004941c000502480080c2080341c4070907080d482c2851561001c0d125007002802044480c0070b40480d544c062050b6400c0462030201c00c174002483c0500d040840b0840203c1126262800f401c05248615000d800d11000b104110074044a002c0840e9a03603000c100040b01c0504d140561651030f04000b0b81c10b20081180007000c00550034800da00b40c0016030700c41102c038140c10001d48025032a03025490b200c00e80e061103141705150180e2031000b000c0c150342c0303c1e00c141080c1c2e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 671279271 1250 671278021 671278033
    0x7020907030603030e130e060112030206010b0304050c102007060e041503060504030908030a050d060501170126160905090a030c020108060402070b07090801061703120618040302030c 80
    0xa50858942d880050085101d41d4512182450120624210034030380c5880007400e4292006040e1401e0340980140101102a980a006050301002a140101180d41c0710f180707940f40030340c2c9094986591500c8107003d07191030b402c4117080601070740c1d8074054500c01600310f03019080850380351a40c032203881c810a4042f5a011514036190300307150141648802d4040d000c06641840e40e5181c800900b4000e0003a00ac0101c21400480c5c1c07024140300402032300b8010399415459042400b00d0200f12441584030a05001d0301700101c00d00104189a158112420507002035000207440004010745288407411003450700945100800d0035200341880b03c26100c040d5030401c803030b6842c24010b40c0d0303a0441c01c2e00030380860b8059102c88015849601c030b80758070102c0500054241031041e80c990100c140e044d0b900801050b1804400d20550307a003446290001e00c030030703a40101d1081800c1c0241d03841c6e00c2104400c3d943e902c0e40c00c0004180d511610340c080f1010702400c2e00d842d4186000c0c1002520b9400558441903140950 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 671280521 1250 671279271 671279281
    0x10f0201020403020108040b100b0c070906140306160908010f0f0612201807081e22020f030601080a14030a1e0c02101701080607050a0c05031e070209 66
    0x5109840a80358103851b090ba403521070b515089800d4030010020104680e82200204c0e41240390710203004000c0b980c80c000c15a080c100f0704c60400f80c40c040d80141a1050190003418140da0b00024442e030030401a0405409111410504541082140c1c002000542c248451041004416032060100240c0c20400308030701521200084035503074401f08098540b64100601c0301d1102d20b00744001d800894010442d00da0316240100c9079000c20403c44880000ca103c83c010001c0701107134860000306d40591000c88a00b14a441401032280c01d10007400150040d6181c18807100315159145a00e04e81d180c0182200c1c959039580f007191307039202907806045802e00b000304002d840f041d81c00400d40c0c842c003019448118440d0203884120482075041000501007040e00c003203400140e110b90303580d00088421569004c1c0d02d6200d4441c2c140c6041ea06034000c3c2d5090340084200300c130079a4480e00343c5940d0009460040704082050038058610300038090160310a034045400c0a81b4503c0010041c01030f42d100b9250541c0690390 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 671281771 1250 671280521 671280523
    0x1b0303020606121507170109021b1f1104080303091c110601090b010c122c0a0b03130c080607030b03011a0f0d0f20120c130608061005010f02 62
    0x1100d180783c0d00c0d50700c10f8041d01c004840c4e80c844964031020a140680341440c0d40b02c106a4045001e0b44402c000c6035000810110a590300810b98030320a052900a00c8141e48101c0c0029099800e140e01c0d014140d5241d9040c10310304038610840e0018440348044980740c0c1080300b0303003d1726101c942c030381019266600c1c003030520114003070a50034002500c0300c40640400c1c4c1c60203e400d006001d0b0b80701e05504000044030048006021f8005117515181c0c41d981c0c501140990b0014210070601c050441c1f104c0007506285003101e1754034000540156590300c2106600c035242c0c3e03451131180d00d89000b4010b011500c6600d02140010000508070300c164010760b0144081c010100a250881d82410020b0036a401084018081030a000c1d90850742040058803403044103210340c8a040f100c0920309011102d060a504201c42c0080ca44041038980340700c00c841003000846102051030355001c90b140307a079000c0c0784001c40c0b8074011140d50340010010201c040948580b4640b00b258000b00c41e0190003181d002c1440c07034184403600c1344 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 671283021 1250 671281771 671281789
    0xa180c0801060e330607060501050f010309020d060c1704110306010b03011d0402150a050d053304020415080402090108070602031b070504090f0b0f0402060d02161b0303020606 77
    0x10a60504540e105944140700130782220001051400f401c001a00b440c0036142ca200501c4000d0007072000040315414030040007014001104018105420f0100320b40c05691403130041e51145500180025080c04d070a50180c1d03000020706d01001d1150b000e8010003040c004212800140f5102c00c90030f841840c0c0c1c845e00000500d000038090200040396120109000d81e140c903584a0704980010407201c0c403c90111450120b0b42d0180c050040000e0b00410112410182c1c0d000300303604104480c803e0900c1a5900703101a1030000034003c8940c60500800c2c555030741d40c840754106c1d000340c00307511400c1155800040029022440c142c9007280241c2034440009080100030403150190f03074244d4003039803621044c0d0003003030041484c41e11942c411740038021002880d6a514450ba2081d644280c4200411074902e00300120744601c0188034400d0308a010041100507070342d810803100700f4182c02c10010380f10440440c1041c0c0b04418204010203548081100390320050012a036102220f100c0c1d401c8030425904c8400303010140c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 671284271 1250 671283021 671283031
    0xe0d020114040c05011110020301060504090b060a0507020118050d08071407080c2101020d20090102060f09011d011d1902010507032304141008010e0a180c0801060e 72
    0x514000300038800d175131082d410400c1c207440e0b407000c80303151607a0220440100d034420703880b403c00f003880010108007400c0b5a0060004000c002c555a9060120400028240c0e22510100904001c058050346a0f040b1200001034080c00f8098054032034500705192031241c0c0d600103101034030903203224038406521440000310b40c0191840400034000191090003808042c00e0703442071518105000c440b52034100002440604480e25410b84042000c0ca4101c00007500d0b2800441c0c1c0f130071981810042034066980000c0c603190844c0f1641030603003c0d540e50410041c01031502d1034400a542442c0e0700c00c500a910150404002104000108468560440f80141d40e403c03001540714402401500135902540c040c002603d0154000d040140d50400d40a40f50014540f10b00045000b034800440d0a00052000035401c0b1900c8000381c6411201c1031294102800303e00052141c00c02c400e18180008000800c00d070030a141100a000148000382a01d1a0a9484a01c0c90103802c0c443c0d031030405c00180108240003514010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 671285521 1250 671284271 671284283
    0x706081f060e0301020d090f23120306130504051f09020f0d06020408070b0d1518090203070f0605041d01150507030c30050a2a060e0d02011404 63
    0x4a440c0c00070503a0101c200300001d991656003446950707003280040c01440c0d1801d110f00e100268002003850480100300441c510121903e91580403e1f6080c500080c52043ca40100c40c00d6980300e6072007200040241ca003040321040d840c1e0910050000f00030001403c1002101442500e000d40080814a40100c4500c514003a502429007003400b201410460808114a030145402524258823095954a0b00d10190300c10080604001400d441c21045482045007110002d40000106880d00b0103403c112110710540da49140c0d51140d00c4030440d5420001080200310551030083e009640360ba0203042c0380c10034414040c4011140802d100c6c074619030110141611583c801d180d44880c1c04071000c850a801140c0c0803010300c8445c8440c5d40100e03209520a0350005001e5481074291030035520381001c500c8068000b5010710205000c3c4041654200d40c1c6d00030315520341e511801440301c40d0303106031184000300c0304007800d014034040c00c1c1d948450340400c1160a1f0021074009121841c4411002e88440b00211400b4081c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 671286771 1250 671285521 671285581
    0x5130515071511040e09010b031b06160c0b180405011226030a09051615050a14030703020c060c070f060506041d0c010f0203190809070f0305070608 65
    0x15010450700c441d2854020000501a212600212481c4d0240c1c01c62116001c1880c20003580340c0c002d02817060b6501080d4040d004403132500c10010380142403602c40f5441240041203c0002666080c0504115604104065501540d80300303890070940c040340d4200b007901d08141140929040030f0040604849800f4020a02446580c880318800041d0307001d03580000d21090841c5200c65134540107103005075000340c00011003840314070f803ca01d80b050207240e070100141d51010400825114070054510034190342001543e9220342102201d0034555000c46107416400030082c03080f0117a00d98081c0003180040c0045980603250b42000902c00d001c1c010000703016800b020b068038001030040c0c020a80003603003d040800e05142e09084107981050a80703030703c0d0160f40030482e071001640e130044a405400705140059440c1c01c18014545020340300d038804650030b200504000c284018001c0240b6030040c81c803010180c1600d5164500b00c0e4a5007400e10862300050001d0012405040740440350152071841a090402c1c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 671288021 1250 671286771 671286773
    0x606040506060c010c0509040f0c090e07020f0708030408012f0d020d0911040b1c0f02010905030f0d0f081e1b0d02091203030408030a0b0f04020a0513051507 69
    0x303014000c1c2082d0300494207204410080000b4024500d2092481c1c4441d52544203d005110403100791380c22101c003160503c8458908241c00810050503110a08a141c20036510940e0503840c00b0201203003208503101e910000038402c8400700142c02a911500028040d81c80d48030300000102050285805050420400750300c1200700ba10001c00721104016005410401903011034000c0310520031003a50b9028022050504610309031140d004201c50440c2c0c01c5100c180381110740b0541c0508000e00900e0b101d03007240604250f81c0120b074903100a08001f0300300da0710940d2004150b0f0b100c905465071400400c800d148040c1c417483c060031a0900c50620308480c03244c01c54501e4044c5000340401b9142d900d8000700d41e4006404100b074480105004407102000ad42d41c0e101c41000d00018490140102a40b07030014824070002400c0041141e4208140c03201c04074504c0d170703d0390004600099011080da8428800248416859001800340c44a101d20b1a080c00c001d6594000b4040c9481034040d01440c4403c1c200074100c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 671289271 1250 671288021 671288029
    0x607060f0e01051b090d1406090d0809070308070804151e020c060304020402031b19120506010e060a260412140415091e050a0b07023a0b06030d110606 66
    0x1080340103000b4414005c0d914141ca49074032482c0b031306c851f09845410190070407040c490104150284c2c05080e00d444499482c08444042d03c0300241d020003042c4030f10008001007801302c0c48050340c000d00504080e0300c40d076142421002d4000da900c00402d400c0d920054040c444071500100d803565141d58007030b240610b5640e40342d08000081d40000c20104034183c03030012900c0200c94039005807403000700004c100702e80a403444402a100b02d4441c1103c0c040c40b0b0801d0b0421a9590303010640d1244040c4c281c41070b43e281c444070002955a014610280c50f45207509120600440c0803c02e5010700131406050002d400e00b01000c0211103514902180c129007141c20401005038082ea4011186e84181515108c480c26484001e11142142506141c0d0b1032607031900070602c802e1900700b9030540200758a10505241804a03030115115071070708030407000901035100c000485003005450482022100326003a1418201c6031402d21015501502c005009108800444803c0c0c1c2c041d01c4041c50800d000c100400182d03503500104 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 671290521 1250 671289271 671289277
    0x130608030405090c0c16050102100605060f07170a0314010909050a02010503090f06130c0b031003020931060e0a020d06110702030f0601091104030b04020415050607060f0e01051b 78
    0x280c11004100141103c20200388038603440d8206c502c0e0b501c0034686ca094002031030925428515400c0c1464608100030655070281100d080c2100c0320815900c44009007000c0e244140c04007001064000c4c001501c030361442e0b241d4089003c0d002203d6080c005a601c4074045400c5440c0d542c0010241d03400150b18a01640c040c902466008007900704030b5801041401c4000e080c414103450202d5004999a035000400100900c0718001c2e0048161503401e603e08140300e102d48940c984000b074060301c200804103248035445250350400e0486584800c60352180c5420031280300684180a03a00d0305d192a80440c4250404100b0f4020315400400d0b0303d11a00942d10f620005100800c6112600710042040310016207081c4915150b0f2114500504040c1d85400c4800c42503e51041103011078180400090000a00c640d1640c0e0708140c05480008198069101c01480e030241ca402003a404000070a45008004131a0801007a28840d034400340270a5515811050a07a08161004003c0e503000d000b40003034082454001d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 671291771 1250 671290521 671290531
    0x40302030a020d0c051315081203130c17030a11010c1709033006030d14030a0603080412020406120819020a061803111606030906091e0213060803040509 67
    0x2200591540d40c00008000300e03071400c540340d442d45c0c035400d00407c28171040329030300000e08800010703221342c0884050015140c031004000008a8100343d03031000070b104110202e80040d2510001e0551043c212801aa0f96504000c02c0200020b4840c14401c440b11010f000c2c40c00315981076111280482042030511026201c01070812183d80320501c08040108424010f81102030100e46c01f84240c101c801200070021040200018001d61100c80c01c00a0709500c08007007603103403100024246e2680c0313911100002070036090784040c00c0d0075070109000c56103c0201c411581410301c00c0f9010000e450b595080600c60714040c420151117a9000e10524000000e044ea01c07a03560f00091041d41c80e102c032241d54100c1101d02c010121203444840044003070030150001711702594104101c0c02040003030f27560310021540c030b2500e0144400301625130014400b00800c0b034101c05203082d40681405460100b88000c50320140c03406030281d111307511f240000122440c55206e0f01c0b054440c06005946406d050400740840804064a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 671293021 1250 671291771 671291783
    0x1315060c0303021e1c0905062e0b0c0c01030504112704080405091302101809090503030f060a03120e061909091b0806150c030c0c01090902040302030a020d 68
    0xb94524810190072135402080c104403600f40c4608000340c81507100024a01e26502031031501250801042000175240d038018220700c0c0428001c400b4070440c200302c041450580c80012000390300030441c800b000f4094204c50055004450049074040300440c182c85090718054910200640500070b5410007007009200c100c04140c0c200c0441d040b03480d8101e0180000c40f02541c681e5004541131100d0300e890000b0a400c1b01c2d14150083c4114410313000264028440c94403c400e010088001030450006528404d0041c202145c0422034054607003003040c0c1341d41c0200c0e507502181c0018070001d03003203223441031601060301d4202d100d64200ca203000034191104040c0c1c1c1c1d034042d400316042c01422900c2600804510010600c1d90340c03801450f2034603020b8400d5440030040303140d0502821407140c0401c0d03031111038264445001ca6070703413001201d0440101140d210b1042d040400e400f00103107802e074403140000d60180c086004e0781e6070254242c0e14018001240a140030095240d0415240d8134054a0039502c0400d50300e024070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 671294271 1250 671293021 671293027
    0x40504030e1e04112104020a1e0302030715050a0f050415120506040b0f130219081e01030816050c0307121a06030706200109030c021315060c030302 65
    0x140015403410042400d03440040362102e50700082d0500380211041d54240000990405c140214020004800c5071090180280c2542c0001d0543d80c80030a010f00800042c0d808581003a04140120030108181c0401ea010381700303441000400c1c0304105100080140260707039240c00d054200500721004074000e40b20b00104002803101248452000754040700c1c0303904030317110b42e000303900e020b0400c400343da00040a5910891810040d02076a40703401c1c041869900c41155100780601c40075040d00001c1c0203008856a940c0845120001e2043e00500d485003d100c0c1f80030b410440c0c420b07240c240308d4600001d0200420001d0103001110446038030f10008280148100107403040700c010700011910701011580546030b048000d00f003010601050704442040b0360841286411240380510100c0da907140c1903c54a170411810040b034280072184460002e0310050030303500030322400c13a950400070484440810300f640300d041800c0c808a01c554072880b1744291001c00300d0303050115924240099840c00e6280e88281c09040d020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 671295521 1250 671294271 671294297
    0x30512031005150a110111090d061107050c09010b09011704260a030e010e060f0c1201060801050f030309031c09170102070309081b04090f1a09010f06050603040204050403 75
    0x550116207003210207542e141d894a2010000800c114054117440000c0e914001c0d1080e80250b800f000c0b5080b5000a45031441c01112601d40079000b004100481000441d01041d020100200440c0c28061a9400c40c3c203005642d032580f5081043e0b10405050601049010035400c0c400f2454280d51984580a03c2000507280c00c01c5d00207040416110030b00b080c0b20400010680c000c01c0c0c1500c18201d11100b038100820004103483c040d10781d502000307483c000c0c49050080006000481e507800b110241c44100b6100d07d100d581d1003802900c03c220a014240c8142480d0b0040141703410008180c881c15007005000741b40d07013040500d28661380800340801800300040390802180f1100b1814150001036a803800040c0d0310155420024018050313600f01c0150b6800031060314031000c2d00240c2000b0f881c20304403400140400c140c6019445040303414401010414000f212214100790140154401d6801c580240030000410400d00300f16402401456800390060000c1000b508040d401954803600c42e003010889074481c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 671296771 1250 671295521 671295529
    0x909090204110c0606150a140c07080706030f0b010503090a200d050703020310051b0903010f0e01050f0c160b0c0d05010b0307090f12030f020a0c0b0903070f030512031005 75
    0x242c03082d4030300c0d0740700b0424420107003846c8206000700c400403c1036500780480080c4c01808035000c00c2800e480f42c070000c40e4141d2950000c0c80032400818800c811507403055a1a070025002d00f00c2d01c0002c07a6003924011034000079500807400c50384a0318001001d48078004645c0e035240750750020300c101d030b2007040d0000d04005400c7d190220f61071000c5024400900040c0c4c914070425140c001c02c49070042c1c0c0349090005118168038060703980b402c0f0760390081405823158280d00c00310b4010240c1d4000d0300815802c10104400b03098044d44aa4000c190300065110142e5411050b41d080d40b150300800000003041c801f15201003a08150b5554001032143d41c201c3c5000f0300d21100b040bd440e000c1e00604527040000042c82401030b00001c0170002031542003002000e0b50300d4481c644040c987e202c00b01a0030300420028203900705109000f061382085d80920300d24100c5448403078030007603600301288060080c400c0c3e6801041115480051000f1070754818000c0c240640040d0313680383e0541015140b452902001100850b20f562 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 671298021 1250 671296771 671296777
    0xf0a02120c030d06080d171308030709053d031805031b0705100806040e0715110f0a0816050102070b06100c030906030c1b0f030f020706090909020411 66
    0x41c03640000c0d61034000c51100ca2003140c0c0c61358445041c5600100000440c1340e00034002c0205a02203810010142c0d49040581880d00503500c40140b4004000040050983e044159402500c0080e54512408000c1400501112001c1da40c495610b0103402c03107080e08852030070000a0b008080d4a0f0114801c00c400100c22440d81841700216041d40000c03032006c6c030204248440040078000c2c030006084083c23800001c80d88010106920303030100300c501800103520380c0300c07034000b004038181800844103515a6903500171a01090342c0a21800901051103410f01c07000300050003117582c03001202501811000f60b0742c60801d580070710041401c48003038448c0c0d940403500078800383c400e10b4098070604080b49081c0c4204244003488001d284207010b0074104150100b80c1c0300001d802540c22074240050082d40256060b0350628a1a410507080007518074140108450110b4803c44544241c0b0b40100100c0c3c02c01050380c0b10b0489000e100d0004099040c03c103c0b155107608107800c43c6001410000d40c030318a440914810798 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 671299271 1250 671298021 671298037
    0xc03090f07030c150504030c06050702040b21100213050f040e030a030506090121020409230f01060605030c03130804050a23030c0102030f0d060f03050a0c1a0f0a0212 73
    0xa90038400400c01c0d8540300020303078882101481d0030341c0303451f003141c1d100c000144240c012082088000b003007000464541b60300c29030511400810a020102c4202101001c580e0b00402c4c58496021344a010000d01c0907a0094601c04200500620385090401081c000e00d06c44103010f0f5a40b0580382e8a2114681384140018504000d0a5a0100b50344ca0302c0b200780403518a040c2d1080b01d4012485c280e556100c0c500d43c12500c000c1d03504407004036000c1c0460802810050210074000c40e02114510240c201c040001910f0520102c840005d010250f681c40090340c0d14081140c0101a01d1010000540e03808500030b00120018440d0343c0ca6403c03e61502c020400e82103013604014031034120090561401c000c580305201705410304070003c010010807680000d48900501e481801101004611250500d51581162000e400d821f50490001c0b039403030800315034450300c08805403070300030703070310501095841c12800c0c0e5811401d14418007525001c44156403182d158404800c0ca0118010100d1f94098001d00c80c000f8013004e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 671300521 1250 671299271 671299283
    0x409021201061416030c15020d020d1a1c14011a181b13030209041a180d080415050109060609080a0b0c03060a12061b0807080c03090f0703 61
    0x1640c18060050710010101c80f030040c0c0707036034280100d98890b04c2242e070304407007154586000c502d1b8800ca481e143e00610703900403056103514008170b00c140c0c11058070341c0688005800b00e9401c0c00064044041c986590307107204403040c3c010481c40e0441c1000c421840303031a00c00b10301c500d60314416126484e81d0b407421030300385101c2e10501d584803a20088072031400e891746191040d84800c028480703041440f0004001181e100b003030105404007103590b252038204a400000290b030080d04d040d46c00d02e09841c1c020800c8030003800c175011a000c00c0d00411940301307810340b84403c6035101800a0000d000158415100040010300484031044012034412003544a805441d000341203444c2c01250060801c24007804070306e695004541c659000321071843c0895840da423400d0b0000c550308040c0c2d503251156801f01e044441c0c0c87d001940080c600c64031440070440c00c0e0f44018840e0b0088442100c0b46101d4000c00c48106c141910400b000030b0049001c20103550b4604001d5401c114088126950600d0f40c0b034006082010552081d160 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 671301771 1250 671300521 671300557
    0x506061303202e050708030a090309170712020a24020d0212090f0301060509100306050f0f042a030b040b01090203060325050a230402091c020303040902 67
    0xb020015004501c0410012075603803040c41c00b00001140742c210b0324110690484490004055003a024004030703130002e50840401c990320700d4000c1c0c075240500014841100041c0c2d9800b000944c040b111070b802000e903410304020b000c969150402000242441c9141681d000d10720380c10020b003003814141c08980954254000c069000191070340a81446c009407150010354210400c82085203408008540404004603050b500c00340f24030010900510907600480c1e008801341d800e01c030704940701c496080b048a100702d0007801196a52180b050340030605403108450508054040340008201c0c0c42004100341c80700a803505095082e410400302c11100c0e902c1030f00c10303d45c2d003010700c0103000c1c18900c0030b805021500c400394078500b03118012955500c3c00c806a000e1200c0000c520410480d140380c1c0308802050b0081c015100c168582052140c400342e40c550018442e010f8030341da07100c181428025a46940d000500613a0502c3d0280040d401818854000720f0b8035000802012071400058130280082496401c034041c8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 671303021 1250 671301771 671301803
    0x1031208070912140109050708060a0b04020f030a050a140a0b01110601050d0312140c21060108061005070f0b041734021203250203030a030506061303 66
    0x1125500203407426042007041c2d4401d02031201c4103280000280d81c0198000492403041001d1801407501380e00003455405103420004011000003051405031202000400c00000e541003004200e00c144044c001e03c1c842d003403001030304000d107542c0840d43c001c0d40c01101052120602c80c0048a986044584000c02941c803005140e103560301c1044002e1100b2204018401da5040800144102c0b0b44440010200b0061013924030300c00440d500700c8801e240030103442040714289240410072a4100509043c0c01d0501400840300c01111445035501409041c2c40b045515103444081c03101000c0c140070000d043c00010030148001640004011001a005421480e1a8105448c00c581c00304a244030824a075030f4207010050b500104100c644495141d094200c20500000200948512594400103580411452426070501501000420910700d00d00d03810703035000504904507021545401c00294040c1e00610a09051900030740c040754000d04001c0c00c0320304003511030201441c410200c0e002103034020340280d0012 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 671304271 1250 671303021 671303027
    0x1101150915050f04020901050c0703081b06060a180b0a030b06090108030307051812100606090911041e0f0306020705010f0209011d06040f0b041806030b0f0a14010312 73
    0x1503500380300c0c038003400700e480d000c0012820356000450320b201c0d0350b001070545200d0703004100b00c1c2d64580c050010b5802c60380d42ca003019404c2e500140c05041c1c40c00003030a80005030388004101107105000090840c140c071f03420001d110400741f090711201c1d00b00940c0d07040040c0703d603580c070854007008622440c00003526140013410300044100680c0000217961040c4144000c040d000426141130080c20105004886000d20020740c41a03c403103009038250007000194088810b058000105450f425242c0440d440e59810405c800c0394211050060310701d01c184028490f80500d8001c59003100e05080008401507202c6000402440c25030340201c5001d0341c00a940010800c0038010707070310307070351070b0340300b08508000c0f2200000c1c00124015a00300030f02c048000556160307942c0c01003502e000d0700042c62002007254980d089041d8550150080c5802030710011034110860784c5038010503040da940006a65107540b5044080d801e517800291414400c42d842d07000c244074414007090414001d500411408504038080d540103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 671305521 1250 671304271 671304281
    0x24041101020601080312040204020d110a1715010302071104111804090f02130906020a050a031a18090712030e011d030d0c0201050f040f060f170703020a11011509 71
    0xa505540240d001000011400301c15074010190000c0002890354803031002500034461080402c1290b450640c0f40c08c02d41a044000d003450380c0035510340641a401401c0800140d0a080b28400140102282e941c90954441e4019101892040c0c101c1e15040c64403d0000e0251440b401c00c8010f490004035142d49004440c1d5100c40c0380440582e410010381219880c0c8402c2074480c000081e014245801c41d1016000465201495441c0c211808544400f9082c00c01401540000170942c0003e0900c80702d1112544480c44420b202c0000420f00b08110303010441141800d04000d140c00c1031303070051034400101c3c8002c840503154480e20075524901d18079051710024044030701c00300114684c503211400c010000e480018840a103814207052410141c48680700484484c4a501e00c01c2a400d80c000c20000f0340000484422401d07900662140c50414440c1d0108483c2c0b060304d030110902e88410b000200e640b550082e0b00030010112207141c02c1d0140481c0c60407641c20348034880b4401c000022140404c1080c200320b8410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 671306771 1250 671305521 671305553
    0x44030610030c090501050c031e04050f03011109120f061003061b02100b130e0607030e030a02030922051509060a081203070e032b0309020907112404 65
    0x400c1010102500005100b0183c90103401c0c180000021010412042002506c0480300042c00341e2011000800740080550030a200d000c2c001c4028a50640444c0303018002c07100018803807181103007405211403c01080511006823081e80b40a00b41c5c0040440c1c500303006c540d2082d00c145009a202500c0d40c6070120031100c014015031035030206004800741466000c20081c240b241101e202080c00c42c80c040015008042002c02900c1c0a40b1700a50240f00020100703046211720100d071010000300d456605c00540781d104082820707005030000c109a4095180030420341160152403408094039080703a031024811950280c0d420f030a420aa85402c0c2160702d010342134a5840781003036031010106441c02c000503968500e00c12000d0515000480046c1085206400c004105180207044901080c0042c00400f402034085035980900c14000480e941298064040c0c03941c07c6502600c0701104da41e860030211006040c00c0400c10060060441441103c01c3c000c3c00e640e1017606482500c4000d00f02490151104074007215 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 671308021 1250 671306771 671306777
    0xa171b0405040b0a1113090e1b1503071709010219050406020d080c0702030d0f08060616080c0a0212070503070518010614040503060406061d0444030610 67
    0x81000050f183c1c0b101581041c4002c44c007148014104940f09918054a6255035680e80225000035406c1202c0d00414405071f40c1d03405898040c0c03020381902c0c0320258903c60307098021100180e100420303040c0c0c80046038030035007600e80300100303016000e181046070f6829500110182e401162840c8160b030070b80b148000526807400c2007803a003481c0c13801c040e4403400802d901c101440000c00c00505152400300031200300301d9005081d0380044201030740240c42c482c805590803000408120000700d060030301078221001203100031881c5d20b01e03013915510400b4a60050280d49d00c14000e540f00103005884555081860b07450301400748c034106040000b8185170038016400700c1c0c0f03e064400c0800361416801d009040c1582c0961038188004041d4403a51041071155601894061043d2820071090108503444241a22461b00750b51060381964078515400f210241e038042c0c0030464807074101c2d148455480b00000568120202c02c030010f5510b00c1070803049070150202130000c2c1c40000400c2841e25040301c05801c1c0d103175581 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 671309271 1250 671308021 671308031
    0xf0605010806010507030318030f081012020d030203070b0c18181b0c12042115180807080901030509071a0a11010f09060609020f030a0207020a171b04 66
    0x80000c0003244080c1999040c000001038400516100b0b4000204101070023800940600c01407038010845204c10003134600217011840400c642c0b0044440790303811588100c50500301075076180c003004098414500b01300c1c158801046204001160352640134451003503c40c8280d114419015001203406240c14050310450100310400c0624075480c6903903070440600d400f05000b01d14010440752017445210007800b09031142d4401a04808080c00c01030064a016100000400d5808030034001741259061000304a2401c2065040b04000c0300d07441b03504500030b80f4150401c03146560300e50310402e85c08213000344d0392203200141040503960103004503034100f24010006e000240c07808801300859401301c0c00322f50134280001024a2001d204031460803003801c0c460b000700034160980085800500b14043c048031410304040c80028440241c2c42a03c9014881c004070615680c0c804c2c0d4510025808400e040341d0103d00902e000c10f2049284840031000420600144009407450082840b0403100c07032036041c4218105 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 671310521 1250 671309271 671309279
    0x71a0f100303021c1b0f0b0912040e060609060f07020301060f061e02010f020a0e0901050a36020414030706030c050405060d020c1c030f061202010f02010b1215010b0405011407030c1203020d0f06 85
    0x9d802160200c80c05c001d1403a05c56210301d00011401d100b801441e81d803000011030300907100303d0144c000b468a180700b100200016551010681380d071201d81c0c420031001c25a4211405c8031040750800c020b00c07640081c4000110070030b840c44903400300d80101d075151000502e00c82020980303040c140005805400100d0b1444040c03864250b8100a2803400c0300381a2001c0c8070005030b80b41000380c0b9148001849030109040d51034030349a070078150012400365030441c80b078410640c000402900130301c61604507545541e10285002c2c1072500b8802c080e4412000324602c0e036801c03c2910040c003000d00c80c810314000010040f0380d140550740d10041c16204003100c000f0703c903454000704018000c24080c900804590a00308001e1303190421105074010140b140b00c1ea50000e442c40841c018611010403202d9240301e440340880503590b224a40c203c014001c9002d841e0105000d4444011046140f4001d07102041c0f0a1601801496255542044509488031014042900403640109a40e03017402001c40030f40c005102005007500d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 671311771 1250 671310521 671310553
    0x16020f0105091f02090a0306050a23070e0303070b0103030806031b01120b040b030604050304081506030a0201051c0c0201060302042d11071a0f100303021c1b0f0b09 72
    0x103c0071a8003200301825a110301210160701900c0a400008254030440d40e81c6e401c2c29400f40008891b00174003a860420034503c0036015603010803181d40089500d2a40b603441e154291100c008003414681e2600c81840200006001c041c00a40a14880d681c0c041803814420141031416901e283d032f4610403001405400d0441e684000643d0050143e02408141c00801501140c010000040596014083c2d07804100500030000002c00446521800301c0b0000400405116041e12095807042c1e40764100401110141d8880c8001c1d104107628442c01a4015100050031021503140d1456000945d444800030810b5161610075100c0e0001e400340c0002113442044201140099603a1001820513914805008224a42810341e059240c1c001d00d03912005046060303420103500c0407103066800383c44c5031001500d8982c0103c441d800320b07a8150001c00d208034141d1240080c030304003582124208605402001c806c0544801ca51314214040c03014810000e00341d080c040c06480300200081d68580c401d000d2000c00702c2e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 671313021 1250 671311771 671311783
    0x14030108060a0c050d0c023003010504050406020c0a030f0210020304031209050c04060909110a060203180d12080702100e0705010e0f0603100e0703090206090409110916020f010509 79
    0x15241c1c0300003c0c0c0e50740c0048241d0381ca000b03502640e504240b42c000000c0c0b8903a0002040e009034620010081c0b420903000841c480c003078000205185d0740d403205000401c4581480c1c0c011b260440c1c8100c2c030160418401d031154a140c0035041e1010b800080e540420000701c0d42e01400f6441c1c2c0140107400035403840c40c240d24003602e552880780c491455941d0781e48040381801024001e1000000b0020020701030f241c0e50b5017001c40500301d1000c040c0c1307009080b910f0084e01c40c58014960030858800b50059420100790303a54014055501c1090560840445110400026410b020780084030101d40c40d401c2641c145860001d24120520690100003440c014801f180d80800064090031640309107440700101003d84080761920034800c0380140c100f103011060103188002a010304e010388018070b030303582e0305c50396005000c40983d144000c003c0c2d0440d0080101d8980b609094020785100750062941c0855900a80c010540744141180e07a81260a17201c0c40d1412003581c18090000c80c492200002c1c030250501c03410040d107803c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 671314271 1250 671313021 671313031
    0x50924041a040308070e0f12030c060a02070302070303051e1c3c0608010f061706060904030e0d0b07021605010e06160309090905030913200c012a1403010806 69
    0x14a62035a80c01a0755901f250f030041e40000303404180c0d20034030700301c0320340e43d0307411050025440c1c4c0107032000600b101c0d4042c801c0e02d540d01d80503030007821190b16544040c0c4850b0f000b8030500003c0080030f1108081030300c00d10010801040c0f04c80a41c40d80c00300d0422941e088805c032111a89040743e10030700c000c074035901c2c6800c0030781c08815a80e030311070041c883d40719800010306a5900179a40b075401c09400c103e4030006603005108440c1e107801e58903541c1140309501521400c00320b5110b0303484403840d070101e0082481a070500e100d4600240c0002c080180035102ca14108808680590040e44040000708001071891848001032a00382003000c800b803111000101c842c0160705800c40304d6100f0202400516120713410a02c000c01e4603e0042002071400d042440d2254082c40303d06025444903104500b25420764806d418a01d0010b890988500c1d0b45c185811040f6071064404180b6592115102920301e52144000c60402d4a1442100c46010380c413000641646a020404a821401800100890400030500c0395106c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 671315521 1250 671314271 671314277
    0x306060c0b011502010b0406080c01080115120c1403040f020a1e0b03330411040b1801050f040f031b08120c01140c0d0b060301120303050924041a04030807 68
    0x301595103049006000110310540d07ca8100640040e001d0700118807243d08080070307a10842c11303030b0b00d5090352456030780001e500c240001c10350340070010180095840300b01a0112890a004441e02c050141d07903103a0010f840070381c1c103914481d40340002c52900c04000b0b4004c00c51300c10141c6116441c2c144201c860900c81c800c641c680c05001000a00380108500000e0809140c0202080c1c8008202cac1a0b039074070300290307510900442c0341c0f180011150300314200b41e9048800384400036103090f1030500300718800345c400c650760360500c2024040c061024601030007500141401200c4500c0c43e528504240183c1c0c005450389440302003000109022240001c5844044a25610505907445004080c0b843c01000e04169082981d4944810b001c00d2414540045c07509070540207040c440c0c0b840440400005200c203104071480c07500c0e22080240068080d801440e4007111040076070b60520b40c80d258000384c505802070716020210b6900308210400055101200d02c00000105880345840c2c40d5038081c00301c1c00c002e8501014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 671316771 1250 671315521 671315549
    0x509060708220b06040e070303050c06090303040b27010f021e0304051e1002040605090405060301060b091018091b0512010302150c012c0f0304140310020f0a0306060c0b01 75
    0x401c0d10b5581011480f00220800c1f0790b40c0940d2401c00400c55000348403500c907140502c90108104840000c141c0c0d0259400500c10f10480d02e4000d0186801d1201040801906001c0400d03094103c90a1007203144030305c031520016903924861140100710001021080e41c44000603c103200200e00001038940b12502803100010100100ca45003d2804403040c01107414580001008244158420f0141c001c1100a46040c000307a01d5000070035098500601a22003602000e016048007842e102c1141e4103425480d0803e11001d001040d005203008440380c10030004103489001030004031031a02c8202c2c0861500d40350042c140080854131207000c0700c062202910030340010fa40d60011202070411914070603801002040342e88900c40d03c00c854150034078800d030b4250700b4207948000130b0000802c07010b69980355070015500d4242007004e8040c050302c400713000f1601441282411403260741e0310710003070440030700c2c842d1415210b041c2040010190765868020404119002039441700041e00c3c2a00c1505540d008c0000b902 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 671318021 1250 671316771 671316781
    0x90c040501151803060f0f050a18080906040305190201140310030f1a070804050705010903030e131401031b050f030a020f01030f15090f0b03060403030c0c060509060708220b 76
    0x10100c40c01340c1014041e50720700780400702c0004103940a0840c08001080900495483c0c0d03090908680c0304c000e410744080482045000003850748401400900700041010f03003025200d4031068500300b9940c0d00306c0c02c240f83d480340b00c900795a001310000d6a04030100d4121451850303c1e6000405101451000824246481c0c0e0880c04201c80120588601210a84134606616201e0801842c01805a4060302d1600903844089560f510a03d191025039415450340c00f81c00c203c020a000c1d59100c0c184c01c80321100c0c0c1d07400600c00e500361a0087c0b24000c500501c0c410f1200071501002c0045a0b2450b44100d10031008070704201803586021444418058044801c0c01c12401041c005902802130040d08034862440c140d80030107401c6014034214180c41c4d451004004a1014042540464042502c6070354190f01c02e100180000307100390409087d038025481c003008094403d0f17580c08141d40041c0d4030050f268000c601000b00155100c0e2405078011411514186100b034510804070b603185000f80003070070b6211030b00c000036 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 671319271 1250 671318021 671318057
    0x60d0b1306020a0201050403090e09030901110114090a1b050901030303241e0914010512031c0509060f0402060415111e24070305061314090c04050115 66
    0x10203041e40209040d5550120048024002c02040720101c020420305000807818016a81380305200d4800c1d90b000798607010306200159210050030a8a100c2503403604170900c1d02c1c0d410f5101050203121440000c211420b202e1a00c00800c005600800e40c2000e81400100710301d6803104409030459400d070500241f0030380700c0c43c600406c08211120b0b62003600c0d5601c0b00060202d81e0b40c0021070300c1031600e001d0540d07040d45615a000542d420340100c100343d8070190b401030200d0f18080c01e1230f492071300040f401c807072400742800560300580703940b20340c010705155071101040702d810300c28401241d20920070041c02000303103402e43c009145801075018440340d20906205802c081405845d40d005c4a580d090100c82001010450301031505a6400400314140507da99408214681055086c3e25400040021445a072524011001014010904c650203180d905600c01c3e907401d40d11440e0425854234680d50101c2c50f00d151000d2030954a4202e042c025840c1c0300042000303d00441032190340e40c601e031038040320412501c500700d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 671320521 1250 671319271 671319301
    0x2010311070b0117010e01020c0d0e13050109090c082e06120804090b010c1109071704111f0203070b060109051e150703051606021306020609010f05060d0b 68
    0x10300e000080000444d03038021100f40f003200c03460802c00a0100040e48203c0c04d00380e0083d060340070515807180a542081c940284c00c3d100301410084c001400704821400807006451080c0e01115515648401103010f20000e810b410001d04200c0d0000d2084030818140420100c1002d501607000c80c883c151079540010a6400080040990b802601065101e86c1048061540f00340308641c0001c0c41d162000c0b402d03500403d81d4040ca1030b0840101c0c20801d42580a00c0400e00c4020035160410000400c2d004460ba50429028042d0b4066403a040c4c4070540c4d8800c2c06000c914a0144200c000111084078510650002c00c84003407039800780c14480e20381c03075500c0142d40c2d00d601604115880704400380200e43c422850070340001100030448900c20746001c6039100204510403c41c01a00084007082038442c000c03545e05041d002d061080c0f034010728059003030800d29200401d0380c00c0b500040e00040c0c02d1110340c8800340a10215500310748001c01c000d042c00b000060060070001d41c01054850100b00055550010200d8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 671321771 1250 671320521 671320523
    0x30d2007031505100614030703150602030d050c040f0b130806040b15100504090515040e030403170c0c090c131203020d0c030203160807050d0e09010b0310030201031107 74
    0x89508068891400c6050010000280c0c02c031540741030005601c40000750025411280c1c0c40e241c4e01000e0011110700d901c15030006002c0d07414541c50300c0600b180010305100e144024041e95000e141c8072030382060040c0c156600503042c0c001903142488140500124442170000311580044607903640c40300301e080111000402c0c1c0c0b10071000c1c01070404000500c203205c103d00e0301c629054150101500c0001040105030701503180c9000015500b0700c0141b107038807043d600c000c4d04801034004129070140c5020014046d1040b00300082c50a070000b0908100300501602c0020703003508212039460821005030015030388c0c3c1d004403400d80d1250300e400000c80c400c0e42000c400c8503d0b00c0000c00007040700907103d00c00c0c10f40c080610300c01100144030f00501c1141051160b0f0480c84200d43c180e000e9803038402d024010484000c2d41450941d884401008050700040e010400d0503801d042e603803070301040001560100702c2d081348160708c11170001070100200005e42030809620401c4c4ca40c242000a0024a4014000b0a9010706d4034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 671323021 1250 671321771 671321773
    0x702070b1b061312050406051204060b100518060c030a141312140c0915010504080f010501060e030d080610050f03070e1003020a1b081e040306060e06030d20 69
    0x83c4062510b09041c0200500c2c080c07800600141204c500031241c51083d8820580010b070309004011400e030710720100c240c015025aa004c0780c0c81c64030380c1c0000c0f039569034404150042140002c0345007501809481079801385404460340b902f800481009070b0f03140c0c031807044210208a911140703a050091810247e955100601c1005060a51250441c4000070040003017070320340c10001c020590000c4d0000508200500d0081c00c40621910703614041e0048410003040641440400c3c4404180c142003080300c3c8000c080c6030302c0007180d00d5141c001d01500c09111603694a001e0b03040b200ca035803650354000785900d8100b4401c7d203412501c2078241d10100d0b080e010360b504d0300d442c0940010034050200da002440d819010002c548241245018076001d500300d1107141d0541010880b90a844040a075414001c003422034060000c43d03140074480301800c2040c10f100b4401441c01c800200f403e2044c040c05200d044060500b10072046034500742440000d40d9036404c80740fa8010846d01043d0340385000007448400c510602c00d94 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 671324271 1250 671323021 671323033
    0x2d0412021207110f0d020f0d11040e01020904060e040209010303230c160b0903070306090204020d021303050706211505030f1b060a0507030c050109020a030b06180702070b1b 76
    0x850203a0000f904000c400d0f103d01c1c041141c0b400907107000c1d400a50b00c180c0c020922030b8140400003e100502c0141c500c00d40d0182085441060181c90754082c0c200500100f0000503522080401003104a9090360881101c0e604a58100001622744200041c150f136010300308840000009101c4c005414510700d12203c0c11100801c0860780380c14000b45503500109500d4140901580f580c0b4404000d0185c2c08100341d01d42d00001d0204041b0380030358060f244035400580013500c3c1c44a1240b800c4240d07130090b03d500c0c1781c4c0280c00b001081848401d0102130060842071034420080c40d1890203142d402d42021400030310341962080c10940700d242d0b0040840003024060300b51240c118405006a03101e02c04001130340c4051503850004802d902d44ac500f1038868890648540b07007801c516031000c031500394801c2800c4803550b580d11a5580580c0d01c014540c030045101c0d43c170301946803608405004010030707000c42c2003007182d011600344030324681c0105d0001c0c19104410700d0350791a000001c00000da416140594869180109 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 671325521 1250 671324271 671324273
    0x312130b0a08160e0a270603080a020f010203070801060f0c050a08090f0105160f03180803040303030b190302090603030d24050105070f1b0803030f2d0412021207 71
    0x101e49403e1041243c0051071051000d0408141c1d0514190b101c07281e403212102c0030912550140c02650214000c0000d00765030002d01e400890340890780160801d80c1d40b4540840d240c60040e85c10400180c801c03076448029801c42c2000d00018000d00018011803062040c466407030444244200e80104200d60010102c6510707426904040d0001d03400413200900500c03030030048001c0d65014004072400c0759030505240200d2007640d2900d1042040c0b5000407420459600a400801013210720014044d04c8580041d5a5480c0703180380280880768240c5016018800b1504004194180d400400341180e80560300c000c0f46544004c00242548216006010700501d041e0184100c0d20b09d01d580c1e149135070606001c8500e4191188010b4940340a20700c0c1c010440c5c250340007020b000030450039290300003050a00c0921a810b0310fa42c04036045800031200c101c0261801010080503110542d0048001d11005c2034960b425001c44004003024600244090039205040c20008000d902c2008040d00e100b10554a0070307211001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 671326771 1250 671325521 671325527
    0x60f0e010f0902040501051002061605040f06030509151303201b09012403090302010209090c0901090e07200a120915020c10030f060e01060c020306150312130b0a 71
    0x202c0981c000c0f40713820008501d071b0921844071100c22019030007d211994072001d41001916a10030840200503042c000015120f00c107180540140000d514042140d24106221a2824056020400d050b170502c800303101d010701c00300d004132034656018076201c0c0110304c0000c0c1c112002042074015070791621807000402c0000700720802541c941c0301c003140c4100b41c0e81d0340c034182c51000d51a08034607800304440702c00304650b43c940694041c4102c94400d0001508042d403900c00500c81210032143c1608501c4001003408040d07902003005005011581d100d469241020341000382a100c0d00b00809402041003009400b01300d00401054405681c00785090358814800ca800401c1510540701d040d031503030301c0000100d04036400401d0b00098140040c00e0743d422400d07155003c6000c0d20066100655203581d4000c017041081d141280030303010b0305294075404d007490003510505140840044c14402070030350b0b441d100400caa5010503040c503001c940c1d0b10100c1d111001e6444807c0280480c1d0f2180740d01007000541a054590 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 671328021 1250 671326771 671326781
    0x9030a0e031f202a0127150501090e16060e010c0f0813061409150a2303060a05011d040b060c06010306151226040503030c0a05010c0c0f060f0e010f 65
    0x411341d24194122107000b09080c26181d81e2424aa40e04403041e1085004404074090400d04600940440c1081040000d0b0b4608503082a0000c10365a03882d00000c0341d04c43c0b410414000100c420b040341d2325120340b620000500c1e60000703030102410000001408001e2002c3c040045078010307000030000340d03100148010904a0120340c0319050100c1d00c500322022900f98800c3c240d0f507280c0b8020b48285405109050b140c0916442800e001040c40042041880340311180c10f416805410041034250740d03401e200c0100001c591890748402e04001900e15040c41c00304400714800c0701144181da000c1a110000000102e0034040c880010016115806c0000288000380c0c211000844140d26407151aa0300c4080c00c00004070800c030701074082004081855200b2406180c1000c00c90020994681042c3d11200041d0865000d20f4000c02c103076000c03008400030700c1428403482d102c541d03c0c0c1c1058484444280d44607a0382d2921180050016a529001200700b100503401822801e402d95000304069440c280310100101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 671329271 1250 671328021 671328067
    0x20705031206010e0a120201080403141b070b0c070e220f20090f06030c1503250206070309030903020a030b040b2d090703020909030a0e031f20 63
    0x404000d0903861a00300759440b241a03646c41607440203444101e40055425900140044080000d40400c559046c0f501c0c201a2072541108458401448443d0500034034103a4140c200b8a41640c0070001002c0e90f48000a0002c100c50901e0000d204d940d496091074443c1d058424040b040d003840302c1e045482000300304200c108100344540140e803d400141d048000c18002d000e503205810003401400f00350b000c41c90303004047d4405c800401b110020f030600c2c008a480d00401d19905c0c110680c010051040b80e5a0b0000d2103400046120000340f12001142c20007942c030075001c2c10b400c0034583d5403009142814452a540c4002e950054091150a80d17285030100c01801e00715000e541485103500030910821527840c0307040302c5070355243e0f10240006071400d14a15a101c0a4850b810a00c51208000016100c2d01d04c03651080c008103000e541c9601d0507580190410074403460702c41c0700383c00210004400b410129210b2030844510040054680d000c03644200c000071100e0010008000040362811150b03245c5d1414110403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 671330521 1250 671329271 671329277
    0x170105070219020904330b120a0f06140c0403030e010201060e01300503094e011505030d03020301051f0504120c0e13050709020d02070503120601 64
    0x15500c80e03000726142d10b03212080000c40115007403840090700d40301c0d001d150400c4c0112882c502c4185c5000540e210030500c00d0105601d801028207900c40c5d030489201d031030314140c01641e06000c58461110303803603110f108000d07005207040c41c420380c28418440c40e588804a059000ca40303644280c2410058809183c106110480000d2415283d4410551040c0502030407039114503043c0480e42d0138409100e02100d203150101c8420402d6080b281100180884980e0006010f04041c0d9030700c0c04406d060114081c1e00e11404034416440d400d404a2303400d813528458902c451042e843ca886800b10401b2651300702d0043c1d01041156003450703071710040d0900381400c950464604030211030f40c001003440103800740c0c00b091044980c000342c651a101c4080d00700a5003e050340c01285813243c9029122105150401c0550000f602d00080c41b01040c06100344100206402100501600d1051720403981d856a540c80b003405550341d010303000f1807060000102c640540d84032992000669403a8807a03500c51916a0500b140e2072800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 671331771 1250 671330521 671330531
    0x90f0403051c0204300b010501050c01090f080301030308130b0118060509070206060406060f08060d020402040513140709080318040612031d0a05010c26070f060b0f060409051305071701 81
    0x43c5a4550305c050319255100300c1072030180e880c10300151510780006d94108540d540b204440c400088107a840703040d5041c03240342240d4aa5046040c01044044014120311564102108180104508112141c11968036020050784030b1849e000320000313014242d011903001201c00c801e010a064012030158410f020642301089500c5e9035203801c86035909101e002d1b0b400f0405100104200b401d11100014140e400500007503d000d940d0310102e80100380c06554029905d5035041882014214801d24581040131031070140ca0340303800c1410343c540764419402d007a55061001110144c09460303580001009080d100201c1599001600f400b401e0601d0030a010f080c14591003002090320b282484245c0180c2e5010f80d600142c00c141c2c0d980341c41126240c030034101c0e80103c9600c811910328407514020f06c04548141040021b8001c00e10300001941c482c80151485078080400e01005901c2d540c098500711403407000c0100307a54841200e003550b178041540024200c2e0069442c00b05042a40c0d1412204040c684802048 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 671333021 1250 671331771 671331839
    0x21201140604180b061513150905210f010e0c12060103030e01080403120f09050115050108131e05010b0909070e07030c0516030905010e090f0403051c0204 68
    0x2c200c5800302c2d00c811840d00745035440008074424940840d4071010142044070040120b140d40102c90b040504032164000341080244032052400b0b41d8101011080c0c00c09800030380c00e290000d0203c181c03280625821003800c00810b00d241004019030410088200000c00040210030169516030f0741c170100c941e00400944000d00466070000500c64103c07500f507500c00714024a15001140c51031000b03002a0200903588800700da8070303400c0384079120022103455800509900c0d00c2c5407040c2034402c080202c5880100640b030400c0141d03004444140c0c040e0400d482d54000104516100b00080e11029105081c04001d05100c002c001c4154001800000704841401303841e80c03444180343c1d450a65009076210040d0540110320307858040d0b0084200315006040c00b604000a512241c032401e5200e960039400502103040800080d40c0060308401e682c0020b481e21351062400203248005180094002800c105001410034100240a040103807050000b070020f564480da900c9000303280c00c620b40380d0650b400001d400039070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 671334271 1250 671333021 671333029
    0xf05030a17030921040608010602031602060f120a05010504140106020d0f11160e100303051204061112040c0b03061003090203120417010b0a0806010308160212011406 73
    0x20000e140d000c0185015125120a80003281c0c1001c1d1240306180b051a6a00d0a200102100c4140c000702209005466600d007103402040b18006034040c1003550402c006420107504a0700c000c040090701925410b0740d070604480d0400191103a00500d4210005d01c000b80000304926420245c1207507811101845001c50300011040070403400c0c45480d0140c1e1001982c0714900b405020a0042505103091032098144072a607000e080c151281d01c603a15007800e4150512000008010840e0480c40c190800b8603014103550f005811031050b1845c091200107044000740c10065960002605090101c48841d03c1e603007281101c001c180c41c1600c0407200008406004200c220b030481c00c0e00d216100042004041e0400c2505c00d030300401c0200f100b607805000f608840c03510f405c10710009100400c841200340800300505c07680182100d0580e4162442105800002c120440700081c05a0560b504410304690300c06a501c1240c251101032000290040822070703010ba008403040d44503921300c1c20201008070690342ca0b00200 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 671335521 1250 671334271 671334283
    0x80606030d0509060a031107020a14040f0612081b070b1c1e150506030c120c030103020a1a19030f0f060302032d0f0606011101021c050402061b06010f0503 68
    0x40d0b800003011700c504151140309410000b41005010711880c60913205c3e80225140792082e0f0000450300d41c045a00c840c2d581818844d0044581c64500200304d1142403191650303200400d00400b420010001c6080c0802d1481402d082825a469400b00d403034070340d070b103c034502c920341c120100c2029092204d07210111101601d002c0c0c104a004004528550203034010b510750028003401200000080f00b0f507a0208090311030a0055000350781c02c40c80e00c0d888600450b82e5008581000700840c2458400b84010030058464211840980f5a24060f107821146c0b100e00c81c500900a03607030a5070002d48614289044103805500c00c1c541c01c44442001c1c0520f44a00c45038109581c2e040c0310094043e800710041544034038031210389488a08040100089080949108600d020a80045065150402c605125280da0020911201016000300039400d09000c240121403d0314038031507200e92141c03528006021540d82904a68100d0203145042c03554501e02c4808070b66072a0240074400801c50a21400b184500e000140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 671336771 1250 671335521 671335537
    0x2102060f04060f15030c23090f040201140a03020403031b02030a030e1c080307080112030905010e010512040506060a080c13020d020910080712020c0606190f080606030d05 75
    0x3282290311a50307a89401086020414080d143e55132107804650012654580003d50044421850540c1050100170007580b6440c010040c0741c1504400540c036441e88030791540d00031000c0b010001c1641d01c80c00181e071a500200c42061151b5400038119001d0f540640c0075105990080c1c1c0c0d03100c9106a10700030104c80c1e0402e0000070798903600c20500c420000f03204540031000c1d000d01074082c0d0b00c24100404929444240d410086903034030130210810a03462742c40800140180008a51f400c261516a103000c0c2030ba0241d03008103810000c0c03800c1d00c3c1c02264090000c440600307a028047e4400c0d8070b42401c0442d200c14003900d040e40708090207000000c035050005a001c4480500601172803890211410300310095228071030750b0f00c03100e80030701440c01507548496088072040420340700e40c501340ca4107810003850582200d074400d0403144140102c1040303000006c0d0035a1300070340613101c0d51504070b0741da621101e0007461a400304000040b0030b10b006c5900c580100e003960294209500f2220004440780c000ea915020b4212 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 671338021 1250 671336771 671336791
    0x3051e0c2107090504050a0f0c0906090e010f02040b22030212060901110306101b051207060b0105030c04030f03020a050102030a0c0e061810030f1518060f0b2104210206 74
    0x85e80208e4000040151403500c103030b00d40301029a80d11503000a6580590285000b40d030b603201d10341c01152081c0500c41c2d5070550444214a0076050210015090166043c4060510f5600d500004504003400c0584003958008005800c1c05181010711940c40b0703002c030340b114200c0d4200121401000c003840180c0b03018540041c0300c200c665140c21000c07100c40c140010000c2c0f4044000b50fa41d00480d00901114480c00d030b0081c200c0c3d50324070345400c101c0c003074595a1b480641000701c01c000b003000030000481581c0550f680031707001a03480321103410300f2850200201c0c4050060752000083c00352244040d030280031010116101c0071400c0c10540c0030029140602c17019441362201d4190700072004e142010100424519508000400e241d02000c0d41c0c0031103020305080c0c2e0405074080002c3c04200c4000e1905c40c81219900c000b4004d4500346007141034021118400c1402c0392101052584441c20b8400b5007505800500d51109214a0141401d8065417440c02803580c1d03e8504031843ca084a06c040390003071040d42c07a05 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 671339271 1250 671338021 671338033
    0xf1a010c030e01110c0a0b07051504050c01032316030f18030f020a200a09090312020a210b1507050a031206090c03150f03051e0c210709050405 63
    0x100560f00894500f1010726140160300003c1140c0d65202d4941000d40707014011f0356201c04051401510302510f810b054804821000708020014400150b0514144001e05c0e0200d1011544210150300c070000c60010041c8080d8101000200384541c2100415450390b039400b4004164000850012101070816010144910030407120102c0c0c021a0b883c0050080c03841211035040720360b103440d80401d10f021110788001c103441d02c0090180c5413507422040682100c81040055000e5580c020b0501c0c00c0081c2c1c8441c207103401140402009008071140040c80b0510080d09041010000300200207261001600344284410450410a035900c101661145a4040e00804c6502050f031000e4030a81c2c600310000d400c8a4071208046040d01060040e600425060384020030211010303907040c1d0160188c5c2e040001010035269040011800005074403105455041c048010012410043da04144003008075941000c640f044210045900c1140c540303072582540c0a41c0c54007600d850380103040e194240c03030203010f56000c030b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 671340521 1250 671339271 671339297
    0x402040504081606060608010b0909150a050310090b1510050c010b13050405070608070504090207081e0301030c0e070f0503060d051e1204050a15020304030203010f1a010c03 76
    0x5911041d005800b89140c642070a4210324800401ea1203201e0071113510380c450000f088269001030341617014002c0e01c0030484c1030150a40100c2d01c50440244803000c12291519800c080d0f03280c00000c18042d181c054140d405041c090081071020300395212017110b000310300c40001000b0610002d4150300449005240c144055502c0e50b04840a40041c800000595130352202c06220340c2d15608006000351a54201040b2841c0c941419801e04001d9030001c014007203101d0420090561020884041e00e02c0c00d41d00580303418950404150070300480c0481c05131500ca841200c05654151f0707018604891040c040112000c4d120051445042001d031a03035400304182e4290b00001e54003400246034041405003200190346040e86400703103081d200090301e012050701c100e180102003000b0700210300d04020b5000a50314040c540008078004040600c5182440300221100a502600c00e204981c015070700100207219910701a03034028000d0100000940c421018601e5628195004405511200d900358039881e021901d1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 671341771 1250 671340521 671340529
    0x11e110906031009020403060506030f010905030d090f020909030c1b01090e0711060f1603020408120c150c0d06050117071209051507030e120921030714240402 70
    0xb01400e20300081c0d0904201198581c21440940300960151b0404521802d00360141400c0c2007007056030700d009904082940000c07680003c03c442c030085580c0c1d4002014120740c104803407002c442c0100254001140e000344441200c1c00000341890307021560958841c0003210401c460419114400c83e800304900f401c00b00031a0314080e18080d4494118200740d0100c54410106500b0100101c56000380f890302d0b6428082c081049000c100014400f60904510782030610884d00c0c0c0d40c403c000301c504590f0f0f40002d030082c40e107170b0280013080d10307050000e040308914204405038004503046401880071081c80e10b080000c2641c0300380000e81c040c5407050190300045c0c0f03d06000320341001000f18903c0c2410380342c0c412140090400c100d040e9036800043d1465034281003010b40141aa503200e9080c4006a0001c4600c01468800c01d0440b40b800d03904881d4000010081100940e04c2031040542030758502010412201b4032000d501960900601d0750159080e015070b50040340202070a0340d081c100d01926002c005801414 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 671343021 1250 671341771 671341777
    0x9010e013609030306140a0308041401210506130203010e07030e01110a080402090901090206180d061107020901060914060c1203040f120903081c1b02011e110906 71
    0x54a02240303900c09062030038a0060b01e4007000d003100005e0341c610040207030780300609506810910440c0ca003585240344d622140418012405000300b00f801c0ca28a1145681c001c1d00c0142940d0140d12080d885007029050f000010175040700d28900903140401469503140721031085a05860030850f0b41e1210b41c541c035070b00314002c0c0301224440d8025075907008901c142c943c850340030b1302c0c03c80c1c01a41c0b1b1001d81d1030948140000c030a005803241056a0504050900682c3c8200c107841c03660700c800110a0110000b47c0002c1c0c4170135861400501110b14007002034000d44007171402460306900995584000740d90341e0201b21404400d0348100e211412100e00d4141c454641800240510200e8008541c04029103210340c00d029802a503080b200c0b854644444802c000c001d100e8a14412428104a1400351568036401d070140314048610346203885580c0c0160b08082e69070300110035202444215010072204240103802040107080c0440a010b240d003880c2c4100d04140541f07449400030120980c14000c01106001081e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 671344271 1250 671343021 671343089
    0x1002070f110d021207180e06011e2114060601080114040615020106050109080115180f0f0b010e04110406050703050d09030c020906030a02220b061809010e01 69
    0x142d01c501c4140c050303555010315010742c201400103046554039143c001403030481008128421541400d5003290000d0000c41c0c014111b9001c18070f14820f40b4a007000c00c00c420703543c90300188002c240102500c02c016000d01031007090301e44100301203044500e504440c656140d20413986540000c1c80301005220b0b0b800605081e03481100090000300307605455484442010030081c1003900140c1d910081040b06692058400000744103540007008460401c0d00424151601c6d80075203112140b07190908403201c10142d00088101d9038240b02040070303100c0b4554007030280c000007084500080c60340403034200d10310b020702c1340524a43c02c85203124a854944001560340fa0899601034083c0042441042a144c2803070046100c010303c00d54a41145a803d481080b801100203805103010354072400e480f00042c1c44903150480000355600c0c03c600c1b920500d030201c8000d0035245a03e40e400600101d40641b014912106040d0910380803038041a10742e032202c103a034482d803100b4803403200c40b42003031229003d0690341549045440703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 671345521 1250 671344271 671344279
    0x60e011d090c010e0303070c082415091b0a0309110406050d3c0302150609190f18060b010305060915010c1a0a14060d060e0c09010e091002070f11 64
    0x1110942c0c9664494140c254809c42060300840c51128010419280b00010443c05401c0d43c4480e007404482e5180109183e0481806000842d001c05c0c0300c0d002a08580e6011104000d0650303440107111001400390103114401c840c017134415018040985803501590041e1400034220069221454071000e10b515001080c115950402100d908480c000c0315400755141d400c130b0a100d030403074109403600904e4587c84600c01010300c030b0b10805008540d03586901c00c942040d54078003210020080031901c0c45c01001d42020451225140203e01000d41420070081d11072140110070400c00d582c0d401c4015400c0e2075044030341070f0b031255008001070310140200c04c454180c20010303d4120a1070f89241d0340c16071010303c900c050043c060780007004c01014000c1409100089002c034090455070b41441c0011a40c1d000c42031130001d0860b07840d011911034010042001c0c0ca80c0140040000d0354a507913030b40c1c021030320140a448130041402020b481c90b11410080c000c036100503611000042c0350650545401c0d144907141d518851748 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 671346771 1250 671345521 671345527
    0x10305130c060c0b0a0b0904020d170417071d07050708040e15040510060503070c0812010303030603031101020f040522090506060f0d150e10060e011d090c010e0303 72
    0x45188078600101904554583c3c454154041c182121070510081880e482030741813403500355550719000c0c0c00c1c1c0c2c1c01c036505071010644141c16241c4420703ca0242c3c00c2c0c00c04801400b080015000640000781d0b4900c0c1420410703189455101d131181c07500c0200c10b6402d002c00010305808281c9561156000701100c600411030581403a0300c07140717404c000d9081039600c22110007052152032801c1c80c041c440c0d50303003185450042c444035a1409501402902000700000306100c041d8180030148102d510031180c00682d00c451621300c1e0741e12840c0c054014101400241c0004814814120a11700144219000004646038160400340380070300b0411810780c16220070006070f000352440840c01d02c081c0500000d40b88640301a008529007001070003a0303c80d044280c41e00c603880c0c12a00c040440c0840c00071400864079000c2c0415002c042d14500c074074081100d591840c20514140000900005031901c982c1a903001c00e003035076100048140340f415066020b548070711103504000540c044542c044c2c402c07d03c02c01c2c0043c0036682 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 671348021 1250 671346771 671346773
    0xc05120f06010b1209030309060f130b1006030e0f060408160602210c120c0904090210120507030203042f1504080f06131b0902270102030a020c01030513 67
    0x400c003802a442540681d80c00b04650443d084c5540342e0991119100c0d00031800c41c0b8011503010740c0c03004094030125000b40c008021403c440d03500a03440d007215400040a07841403d05000140305803a00d03100b54800070340303000f46070350031030f0742c046829403480006400809036600c0e5601c1700b13200366110104180032030030343c1d4251900160b0300b400546440c006c2d06099070300302c06448618134500d0100500d8040320360f404005031003d403c0001e6400e500000b14029645d2030782c04600100e0020401190301079800b50000c00012407456009039101c0d2041c900340814491a20307441c0064080e804142c8000300444d180d112802040e0032911001c004c0c1c100420420410203e00380007040d88840c1d08400800030000018050000c414100044000d00d512900100400c2c5401c2240c003030808400c035002031108407900b0410b5059010289240c0c0500394200b4211740e500e20541000d00b481241802c0030071040c000140e400d22560010003030b1902500903802800a9001420044004041c01401c085540041c0d104402c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 671349271 1250 671348021 671348023
    0xb0319050c1905030c07110a0503250f06140a030609020a1d0306010518070c051c020f0c03101e020a0c02180108030d0207020117091b0603040c05120f 66
    0x140c001d0081d05022695a645000b100300302c80460b15820003408030030000d200c84c04640004460507160030031f403211040790315a0300080c46407003e64007144d0701d440b82400789118456183d101c5403240c0101a000c0305403940d14030803180e0500c11441140c01140c54a60050414a0364400030040700581d840c001420075100c1120030220f03040004e10800084000d0b860018515030031143c800b91782e40803001000b0b95072404000076000344101204186024404001c01c034100c0c003a141c04149158050706880b400301c16641c26040074103c445002006200c2d200020342d02c05c10118080019480c0540680007480300000702c41c01500d40503584902e40800da11280c18201500d00c0a015400d2680d40d41d104282d0a900400402d1180c0010f03c3d69080505001000782100020440382c00641c0800d000d62902080d00058884c00341ca01801c40b40c00080700c08003c000b0401050280b220819a16400700e00c221a80c140861070000b103900a0007464207a1080c0118604030509415040b450011507140503200203003a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 671350521 1250 671349271 671349281
    0x6030319030b031507031113030231151517060f131b0906090e07050720040c02030f0702041a061b010b01261807260a020a0b0319 57
    0xe4100d85100c1c2c0500001c1e56041c0a5403240f1f1514140281c180300c0801030203002c00c0709512000740304010003400081c90030010102840820004180c2d003149940d031610580151001c50142c10f00c8498440c0041013026006201480c210320035902c01c800c0c04642c4070052100b18001e420b00d40d12602c902070a81d03107a80e648260105050100c0e0004c05c00b15a207094552200c000c0760804010302820a10502c00f9a0f4814210000c803804504d0508050b2030f03686050b0380300c1c4100c10002c0c2c9194501c1c0511814407000f550103100841c3c056804214040060724101d0300c90041f880c80441d803100401c88240540703800c0d040a00c1500c8194a070309601d5003c100000d000b070740b04801d060f09900d41d0680c1504d00010a104541d1102403e0909400d040e0200032030032aa180c0064402c294441c017100850140c0d40080710003800001240c040312401519070000640c0002c4a0548142884101548400308040820200c0302c1d1755020303105104c1c0a0034a0744440c40ba0f000107000c0200000d255501803058070041c016 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 671351771 1250 671350521 671350543
    0x20c042007110a0f0303020a0f060605120f0f030f040513061502060a06080304050a170a1b08071406030c0304060b0910060e09040803070e0f03010218011706030319030b03 75
    0x2c040304030300b1401070150b5100d25034030442c3d010084e2181000403035000b06404854581c808401d52402a05107003060040200790081d0360001c5004940d0400d00c07000140c4100075441c030108881010109510a6940b480740003080e00130400140800c12440c1401c1d41d00318601040300e00041111a225440441e480c00705501d03c40059200d681401035510702481200e0240801c80c001d0f514240c20500032a070083c0c01845044a101724078802850503802c00d00c18042001d0384104c2820350410350a001401404031405182c0075402031440000d9090f0414880c1340c90150090122411035940310018034154000074419100349481d40e08482403a5110711406204d0450303802c020301c055041c144010180c0fa4021049030098080106000118903000241c992001b8203141ca40e59481c580d40108461207601020035800d0360021030294142c04006528007100780b82aa6142041540702200040100c2c0a541c0d07249c164100700710041032036003000c0820682110f41e080100e031305000c8901182c6071801050f0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 671353021 1250 671351771 671351783
    0x60708040b0a0b01020a0f1407170106141f141207080c0307080f07020a020a03110306090d05030f0601200601050f0f031903030617030301030302010c0807020c042007 73
    0x8104800c1110001d20640c104081110801001c20f000e80003035680c0c2406070020f4011300c1e0084080b4208040000c00403208035958080e60011951420841204001305441480e0b550a104012500404d64151650040d2001b0400f034920481c041000241802c08081742081202ca6910440b900703c1c2800208800c103000d840f81d903414503241500800c6800050715940345144200103000b80103070701101480e0441e41507043e0321069101d180b8240d10f02145150029080400540000140020314941080d408010390540d50196650b01b0380c0e5842c0c45099490700301040061000c06c01ea0354144072500e5011406041c242c440b03051010708040303811403031049060b09501070001070169003000011005102e001b9a031164501a04100003034032408041080c0d040706000a60900c141072103500440010075041502c05455040118415140d900900050f40558204640050418404c10b1964890a21903010348580105002000b0181548482e590a141c140030b40c3c0558802c0420020501248180 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 671354271 1250 671353021 671353037
    0x1e1207050a0905010318110f040e011401050627032d070506031005040e1903020703050c0102070e0105040507020c03060118051b07030503040501060e070c050f0c01200106080607 78
    0x1c80003408a1000d4100074101400d0051a1150110308a005903d00b544078120540d25950040882e03104902c4000755039100e42000303403201142c0410b41c40600c070340074150b00c10070107682c07200b040c81594031030311440c04000c01c205000c2c485000f0a01c03103009000c12b401000e031000303a502d2000c405080f0103104040421400c10f0000c5541180d410441c2da001840150b56103415450500c103100403220b04c034460b0b940101d4480d041502c000900340b1460030342894620041d5400c250300d044c000d5868030907000480385407043c0100c0c4103036903000242000032918460720f4440e407a0300345014440500000341c03034501544580441101c0c1070398184030303080c06003407410141c0408108041449040d9080a04140e401800e076504042c12400d0000480304e000d505410900d90301e4540f45080390040540341d10402075001004148040390b90702600e22481540601d048808208505401075115108001c880d0b02103509a40c45102c8811a10581c00d801d101c10400050391030758402050303040040464119000940314 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 671355521 1250 671354271 671354287
    0x3040819020705060906072603060901080105040803070e0f03010501090c1206080303060d02060c0a080d050a050f010e19020409020904140c0409055103031e120705 72
    0xc0c112880311460544010600380d490000072990074440d40741e40074058640040c03800c051054100c19501400082d48460140320200c00802203c1e0304203803503581c03044000c400006915101400380e903000381d0700f11000300d141d91100340003944c000050b1001030790001103102d5030f000155028499540246440400850b11010b1020014680741d9515900070718249084e800384100f0700b00006131b03540700d0701c140c603d400e03040300600016190b4040c02401e1469072180110341410000100044d1000e88880d540034009525201c2074201518002c4038100200310700c0c48010802d80c00000306c0f907a000079412480300d03540030450f1a840187d03407081d0890140300e500006c1a20650603c1d10680c1015820350a1400490804041640043c8218400d5005407038580021643c11408280d82c032400c840c400102150b1180700e000140311448012869040d510300304d042c5014001803c020304942000010055850a41440544c60300c00c0a840038403145440144050302c941c10202680f20f0145e25252103060700d400790 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 671356771 1250 671355521 671355547
    0x1518130c0b07030203041802070c06020c0307060c02182d090d051306030b060904090b1021020112140702100c14070807030e03060106050c01060b0901141e030408 71
    0xa6a888001c00d110200070420109902006070740c1070390071180410031451b1000000e0303c040d006030707200a040822003443c0020100d40004444440c000180c0c241c4017125515036041c0d071284007600000e03400c80844402c101c07540e8422030005070b11546040f100c4025001e85640b03000c030816006807903003e04101c3c1043c00744a5a0400010054110a140c010b241168540700c00c41d444006120300c809040c0c440410300105d99030b100c2a82c00b80a0b01400c200031400e03407400c14001c640341c15070b2030003140906610003244809180201070045502074843c0c0c0f0b8201c18550044641d03541200382c1c0c2402960314001c1c03881038914003075500e0050307500b0790080c000b2004222002d41101c005414070018003c02d08003441488029a054031165a0001d01c4030f5290040e0f4242507802c3d92207903035915414052000041b801c00c0c0c00c00040c0c4031010a0034000c200007a160010408680305032460180459048002c0351040c0080c41c009001004a500581101c5030030345403644004e03001a40c0413035051402064010840c0d203 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 671358021 1250 671356771 671356793
    0x90315090c15050403120909050a0204090e1218061c09050f28020103020c0105101403060c040e04080c010e0109120f080f07170a02040608071403151813 67
    0x200e22041079402c0c1c0c0100405040c502c0740d8400100300c0c030301201000604601035070104004002501061006250000314a402584140074001125140100090080000181c0740301400e240d41642e51600c41e1000584503800000d50505511140800101d01401480d01080807582c512180c04214030035a1300c2c1c0641800c0f605c43d014003841e4800241d24007481c51490420038003c2102d860f1071340c0d440a500041f4080d03c5040c0001c0c09640c240403e00c4549040c0219035021502c0484189580034600c0c01090f40b902400e807085004078078144010320001d40c101c2d2000b50071a1133201c1d402e1600d0201e8240d1804c5d107000d83d5276a407844c0d6550710710130180002108492004c0390340740f0704504074440b0b60002138004040a801c2442c1400d0700000112410b000b0011400800e452007140c1049242403550180694403034015240040c0030300c4003150700c9070b0140c98100024280a4138a5045d541e4408402180050f224070f1070b648945003102c2c481c144441c2c50340403800388159120200c8440351508240305060 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 671359271 1250 671358021 671358029
    0x3090b120c161e1101080c0a140903030307020c01020609031806030c070507030503180d02240904140115050f1603301508030702040e1501060203070b0a060b0703030903090315090c 79
    0x405070080000401007c0f0480303404401e81d0510300542c586034107181e02d4074000d04c151141c2500c00082481000350700040c540140680036401c98000b40d50f401a002d440e030140340704c1500d0300804440d16095a00e03002c40550344c0400480c060034205115600e034a403800032142d01c01e4600780c00c00174002c0106142001d2607a01c440060302d108820103070f9a40491400881910800701d8982e62100010071910791000312003c43e400140240213403070460802c403065240a102e001d40000e40e001c1d51603000340c000c40036280c0300401e080a8500700311078202da80071062076980d400c90402410588003020306040003d0040c001000e010082050920f41c80c40908a0f20080e05400740174030505030800100000100b102c80c4250b05030380c0418162800304c1064a4403000c0c4040c410b401c20218004540542d0000150140c1030040410007410303103c1c1c0141d10200c136401d010b0440214402c22084000ca0f0090300268103040c03191401c1300710242ea94468150072901e000503103a5840d01c3d41000d00134030101842e004050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 671360521 1250 671359271 671359277
    0x1b0f0301090c060f02010603030c0303050a242301360f060e030105040b0627011202090714090d08130305010204180605092208070f03090b120c161e1101 67
    0x15808c58030050f0440c40c10300c500804141d02d0b4400100d030039400d81c100c94440d0701ca61403c6507800d40d070302200d42e8100d440c501608091550706e131210f03041c9a5007480c02c0c90021700c068440d101d600d41d0340700c486005134140c1184c13001d1010398903058402502032100544010170380c19a580761042d042c070a004000025646103680300e6070415041c08041b0703140d01906500306904403001500321750380c15040303440120340305564154074803c000001a4882810601d00c111761084844410b1552440740c143e0f010b05022034600450750080c000d1651b581407030011409d6841c0142410307400e00f5100301c81010061000d0300203c03100d03500070034108036040b800c0340d002c2042c0c11100000e015060038074001c40c03001d12006016100f03030903e490390355825402c44d81501281c250040c1d105d60f542c10f143d0a00b11a42400e0a0040f000284200030000d42604218299030101c1456203002d401621070319000300c80c5410040100c559a0302410239003001614070000b10f0320480c2c1c50954800400c2ca1810418840c42c0041c0c001818 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 671361771 1250 671360521 671360531
    0x40f140a0f0b28180b161407030f0e06040302030115060815031b120d030b150301050f0907020f0a0506010306060b0405060a03020a0311070f06050601020d021b0f0301090c060f0201 79
    0x89034640000d00702143c0140f07100010280d5a92401665003201c440014140c58050b1013440b0080c2d107449100c224000651321012000d00e0304691008084c03040b07001c0500003590070901d04481d180301e080904104074009200505142e203a40011342180e4401d0b1108130624058442048140e8001d8000c95011075213080008083c0764013400300752603007000e00c5c0ea110040707900203032030036290b81c1c1062864141142c40222098101c2c8070070040d0090030780d00700980c459190190744003c80084242180e05036003002d814011603034a02c0080c0186018094a040c003076000d05902c400030305000b0040011028069402003800d545141070990840301d89401100006100b000107011035120744040ba007810955260042e603954130424110000c1c071100b1000340024070001009418000240180c9403100d00a003400c00164a82000581e640c40c0001d21880c0582c03c100c0c10b441121030b400d64440c081e0000540354191b211b21982c002421180516800ca400318489401804040e5014030301e94044541c41c0000c03c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 671363021 1250 671361771 671361811
    0x10608100306060b03061e01320406050c010b030102130e0a0b04020f0a0909111606060b0d0f0c08010f210209130c06090302090f072c100504030b040f140a0f0b 70
    0x40360701da2060f8120604184802c0007800305100840740707003503038100c41c03030327040d01c590301e07000b0040c003a0340a014414150f6081071440c8045140610031141c24280f0aa0740c0e00d4210318007401a21141c600402a0503030a40e18400340a0646a03400100008d4010038943c43d030303958481101600d81101070f004250304074075116a803216089100115415115641c540000314101c1d49042006400315030002241369102080d1245841125001952214050001401403482d86401240d2100c000d00c54440d0040f148032040201041c03c0c21014241401010460400c0000c1d0f00480c0c1e400701c0a95400f0780403507281000005018001400d000640183e1400044c2d00e40345400107020010041c0c408094018100c0100b10b59a01a0b0721503605456140c032450041c050043c84c403107100c4244240c1500414585801041003482102201c0c1038981c008042096a00d903030b01d48180802440004444800e5201440c008245041058081d054440c0e58800304000380e0781b502100424002c0d00c0b80300d2301914110020 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 671364271 1250 671363021 671363027
    0x307110a0c030f0c1a09040f0e06011e0b070c08070602031c020d061805040b0a20030601050909010803030402040609110d0b0f04090303020c071d010608100306060b03061e01 76
    0x7040303d4000d2003101c2c6400306420a442c03503046907803003040760402d0300e00c10100c52060b0074043c0800800403641003210850704110081035400b1031802c400c0d250804e8005000c513150079030082d84848940102144110340f11704000015600c800d20940700c203811403c04000e6a8820404040035010a101550401811703040214825444080f0f0310405034011502c002041c4540c2c1c810401480d400c040c50011003040004a002820141d80945078100083c000401100044c01a001fa61200140c0403080c44550302c401d0a0640015090a041100801559100f030303540000c52806404e0b090059035803402c1c280704101c1100e03065030240c42341c94140b402082c0001007045c2600e481d12640100810705041160010b1803c28084007080e80c8207141620500a065140c0e0103000710000301030841c1c40ca661210381840c0c8030446258000a280849401840f00d0380c810011590490101c902d003108140c0c8954820044d034081c1e8000d6510001e02204001c030398980400c000600e190041c240c10f80203d8918002 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 671365521 1250 671364271 671364293
    0x302040c2309060915070c050f0607080c031201030c3605070903021314010506031612022503022a12030f0d0b0102060108061611210307110a 62
    0x3200000002080d05000c2d5111103080390206240240352a040100b6030308120090b400601007a104e4a075248004101ea0402c2c903031710344c0300c458018481070905204c2c1d40c80c8115a8810805000c1030300081c4078030700d4070040394044075001c0c6120b100c076159601c0c14090f5044000d403000e044800c00d10030041c8010079603485a4000c2c5020504400d010a095803440019200000194002500000c650140f004070480c50b612481500500352214001c5903030700c50404c0080d0000743e9080740c02c6200c0800c24071840f8041c01000d0302c0c0044900b40075090a0015408213110070240c070480048011590011042550502a02c440307600c0c850300070110101d0326892021400c0c43c800c0e40328002e0545000d840e056240400965089601c40400c241d6a90600018280680515a8018094491a00080398001001c01c034030f07100b40c90a900a014001c0400000c5035001c48030340c0046014080c11100c1303e6048103044410300c407d054014070039641e0800020040541d4150400c50407142c01c0f10703080c0b1000885507044c0b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 671366771 1250 671365521 671365577
    0x203030709141827010603082a0a03120e1b0112060e01080a02031507120b0604091a01111203010308090f180406051003030f140c0d090302040c 63
    0x72031810500c007000c0781d410780f20001c410030041d0503041003050507852891a8801100744803d05860400d15441d11420b0321118000100107000a02941740c080c2490b189400305c507a4084a1074449035010f0040340d0528224403030540000340f0500144403640014040d1f04940941e500007004551210480d82c080e016501010a0400115035000c540c2e06a06d41c021101a080300c146444180d40e440000642ea0b500041d81240207005038007a161001004003846440303100c580c0c49010f00d429050f10044010b168510106a0119003480045100b0f407003481800c40946500c0c0715019101c0f0014009440c031112020071048661024034190014000002641c1c1180c0d440303540c0c3e5444603451000034444000340141740c0d401079014400084212448111540200e00801040005031074501d040c0c440d0709110700002d07000c108260058804039220740b003100300b59210b108080341810403040c091400c2050b00c442d0240043c050800c10310940c41d140c80342d40106003c0781070200c2400c0420000c081340c40d08002c030b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 671368021 1250 671366771 671366789
    0x10b090f16140f0c010c02060403090e041a070305071805101803021816090302061213150b0f0d0c0b03130b0709140a0b0d0f02090406081c0203030709 66
    0x3107441500850702c00b071a24008410703040e02e403012000b00300c1440c0c001c1611391640d58203140e10810942d0011030704a0007580c155481070100c40c01c0001c0244028405401110306c1154200c00045442c88610498011446a50086050304241c0001059503448aa6030f48078007441010030841581c40b55001910305151f0b00701001100c40c1d041d2940809041741d840a500a0740070315154224054001c0414440c40c441d05400e60701c1d50401e241140d260701da0b408000d4200e1020000d4502d01c1c1651a51035030300809d0f1100413034483d1403d03528000400400d1199034099a25074803525400e180c03009010803151016102450b544502c0c0d1940c0c0c141c1e0043d403150700307040e010000108a072400103040c0c0001e92a01720103410814100250300800b4008144030380c8180d19000540044c480c035110300781d0350803a0500f024040c00c000e104c00da002c009021140350003840644c00c1020300c01b15100ca004020080540401030180780d10101e07044840c08a80714100421500100300300403041381c012807250182c80110b1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 671369271 1250 671368021 671368051
    0x240806070f030603020d03020a0507081603061a1504050a14060d0b1504060e01120b090604050a06030501090602090114160f02010909050a0902011107081e15070804020102010b090f 79
    0x907006800601c03050f00042c2d0080f4202d20704000341500010b018031a50320510480e0355107550f8809468031001c2c10010645070300c64200d03082000c12243d130048101140001d009881c01000e070300001e80e01e1003884040c0c0c4d240c8140860100309500d4000c400d240204030090a6007031907403030040020391070720030100108202c540c1c6039501c3c81252150800b03400b00c44030650095a070f4540302c0b203000c0c0000c200070a1090008a100105040094007401903407440d0102900394409619004100009010b00804400500e85e46004c0003010a03400d000b03080406000b4000180e83d45001000103043c50320090a004d030340310041000701d02c06180039220845081d04200392404240c02c0d0300c012501c000050344a50043ca0607c410b01092141c0c6510017a102c44c0300762a800300e881c0d00e50b214251101194420302081c1d07001702c0c00c00d4a588040c1d5090005019a8100f620760610315400740001245003036400e4400500220104411940c092249007215541101d141c1030620b02422240c1054100412000019401c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 671370521 1250 671369271 671369297
    0x60409020c211207111b12030f0306100309021c1104050403030b03070e0108030906031305061f091a222d020a08070c141024080607 58
    0x3881880729000303190840030300402c481c1050054a81020070154550b078021804510b6103809900801082c049000203800c818502003803000211002c0c5c805240c100500b80e0071500c80d940e09000810106091000141d100d003010301c140720b845144e600d0140300785032605d114034000d070b5507800080c10910107541c1c0342c005410072440d1500f03100d00c0b00188550094208000c1c0f008041d01070308a0051f880094048582c0c4603a603011824041400303114164243d0000c0000c0d507241d06041c001103038401d1f50004400c5114450703036182ca261200c00c0b1245500c0c00860000b0140340713041c40413410f004003401401489101140341d842842d007031016540354491451400000b84a452101c100207003100151720800030030300b1696550500040032400804640881d0405101d01e281a1083c1d601c466070030b52b201c2e1204d9131400401d440540a40c0010b07280280305043e00d8180c80010801c0080c001000040403660551755880320400000030b204803406a2640c400500c0403420004000340c0c00045868410001019 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 671371771 1250 671370521 671370523
    0x30703021b2b08030f091902060306040b0102190c081011090405070c0204050a0c0e061e0705100606030603020f0102030702100e0a0308040306091e030507030f0e030a062702060409020c 81
    0x80c0302d10003400c1e4480441000495071821555501c2810500160781400c51410341400215941100082d4422420300102d0800c4c01d1a038026440148180111504101d1007104e00c04e076040e00300c408550854102c1c1050101840034421920161540703841030000d034500c031150b11294041c80700080d005560700d800190303410303100d0101c03600116005002000242040038002c0c0150018207072145c045030f10550030b030046003482c004803400c100c04658880458400084115415401882d080c1c5203803180710880d07034440c2c126108902c010a0b1076240099010301d188180900144003aa082c1d041d508107010510243c2c44009100e400b01d1081c3c81c00c08601e0703860200007013132840241c0003d003ca45007c5804410890b09a1181c4105401070041685015203a00b011026240441000300081c3c0d00340003080000b1301800d4008050074241c14001c22544060022a1030039101503070580b1601c1d01c0b07041030500304400c80d0402102c88440ca0f0740071817142458000c0f1b0304900c01c601c5411801d40d400a011015004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 671373021 1250 671371771 671371849
    0x70b070303021602040213080c1504030209090a0b070c1a09190c080d030209040b042304050312070806040e0f190203030903070b030f0c07030f0f0e060309030703021b 73
    0x4d4010411511042c039000346030390014050245d5443c03481002c070780280e40d1034458a4003503c110030703864962900e8103603420710011001c0506101c4441c418140d2580002c0c1c1d2a2812500c140d41c640c1d1081440070150030191828000c040b0410702d210324030010b0060140300450100c04828441518013807021151800e9042e110040d40070403105d001d541e603156130540e45a00100241203007158140007501c000c03c00c120440d0301460440031107040102032580748840c100400c0b5485401001520f050880201d191861f19004a46901c000303030040c0f041110340d00d014812001c0c0010590014139039000d40720b00c1702d42c1d580101101d01c4022149001c069045540400403207403130320f4000c1c050351451540e5a661800c40d80040d40d1707843d01e9505600000b030045204001362110250503680c0c00316000113409059800e04031141c0a0000c211740020000c2040e159a0001d6004526641c000c40d80c82c038541c100281400c400000c400b28100c1b9004c80c85055540e400904003003030303200009014601d28a55032981d03400c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 671374271 1250 671373021 671373023
    0x100306050703060f1d06090703201b0109030819090c061e0e0a0315020705010606081f05030c01141231031e020f030304150e070b0703030216 62
    0x2030400c4200210564160002001c903180040e0410306151200032140e00031103950302038040020303444001003c0d840c02c581c209070494500e0500043c003442c1c400c805d02c02000e088511001402e00041d910304c00c685200703544403621216500030003101000395401400144080c04041d107030041d4102c100148407155100e020307440e50020441200c5a541c4601800341110100b400f00c40c00c1240000b180c416000b5000415281802804010058110b549024003461202c1540751001d5083c031141d030014009200f42c1e0054103541c5c8980d01140741400d400072000400466802256070b100a00b0411601c00203101c94907038509090201054102240701c4007280506180e14482044400520101d504c01013140411240c1c02c8030103041000e038901304030b0700b500d5100030004c00040c00a01c40100d119540001107005101e14415a4011803001155074511b4006450030303030350700d8054112640c0465081c0700726002c200e500320180071070500c0d240141205002d0180058189500020144660148400d03014255 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 671375521 1250 671374271 671374283
    0x2010212180606060403110108071b1113020a080a020a0513030b01030302120a020303180709062312030a030b1507052109060f0c0703080c0d171501081003 68
    0x245801507190890445000c8a4030041c0600c00218115080203070440c0e00b03883c2c00180e03c0c0c0243e603a00d001101c403250002e022408100c101c080310a202d041582c8000d501c40e0007a183c0e1102e01c00d00d10108018051032081400205104005803003103e5000000168408024078005031030307250760f10054840d40300342c5141d81c06003070340042d021042080701010141039070b0103035080f10140c10040844070b04030b12a06811001692090001a407890b82d2000800c00101e110340541c1d40e281e035650070707000580b08550010320450340000e840328250361041c5c2030840f00500459403015241d031400b42e51500d92017820203400c10541c4510a280403a00c501412620610b45540355903501d0102d82006074a8080c01e00e9070041e15400000304140f1054a0010703502000d0004000b2440c110045413680b605601a0380c60b0484c600078210300201007094200980100742c0c0031000741040d1454098000c042420300c040e070031004140e6605221003562050a180c0a001013030a040d41e094607000464103811a407544002c1c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 671376771 1250 671375521 671375557
    0x25120906020f040b04150503101403011104090606031404030c0b040c0302030d050702090601020f191b080708071d010909061410080c01020f1005100b1206010f0c0c031101020102 78
    0xc200c4c0b540010412910081400d242c501e135404000c5030f0500c419242000d40c0c5410100501651031001a08014044020f00004032282e4801109041d038016900c8400956640c1904221540d0540107044041c8000703400a40189055503019003803440944014020404682c005010802c06419150185400404980101a600c2e500602d2507001e0181203000f81a510082141075000141c81200b0803110708c003070301c05120354260a0503505000e07201134940ca0202c00c1c1c101340c100300c0c8040007800f4001484c0a441101d04008080389450040da01041c0359240c10213000e58401c0c2c03680485815a000e0790804603442826003400005480302c0345140c2d041103000c0701400780030119451150200c0c1c424005450390700001600580e11852030b03e01411041e00054100381d01c0fa00b00754000755100e02c43e0100e1034481e984501c540412038000314030400007074900d0000e00c800ca40c0c10110b20806030915107040c00b801660782d9101c50880304644402031556082c88403000c4580e0003901a996011034050f04072907 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 671378021 1250 671376771 671376779
    0x90a0b0c060103150c14030903070b0c0909240f04061508091207030203071203061715060f010e040902060412081903050705030112031b050625120906020f04 69
    0x900c4010030f100483da480d0746014142c24180d018020b000f0081c40380d40701d442d203484001d401942c1c00d0344010007100250200304640c100140f01011014086c10701e0118042d00c804522091244038170019103d80d8100c0301040000c2140090081442508001038a00200041644000c80e0142883e0707000203e891004000c680d10407a4040c0d1220321403810780c000c0303a65120741000e568415118491010380160070404c250408523880c190f150740c4078a41490001009a079030544050701ca151400c00c154940c10505041001d84c01807d420382c1c1180c030880d41c0c1081d00302a41e0000e000c410001920500440d22480da00044d96a6402075a004203c1c107a40aa103815041c54903003a80da07c00003107852400641d14003040b51600c24800c0d01d128040f60744500e403942c1d0070301c14045106e0b07002c06012810000c5500c01940d81075040c050b0041a584140002d00b018201a44121081c03401c0c109402440c00c0782c14001006a45c0c0060300c10404e1b0400c1000007500405030810402034410381200600359000020300107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 671379271 1250 671378021 671378023
    0xa02030618011413020a060806010917030405030601030515152d09090304030204051005010c150902030307030909050615030c160c060203041d01030c05130902090702011d01110f090a0b0c 82
    0x10f120b40708542a403141d42e280c1405070342340740056034190b00080c486807040c03207913500403400302d00d40e44091801c80c0d04040c0c2c0c502c002494150260011602a0040c05514070405c005111860300035064902c0c4400c41d04030140400c5c081904071044041851040170a150b02e120084042d0000060150040d582e61400b9801142d0380e034000c4c40220b000307a2502001508001c601d0720500103441050703541e12141034103a00c40140b0b40700a11500c1c00065555415400182e504100500c2d800e4070980b60114a00d00d000b81800441d84000c0c10740d80250403154000c0881c1c4c8200d8100ca50108407004e910761544a083c040c040d2011b400e042c014900750a9a00c00718000c0c1e00000544119030500e00c0c11200c1c03e11420f50741d401202c00703100080c00d000002c0428040c034504030101141c5401c4010b400034404100d13400140c2c02460665100c07000d81d6541500605080c00d005480340786074030b080028031010852126180d00d034440d8803001d40e180c240105422180d640c800d80044024090040e105407a4100c0d403c903d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 671380521 1250 671379271 671379301
    0x1090f1409042f2b08220e0103060b0904050d0f0207030b0903070b090d09051e061603031a06031303050c03040902130906050d030c030912230a020306180114 69
    0x1a501c615070494804596480f0511070b2038603444c15074003840c10088244d03204511074004500a540294446c440001038107103850702d40f0010034072901d07988419455400d09108640d206440ea5014052000821001c07075400501c6110781e0121f85401d40e40f04001c90022403c21200c1c0d000103000e000031030140100e0101c000003809515014070300c003080c40d48400940c641d4840e442c51050020070f034031960400281c80d000241c07004040701280000d9032225080d0008150303501402c030218900c418100064141341d410b100b04c00d0307445003410411440480c0a00042c0c0d0a000082c000300d10518194511410107100350b0a1700c040c03d00039002c80f500d0310340343c03441440650405018a8289091b46000244182c61801031170120707030340900b8488420178540c804841242030784034240c0a100303e01c60000741e410f00e84501d070043e8502402c204043d030840c1032900c40d800b50a402141c802a40191750402c0507940c00315409801c6818082e40380c0102c1000a0501c3c0035100c0298010075005415040081d020599501 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 671381771 1250 671380521 671380613
    0x20a120801064d070f050d2907020d080a0b0f041503050109151a151602100f02070f15211a091b03160c08071101090f140904 55
    0x2035502045d1501490030520301944120780e03001e141c03480700c81c0110748000001c44003414010490b0070040c50101d0f801d6560308040d40c4480c016400900000b5241da40070071040c0c0c200a40e200305000403655840059070000018004070320440e900d050300780c481580c0f00d907680c000303551040c001d02024042e402c0c0b120003441004202c410050800550362590500c60ba4000c2c03420340001e08120058503640b548000580200c824818018100b0450034003503501c3e80b4a01c00c0d03d80b401d6890b00100b00a481000303003000d00340d5109030300070381c41120240301c12403407888540c5064880d8600f840e002d01544407004d41c40011040306140b100c8c0703003510401c00c0e42c04a01d284582614280c42c8078540c0e031100340c0290480c2900c1d10b03003031f0f61410301800401c0481c444510201031b0034038a0300d00700000c8607198071010941d5002e03810840740304464100c000e10030358001524034010850462540381c01d900d003c0b44408481e01c060040780c030030060307080024200686410300076560449044040c1e895002d149041e0307044a1500d01c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 671383021 1250 671381771 671381773
    0x90c0609050306130807080d0e0a060204081b0f0906031608160509060306061018180608032104170a020706030e0706020c10021507020a120801064d 65
    0x80090042c45042070400c4d54251321841c0d880c40d10030a5200c07121581c0081c60b00a1255486880c00074000204100d50b0703a0f401c0c0103a8005a9071441c05002c2c520b440c13500304810080034605001100c0a5480240c0350340c503400c040e501c4210540d40c002c0001d040000038030142003420102035011650b600002104541010000c90001e112078844c4104a06a00c0c2103407040e03819441800017a0b280d0500702142d0100d0300642c142106c00010105c84240c110b0030035005145031081e0303401100d030406601c0c00f50030024403061000c0c5107040040e20030200c0c00410a8100d00d03d25401c1c00c042800c000f40503011082c003901c24003c441d200e68000c40003d45848051003000b0000c0c0c00d003800c100c0076460106100080b66030340e80040040b1074030700c4280100022482400c4c41035005540345a000c1020001c0010b100c0c101d00d40c09007120b0081072a0143d40c400d59000c980003007007030500045c021386802c400c0c10b132008460100103542070000640c440103110381c1740844500029655032055641c0d14400c0803a481d504001c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 671384271 1250 671383021 671383033
    0x306090215071e0821150f15090f0402121009020c0a0201031a030d0906120203010f060e04061e0e01291308060408120709050a140103090c06090503 65
    0x40c201c03004500800c40d0180c540c2c8030400c2242041c80010102d203402d80c1c401c003003250400e9030901074442d03828940190481004982c008010506103480b0109010060071a82800201c0f0716a010034680300003c100300b1148000003034034823240d6895242d010000600100207664800703d441c440200c01c141580e0700c0c01c80c1480d03141c0116079113085000f0384080042180091822a240d030700114060004000043d0002c18002241120ba44007842403403681040c40c0c44078070180386814001004c007141c000d003041d03810b4414401400580b640264440495410f0b160048809219400041c01070102d5408070004200f8940360030004030000c0a540122132464054407410703a41c500c5414480b400014403c040200c4040d4140416505840a841e404031131307251031040681c5404125103000c0b02601c003a6080340011400d41d6450f00007801440c3d000c0c06500d4405051490240402d844603804c3c00fa0143c100329124200960340d1003940710840310340d0001c0b24403000e10355641c00a4900e183c2c42c015a07000740642 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 671385521 1250 671384271 671384299
    0x3130b1312020c0105090609191203020714010504030605061306080705030d0212090d0c030501020f1c0e060c091203120a15120f0c0b0a02060609012c0408090a03060902 74
    0x1060081c5114011785400d483d00950908121450b8810f01c080c66200d418441c80c40c030011581c4ca0201c01800e19004c03214a001d803281406032030000d140d40068a05140d0020103031480e648681518200c2e54041d80129031a2107181c0029015440d80c40c0c1e0072400c41c6070030300003da2900002512011154260152200404144e5080b80c0f01c00c0100c40f44125154200201156070601c80403025001e401001c0b007012080d01d079921682a1ba2086007000a400d00214510009102c0010300700f00e121003582c0c0030000300001c180242d1300c0b001e00924800e8018008102c207442500c500f80c8100201c0441001c0e26900c10301212520030800094551f02c44c81d0313141108107400d8030300583d4000d095a64100503e000810240e0368410344200d81602160104004000018884a00c501410f040051900075040750b241c640c0500100480580c048590310b04e00c0d102840d001c00c5104c0d5100d041c01e5840d5800e000a6440341000c890900c035114065820050300b241c0007050101d01d500ca2900540b08807141d07c0d5600305 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 671386771 1250 671385521 671385523
    0x30c03030b0f180703020f0c0d031a0d030809190609050c0d080d0c02010209040507050a1715010305041b030b040302010e15070c02190b040302090108120f03130b131202 74
    0x180403402ca4011052540d4400c0e400e58580030564490298900540307400c5050600c00c685800c4000380300e040343d20109000140c0c58240c000c0d10342050041005104107000c0300e0010b9614460244081c0902400b100804d20404e0309018049002120758544861380c0200e01d4142e0092803035070000d50300e502a2242c81e1403d450031400c141d10300741d00521400d052140345540a401000c9210400c1c1c10366508100c0c00c40c050300e0354056a4803400150f115151203069490f009003004800c110150020311a03941005507182341940c0032001460b080c038000806913035500d869a10b180d01500d0400c00715909000010400280801092189110b940244a182d0032117820b140e5600c041c640c3c22144181d040c2c0018039076485001c05a0100b0300041220060620a03400d40740182c4007600044a00840017406000350700301108860b00411001c4003c00c4600680103803030302d5a0252003080b50503464000301003010740d0000400b25002540102d010000c0f401c10342d040724080240200e08440002913489921000341c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 671388021 1250 671386771 671386789
    0x1305070b0c060610050d050106080a0b04090b1311030106080a1205091e041508010506010e031209010c0c030c3213050702120f0909060a030c1e05030604030c03030b 72
    0x203500000703103025283c4504101c6540302c0d0018803c100881801156428021070040c40e000b01441d480e41000e5041c492416003c0c0c600c2c1c552058040c0d414401e4800c00034010302015030344003091061050642d080ca2420030a600c03505031003da815802c103d80882d0034035001c02c180020f0b40c8660402d03801e4210400b4113540138040d80c000a94003c06d2425141c040000c00c00d0030300c92282000b071001070a400310320280d021040990b005862a84e544104200c030b5542c0104a01c801420218010801076141039407c003144d00c0744c9140c40e41008102c541d0f0108000c6240700500195070301195850030140c0351904178400500403580303900701c12452a40342d8100107aa5024801044000d0030001d86400703034662407000b910014080340c00714800d800c0010b024903040030207404030002917410960344002d040c04010811001038a02131080c80804001c10002d4081d251210898520310084400c502d441403a826489421758812600750040b6000c0204140c0d21001f02404103120391002c2100e9400c000502882079 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 671389271 1250 671388021 671388037
    0x10020c011413120c1a19061a090a0b031e1006020a0201030c1e17151e04090206071a01210b0a0e1c030e03070206070b100902031305070b 60
    0x9031441410000c901903042c1c454000c00c95081080303620045565001040c400c5294050b00113040c05c060200480310700c92400300c010b940002c28440942013000b21b80101c143c030006a80f00c4000090000031503128184036400500480807165168685450a0300d90030f114540c2458000160800140c031305144904560242c40e842e03401400301450f9030f4010b41c0108107030141c607414403280b02010308001c025500d8014540d030655a030b14014001000103182c251402a11469050424180d410020f445043d42c04418543c0b034002c0000a06281c2c1c0480d0003401c4100000e0340201e000552001445041c4403040310096100b04d050400c0ea0360352810304e420402560306010b030751210348000030229498a1649070409140303080060350106078801145002005140e000c41307001e00b40e070030442058040c0300d03080d00d080c0c09002446c40d01100f5400180c9038401c10f54020008240303c000b00da507100c03100801c0405005073315021542ca042041102030a040c00100899151041b000d0100d5451500c0c81a01d80b20303 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 671390521 1250 671389271 671389291
    0x70801230105030a0e03030a0209030f01140c1e0a0e010f020606011b05070b2101060801060212071e03051e180603190c0914061608090102010e10020c0114 68
    0x520003140111000c0d4000707040034130341603160b40c69400350721014002503000780c10800d00140d441d10f2003014503040c0713040f410f0200030a924018068003009a03007558250701480a03081c00713585d400d91a5032081000e52144a50030303035080201d104c0700280d030020580700b4180d000340c8581e0503000200300202d9075404200e480078002000491110005045206801c00380c5100b04241c3c2d404648070500e1070ba468020750061000f455a01c81c10030700c1004002917003400340009281c50625507040c02000b954030080c140d80c44201c29070014101d014071501c00d5041c1c22407042030901662040d1079080007401c40d080ac080300110310b0050845000e0541c80c40b011034030240100000d680804c1004000c01c0800d4100908150100d000d0036171003c0c0d004134034403860b0780c900080e4503060071140c14a4170383e0302250000901c0e41d0060700c003040010011506070351000c18a0b40d0001049075903401c9540100c1c05809a031401802e10320410f80561003c028079000340c001c2c8810b41008100198004800070440801668100d00d2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 671391771 1250 671390521 671390579
    0x606091807060f0e040f1409060408030c0f0d05040f05011b021f1404031d040204120219050d080714160303030902030106050a080d080603060c16020d0206070308070801 74
    0x8024014003d20a0344801030070b00c00e20b0303203102c80085000d4586031b400095040784d40381c2c0401c1d0540102c1c000d25402084910007070441c0d1078a603586403c030307100140040c00303c0700307010841d000c20560517021644107038000501440f49003060314005404142201e03086600f5401c14860791601b081c2030300c04180907101d960090950060508091000a580f404d20500700b0352680040031540d013a403403206000e940b113951031400340b0340300241000740108104051445580104420425038039961400944240c04448880c0b200c95460340b03101d400c42140d80129003000380d1450040510040740080c1c1902c034000d0004038004202d5401d050b8072440803c520342c465001c1c000d41400460310a42c03010880314805000003c550f1740301c0700001c03101c500b1940060b07083d03400000703104401d507448581c050b049103050300103000c1424003040403a01400b42c1c4aa040380007802e549514159502c00c0001c0c410035070003510340d540d1204181401450382d0401c85500b00030030b44010002500901480303100344040030300c2e44807141e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 671393021 1250 671391771 671391779
    0x20702040c1d190605280819060f090b030703290a0504050717010b0607060c020c0a050f220c0306051f050a050306010e03101e0902060306060c0f010203090606091807 73
    0x42c49406c20700e2401c035406081341a04c2498601c8281d0311000480d1501c03110342c0d07846c101d50649182002d03416001001401c0000402152054610303060544101d60400b2a41c80c0d12080801d140041c1c070ba0010f003451740c2903030b980005c0600e40314004141640400000c241030fa600552441618070585000f049503000740002c222000050420342d007030a85020020a01100c100f00241441e00131850a0762140d5031154010905074040100803080ca802f615807040f400d1401002481d2100d03e101c4403130203640900c13100a96240c46220300020a0801c2004109a240e881c400800921103030103418000c01c09240d2685a40164009090580b44540d803980e141540c1140c0448207030b007024144505104c0205910340040d901881030135079440e8900c40004079540103800c400807600018071411640d6241c42c40c0d002c0581c80307481c01c0b80d501500545d010b035034603162036914a240118540c0e00701d103954401300603c03e4501e00461a1400b44000f01c40b1000c8544816400d5400c004000320420080e0f80082c42c100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 671394271 1250 671393021 671393027
    0xa0b030c0a0915030b102c04170919140303041a07140d020f0d0e0a09020c0705330a02030a030c050f0403050601080105012412020702040c1d1906 64
    0x51240c4403d0a1015011940da90b910086405c059510701400191000f080c40484040c064105040c0f03503003843d44011042c0d0742100006100c0141c009006400d180000c400e010545104856180380090100e501c10303030340c1c91032844031444c3c03a0203414049408001518003600e00082641d0a45240154200d03024064071028207a6030b1001e0821105410346c403013182000e09060000e48200c001a03000b5000503000410034504000d1404072150178043e8000000c07249841c0e0301451400d40300c00460040e90b450705005a203140041e2607218a80c00703000c82c201210311b10441540d0220500c18070220003450315440000c25181c2c003860399020300581c014090020a68401e0f080400c00151b00c1c2030a40c039003000c041000c074442d44141c00540719079025000400000109110b05401018060b81c082c800700c20030390a1483c10707041c0d400008200540741d0b641c00c1500310507504540300c1940c0100700b007013400b4800d42c0180c101003c108400304210419940385a20b03007405801e402480b13001c05059a0a1410104c01b5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 671395521 1250 671394271 671394281
    0xe0f06030709020c1f0c021f060e07051305011d1309020301110c3309030f04030311010b0409122a050601030c1d0109090302160902030a0b030c0a09 65
    0x269858032610900080c182c2c1d01e480248030341c204080c06001800f00403e400c2c1c00e000084040e00003404e160100c40740000c0d5000c10701c0340d000c0741034003501b0411461844412000d04070581102071200ca5178401c3c048800d40081c01080e01c6001d08501041142c0e4550055401c0750481031440651a0b052080d81264034110740f89045911041d08001054005600440e003100c0302c072000a41d100034001035055100c1010001e40c0300014a4140072400000410b540c1001d000000303c0f88100f0b03620041c080f496002d414403d0301d03c25141d006807141c480d0381d2814020102d1a5241c400c1d91154a052051112820580201c040e51a04001009010031088504984058020389181c03c03000a40d004000200400100c100301c05000d10300622280d41075003011044d108003a40100c40c5a160710350611011b200c614501411107441c4100028203110504040e420101c0071441203069120348000800c201c82a80d01075402041c81c610100511146030b018540da481440f40c3c9a54013002d4003004008141142e009 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 671396771 1250 671395521 671395531
    0x60810140d060507080a060503010203060609101e03020301061407031d0f04110d0b0108131106070b0702061906050a090b04020c0a060e060f1501080721050406150e0f 73
    0xc11100085444100803a201510303104c001401c11000d100012880e0b00070503010b060120021491802c207140003414610551310107a0040c401c409011502e180140b840ca8a060001c9020141e01304400c80014001d5000b40101000b00b003034400b6119074411082e054420342541502c0e00d04107468a81804150043c0101c1d0495006500c03403044019a281c40c042e10b43c0c607091510140352030304c0c40d58100ea800e80300f52848080c104038a88003000300d0000404426880590801c04a0224202403004a4100d100d0f080d809041c0341c404506201502d0740c00a24144600d1105000d040d2208846095030151555072140ca540103400707410500241e12603511007c10380b038004000600d000329140003103051544600c026105150340d0010203000d00011300460350303c1040101c019542d441d1a0540c0140070200003000c3c0d0401031000005640580140401106943c04a40c50500c9851422003140a40800c0b03804076142c2c1d061034680f4207552540d2038400291582e15680c0c2c0c1c109c2d510600040c00790440209 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 671398021 1250 671396771 671396779
    0x207031d0f0411042c090105100e070210022208031e0d020705010c09060807090b071112070801061406030921040510080103021f05160203150903040e0106081014 71
    0xd11801521085e0421002d101480c0246549900e1103807241c2c4001004000c299041508114034801d4140c0c140c41540d6108103807210544030480201d2812200c0b604040049200241814078100713080d0b52008000103182c440800c0d03030340b82c0c2e0300c0a88a018075550301858040f0700514801034143c030b0001d0b0070300702e1010600501306082915400c0c00c0d00d00c0092403d0204200e14020b00040d6072040c0105e41c445058244030042c94500a050790003881801310180800d4540d1042d04026540e42c11013001480060084505068440c1040c50003070005114404103648646e003500a9401d0840559100f100d03924094103601d020740340c00d904400f295410071401564104400300f0310b0765800c00290389404c9640d0344d00b0342c1c540c1903105000d50700b0480058035101088810402c003031594000b04648cc4c42d42d0604030303080700081c140b0110b468429101c00005034448001d080110060b07000000c0c0c412a800e079100a1181c0c1d070794220a840180007038130001140000c80700144111180c80d200040c100d400a0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 671399271 1250 671398021 671398027
    0x70f0e0d0803091002041d040303090b10060f021603020919051e0c0702031b0114030a23010e01050d0311150703060f0503100b060c07090207031d0f0411 67
    0x380d2050580032084880c1c40c000300c00d0103410007080101080300c082c1803500b14a03040c205001000b2805000004105a0130b80000280406210f034000500d400d50102000c2000d04140100c41c1941045000b0341000900784517108107c50b02c00100d1003189a00c040e040002c0505640038005690030003400442502c00c91302c280e102c8601c41e4032802e84125031105202048000c2d040711010130000280415600050078001d61015030380c08a04044400060303044284040d0005c0010794401c48044004c103050a4040100701800d0350b19004039008c5082c40001c40104034a00300039210a900030701450300c0074440c02005010301d0400320103001d00d1501900703206560321f280f0100e503403030403042c0171403c69040c0415041c0a81160513009140141185840c1a01ca580c00c040100b652020b801c03684010070354640f9249074650b01d5800440360b0000c3da01041d0b90b0a507440c0d19070f860180d841110114000741400105500c541310a144010b882000140003040d03d494040822015000080941010580030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 671400521 1250 671399271 671399297
    0xb0114030919050606030c0a0e0f060f13020903012a0302070813090b0f04020309120f090a06090e090102031b181c05070b04061e110709050f1e070f 65
    0x6114042c1c04503104100400e05803400000b814284003003000d00d0b1340500140d940c02d120406520321003650012420501c110f4030f546410004880c1100094a40d401c02070f140102204402250020100000290001d000c00902000d56403500a014414081c0300d04407081025441e5129400600c2d445000c0e0081d241844840d00100c1c8900009078090001290f0300c2090055a080c51480d00c2e5182e0310840e01107045140a29203503803140e41001c0c008100c50380000390311204810340403d991076148040e00314210303181c0b203440142c04210300380500c002c2510f1403800148036001c14003c492142000302c1c0d084000655040a11100c1e400401042401004c20340040c9020344600904004001d280b004031030040c0210b040460402909802100505004200038801e49410180c5880040c00221082071a081000c0c011038500d0428030404a983c0181000001c64100c20341001d030040d41201c2015100351200750769440204202041641d10304a000c00003461540600307000011248c0c582804d4508141c0c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 671401771 1250 671400521 671400553
    0xe0d02030a050d24030b091b10051201060201050f100501050d18060923030304020901060806130213150509031e0138090919082205030c01030b01140309 67
    0x4000740c0001110481300c10818000d0411303400d60403400e18000340c407403e03003456a1113032940c0d29070802c1405076070b460003218681e5214070221003103c1c5910104c65003e51312014024007078182070b281a11502c11080225400f4a101c00d02d901c11240143c66541c0ba000706c01800b100900541d20b074074106036075017880f45000b02d0200c0c0182e90b2031078442c0d0881070380e010070460440d5460503a030030320580b694410700400c00141c46517000b00d03040d20301c01e0400401030790b100400504044d00c138240d066001030020034200b0490441c00c1048040e2421a6504601c1200d800c0301265603008440143d5815880414a13900328030920a1251071450400300106201041c00340032588908488054541c841d003e0106140c80c1104140c20b0403050422071341c0e0000341c01c26654499030b85400a0b4000e20480c1c0e0304a00300c041140c0e0b0400c6030528000c4081c405000d0800258003d0b0001003480b8050190058502c0741c003003984a071003034000041c0c058652407120348040202484c2c03504014150b5150b4031030740d07005c20340d1005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 671402877 1106 671401771 671401811
    0x12141302040207050a140723090402010212040f17010c05040b0d0b0a180c0503100b09040608030f0720060306091b030709090e0d02030a050d 62
    0x303000003002489058030060962041c904002c0030081d0102600c217030000311000b03841800d95900c3c02202e42620b038100d0705c049400074018a0701d01345400080d00790494010702c102c40401503451529103d551164000310060542c60401300908012a00403c2c1c03595a0f00b0024011310b1685100900a4003450140c00109080810301e040c810f070f0181e100c6c0d601c2d40c034000e0400c1602a51360320f10b1058605001e40e550710701403c242031010601c7c0204100c078010b600303128101c00c40c3c030326240342500380740c12940090768015110000055500d50401c05030400556803100150369643c18a01402c441e0b040400031010340c01c2c50300c40c4030002e50301c00c070039254001c606807002c288a80d690942601000400c00841e402e1080201c03c0c49110769200083c20b046d9100907004002814518200d181d039641800500350060340100101c41c3d072035110708084d100424a440000c60b8a02003202040c1707070a4 = true := by decide +kernel

theorem cover : BRFrame.Cov 671223021 671402877 := by
  have h0 := BRFrame.cov_init 671223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 671223021 ≤ n) (h2 : n < 671402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
