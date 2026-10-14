-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3623
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:12:02.157059+00:00
-- url     : https://prove2.me/submissions/456dec2f-3177-45d4-9cd9-b0d47a2278ae

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 651438848 ≤ n < 651618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 651440098 1250 651438848 651438857
    0xb07050601062d0c0b090a06050a020c03160203030912030c01060b0720210f06090c09011404020f030c130506032710050103050607090e130b040515190506090106 71
    0x807002418245801034000c5010f500e850881c020140d1100c14a000c0c0955100c011500710485d07050511440d4003c06500c000180340030b602d043c0078202c03030135070301d10580c3c6e9000142c031503040342c510441d81c0600c02c03107191072802070034180032510140700c0c2c40d10383c1e11064200c4941e42c606000054a0301e01c6c03c007641c00094010072104200641007192504003840c0004c200d500c6110544030385003400c8801c011101724100300c0d00a040310f804544409103410405012012282d0080940488942d80e940d566419140482c0c00e03c1d00b8448910082806070040b240c946504400200c01c00c14899141c0000d0079000c1004a01040d0881e039400a02c0890702c4141c4403440c462a041d00d9510800c903c0c0420912501384160403181c10302105000704085030750a810484081e040481404a803c0e4030416500140807115040181800c1034141e46100900210004201d81c0002000805001050050300f40b000c030050750510300e42ca85100b6001150f420302215070f521914010200d40142412210700e41a144941c85 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 651441348 1250 651440098 651440147
    0x50618210f0c07091b030501091103010614070b070e0906150409020c030c0a080a081b04050d0302160f09060e0f2e030b0f0609060d1115040b0705060106 67
    0x1106445980140350b81c00c0d040c0315114000440803001d101c2d200303070f0085d003100526841d40b0700c000084c02d41d40180e02101242d41080742c1120140d40c1e0f4002c40381107540c90305111302d0903407112890710040c0c040c1103005829411540200840306401c40d4002007000001c450020f050798a2204002d8400084684281d41d00814002804030304e0b015801400042e42d200212410691300c50109464400c4c0380b07000729800c45001c941c1040c0160040c00d455041030079220703e5402050f142c2d00307e00d02409203110b101d20498072001400c0505000344403951840e9160b03962007440b0303600c442d4440210321040c8515510507180c0301d00003501c0a8643d6900e4068803042c0c0d1012555240d0107014200350414032010a40b2406980030780c161079460010440003188100c0d424542c0303191440d4020b8201100510303a0707010700c84100070400c055480040004103254001c0d145a14003619001040c090183d00b0b000300b14032280047c1c08940c803480c0002903c2624802c2c2c0440701c1d1070380ca501045500b0340000064101d404081d42c0e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 651442598 1250 651441348 651441367
    0xb0a0f03020313120c020a1409060a120609030c060f0605120f071a21090715021f0f0603050a1e0203070b1e1b152701020705061821 58
    0x1061440c2c080c0d041d141c14a0040000d800040b031300100b9178458061143e507050f0038806810710480d09c0e44e1051007201c031002128945450a0b6025181082c01880b043d600e800002c1014007032000b009500d81c1003d01008504190489800144a28040e09110b070016040340e945204000070030b080000da40502500f004c610341300f580340300c405180c0c6a0001c00b41c0240001c010540d030140350b550310844402800b00d00c6052400c9030604084140d0416450003410400c0902650f40014001c1c00301c0d004080d410000ca900c4035008001001c01c42c8130f66079024107241d80001403081c0050403400e018040c104117040c3c4c0801d003e840070038261408000f0742581061404003c00740c0f21401400c07103e00c15100c62120300550a480f81c07010f900130484000b03006500503201078492000c1010401640d0003140610741401c0c00d10203101003c05500c000c5035000c10750b0681c0262208217405880d0465440001c640171401c01ca070504100c50f0350f801c980d5016105020003260003104550307101c0642c0c01c001c0103842c544002e94 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 651443848 1250 651442598 651442613
    0x4020f07150e01150317030103030e010f120e0703020909060403020d1115011205010c090602030904020c03040f06210c0804141c02010e01150503030d0203130b010b0a0f03020313 78
    0x5400e5045025036a603125061202c0a0003a10716034481c1800321070000e0b0451401c0d1140150210314096001001d00040c07000941220703242c0d40d105070034240f45400d0920201c0031a084601c9482d90031605040001c141044000007940c18107603803080300c01c07078403640d6109909640c0d000304481c081d006034404e0fa208200c40f0300800140a90000042c207492800c061403c0300c4002c00020f038170101030990b2508500c42030140038407644580301c071503150000b0914a4040029500e02900ca00680310b5a400104401c51040810403240200720010408404640d50240a000f85040760b40c2130806500c07011228092120354440d10303121080503103a080003904d071600c03a1408180c1d000d02c4400184901e8004540c00c22682d10003041d079843c2076002103441c44900141074251105515040c82ca24000e40c800c2c400f07a0380110a0f581840781d0510010f840f0b41d10f08850302640c1c4d116510107440c1c41240000131610202040040000d115503803518211a030b54002c0440480c881101c0313062861400e5203071400082c103074 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 651445098 1250 651443848 651443873
    0x2100305060d0501180b0a2f0d051816060f08220f02120d05030402040905160303030605090f010506070b04020f03150402041503050d080c16031d04020f07 68
    0x2425249148502c0d50324182160b0300f0160080000c09007000b56020009402a1958040c0000d5000e000b01d43c2803412103c580d40c946201c0c2582030f107801c102c103040c44e42001c1c15600c0c0e03044510818017207420301162010982030000c0e081100780c00780301c03008201d0988029103841102c8581e6a0111100c594280c2201c4401c8041d041081510303280c2c0386501e0406175455200b010034012000000509120320400c030882036200d4801100380c11504848800580000a0b40d0384103806640101300072034145851801c2400c0301d248040b090b10703450808814980d16511080641d0401e0320f05120b29255240034803000c2e40240700302640820308000010004c2c007101c652035041f610241035084c40801c40400030703083c861143c52510180756018104030540c0340070300445411082030450014040d08507201e41c1e86030f00c0c074000318800f4820300781c003c1019015030900300c440040030b0740704000d1764075034628000300004104991140340032114a0303c00761038903151007151041401d02c1001841c005a903130760a00654003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 651446348 1250 651445098 651445111
    0x150a150e010302042c010e010b3c030f10051507140d1d0621040f020d0317090c1c06060911030609070e03100b030a060e030c0c0d02100305 61
    0xb000d00001640c50450318901400710444990b80403604a071795101c00502034161711016101344060010000701c2c40000445003c4042110401d100c00f00a07a00308008221500383d0140c600c60390b0011401c001c0c1c0b00d0028500440980c8109041500e6041c84c83d00800c803607001d89a400030624003001544903c1d0401000c0d014400e5643e4840042080b80d4142000300045a401c04100061042121280d0044007111500070032202035041004003a440c0408102c81c00c00d01d80e0540d80c3c04086018421342002c0341c02800c1d03004050034200c4080707240003804907801d100360f01042c5008070041115200049400126401c02400f42c540b400b10841c06031400c1c2940e05e030191a460f998900200d050b0a182c0124008500b0104c0a2039890401c042844281c403401032000c0d00300000c40800d000541c0c0d020030390a1803d003003c0340202d10707110380e080041c0c00c20340c3c00400241000d14000c8a6080c0c814084060005000c1c0c0e10203031400c00e1a51810b00040542c9103200950040b14210248801c0313010b9800340d41c1110 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 651447598 1250 651446348 651446351
    0x1e07030e06070806011b0807031b080412060b1e06031009052409010e01120c09090b0a0c0c0c0905071b08040f05121b0303090a060305150a150e0103 65
    0x10300028500d04101c0300741e51082c000340c0310300c00700002c80d41c03c00c03800150101e02900400b54440c058690102e40d001e070400080800000e01d8070310030345810345007404ad4402c0c0c20a91540e6503d965080c40c40032500610030894000d41864126200d0785007041c503c80715440c1d002040800d0340c40b44000c12541ea840109900a0b900c0b08841c0410b00d100c2d580f00e4140b20301a00406469000c00001d4081808140d103c500ca1044111100511000036041d00450440394000f0b1003c0d095405481c0c800391814890300035204003890080008140565500524040d0641c02010481300fa0001c50031910990404005440100700c203030100484000f40d03012a900c00014905070300c10340a4500c8820300b400c205542034603512004242440007201e00c2d45400000c010031600143c800903080d50f016210280041040b218180c000354240351614144200d1784064401810420074035180d800180040405035240d0001d007102802040560802030b100700250381041040c0030901e01c800e201180c040d03804070660350405 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 651448848 1250 651447598 651447611
    0x60711012012070c0b031003030c1109040308180319080a1b0906030c02010b1309230a031713120507061401080607020706091206060b0705070317031e0703 68
    0x8007000e00c254400d000809440d1a40e6030303a00c0c1080c96142003e038100c0561a0003c000303009030f220180c3e003101c0480780d15003014a26246181807031240c4200070540b05411a181c1c80c02c010800d0f50109000f403180b8180b0300e911080c0801e44020316542d0041040c20203200780c4002c5042c4070709005002140d800b0806035800f04e0030055601c0c0311102084001c1c21381d40428007440c41802032075010300409101c05814030007040400d0404000810581048412141079a03942c190503092113031284169400c00440550400c1ca9014009404d641e00700c0010240c2c0000d1240044400b10710b01d480c140c0380940400c0409001d0320340d294480d2a82c1328040c0c3e403418140070b010468400055161f02503240c0031805031240d40d034191f24280005060000050400045400002d81840740035000540e2105480c150406110f03015500d14200005200315040003041d4400070600360100f10f40000c400c8196441035203104414078a15043c20101e01054682105280d81402181002406c00c1c520991050740343c500440c50 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 651450098 1250 651448848 651448907
    0x20702010f09151d030f0303041e11061b0f0c03010e01050c071113050f160503040201080f0c0403020a0305030403060b0613050108071218020a051e12010e12130506071101 75
    0x10030000520591b083c2e007022041000340540f502420180801450340d8003c0c002d92682e9070b1803c0070b4507030410ba20400000c1200001c20070410031aa0410b209074080b00c031141e4000c45459601c11a0606484c0310b9820440d4007094900180120b50080003800c1109041a80d15510642031001505030181c0081000e0b9011400319090b02640c0e024214400303900c40c590400d03a80c1000380c8a07520f040301c014014100148401070341e202e90425804441e22200b844583c540d02c0540034907100d0350f8000b0b98020b9107001d012042c004040010030440b8403800c01000091000010b0200724090541140303000000d90b0410000d0354040e01c59075a010706249441000504c0324000d0304201c0e40a040e9000015403c0e206100c1103091401801c0c0c0504001c50700c00600014411718100c07509486031000340902e00c031517205114180c1c250001c0d2110b02d41c80e026100b400000119050b07068101110704132990b040c414001401c1c0c00e2000494402d0340c0c01441c91110b1220b502c0040d184120780000c00c244a182c3c15603100c00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 651451348 1250 651450098 651450103
    0x90d0f15180f030e0312180109081506120a051f0b0607030e0a17030d0b0103021602043b060a02040b1611040c05090f031606080a110d020702010f09151d03 68
    0x2c0c080341b211100c54031100d2600a41520125840078181440074411041c00f1040c4001070414141c1900000d5010030303030f19000454400c4851035100d00151080d10380c05002c02a0115054484991070201040103420302d8444800356444601115000704040100c4004030b480740c51060884031000c0c00c0c0300c0f4100e40e1900100b41d403500a204103880c1d5000400d11007011452402500e206140900e41542080c0f07220002da800040c2c1164000d1090340c1d140200d40d0140a0710107100815884405070882c0c40312400c801261025840d00d04120500500c00014000310301e52095506032188481d02070b04060704400390810100300e4a00aa07040742d440702c1510f010399100c0c025107498490359910703643c494482200b070114000c850078409200b600314400300030303030041412560030446640345040702c1c66403030340c0f4040c0e4001d0030050000f0305500c10009027004810815002800881d00c01c5e6a9a00d620000d000304961004040c0924500b08501d840004036043c45000410744156104100101301390002d80000d1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 651452598 1250 651451348 651451363
    0x606181a010f2316150605060906181804030f080f0f09032205040c170705070807080703020a171207110f061302040b0909031905090d0f15180f030e03 66
    0x26602128074840b002040345501c0f0781171244811100900c081400c0500050041c018007030018000c690202c0e0400c000001f5442130040d118010b050155114106030510300c0396441250280c5c003081d100d0040d50300f40c510424642e07126801c40210f424558543c400001801100504600200c2c80180308124429040d14150040c80400811014040f4602006e00c07041e106158001024000f02d10f4840b0a491202c100e25907204949185c000c2d07031200c84e842d208030f90f40600d00000d0280800070864000701170300020921240c6010748445101003055000d9100144035004421018299140201d0107460080d001d0341040000d01d0165402003000440c0280b408004980805104401c44010003c1d801c15103d01004803c06480c2c44c0c00c47e280c0044895624860b43d103550f00d00307042c00320040c0c048510038000d49014040040000010144606240300c00c914401025a000f00b042d40c0031504000c0075101d11032100c841ca1400c0003a41c040c580700c0520b109690013059040c042035507021b1172151f50900480 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 651453848 1250 651452598 651452617
    0x608120a0f3005151507080a1701080c240a0c03140d0b040e01090803070c0618030c020f1903081e0f0a0e010201111b0106030606181a010f23 62
    0x83c40d40350442c80d8940600c0c00d10b0100c0c0c0078408081c03925019801160455032516000180181d0b9001901c5e400c5901d00a030700803611254410b0000840c41800c0031410f9a1840811101c41130401010300c1042d040384441098600749030001c103c2d84c1d04040c0100d8140811070300906208681030040b80c40700c4010350041e503a00f054983c0d15020741445141c5482120018202200204005810b655541c0800d101c0036142100703011102c00e940c0104041508071348010940101c00903012001d500c0e000c1e1040105010482c03052521000071084c0707080c04840c210000c0500303c40c030b041e198510340b51402194890b0040c882d26942a101c50300141040070010008000035403039040e030750564540010107034110700b0601e0381103904090008024480c84002d07100c2c8034040040c5490343e0400041c0741d5006110030390004000340d0400340c00150f044c1d5002c41000380c0e4010544180040d240f0b62110348605c0030f0b044d58440c0801d640c5038201c1102403290b00030302c5109951011818032404805490031041d04104984d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 651455098 1250 651453848 651453851
    0x5030103110d1b08011508030a080a18060204052e0f12050f010810150b0d0e0a03031d060921120f06040e0c0325180608120a0f30 57
    0x4001004c024840c5501c400c12583c00c0c13a00203400c003514140c0745c0c49520f0b0520100140940030030640601a842211403039014107001420354030a1034688042c3d0024413800c4e102c0d400000a45d600d04840050300c05041c80351885103142c100303030180c06071039004c0d00e9000f440404c804502422150002446141d00030380c0a00c050b10446d40c505072182d440c140301e81c481c090015081100d00c1d121a2031080341281603600c484102502c4110383d26036040140480780d6240d0b82881584103820038550154449010310728500344660408061740900c96840b54151078400c0d4652016040c1c80c1c00702d4405036800c01d00300348a1764482c5403010030300210300007a005403403a000100c4407006014140c6040d12481002114100141419031000c0740003d4484904860883e905a0a599240b60003a010444900900500c041d02e40c44440c1080c100c40c0102150b01810b04a4820000c8400310501e40c0c50945840701c006176246110248500c0c411180d114003003c5544061504540c000d45c00003240696291130440c8180 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 651456348 1250 651455098 651455153
    0x90b03041b0611030d051e15090703060b031308130803040618140118080d0302040f05090402030d03020c0307020409060f05061212071a10030b0c090105030103110d 72
    0x1080062040a54808401e100c5608044180f0341008415070355241c0707004030002441e50700d110000544080b50404038206080c00070030000904c51076001c41c80b030f40c1d00540740c3c0d400c00e5840003c00d03400c071a043e00512440704010b00000307503100390a82188210078407405825092040c00c0010000c90724454001491581022038148402580b0600700c0200701f02c071501e004420f03403400e40041c104041f01034900341000070020003001079909410566005015a0f003c54007580c0724540020b00a4016000d224641c0b8a1104000342d03500e08030300729502454000b005850540b40140d02600250b00404a140c2180010f01c00580035070b41d544580301140b80905804203003c280003074034400302c1e94014502c5109018030714820b2503c8400058100c0302d61074a0503c1c907a00c001c1401d00b1600d203010150b0031080c6954050400010a01d42c800c0c4a08a900c520211b201ca51910302042d803150080c1d80c40c3c2c60001d1014030040000c61000b240c94409220041c0200030044226140d07900300c004142d4405180803100034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 651457598 1250 651456348 651456383
    0xf07080f04090c031a01083c180c0d050a020904061e1514030a06060b090109140603060607020d0501052806030809040b1503070801060e061804020a090b0304 69
    0x3504000310a0f518042010400c90b44d0010100755081c944507040000e07440c0003550f844003a8159100640600c0c40d84080210400c0303106e00281040404c0400381c440400101c2c5281e001c0310a0684481040b00160010103103841c1444560300b1815420389181c40341c204000d015031188036190380240d02510380807440f07041c0d00c440210801c0c0804d9090714680c0c6451a5508020301494215090f02e42e507805a0107a01c084000180c40c2c0b0355144000342c0034914002c2d00184446c0c0007001010800c40a0301d514941566a000c6001d014080d000c83ca03800070010030001d01c261034040c0081c10040d00c002d284400444403911140c4c2107035402c440c030440f04545c808151700c103e0f039155150405d02964140c1401001c0c02c642d504c68843c040d84070b48902070391712424900c50315a2002c1c0c5c5403d1048810303001c107031a498600001403c6405c2845150080741500120001d5428018100c40c3c2c40304800403001d540030440340910000394094481c4c6001c010001401140b282072a900560241d4080c0e00d01149952499 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 651458848 1250 651457598 651457601
    0xa0f03120b0f010e010509010c05070e060102010b1c15290307080a0309030f021203030a1a0a050105031305070503010e0c0406151e021005090609060610140f07080f0409 74
    0x24041c5031040007500c0b18a8002d03070340000c459481402c28a89907896442c00f5005903070300c03028803600510a0003050400f048004d213810f04c2910a1000340d000f48640c0c590041800902aa140c080261010b00c0e04401d0000c41e02203a840b51410f91b89410004a02000b406284140381c507041c0803148034074088064208900c1e0400108000d08007441c003804407000940e601824a0711a840001c2c10300320002584420b66032150315000c101800030bc140c0381e60340742c440c0021004000e84440000821145c0004007440d082c000f0885083d210180c54440c5142c9030122800d043c0e901d290f0044605220b400c4010130241c4080c041c2c0b01003244014001d064600c8003c0401095580366048401000012084c010144d03500c650691114a012804101c100002050403810256510401c40c2910304060600c0111140012014880d4101001342c030002c3e100c80080168441140441c400000c1e081103104031050765010080001015450703c803032924030542d640c040c550300481c402070280703440820204800d0360366 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 651460098 1250 651458848 651458861
    0x21906030507090807080d0815040915060807144e010506031e070306021225050d0f18030206010806090703080f0a0e0d1b0905090703060b030a0f0312 66
    0x710805445401e0424000b031f030383c0310120705185c0200030b02200031480c01d1845803000041c4160160080c880c0340b07010305000c201c041e070301c03520440010300d40507001034802c8003c40c0d84070585000c0d4000f4440d5661282c10082d030490b4844c0d64079118018148400754031000040d40342e0590307050900c0100107500f08814071035054454401203540780d0401041120554010520f540d1342c1100003408000e51440000c6685002025000208010f20000c0e81a03121a40d080e100d61044418030302d44018000701803001000031082c0080da00c00306900744515210403a032500b00c525603d90311240000c4030a13030314088101c0a03000102c1580542c0005006001e60b0100707000840e032106480e0010202c6078590303503404400d84031700d107070f8072a0004000c40d00558051040350081c0211000402032100d0340c0d60350030095a800c59000ca0780e009400c450400003006c82860081b9803041c1c000c83e004d081294556101c40000d42810b41c0c910f9494004c41c4891000a0100c807482c080460103a9038004811011000900c04c507203030f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 651461348 1250 651460098 651460109
    0x100b030d05094209130b0109030206030603150c070b1b0706020304061407020c09060414040b07270515070210120b030d0e0f0904080304080702190603050709 69
    0xc00841041c1c0d01c0b0502c40145440c91548443c580c0d072100c501c03202d9401006103000c0c11040f42a9200084089030002034004a4030480700780201040c40d001010450b04490990350104403113070010005860711a0266500500c007400b0340c0d802e031070a2458100d012200b1507800400e1344003c0360400611030f0306081079a010800a1042e800c00c0014105810b040c020140002d00050b0000000340800210342c00a004021400440381000d0411080c06900e0326501040305004010440000d0034506e050b0040281140b41a10740c00019100ca45038003c407040018040d90522800c5c071b0080400318050480090b00040da04242c1c00101d08042c10080c42d10b1030f00c80c24600800c4184202809a40d41801d50000950141003501c21048201d442d030000e804001c0226525000b6042c0380e64025421403445522040c0c211021403040c02080108180c242c0241e40103044030006000290020f002a00149032041c0000c00110100346401d000c406160400d40028002944650a11002c0340c0c2004424002d0b04 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 651462598 1250 651461348 651461357
    0x50318100504031b030c03050d11010c141e160b0105010824011809060303090b040f05060d1103040602040806090c01051e070f050c13020a02060609041103100b030d 72
    0x45003801085070250303000103400c506400c810310304c0901c03620301e03c84001d680c00b0002c00ca820b40d0744c0c200640c9907410b400d85000443c6041200c100d440d001031003501d403d40d1854030352059115aa401e00306164220001004200d40b100708508010714070030740500900050040d56045d81c0b0030601d0918265001a84001d05000d611418801c1000d806510388000b0028410300456040b00d0000494640d403021008641c2c540c1c080304007040c00c118a81250040d01d0090700e85e00040d41d668003078540d0341d12461144010510644070180b0140c5000c600520040125013404102e0490909103140070303074000d88003187c05503030000c0d00308043d103001e0192503442071380d24010b4241d000d107030350000c0e01503c2001005d4880403010f810f5040c8a80d1480d0a54901035003002c02031171808144d19219941d840a112090701c20304551250b54010b08081c02110b0340084e01e40d0140c240c0d6125401805015500500120346808090300700900390b440800c0341c1440102d640b2800b0408509a41c00c0c107003414404400c220401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 651463848 1250 651462598 651462619
    0x21509210313021e0a06030509012927090715030b150901020a17040e010506040303091e18061806050f10030b0303030f09070f0815091603050318 64
    0x140d1032480140a1901900c80781540180c40709200d0402081c2c4400c20f5000041d8200402c01c1545980003602c2043d0b644000c000c90a04e03512044496500380712f1074903e000c00c0598040320303801c20355480558200504035a05000c41030b00007000c00a10b0858200c1a80e038882e2404110300c00d01c85952126640b4641000c1040300e040300081010318101200203440e41e40d000420783c1c040e91080103011459504940c003401041a0f800a01d000303540184500c00f485959130001040d5071401004940480ba0300d5110401064544040d03030703051030b415000180b13800103c00c100280c1203e080f4030340003d591540c4400660141011808007420411b000d0441384549801801d12194541640b80da240000c00c8078420050300400804402034000819819018000442841a03050340c2441150184d07404000750343e1a00d44078048141d41603c0c500c20704000e0b81c0402c1400c458203120412198000b0340a0082e107440070100402c0b609612459030040f18180d000045041c0c145000107021b2a004800b140d07201c1c2035 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 651465098 1250 651463848 651463861
    0x180a1215110418111606090b06090106122a05190906020717030d0e031902011a010c170a0504050a0f2d03051c021504021c030215092103 60
    0x20205190707055040c0303541d190150001c88039401982c5d034040c0d461046142850382454424064410003000300c2c0d12801c08404141d45241101549050700c03a265200780701d40e03c1035041d11002d805521502c1d800c000003c4c508401000000301c0005000e85a03481751917a607440d0321a854203500d00841e1100c1003080540707081c4126640422407004581d00a6440c50154143c1c0f9002d6055200e00d101e00f00001c0c0c80c21203610004030010006c0c2101100d104003031400006051001da098456005940c59224007034030303029016601840c000350065028143d02500210100704104140d44100d254402003540070404000714600503a142010f0a600c1081c151003078078040708020034411003506440c95039030140302107580c040e4202e80c250041d900401200c000340c0030b062440810f203002d1851100140640f1403201c0420002d807001c90f0165601400074500840c10094113800311602510481c118000c01c800714607580000e481c82c0e40038071030610150a41030784c40c0b50315000d1410b1740948056804010b2041015 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 651466348 1250 651465098 651465119
    0x4020f091c060212090c0a0f06050703021c09050102070605090d0b13020d03020606030c1c080a0212180a060c0c091d0609060924060904020f0d0b0a0b03030708180a12151104 76
    0x1241ca074ae0a12030707100d06c50744c5800c1c2d0034800c2c00545c034032415001d040c82104055018441c4c1045407005c0e0241d0b42d00503150344088415118100c9400d03001004540a03800240b284a15990f00801103203803032485007401e60008480a0f0109402d0700103a00c10f80910540385420b02a541c407000d01224088125580040010b040d140b5000e4090b141440c04184c0f849041e00a002c8a10040c44941080d07944100c45d0700500c00c644840301003540160140b60011642034011504c03114090707000b02004074030030301d03001c81e0304082e2000000500c80300545445444031403004001445c0030342c0f1900064041803402603d1240741444044170002140d0a40022a240e00c01008505411500035150b05180307070b586001140594500fa88602c0e00050b22000c020140100300c9005405a080c11300d051180400d100c1c10580c0da402200405485040c0401400110300412000c2d00710552000d0000c2a2030742d40e590031403284410550701516001039041d001008940d06c0e104d030455006940702460300b49401c04d4130034003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 651467598 1250 651466348 651466379
    0xc0f0807081c0c02030d170f090a02090c1b011a030a0201170919030e01030c02011a060310030212061e2e03080406020d030b04020f091c060212090c0a 66
    0x5041e04031900b81e0041031245000402050300901250b2881e140c580d0010080c11103000380a09103100354001c20312038056403003030034010b00c0c004009040c203641d96000c00c80030b00800703448194903210030095480b034090200000046204150000034444103043c000768407405074080d29912030f80007001e078000140e07046a8044c580702041804241580d44000c11186000311200640d140c01c0c0d0000d04e0325041582c4100300422840080c0e80c140301e00048814142c3c240c4492005c00c002c0240c2030400010035050000103903502510340c07411400392175525000320354401e02441d80103020390072040400c46145000710040d4508030040c604468a45041e11200c080e203009041c407104070700b100d981ea50f4202c60300100041c0155170802109076582ea901c00700a981c86004c40589000b013820000c000040b4039091003945c02d5495a111500d04e881012002c204c03104104c001101014561001403e010408a10142c00b010b424012a0341041c18124280341c50149640fa26610030b03080d2180a1189102e0f00360b40c03c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 651468848 1250 651467598 651467623
    0xc0206100f17070b13140d0b010924030c1e050f0402221415071520040b03040c080604051b130926030106050906180405040c0f080708 59
    0x22102c90409146080c10804140d00058445030f01068400d25948440300c14012528070f200031016940c001001c0c411490126800a400c40540c1401004050403640104078405054071842245d07214480b841000c40c00940c00640301481120b40a01c44015000070034500c040301219120074843c50140010360040d2000b0b81d080c02680c02088000d1034403148025130003d101c11040d540b12072034031086071281c0b0030b8101312841c0c85201780240d181072404184045a4005800c200010a0381c24000c0c501405881c5040300078507000060841c425001443c90050005070400920f05c0351b40f804e0034180704005114070340240100f42c0001d010300000030000130399944003140c403c4c3d05115801400c400902e000802030540302c2271508121007281005968446144c0d06040b20881c0d4000c00e5281a07000c403d4002400b0740781c0400c504004d1013a440c90034038003915004692401c0d902916002c01e0225055070360a403421541546003250a100080241071030501405280004000151800361000e43d01c1c040e01004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 651470098 1250 651468848 651468869
    0x130e1e07140a05040e0a030206010b0f07060902030708030406120b01110d0e0a1d0412080f0c0d0618050406060503011104050402031009050405030d0501060e0117091c030c0206100f 79
    0x14003079072640c0001500070000108100f00000c01c3c4201340c5e032100c2081000302d00500851002252a4185d001aa084540036440032410184c01d175503140c00802c91600d05a0303251103106000211008104000d0020301210f07503c3c0d0310b00791013841000095030450501c130790601c00310f0312184600010002d01e079074841d441e503c1c02e00160030404000c104405115004448000c5200d00241201170956403038501803482020040002e0a03000022221020107458140b500468400400d80b03040410b80944502e100c02030001580780c0d55041402c41d1140e8011038451002d4482c403c20050185c0740c4100e02c0101801d90007880071008002c1113120a03c114000c0c2c2c2d11460380800450002912400070320701030301102d5020083d5003064202543c3e20742110f4000d95195007040c0c00446e03454030035009014414410b8480348a180c82c5070300002e41c45040245090514030400901d00003203414000040fa40c645992000680002103560003420000001c6c02d00150301c00b28541040790700c0c540e002a1741155000c425 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 651471348 1250 651470098 651470129
    0x5070b0711070603060608011205030417012a020c1009290a050301051c02030304050603070c0c2601060e040f0206160c0f090533130e1e07 61
    0x42965988044646020180b04055020500c2c6415921810079a04162503100860380d0b81c007042581b0000c0000010000d8000340020000c9100d0045102c4000301d41c1400450a0440348842c1d0000c608211010480d001c94609a0071203160148038550703210006540800c042c1860744000307405880c1d14860498009401208140000244c20032170324011125420351b50341700d1044000414503002030203528031460501044000c400d40300380d43c01440f241e02402550916182c0420007029410017492041481307600b0380014009001220020080e0155284200c12444d50b251002c50210404103004110303894804144220f180350200c140d403281d40314030b95480b10842d520128401d4000d20f000008083c45820703800041000011448081d101c41c0d4581498050343c0312400801d4a0b01924002040b4a1070921003d0003910b05140d00003500e40c2105d004441c0302d10700085540c0445402c681041c0c20354500082c91304000510010703400f41c06400100700086540e00d04207481d00c01c40c0c41180a903004c48403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 651472598 1250 651471348 651471361
    0x304060b0a140d11210705120a03081609080d02070303080604061a070c030b010b040914220c180209040b1002060c0c011409300403080f12090a0618020105070b 70
    0x110350603034214506004880c05040e0907441e644181c94080c207841241c23441401802e0590000d030420360079400d551380038000d40719102c0030b80800d03216800c40c804120b041480811010420403103101034880b02e50090020604e1800c0042444802400da41d20031801c0580070050340c1e004013030701801c5800d03030034080b651a80d6034500319611719520b80c00140701007001c800015514603603102501c100c401111003031240b0349850b0240d0204460407140282c00103020b900550b130000c0c0607021500c10340e00c00c0034044203658540319110787c1081142e07140c10601c0d8000881c0251420107010350f89000303a0a485000d900c110908019449000c02846100804004204081d00c11000d4120841e0050301c030b02c0080f41c90030403101c01501c0d00d0a400d81d29201080728a00403503070341c600048842405a04802c681e00f840d09580d0b803854140d00c802d80340d94429006218600700c280500884502406581006104492031480c01c04151003284c41d4840c0800031002c1c9100141c2d800208440c7c805500881010441d50b558 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 651473848 1250 651472598 651472609
    0x31d100f020d150f0504230a0603080c0a03090b160b07030b151b150114030f15090d02010506090705070f050604120e0603040c030f0206040b0304060b0a140d11 70
    0x7a03400300e0038141030101940c580d01c80d002c00c040035546184c40050030151070700306100030f030303040c0e03a807946110110740041c010190310b0f000a15821544283c4045040c0d542c0341c4a00015401c0384941d04000d820501c9141d04242e0450400b800400b60030301402d040008038800b440742003e400300003525a5a041c000198001e120343e0248801400040036000703d030000144c008142d411200c02c0c21403202103500c0e068044200003c690040c1c4100c2d04088580e607081800002c030306000d8000a640501c64110007007860081484842c0000e07080d605164000d1074054401403600b0004211130b03080da45032800317000d030544075200c01c141e010400d07090043c0e440302249044400c1d0500704002510074001e14003400100003040c29040702d54501030760f4003035801d0003220030041c2521090310010041c8c1e00c150003c0002965036105843c290f40010807041c00c2503619241444075901c1164200c07046661a0050240b81c41c2c5484244090010303148800910000b41d400b04040014140020f0002003450221900e6682d40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 651475098 1250 651473848 651473857
    0x80d0e030c130902120601030534140109030501020f0306030723060318030c0c0301060614040306050703060b0a030b0a06050913110c030708090a0602120315010e12030703031d100f02 80
    0x170308007115013540c0c4d6400d0068496880400761000c0e24005840c002c6000518094103841114040032507210919000c40ba081460596401a0600041010010114a00b84003800196000c0904140e5900e0000704250507c2840e421004003510b8100c031260320418088681102e800098542e40d95031745030040000f8527141c6128103072202d4400020160248000801d4030a040c43c002e40c0244281511940259070140c80804811001701e024401040404c2c81c6811090b0822290b0038005070003500c50910000c5980450080400f20f5101c04582c6540d09003030300d001008104500d0a035003000c0c00540091503200300c441441c1c0d1000d803100c1c0b6401000348507804031a07031049032800b101d54841c900c3c0fa10b0007044e000b0003440341c818150640000b544500218168041d00c010749459455a507440f11400d4078000322a821604001c540b002102443c0c0741c2d00e9400003a920150021500c600702072600605480d540040c084034136400c0c12551030701207800200c4800444243d90007081420001c03001b02e009005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 651476348 1250 651475098 651475129
    0x40b361c030b01030e030c0c010e0619020a05071d070f180f050a241b0c0f0305010c0306080706050c01020d05270c030303010302040c1206080d0e030c130902 69
    0x30010381000d41501640401d034082e4084e03d05008402d51803000d15100c0c0a101e42c2c0c00000d820508504480d9032103150658080d034401821941814607030046042000103840f440c0d00564081e0003084140102040079800402d2079803185e01e50049007240c2d0b2444514007400e94424000024980881da500488551400f40e28042042450700da0f51584485020514820300303008555440d07000c20a074500c1502c0440416522003030300d140000004089039900702035810450001410344051000036000030b81c2c0402059048000c4241d282035042860854140308108003c4c1847d1502c2000000d002241c01800c48480d41401b5440c0d0307160a1010740a44203008100398081c1c0340c10200032442a44a00d0401d01c0015004040d01c41d21a9000300e075601c050003070034180e156205000400c01071400c1d80201c2ea8000c101c1c0303001c015483c0c4111040f0103580e45a080380030190031111006000c1071340a5240408c07007804400401884940c20040740c2040b2604d1041d10f0050740315000441951034220001d0013a00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 651477598 1250 651476348 651476383
    0x341211060901060609080a08041a0c011803110c03061801021213030e03070b2703010905150c0a090e0a090203100b0108010e0411130b0604030308040b36 67
    0xd003240d01d041c001d0029000b004045507403420080341da0741000580c0c1041581c094a501d24040c1400c074000b100c00401c03203852521800030030031800c440f0302c2030054032000c1d0070000094030f400c28035180207409040070066140c1c840d0702c00480e0088660700002e5042c2c101c070400386115203610007151168060710842005411140f101030a0000340a1018184a074030350183c0d80c0c10320645119010103071220017074030808bc014402484000382c50b08403c105150f1507044105404040c044800100b401d40d00c07100d405440d96001421030841882c18064807561054081841d0740c58030a1001001e04004c4007809200c044100c15000250144181e51207000600d80040498402110481d20140a00100381035180007030444800091181c1020160781d0040307602160803a0031a400d042404100940035002d1345030252610b0070303412540c90b88001000514020f650318a402d24040c14101001031001d03019480e080c2c00d0341030447e01020a03451a00d207444194609a90780e400400b05589440c142113403101040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 651478848 1250 651477598 651477601
    0x60102101a031b030601060e01020304030b070c11061e0304020312070b0a0c0504050d03081906090e060903030c03130804152a0b0c0706020f030106020334121106 71
    0xd0a400c40d8010344500450484030140c0d007003d03c0020411100400365015844000107000b0175004000c0400c4024040c41100d0a003580d0b9160aa4914425a4250f02040500d4602000c3c001000507521b00f2480075122240b500302d04564500001c000c1e1080c0603a035803c00300108046550600240421001c0c1c1074000d40c403070728581894a04114240c412142103807030104070005440c010000c0c1c40407103400800641c400d0f03000d41ca0544139800b00820b4a10850b0321503d4520313425100d0b11601028161170304001822001880440c0d10380351014001201c5540284204042810040c0849600242c0b0b14a03100302e074109403506060b64040c42e0400c030030301100c00045400007a0700c101c1d40302009050b01d09056004141c1c2044150004400710f000d032603809480e00017590074284800808001d031042000614145040841041542081e001000140c00003d0320380b20000070340304120100408016500180c0700c828030210740200c0301400080c940e4440c605050040f60141441d145042d0440095235104d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 651480098 1250 651478848 651478871
    0xe0c0306070305060109080a0f0807030210090501020d15120f052e0501241409040e0703030201050f0112020d030c1401060e090a1106090d020604060302030103020a09111206010210 79
    0x150808442d205d0004060040c001100600000d0380301c05940c00250400344c201464560b000c20350b0110368290198498a400d4103a00c0c0054400c6291382e500450006131100c4504c0400020b03506080070041d2005034650041c045041099030710003070030382d00c1127074000d6681d500c0c0340050800118000c1301075441e9070020141380c020300325004100f07a20006030f0100203681e00c40103000c101c074140810012218846000140030f003030003001e007076940d0403002441600348202c010000d01581d507200d94911441d0465a0100101034090184a40002c003403410401c6640c1400c00c079107280300880314081e11a0305c1805200c000e140c00b40d03200c000e80640200c039a103c1d0701c40c1c10b8243c0f07010300b2491003280c0c11440d00b4400280070f5000401d42c040c01c070380c0c8080e41045116201040100e16000402015031040700084d1040040e9610401040204040d80b80907889602d580100102002c2030782c005084030b4204003d282030304c040e51049803d48050040c005219454020040340f400f1a001c02801341c0da03240c28050030342c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 651481348 1250 651480098 651480101
    0x20a02030f1b030304110406060f17040201030e24010609121704090e1c0e0a03110f040203090d080c070b0601080a0b030102030108150a0b011b14030a0f1709100e0c03060703 76
    0xf00006c0648040c0020ba90b1190308413180c90345195028006036071101040c40c62104403840750380003401490080389401030072895a08203241428085040c5103050300548182221760051401884681401c505443c6410300454086090f110010140c600d90884c400c9026020002c1e2000b52000003010060700c91628590b540e2540101c043c0c205104100506a62a503c5003414440440002e031603000c10070b2030365440e1141c03030103190701c0540d00030070258892a4544451018503c82d9502c440100403500d0a038401801ca0354003c0c040c2808c18400b000040c021903507030011140c2090080c80c0c403084a9035180c5000c4000e010180800394154000000020211300026504d442c04903804040c0c64680c507440204411107100711951408140b00342c07201d4181040c040b581080381f5000301c11014500034280429030540e4010310324680030480c154494815980d01904114816166460451080c182051419035903180210881c0c01d15490f40b450f282c420105200b02504460058116480c40c20031110160 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 651482598 1250 651481348 651481373
    0x8040e1005040f0642030605090702060915191a151303120215010e1b280e04090f03031803050d02030604021911010c03020a02030f1b030304 62
    0x14400c50515011030f80703601903445120708035568000740b200c81681003d40854881008607145951071052004039001e10b09014510122290340e0b81c0001d81e440c24541041992100503254004560115041201103400060b41e0300b0031901c548214415683c5a40d4807582018ac081c0d101c0203070300d0905409141310720400d060300120500c00c684040709a030001c5100f141c1c3d4050b004070524405c082c0c1e1801c01c0070880ba8800461030090078410780c3c6e441d0031100941415102e0030380c04103655003140c10070000c100c0070ac1001003050340a00c40b851032810030040c50760710100c4c10403607006405c003200980910030603015494072500701c14094001d001c00b082c907080c41901c3c0509054158046802e040310340341c407040100492200907500d52110350130103104136031240c001e4200070401b5420650030002010b2903202000c0388190601c2c250381d6001007400c0d0013182030039152010940c106041c014030580040b02d4000c02034864460a40e00a1501e9145140940000002001840c20540000414401408800c48504 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 651483848 1250 651482598 651482609
    0xa020a03020708010c050f03070c080417070e07120b0f0a0603051b0c07090209040f05010b031e01140d02030319050415020303010b0f07151125030e0d08040e10 70
    0x540b4503a0761005050300b03039003030b40302c0c0040025001c00455800c40403a0f40a150002100d25080c03908024a40e501c80032980a034000500c01801004c000401d2582008004040c0c182001c203c4060709101101401282e8029820491580c50300030562940c0c4590500320b091400081c103071108203035100c0d0040e00070f040984501400d20109800c0c1c2c1c601c03004d0481210200070740c0c41d0042c60032600d0b0000550083d08000e022a9015440c2c180c5040400c0e0300307001d41400391082d081196900c0c103000701d0410b0415100c510844054a20000402030030340902c08001159100b5a030010518405100003402c522590000e00d407a0f104440c41c01c4162680070020700250341e2101d84040011240940590340c2c0c2c0000d100c1c0089111082100c0c120200d8014094a1100c2c402d80021310040c007180c410340c0c107441200c0706030801071101154a54250b5005e0754440b0503148198a0040360405a44004125400101d0514060480d41e80210308103c0003100312401810342c050461007500380409448182145071060 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 651485098 1250 651483848 651483853
    0xd09061e06051807050a020a020d1a1008100e010b0d050c13020c03090d0609061b0e040218101e170109050907060f030b190305061b03040618080a020a0302 68
    0x100b40c60620350600400380038896545490741e03440c0c1034210381544c003907000d60045000b06407415006231521285a911603203d01e480c481c090060349103151003d44011f001d06204030103071104000c80354010030f184800c481400c1c004903520381e0383d00026001d000899480e0b60811401010a804c0c0b01d00469880741252003240c03003030f00448010040400303900036401e004201c4d41040100a005291142d80710990911401000c074900d03400392200000c4410301300e18210120b00c400441003055a124404201c65401107500b141040800c1032088122000b062034280614141c80100b14250b0103100360b040c4041108100d00c03a02654800010050b418003050307441900c4080e0008542c0014a02034203200b40e440000030b01216251660860b4040001c0b0302034800d1540d03614126005031101c0142511500e1100c2c00f41101c0d034914036001e850700308010710b02001103403104007040c5030b0150002140e07001908950040b130070700216061580482d8208038000c7c102c000000b5240c1c0450f801103089a24107019400303 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 651486348 1250 651485098 651485111
    0x9020301150503041226040c0501090506070c0b1323031e0c010f140c01020301051503100e0c0d060311120d0906050d0e06040f0b070f140d09061e 64
    0x40c0d0301c0340020b1350010210034042244900742c510902d5a51a0351604400b16072440711903011640684405460a8483e1000f590042c055941c0008141009203026036070240740c4003064a0348254400c1074050b0a040000c0003a07404001e42c4251741800c00313040031039900c103006442030714080c4000125601d258000d000d41000012503c00c040d0001000e45080406030000d02d0a0700e004588440200c08040c051109030f01101c0b01c0c501042010b070055040203c00165a9410070080029205201c0c02c41e0040751400c104221404220039514400c54080c034204485503201c1e9108070700140504240807002e1032500400105000c0721000081300380070b081c0d40c5122024000c6004a44a0b50b102d50b059000c10001c18041200620443c020501030f01c006c030002070600c11200b00141002400c0e44c081c2d03400070304819000c041c403000110217500690302c0c1c00c1002c06c110540901814021003044801017030322020503043e013106031f0740d0444510f15522480800c06809000440c0303002d0943c0c040c440c2c600916040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 651487598 1250 651486348 651486389
    0x40b040f0306050f10030b131e020108060d1e030e0907030606081f051201020d150f0e07080a0b010c0218010f0b0301030209060405180a050d080609040c0b03060d0c09020301 76
    0xc4c40c0d0060039000c810031074950035134981500d071100190103840c17200001500035004c107590880040d6004a05064124021498000100000300280c03800e4410060641c408000450502c2000c4801400e030b4070705640ca4203142810745140c1e0304280c40315041016441040302d5581d040e0300c64001d641c06619807092540b06c69640907900000408a402c00041000c130078040307480c00582103049504400c0c0003501c0d0290001d486401c4d2454070f14200345045000e03106000002e409408400640414519441d6500c0c00000c000c20701440500510030490b80e48440301e280341d20500207401d41c603401030050f41c8800241c3d02d070444003900274401c5841001e099000410361080756000c9030304983d0010054000c5440300010440109405080328140e1000a48200503035501441015140c1c5d000d18040d2000d1204010081c1944400901451103050100100400140c040070706501307a8906040e5251a5598040400d03491840f0040150074048010400603402c00c6540003941640c114410702100d141700748 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 651488848 1250 651487598 651487621
    0x809010c020601050411071403071a0f07080c190f03060603230c040f03110a12150e121c0606020a0308040f06020d050f06090f1e060402040b040f030605 67
    0x20a00300c0140c00c158010810752410350491034104604103480d80c42c00315a07544003440348081c031080045036080841d07044284104907000015640700717078142e590140b80020090100c1c01c0d00800f041e00303001c8554081440503002c1d5094404412480c5180c4041032510180070b811180680d018400085c1810000b1584500c039000d042c005000301c0b000252119540082950300d550000d22010407040248000920340b0202c2e071800c00250300845240c0c40c40174115050103c42001a04449a00d586802940000a104d0f40401c50342170194140040c0c00f5031240d84035810401c241e161403010704000728204800301c5070003081c4944421138840030800c2c42c0da6041e050340c5915003440d001d00441d45210000d0080341e506045000032a03c0350300018a05258400c1c2d05007110015039000c5000e04400040181500304090043e810580b101007142562400240803860075a034035108040342000b220114085031902d4064501402c1c50183d060348a0391234110756110400340c1d110075a0b2940c20000480c80c0d04124 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 651490098 1250 651488848 651488861
    0x1403070f15080606070501060e1902041503021804060807050108150f101806052205030309060703031404050f060c0c211c020a030c053c040b0a080901 66
    0x21005205000070051000c1e21090001402207810140800141c3d00081c800c1c490300d0003808254030090038608108802c1c4180c003c003002011459481040103104007100c50386011540030480c81c016079114940140b00d1a82990a0001038100d4101000403944030070209029044c0c0b0820b0b602c0c540c03590380d01904001840341d854075807038111001c0111400710717040240680388480301e04e0410307241c1c07081c000a44030800605903101100003200490740f005000400f07640d5448403c09920604240d030b041c01c000a44a10540745040d01c5084c002907540c0c03c042c0a508910400c0c013071002214a1440e140c10001d480e41c40c038208420240c00394500140350352a0b00d8082d140f0311705030328005110900b1800402001d40384581c1030712660440a108480110400c090341d80181712940c0005031719007980c80300150a5401c000302010601c4414003c500f50703000b06203000e10f03034500e044141e00c007043c222500800c4441c048414007940c1c1d01d40010007040c2545801d0052802c181c0700d546115855a82000d05800c071100c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 651491348 1250 651490098 651490109
    0x709050f0108041a130b0108010c1412180a02031005070f020d051c0b033f0f09060417071e03200609040204030302060a060e010f030803040503090a1403070f 69
    0x1c03245500103516160134429940125503000c01d400154241d2922880d11500b40e00a01803a174403601e420040940c8024400e60690020a000d82403007410300300c60b138403000024803082c000f08130815803040e5040104a030f4540c15801070103440140308004a40030140404485101c04241040b0ba01542c0d0b9100194201c107800b03469407078504001c8000d01d09071503d0544024445160389400d040015036805000c005100e80491074484180581c9080094a07408503900340754040701c4500842d00c00d440d08600726500341e401c0c020b502ea030341e01c030450020b8490700441e08980101c10700880c440e5074400700058120195440000b1b0300301c0e07040309841a40304140306808018251018040c51b20020b03002d503c1390911003000201158109104100410101d800503131080e0b005a00c040e0510011050512858001d070040518082d120741c1042c0180701004024407004054100000004050050030320642e9491070004103015030349a0764071045100e040c40300020302d00c01e0190103030000c0e4401402c45079004860 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 651492598 1250 651491348 651491363
    0xf0b0301150804030c2001030507080c160609080403082521030603141623090c0403080d0501031406040c1505070503220b09030c09060103020c060709050f010804 71
    0x12001c4100e40451000d00300b242801369100032080011b004048070540f02d545400140907071080440010300350b81b40509014144100a4280324002c40400101c07000c69940301903100071425145400b07070041801d280302802c0c8010100b1b011041012000041200c540c0c02180c40c1440c680030611444c860405200003009480a8820094810b141e90000f03841e20b441801c0c000f072000d40d607032104071902d02010202c3c3d426401c03011400c01c0d8103d00b80c0505000c0c1c1a1000b01c585004030007520403102924001501c2d11443c030010010301000d15507821a400340d50b000030800c0d1201031f4040d079040588001e00040750f205082c440705075643c03180007405c28442c6070041c41104e1348610301001c4815aa4020b5611020004200041404a08108002c0615035100c0b4200004481c80300c0c049018100700d90400040c6140800450300382e5900054070b800555000c980000c1c4c19140c80f80103030002d101d0040524081d000310303420021000c1e048402d6600300c0d4420384101102030390720001140d5601c01194000c006a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 651493848 1250 651492598 651492629
    0x90b040b1602192402060415020f04092322140c064006030b040e0f0d0e0a0506030109020d0209180103021003090308070c02030c0d0501060f0b0301 65
    0x210101e1050114440c000b401890119105410200d9140019008145880800b007101c496113820710714000566440381c4080c3c0030f24200350341c81086030004202a500220740104002c0001e045210440f0010300101008000c2c0724200c0110f15030340f1040003216000c003c810381c0007a0318080040d02c50206c860620300030305500b07441036480c84d90252000c00440c103548039910100c88180c07a5403000f4458004100c0b008202911420202880403200300d8101d00200300c124180c940e0b40303503c050303000305440355403d010841010176400301700180f01e00f1034000d000341700715003910601ca01d0105550921118aa4400440c510f44005001c0c0341006449000d0b0020340800040043c1102c55000c1e00c43d0b08c041c550013515140f002c00019109a286400510000c66904010404c5150034140420941e11070304060200c03e1094a01400c40c140040c9090305106071400b541003196000d1205082d8500c0c000d2107600d5050450078194000c010600924100400050000c295019010140d904803030403001e0300e5960 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 651495098 1250 651493848 651493867
    0x60f0813021e13020c16080307120c0821010501030e030403060b18010e101d06120a1704090e0307050a021306090203040f0203160302011b1401021603090b040b 70
    0x3803101482d8070340b501208400c68074080ea41c0303081034640807041031405170f114056290b0842c140740e4455290041c48045500401a24101009071003003181c101034094024110403e00355214002e0020052070300000045050811040c00b604009a24288001603005da07240c00054040b18005170340c0048076802800108005103498000f43c1d1842c0019203140d01c0042d1600c9234802c0c64000f0381202620030050003c0003030038510301341030300000d0520988106500342c840048400c0408054400ba01886401441b80d9a80008120b420360040c1d00802520000c04101e1194507103801c80c0c00313519052070908030b6000f00302c0000030550f15010740150180800d00e80e075508001d2204030402e104020642c4441c0009a201c1843c4099442030f0701440190018400380e10406040c60b071100b80d894103c00790f0380030900260340e010740951019184440e80b4420a141c50805103d00030182e00e10a10710341c00010001c0c252a400c4080300301e603600c02d48441c582207032940c00e01d4003075001d103025501410034144920f548 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 651496348 1250 651495098 651495109
    0x6040b091609050603071112030c0306060a02011b05090f0d170a090f0b040501090603090506160e19080c01091a090402210711031201030807050304080610060f081302 73
    0x1e1074081400d2070308001d590b900100e44950000c859035404103c0b0000008040e000074420101d880940c5555580f6610300f071580507103d80000fa08240c0a1034021811154490003540301007481805d24520701740015060700000c0441c0d01a0100c107000d480707a004002101e0800b901031a140c03503404040940700d5140742160000c69040320500070104580c010000403991442060316020380309055110750350340d081000141c50035450340d10200415141c965a800420408265503070083e808080021080700d034045e00b210f2401c0071410b0303280d0007080d6004080b141d4010403a140e003154842c000b030301c03540d800402c015103419001d4402d80b40b0038190151006c40b1500b124004000004000f0001404d04058000100301d40c0001000d810105c0400e10a10510303941080350720310001c4808004620348401001242e1140708184001081c85001180c00410480e0510603140605126811110746241280600000504134854400481e040d0313180328007078920805403203120340e0043c038058183c10f01ca1390070f111 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 651497598 1250 651496348 651496381
    0x30a02130b0d120302031b042301051e0706050610020712020a0e0a0506120c010504030609020604030b070206010311030d0c0209100f060306051903020f1512071706040b09 75
    0x15800b00c8408606000103032840303010305400754203a80c010788034a480d540149403e82c03080c0c400765201900344002c200781e041000b400761890014100120083c0b41d036a00582e61400392014240c820445c014885584100e648068480303580540014030a41c1c60b07440a01008054540441c030040c0c0044000348880c2c04e1103501c4104044c809885514215070b5420f4990794048290f40d408407041e150703014450549010b00d4140705480301440545400d200d0600060042d1040e0b00c802041c66454078802410f568407003059400454000803810f8140c40d106c40001c0d00c54601340001c850b10500c444c02c941e01400c000550105ca00101c0d03d585140750413507020820a500c2c014007800d10759072814004101e941d409140c102c003e00d91602c001c10994144810040c902c103402c40151101100800c080004d81d0b40c565107118589800e4030170128560a03034410110b0f03489443c0e8a14004080002403020340e643c4110300c80130f505110308810311b103600c40c03038200002d6808940c400e03640803007500c0218544204809010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 651498848 1250 651497598 651497621
    0x2090609061b060a090b060910060e040e011112010906140f1309030315050121020717031009140f07050c0703021c0201091a04060e0f090a06080705030a0213 69
    0xc4041555550348240f0f441c02c215141c44d20300352102c0042040042c10000796810000c00c6803c1000e41c60502842e4941030600c2c45600308000d1001480c0e282900c0d29848074000a0241d80240403842c1c1034203901c1d40d00ea001c000c074041d544050900005503040e003403081205483e000700785166005001800c001c070a0800e510060b510044041d0300b60340d01212441400a00c0d807103030b24041070317235083c06848802e0344d103590b4801d41c1486811200440803505104001c3d0b03d011500710b0050310307841c0c0703428400c0149940540075030000b01c002040c40343d65039402c500d410481d00703407203000d001c0c00441c42540048550b056450b10031903506000810045806040502841c41c030043c11101c0e000d42ea0380010385003148400c800044038041c4409a01035583c09802c1901814040001c00d12420f281c00d01813405100b2881500100120420621080e696014075505010002000d14032030b0308001c01440e004001500c03a01d03a4610610600080d142000b14500c1199500103100802e09041d00141c54058452149003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 651500098 1250 651498848 651498877
    0xe0604060905090f01050703090f0f1a090106240509010e1309030c02330d09141e011109120c06040b03180a1218080102030a15090209060906 62
    0x11070300c02a070307110346845904034000900c1521004085035003110303000f80284007058280082d05020a07040380c211100954860b0203039200480b10700b07040b43d04400341c00c000c1d81c400e00e4070340508c06105015041142610913125030081205480c0a1501c0000e04019000f8081942840354509c0381d8040c8004c410300c140050321511035961184022400c0340e000a00880116030305140800039400e1104006084003030100c48a17040c05690151100c400c00c0500e4a5442101d000036000c9141d103203030f0020614140d00042040c40410705800041d00c1e01c070300313000383d441c0603c075564021964103050080b07101900110b0b941c02d180041482c107010280308580b4038006544030b2039100d210241c442c140140010401480c02d03d40b2402c01c0350292a0005d081d080c1c5601590000c019440840c0c0707002c40c034402898030341c10b01010400c035651840029043ca80e01040c0c1a5101104004802d0f020341c0007540344041c2102c01440d96030301c039410071049019030030710725800c0001407081c0035040c10114010140d07141c0d82e290 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 651501348 1250 651500098 651500111
    0x30507090803040801020a020c0621090309031009020909061501180f090522150207020f03010912200601120515130b0a0b0d022b0506100611070e0604 66
    0x16801e10b19406a0b002290036903000414141d007030f0781400000584030040320003030710b45880c07080040d14103004050034103455005200403a001d15030800823a110104050241e0b52402c90108070324004080d0b901c0e09a00078011f4000240003940082221031051074000c840c06003c5800c0401114a071820b03500c04a810301040c1c10103e810b81a48600300000c0182c21400b2400c0d181690343c0004508880510a84005800c1c0c01c140025104045c0c080240510008c01603c61950b80001503043c200f998080c2c2d0954649620402404034402e10040000401d0704c03003080c00383c0c0350359480301d40340448080988281c20110052240100c481552540315004c1d508403080040750048030f400b88001601c80c8068299a54408400c20800c4650103038000005001040500e2521002c04c9621045c0f00703000b8442c034006900c40888150b43d200030100a151058441000f00240c41e2142da40c03035050f03554440c280c010005c00520a0f214001d4042c003060100080c0c525145031581040703220301c01501095010351980d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 651502598 1250 651501348 651501359
    0x12230304030f08040609050316030210033215010813050102210702010b010e0303071103030c0d1110050705160503161505060402090105040e0a0e0312010e09160603050709 75
    0x2c0250042a005818581e0b541e031404401030408607a50b4006400391b08000801008103001c440d0b2081282c0d015901021464078541040300201010014001c4120072007481c00c1c00070301000c01d101d050801140d0320004a07100e000c000076510798032031201c90025614200260f8075180381c1000d038200e40d104100240c107000140e05888107240304490300100484810b000c0180c041d5090103000487c00d000e0030440354106040004c039449208081026120705402012000144c03010001c0300cac0c0b560021030a65040e40e000b050b00801c10380f820301608600d4403d403a000c400c00001071158601034071468542030700c0c0043d02c5103003150050000106440d81e00042c004020302c4070f00c240300f0030f20300c5110f2020701500c0081005000704a810240c00c40d40946d03c148074034126640c01c0f01c110703825540c410b0907130f442e9503441484c200060006d496445006000100e192141084018503c41c1616980e003a95003440c0e41e890092503542c4a0700f50014205503850030100400b500030360103140c0101481c5001002c40c3d4460 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 651503848 1250 651502598 651502613
    0x5100b07020103020f0d0204062d0f0f0c17041404020405012703050a0c180506010207060c0501061203031512051002090d05060408030108010c0806060417071205070501091223030403 80
    0x271790001010409801410701c1c042d0003004010300014800c40e03003103030000583c40b008103150300a42180c41030101031070050070700341c2c0682590741040e035200d60401c0d00018018441009600117100c0c41000e60b02c811410140d0740742c10300a85050303c0040e9070742c440a804072404076000315125075503101c000c011284040301291050044261641c0200010400d10f40341034946a4105c0b58403401d10740e0685000e0502c100341e0390100d40b0300308450081ca800c00c00da80751410142c0c01850380381d00c846c1c03071144540d1440e410590181c00c5090030801c1080c0340360f0107560318091141c04d035001d45001821900001540e011103102540901010b010103010b0243c4043c140d44c880349031103010b6030207503542d00000c0010407080ca02402015811196490405807605060002c692980900d001d800465980c810540301e601e001080348400506c3c43c4903010380401c0b0b0a05186440b19a0381c06514001080da43c00401e00e9003001c400340310001d9014280100301e6907440400c0e080460308110141850008020000116204 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 651505098 1250 651503848 651503857
    0x105010306020a1b0c0501050a05130e010503240c07060906091a0615040302120115060c0c05011403040f21021b2706131d0105100b07020103020f0d02 66
    0x80c5401070707480c0e040403005070695101e0689004d2400e419805140007442058008013110001c0c2032035510780c0c048400644690041c5c0b0038007a038510700d101000444014000d8070a048440c01d50940f01c1c0c0703240140c400b03902c11500c4a2415800100c00700490702c2642090010035600e800b610300001c8441582e82c0e0b00041d90003030a03041d102a2800d4030001c00c8020305101c1c054004204445002d010740d4000200c000500071840041d01c5901040c3c01c50000103030a410203412040d100309909400354441c3d2025042210381c0310300391107845c414030002c81d0382d50080000134185600400f131941155500e90341c1181e1070380c0d2214115038450030300b0708900e01101031100360040034801c0d0700a0040907540c043d200c0d00072000200034030710404802c000000750421440504507001500c10111520359140808540d881c0580390040324114500202c00e00c2da92003480c000b00103040e0980084c4115203031588940d040e80054006c281c2c0040c420410180158041e0303008000e003030b090004082c02c1c4810300c503180003260403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 651506348 1250 651505098 651505103
    0x5070206280c0f03060806060112020304050a05060f0103060f05010e0a0b010210020a032909040213140f07021b0f042403060b01020601090e06040303180c080d0e2403040f0501050103 80
    0x143e00e8039003001c4d05406244054040e6500400301c0f454400c0000300046208054102c04a03070010114080c04400e004410841c0d0b0800b04a80190800202d000d401490920080d6000c80c5130281038603070500070340034082c104e0304810382401c030a071582c001c0e05002303040184000d41580701e000650500441c0300e00190210302d1031900c0000303c070740c210a8900a0031642c0c18022401c007440c008400503640d2411040c58020781c0544810a8064144503444011300d40ca9503140c00c8100100208030000c01150b0030380744540c8890b801d503010740010050503280c0a4840501d680d01100c1002c4d84070060609a1008141101c840c011014110800901c08044c40c8140c101b40c0e00b194913210700c2000341d40c0402410f40140861a020070007039480d0050307640c0f1200040c000508050701c8008070f02d002080140c8c20180a60420a03444000780d4170406180e84210402d468004a014560400303818904821860345040b14000040c1c3c5041400c661490301c1c4e40010012142440780c1c00981c03011410903c01c40e8060751 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 651507598 1250 651506348 651506357
    0x319050408100b061b070f09091104050907060f1211071a070c060b0a0b030702101b02070b0c01090f0f020301050105040515091b070b010f060305070206280c 69
    0x905007803100c0c1c180b020708911103a00c5420010074118035183c2c001262070810b0324117041c0215604244840e420281c5903030208090701c01c0c1d14000704507042d44c2d0b44045150303482000540d16481019083c0401d0703a204132100369480d000b084003000501c0c010060b03150140300d503240441c03a0388071003400303201100d10703801d0800001c0a003c114003040100f03098a401c0d600c91103138071240721881c2c003000041039001500d8006042c02d4880015503845c0d26030750811000340040c0d40c2c443e03480e4030384031500a6a420b8014000d503d058100411564401f401648540b07518000303602508a050400740201d600d544020384164541d9a10354120303020a02c0a51403564140c850b5141d1288540076004050035200d060304074500ca6031a080030b001c82406450a0301107514410b8a800d61669034001c0140d03102007a00311825008200054000200060b884d19581a64010304003000e01c2134035020204c01300c440c12074011016a00500200b048074400074a58090a030f090300c1c1c12104800d5164803101600c0b40c0c10031100104 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 651508848 1250 651507598 651507607
    0x3080a15081c03050c18061e0c010f0501121415040f03080601081611010b0901120303060b090607170906040f05030f0f0613020a050d030512090607020618031905 71
    0xd402061010360301e0700f80760034015400c2441c0d21403003910030440c41103803080e030f8041c0c61580354a501095481e43d41d50644600306c08407411a808030198040d9803c9078042d46804141705002c0c1c0d0a22529042c0e0348039587e0304d402e41c862591080340e070702e00f54040c0b10305c07510805103041103040f0629003651243d4481c0350605000e00d4a0303e0003401400d40600900e050001c8030b41080000c03480780c055440382481030b1030001907107598141068014070801190079000305071074002080c0e0241e5880640c8407a8800e5804100803039481b290032145020340411594841030400500d00851641e0701d841c404206001905882c2c04141c0340024815401540101c4540f240c0f14010003035481c05028940303032481c0c4000503000d0311000c04500707074503114010940a10601c1501c000c800359100c0c810044007030000506104600101410090920b400c40d0040401a101e02400600011001702c1c41364011003080d00100321a4446000d28400041e80e141401107510040c010003520195541d001c8801d4080b40d100c8660340c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 651510098 1250 651508848 651508873
    0x30703150213090633080a021803060405160e22230c0109050111122b050a050c040f0e04020d06091101270e090c120c0118060c03080a1508 61
    0x8040b04061010301603200034036608aa1a00b01c82251f074410342929005940b40100b200115a000000b00681c2d010310508040008201d00007079025111010f800288a6581ea02c0781c8034642400112210411188403040c038901d030b20305000c810301c0c1c4244a8400608504400d00f010030008404034140071065100c0501d0b4101e5581188000e00640402e1070503c0e11081061101a1f40715542984441a03200008200a254240c041c0114003c124201d40d011254113410001003e0042910a01c0c1e4075450300010544080d100c4044408a42d02d150399001828078201c4d985400f900b0003030043e030b0009030402c8058009001c0744901ca0315548280500e4004d101c1700720004217500d0107007003070045466100940c0c0d490300110340a00021549000c8803440241d0303529821601f0007810b8401d503600401c071070907020000e1002141c0041007190030390325983c801d001a56140d414920520034400490510144040402e02c92040c02c0e501c2a415400440c0802c2c4101f03030f8070a01d1200760701c0300d2080d82017568003c40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 651511348 1250 651510098 651510149
    0x6091f152102190b1209070f090204091119080c130e0907060f200705030a0b01090c1806030c1403072c09010e070c050d031a0307031502130906 63
    0x107140d41c3d030315040e45901d03007818000619403052840c41d942090f02c3c40c0c0007540d0f00500300a5140500540c40d1040003c550b0340d40e216001e90054060841030358148881c0692030000101616044101d1801e040c4451200e40340540c0c909001501c81d03100411308100181820080680c03c1c00141f00f2070001d26580d2802d00c5006040900301d0308640d003080050325080010782e51042154108446030001d2407480d207040f01e41c00d4034100c09940095011700030580c07003409000a445800d8125128488144006401a8012a405503001041e000c0c8448038020074032810748280d00c01d01c1068100d0904140c10200015064030b20b82040702d00d4000101202d001740841c0010100d074440c0c6904200c0e801d1102110080001c040500c14040c030384a4203078500000e41d1044c0316503040f8a4860304102a22000c411955000380901048030403031200d10704240401d900c9040c00100003080343d40058041d4607055000c8030f80c0000e54020880102c82002c0c0c8240071036840541d1060700d0081c8045000c51030407005500418a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 651512598 1250 651511348 651511369
    0x1e0904061d07021501090f241a070203061b071709040605041109061e03010e04030806100806040209061201090504020a0f030f0803070c0609110306091f152102 70
    0x20464004148a56884d0080480c1d1415244060317000b0880b80c500410701d00003000701c03041e180c03003001084081174800345072003a2000640300c5000d172860b8024019003240000e440f80200094140d88030000003052920007246c20070100307000c0c1c114645002c51319219540310001da80440c161502c0c0003d0485c0182c0341078410140180000e550501c100c180410850026014030000e245c003801c8000344004030041c500c44110040d03080d03000c40603285d5840d200041002c0100301c904801103601c14000c1101803500d0003a81d402b680940c0c1da0500070750394002c2448040c6d000558110342080c814400000c030718801c0f81c14240a805100400210f85c9081c1c01080a00d10181d40442ea0702100b0702000c0c4042107490400c80310782600869110b40d0303030303c0394941103c1c0c0556000010b4004c40c034103403002c4200011100080f0401d44110100d07051510340381c00154850600e580c0b42076181204440070b00d0359075159084031041000032184060029910030760700400703401001e0b0f010204008001d4500440c0742011440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 651513848 1250 651512598 651512611
    0x11120d030f180f061104120c06020709020306032116030503060405070c2d020411030f180c120a0b090a1b030803060d170a0509120f031e0904061d 64
    0x203242040b1640340c40210000020010740a40e4540a0700465148018104c03030040002c1189003842240a041401c24200e00e8001c51380140145000001d581c580e600036240038078002009001d405001854948450360304000c035608000e410311007036900c0201c02c001c1088850180d107501341d49107400000c0004451000f8240e405100d0075228583c0400c030394181000c60549020701c145590352a0030001100d1b0300341c005009520900b8200b8a0740c0c40810300000d540140d070040d4030341001c2d4444445050942000e07000780e03507084d0700c00700c0c6030b650600d03140d0030140052402d1400e8807080c5626848480c8450022241100903610a00500e0f00b08640902400c0300403844040112100b42160b0321a5a01c4c403000d00b0052140319000068020311111101034058400d090016a50751140c060380035000e500144130b054826215007005902004012550180c42e42c444c001451400b1401c001300410071250501c0704c0c80790102400319100549a900c10348029200d07818000614226601c00a10959001040c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 651515098 1250 651513848 651513881
    0x1009090b060a020a080a090f060906021e1209040f050a0603020108100f0b0d0e01090c1404050606040504152c1f0303050c0a02041103010f080f0a11120d030f 69
    0x844003030f5010590b10901d5034800b07041030b0340345000c141c202e0310745032190002c04050680c25400a40c0c070b40c0201a08045660035020b8a8000c0b01d41c2e1001c030342100c40e40844a44d2a00300d000d03401c2c007504002000704190b090090000901038100e0401c60201c0c0c504482d515413039031761060244103640c1c01a43c1154411484805903103602d050290b008460019840f428000d0000860405500e0301e1507000b40741861005802004504958246a106c03815603110b11400c1607401e007070446581c145030188601c80c0e507002e0102880e2500d0241413000038181c4007024815044000b101190941e10702d516044e004101c7c112510200c550101c11401c8000c0181048641c09e1200c1007040e0341031100708402d41141c0c0c040c00d2039611419501145403d10200500c000e5100f0b01c2c2101030311100110030041d606940003030f032a9204250301c0d19185c5a5900084925a02552212100000040350f1240104031508064000b13071403c0110710300030346070401c0d000004011030345070303041e103801410702d03200311504001031184 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 651516348 1250 651515098 651515107
    0x120f040e090a050307020d0c270e39060408010b01020606011d0108040c180203040507090917071a010e15030607142514160b0f0a020a021009090b06 65
    0x20385135540e1181e020000e0190a42032105414008c50f006003800070501e407114404910380309020213580104406c3c00c450541d03d080d40387c841280300080c1500e140c0c1002c900440c01c176001305104e040420455a0100350400300550040c80035101c060103840107088440012a8042000d000a42800c01c0100280e0400500d8015041e040a40311094015036400f82014140ca4840e4213042c54100401d40012841440d01c5031101183d01c1c02e42d0085100f6401581a5001103031074504031016540401c5000d00710300003130f814014048071100000c16000b481040d18109811100c0e4001c078000030264010302c50120120100841c04012080107544c168080f0040d01c03451800b507802518401e52100d2081d5015030108500030910b120340d60200980140c103049522807130302c0e40340a02d0104118142901d05002d98140080003004503120754058401003002c150929518a02d80686500704030100e00c114030600b240c0e14050703160440001d0b026150703a910400982d04152080040e52903955416015100410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 651517598 1250 651516348 651516353
    0x210050402060304021309021c0506010b0304030905190801140133120e0601030b1603050106050a0311090a0b04050f010206270f030f0703080708071d0102120f040e090a 74
    0x1040f254803941c1195501c2c01080990115030051180b2075000350054011060184000e000c1401070080a100c0c2e82165016a04c940d24a1654001aa002404103500460900240c03400e0307040f038100c075110000c1000700250744c1c0b070046080d40c82c502e018022420400e00103104403c1840c519901155040c0c1c0302c20340c0d61400c0303035032184070650f508a181c08101d03d640c48d444170711009400a5130698131150423503249586078100410901030580300b0440c5014540c0d1100a854020700445048031503c0c2c03240d5060000d205020b50103850440c88103c0390b03c00c10172251080d03503600310744d100240c0342c00000c00e51940d050205200c10910030850207819036202508000788542140c01c00c541c105802440058002350740110140f9090041000e03008901003c225402c2d600040800752071030b43d019070b41d60301e110384940c1c4080c0e44054040d00e40900181c0004124896140800f00c405e02085043c4119000d0b007524031011031554116036250054820b00060800407107964404a41d001034110b40a4120a0403a6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 651518848 1250 651517598 651517609
    0xc060e19090b0f030a0507061b0f021507240b06090a05040b03160b09040c0c05060a05071103070804080606040c050d0b03030412030c0605010b2b06080106060206070210050402 77
    0x1c1c800e411619440345002d8569859910709490789a1010b42200c000381caa5140241c0c43c2c03807180c010000092041d183c3d041241420240c8004881e40100d2150340e00722080d02444000143c107a0b060b10482c20030032090340094107103600c01041c0718643c2c0c6004280c00074002d60b81c05840800d81c40c2c9100784003d000460b0540c0d201e00a480c1142d0049034002400750740c590100b814a030110318101b845001403000002e0a107091401000420030466007006840c3c800c060a41d00c003089494060001c0e8006400074406000d170f5800113030402a6400d005050f52949021186142e210602c219078088000c1800c22541404100740c42e000b801c1180c0500564490300002807980c001c21241e0080c480d02c600515550785c900348115805400c4141114584240c0d9080281401003038102c1118a58503150000582c4004d49095941050707040030070041c44a84954401c61540e070030000210459a03800300010800c2c42407299030000c00b013030b401a140501d402880a410204407960107a00701d0f0502c0200401179851 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 651520098 1250 651518848 651518899
    0xb0a030207081603081b0904090c0b122a0f0705100507020309040f06290403050d030902030f0105240109150305160f0f0f170103051e0319080c160c060e 67
    0x1900d00140c07504941c10b1071244804c0b0bc0c0e00681d0020307000a07952040b03203115100d0303070f204110002c0b1401b548a101c3d42c00700000740b1140710011286405210300c1c40030440300c0006102e00e6000b03a040316003115000f413855003154070a840542c0941d000003507000081c1081d00034181100749005042141600d0249100b141e04402c581ca07403040080c202c80c18805100d000155005140c00404643c0394080c0c102b80640200301811083c6d1082c8500c0d0b0030803182040c14094148a100840c100c9003010818071520b02c40342602548503070520610080101d0300c0b50340d405a00d0140034066401003180c0c202146281c1c511401e05060798100489d2895115541da0002140303e4959240d10301040510300d002011565441280314806c080b41c0b8910001061010024420392480001410440e40d41c00f0340c00c4403a92485240400f43c9000c56007042e14191074002c2e064154400301c0b95403a6441c1600c105400d10800b040500d04a5140c540301d402444541d600c5075885001420940d8801006019088015a0810b9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 651521348 1250 651520098 651520117
    0x100504050c0f12011104050109140f120a052a0d2a050d1101020f0307020f091e04050f01140408070b060301110f031b130b0a030207081603081b 63
    0x201c00b01c1510386032102d000918018031258000c0011410450b140c00180e405445041d0000e01c10003400316071030202d008080d42d01b82c2c004050941d0f6403c00e07414405054042240c0100fa8083c41c80901c010030360034000a8040380310710281442d4540959142c035101c0d00b0106155004508404104000401e003407850012002c01040c4002418800c075044031703640801d23800041d00300c240584000c080201d14000b03601101002d8090f1910f11a200381c0d281c0d030724050690082c0d48031002c581d1440040c01e056044a8101c0d090800280036080c000307440c451144015a01100e0ba0391005c4040b4190000038880d610030891004072203642801c0c191590b42d500d008030b00000e4590300f004c0c030104902c0d98003540054500d01c42d1140c51901d60310701e00d1a071200384d00100c0e400d141e046c0e0086101b41e48803050004407a0942a10880e0001c103c0c1402102103a0740c0200d07080c00d0601d9820049540800c0302d100180c000031a5103907680d00021703100e140080100b0006450414020840e44040071010b8010f03059030b91801 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 651522598 1250 651521348 651521359
    0x210103021c0f1a0405010e0610050f15121e0112080306181608090105040309120f0b040b180109020102030a0311120718080c0a030f140d11100504050c 66
    0x1d07014100000500030004004000c54903548080400811040d42940300d54061402042009084211a525080215070180c0c0e11000a1428451440c001100309161200500703011901c100e03410904d00b4540c4401c1d0100b050410800801c0724610400b00030075099480300e00400d030b055241504000c910f03210004010080400400065019122107280c040d8642181030010b07005d08000c200241221107150000c000100101c0c005080c90005000e110700a0b64103584540000b45041600c01214102480854024800400b081d000c1100f2110391401280160542c113568140a11003a025044502c0030305030342e90410340703a100581c0c0c011040e152441c50508010900b8844082c00840602c40d00c400303e541610000c041c0000550b0100b495589400d0825a10020301d483e00c1140341d8030340c0c0b4100c03040c1c1c0c0003050003001e00007e02c44141c42c148543c484ca800340c2d510101c0d00c100714180018984100e0003e0b0312405410340c140c2d410480d841d004403609104012509141d15010b8988041e80841030256 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 651523848 1250 651522598 651522649
    0x5090a0207020f180703060905090c09040302120307031401060305240d02031f1518020a05090310050411010e0d02060a0c0f120e0a080c0904060b1521010302 69
    0x1500c0d24030f4080e4a01100030a55a0300344a05811110581425a40000041d25140010403c03024a100d031078040e51840c0000c000744803c480c10003003003e2000704110110301031500b40c010355810000246010707410325200401c40700580c402c0700c0844201640308100b0036043c4000e000c1e84e0903884401907201c0c1420502181507003a484041840c241116000035014402c40011121040c1694128200180c50600500c20821040f0b241c600108040c007440d0482e03904a8019031260340c41c2d90081840d01030a01300b0500b040106400641000000720108070040c0c1c58404000c05c102d081214030140c10006d00b40340d245002c25102284100c0d0b400c0b10001d000e5940028600000e42c02446c1e0315041541c010b4190051000381c0c07804640307034210040040d01058400040340980c0c9821702c003072400d5404000061800c4100341003044215100a0429070f1010343c1c030741203040c15458400c85080d01c2c541c2c032401c065071031569849007001c810300130003c0c11580d4420030050005070f545030800701c81e035404d062406200 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 651525098 1250 651523848 651523853
    0xe0610141b01060f0e090105060103060b031503070f08032122020d06020c0a030e040b0f0906011101060803130f0311060708040506040e0405010e151b0421120905090a0207 75
    0x43c42180c1010b40009082603000074220140b5410703d1003903d000000b1710103911880c00641c1a00c0e180e01071020035403c240002180031110040d90280e954006084401c0c0581e5121081d9040a82e07070000e448a0700002a03050030072410100b0b4410b1042449000405894054480e0700c81d140f40009081440c0202440141959144000044080e0700a20300310340e035195041510341e8603840c00c0803c90200b0a03102d10240c0c107142c103102d07076104100c025007500000d1003c50100060302c0c030000c040c030b4144001d01d201504402c50911540e130190480000841d907910003580d1100745401c036648010707004081060700380001100400c10315001d100c165403164070f4000300e1620304600d004507044150040400306001603160410240240a24001c0000704000c40280d106c060b04c5a100c81500180c1d42c00e2a00130032140d01081c00e000605280840303641e42802c4c0c8403c802012001d40f81801d8a110342d84c0b92204003805450300420400b80c0701130504007551482c22010070300e42940140304403030541d07020580401303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 651526348 1250 651525098 651525101
    0x170a1e0917120a0f080108060402090f0c072003070f0506070b0705041805040308061804020f061b07030b0609071b020402070f030c1b1d0603160e0610141b01 69
    0x318402c0c100b24040e01d42c40018001001d0841090300304000620300030001510302404160240502e4000c0d090943c03990343d80000802000018000240401082204c60040b40594649610389203c902d681c1c00301da030803001054684070640d04034490032081c0b0f400807c895070701d0070215032046070702941c00b01159841d044140c0305400b9945c460481d092440d0703240c0c4400b004513400b681c481e5110341c455003c1c640301c0105105040c40450051706100c2504004a005898852406e07140c3c1000204018074200f180d44281d4103074900428030103000d03803001c1000c0c020082924100d643c05401505d201401c1c1c41d1510000300f044031000700010707894220600141c00c3d9280d640403181d80941214036014000750901d0000c03d098504842500e4205c81184ca54524948080c20103080f24015804c0a442039030b45114a0071a00000d00100d507d44100036009001512603d00040149099030f00e620301e5203070002c01c2c0409e0690941000e030411074411152400484003405941c0e0703d6803240b03010140c0481004c42c190 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 651527598 1250 651526348 651526363
    0x9020a1d0a0b04030b0a18021003112a0f010c09090e0c091e070207080a0803060604030b04030c060b06092214090706120b06030f09010207170a1e0917 66
    0x51440300c00041c00700902c0500030005000740b05a090401020300720082a47c400911400001c0d80454025101c001c0c0c10310903049044001c0014000c21b1070000030724418811128982e030385240c1c1c142c0854140c04400d0041c0001405221810020710620310803420007480100ba40c0503810341540d8681d00100c046100f00b0410211aa02414000d458104414800020000c803040030300c256200031300040200344046200d404030740040c4001d180003509681c1b050440d420003008d098002c42c1c02e01c0000041103c2c0781519000d540651200001d03803040b800c1000941c3c404201450107200100801201510f03404070f104011207541c0540a04060000c1030500540740442c0c500800c0341552061181401e0041070401c200c07002031310f42c0784003111480da06100307880c03100c0300141d440102400056450400300b41016400700300c61000604d854009d0380c400000c00035107000a000c0100111b04074880316003005031880201c0800201c411200d019520040c6801c005002e9400303420307002c644005841e8000c02101 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 651528848 1250 651527598 651527609
    0x5060a020a050114010e090706090b0c0c040f0204080d090e070c0201020a02030708010506130522140a080909090f10020a0e0901080d17151504090c0c050709020a1d0a 73
    0xc3c030450b600320704040d0400c082805601b0300c544c01c40b004180480742c001810720440c0e51644614a0140c586007007899550460a0b02d14190f02031030a05202e00d60b2070744030b1b50901101003100142c445051900380d924141c0c3c04444001805090703e03041c80560004100b95030710002c9481c1c00c0c40101c1072880105d01b0041c0e00007000b9014420800081010801904a1441401c05888191b14440b0b07440b5188155082a01c1e010311088002c03100320344d01c3d46e50126282c081e900503030242c001c11100c800114905003035074070300f5112444046900d00030341c070340042e20076000123030300008102911840032083e40341d49100080400c050f6001400400e264025000002414002800f10f400c2e90394a0a22580700c050804409001030801c01c82c00e80c4074140440005e0080b06c184440007441d404180500101c040c14100d440e224140900c400100020345004034100d840b45543c80400309405480c003285012015004440514018460440360940c0041e6040e8495040c14044841d0b88280001ca189207029030801d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 651530098 1250 651528848 651528851
    0x70c090c0c1e050c0402160f0c080708010c140721030b0d0609021525030c17090315010602121b0703050a1202120a051c060915080c090105060a020a0501 67
    0x40c0c2c841c02c040304000103107240264241c40c50103040b002088224840d8078440f51900403d0800803003c01d1000b8481060b240c42508030032041511104070340c0c5451030039803020b01182e44804089000560088001d40740300b80044403603061002550390b078100400310301c5032b50f108152115a0308131403620039040011107480103862600d13a102b9038100800a00035840050340a44000b1070515051000c400c100d41203405161103031102595518503c145941c02c81a0640400c0203040e12540412080503113954032541c01c2d45115902d01081052508280441104c2214020100010040305401140300070080b149450400da0719043e603101e45850490f18541c1d03030a07902c5500e00100c20450000b64202d64140504820318035054600c00407a80c0302c50550f60070307a48941c1441031245d1580504003510459410a40382c040f944034601c500c0040340c04a521031090507460b5020001c038a2a07010482e03004c3c1c9200c00207014011002c1d0081460081c040c414a40a0302c40003603084403043c420701c042030036143d01000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 651531348 1250 651530098 651530123
    0xf0501092d020109090222060e0f0a080a02060318150114031506040e1c0309031106070e10170c19030608060103021002030c0712020f060c060406050907180c09060203070c090c0c 78
    0x24007c9c010880303220014012011080218118902003100b0003c645d060002003102112960a11540f900042c200380e005030502022802501800c0c4860018904030381003500d00c6603d441c40c4c030880001d007090340c940660410420a5180d03480e20940c20b910603419240858602c1481290f81c0c60488120f020300c2020040843ca200c42540c180c00c10400a030080c1d079400d1040c0103d661180e102c80c0142c03400350104c0d40c3c03a5041c0c009402d006200d10181c0d0760b281844540c0980e0120010002d40080f1000100340c4c0c00019003910740440b500110010303150502c1d0400c07185003490328050340e507281800040c2c4100e8070701d1003c0403258400c0003183d400c010b10506650a060b0340d081d00500040e45030101328070400403020b1191082c1040742c113803821141d0100c0140070546690302c41c00024480640003142e40e000d5484082403c090208000130040c2092100180e03503414030800030211036164205030b0464104200c00c0303000c1401c00c403090058400c001c0000803001c410442c20348056400a00081c151440c03102e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 651532598 1250 651531348 651531359
    0xe07050603010b131a07060f110307080f160801050d0c0f0e040213020c150a06081b040c0806090408180411090108161b0f0501092d020109090222 64
    0x102402081d8915426030304e1068440c3d4600807140109052201090b006000d40008201180c2004024200e08000000c82d0a6041c00200e138680c0125001004109200c0c04d1080790441070030902d5002c0781c0c081001c00110b5221100604505040c444c40d0300c19220b45038001d0034072a100da421002002d0002c08001c0e0565120f010729007418080303405034802c1c01009058890f0b00c4bc14000c5560003515000504010828900e45803211036000c2c20803402c00341d80c0c80020904160411060110340000803000f40c1901041c010001030b07031180811a001c0204038000d000e072640f2410f402a412a034403401c034503182e400e110400d20240741c070306400c541d04c1401d100c20030124a01540c01002d03c18030aa031005016502c204202c1d4245003401c0a10000800310483d186004804610300850300c0c4c410603000000c8010b50b140c15007543c010060590300549024800380407942c00102580c040200070440460703402c802c0d00040c1c021b400f14443c4514080e000181031407490201040c00c01000303c41020004030a032142e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 651533848 1250 651532598 651532619
    0x4060507080906342a0504021c0f0e03070209192a11071a0c0102070c081b010f0e01020c0a08030309070f14010c0305120c0909070e0907030e0705060301 67
    0xf00d02138000000c5590078109545010401d000c6540d002030011642640510110000c08030320040019503020900c00440c556450740010808540754003180d000030701c441d044250444000d68084500b10b49400d5000c921607030044180c030740968048030f00060f181d65a4985034500440c0c0c940385401d0928100750300201c402c080010030031550b45503501216501843c542034503201060000c040304c41c1e00c01601046502c101c078034140e4040340103c040c0c90034002c10414450990f00400012103000b00200c1c41440400e004018011050f40000e05520050f0160400a4503842440e104201000341c00d11500095074001c220721405640080e240326003a030b46d42c0341140e44a400641c0d840c0741c3e60282d00300c005100c80d100310400d0240c6205030004a0041150801901e000400b0380007281802818418480030941c00f200c000c2c401c0d1015010a0303600e09101c400c0061410f4001c7c203030010300005030451481034407080081d0794880344900300000e0110030742c0041807a220b0203900c80359000600000121b01004607 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 651535098 1250 651533848 651533887
    0x9080d090b150d02010215090a0c0b0301030204110a0e0105160b0f04120f020606130e0706020d030b06040605120a1803050903150115120603120c0b0c0f04060507080906 74
    0x80d18807500b0460310305000c1068894020388040d0059000c0000c4882c2c0b01c0c5a0451950840078050444040841c195603034142100c1e1030f4800020000040010020f42c00c15000ba10028020a86401d107010340510000d0309107100c9454480c10081c010411660195160151201c11500401449507911340164400c001c035200f01c40403078003003610a0a400b900c82c012541c907981c2e41c581d500508070381d40c0c6402c00d0006000f2105800c3ca9003a0700c1e541c190018080030f2101d00041c00640d40509924074121307201401f6116640700007801080208004c2000ca41d101054031907038809160022400e85500c83c006014040c41a40030310900c65050608041542090040c0340302c200603016240844082c1c580c40c081c450b001d206200b5600e88646e91112040d204441c10003d40e110a00f0000340903407a40c0b00c1c1c22401c400807413b000801c0440e0141c5c0188135580c0006584540b4500030340d07162000500c80c010480c051881003100344070010420b5020805520240d49c11104041d24603611000c821544050041c038 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 651536348 1250 651535098 651535111
    0x5070b0901091109011d13020d032c060a180b04230904080a0c0c0b032d01140f0604030b090105160e180910090521091309080d090b 58
    0x241d9803e005190700b029032266048880424041e4000700b401e207500c2c424007800030a0084082c9a0019000050381c0b05001e50180e1400399031105981060003464140c0415844800d9050780c5c20350039440e5941c1d592000300c40e506130301481c20801d0840070340d18410b100c00b03454120100c40100402c0104000320048c00303e80c0d585070141100718404000c041030004100f029a03015250b41c0c001c003d4075844502540300c40308864803509400d2605da41e10407080780503800c1910320a0041c0d40020341d2350803041140c0300350700100e1420030140401794509000402201151711081f4000c802c4041d441081703941d240c00782d40080d90854900d1080f441d00200081c000e01040f00c41e440c0391000144481340c218410802540b1402000e4559209000306850790040180e006013011007a1142ca461140080c802d4000c0d01521b52081700104241041150300000040100e1003010b480c14042c02020003aa94040d4000100070303803200000b81541da0f504091708280b103090401820182031420324010458101000c42c441c56 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 651537598 1250 651536348 651536363
    0x30f011e0b0111060f04020a030525080c01080604150f03062f120402060c011b030c0c170a0c0c060f020606040603021008060f120a0c050604080d0e0105070b090109 72
    0x228100019100c80c3c1c02220351140b158051000643c070002d000d0b056940050005000d002d145517039640d81407502e000f9030f8209402e902d10181200e03c40001e035040c44003401e2070f100981031121421000070202c41e40102034510841d21004040d00303c01c10007035840b0145c1044485017010359104e09010002d00f04241c0c14459050400800c50200d1903004040e2151030116180300307240244141060821503030290069034050780410008003100ea09100301e1801c40b05401c0c0c0d00301640201c03080a011a61b200465005002e07166010100203640c800220201001c0c0b9105240c8680e0321070821900c8801600c4018040c2002130b40c04a011170300308041d0440e050007036007100e0b010b80c3d480c0309010644600d848000d400962000503480b415014601403540620044c0c45116071500d0308000172103002131007480c11200c0d00503506020502148400a1018201c20b86074140382070304e0440910359400442003030300308124501d00038202c103a1258046501d1203400503552420b07070030403199241c02440301600803101c04 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 651538848 1250 651537598 651537611
    0x60e0a0605090108040f0c0b160210030c02030f030a11070818031b04181502040e06060a0206041b09050109050a0b0406061211210108100510050d02030f011e 69
    0x30384124222005128183d5a0b0480740d202d964039103d800d4551641228064082c6e200440c02d861170304042d0030f140d030307a01200385244041c50050000c9403030140607d80c101030401050740000d80e000411250f460045043da1940d9075038551a01004020544110b602c50708000303104001e00c03415801400d44490298a541c808811940415968248003220344640040d04007015403103107000d502000050070026110107a151440d9a20318040340aa2100b4064590100b0144480d074882c1c804035a10100c25500b09203046035901000e59903020050008100c07d08040d2000d1003107140001b81c10060180b800148440d58451852a0141000316546601d03189040c2600f410f5240a000d5001107484e10303101c0c120702400318a8000d020f840d0f052116030482c0c004025051048031401d94810500c4008510702d52254140100c10741032034608038085055505003018132600c1403507501404210796045071040e01036a40c910100f82400c2d0900d1804406518058400904040510554503290740303602080115 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 651540098 1250 651538848 651538859
    0x7060201090f1205130801020d1406060d0522030207090c0516030e120f0705030706140a030b0112020d060510180b030901140702150c030637060e0a 65
    0x80301c2420002420510742c50054030045000405049031440407071405500d400704002c60b07400500841c1c1c3c4094456940065148031824092241d861002200c19a00032542460400102e0b58011041d0000c0c8299441c404220607030103400e0560121100c007a07413030b0104022030074041d4503020b4900c1964100d03800c0213480d0b501030748590210b1b403402c0e40b541c1c03518400042d13070b441c1203424404400d000c0350481404035206031003040c104052454005508000c0904a00300300c10315003403810715030040c0148808405a0040b81d84001d080d00d03c4002d00d4900020300300000350040fa500162600000e107903500c0080c041c01c20400a40040042e65030983e207420010b0000c0750211211601c000264585841c0e86d0030500a13023a0403801190400308aa0020070014005589140c0382c1c601521101c0240e4000096000214203d0901c41c2d4803005120301c41c0d0851070075401180400d107007503104110010080c03010b40076400a0002c9a021402c4c3c0b00410b2000c3d07a1540c001900c022043c0030101d124030781c0716200040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 651541348 1250 651540098 651540101
    0xe010605030c16050106051309140c0307060f0207050913020307210b091005011d010b0a0e0d140d020106050103051807060c051c120b18180102041805070207060201 72
    0x1034190b071007200780703400007050401d00d400d601c09000300d0b50741d501c44e10005042d540711498150320b1301c012000080c401c00f0914ac05a0000e544004189981e00500e9100741640da0104103001140c020f41401c4441100b0054224101907694004643c8004000140850000c8100a00034a14800c0d000c03507042075211141e280102403100f008141d1000603403030540003d82c00a02440d04801020111403d020b114030800c07040c3d4400b41c016030003601d200c52882e8a881d003107031803940c010440c1c00f9400b450310b518024020f2030301c6840c1d0001401242d18208202c01c200034a407504c400f64203080183e6458040b0111b00034081d04180c0718983c002810030001c01e402e081e51840325a4070035421001008414580a001d6585601000c403c0e50b05014a071501034224039040440051714017151b03900c00c000910903084c0b034111804d0340c071070383d010740c0701c0c07802008011410a40c1d05411180308904c80940003038001600340644160f0704481c81140741700c0c0b03850311100d1146c4c00c401d004074000d4003603441250b1101800c90 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 651542598 1250 651541348 651541351
    0x20f0903150114060c122215022e0905030405040b09010806070c031205010626072708030f070209010e040b040213141e072d111002040e01060503 64
    0x106480f07929034400f8a40080145440210141a0381300f8108a1941c502180c0229800d41e02a0703032200c034103075905984891484c002e0300a103118000040104030000b981d880f5402d4080703d000c4d100ca020b80f921074849025041a07030303180143c2070040f0303009898090b899412a02c00c49000720700f000072030006840d09020075816203042e003004101030303038940c0000c403030b5040100b4041d014010041468002c0d04034a00815004e07048603110440350381c504064030311280e4460300c204071070014503009000e590341e4025144040910000c004903025040031402040c029129401114940b00003d9041a041404000742c40007034000c43e4200c42503a6a442e81a04020302140d0040c444060400010010301c0c0a440d80c0201403a0b80200040400d002250075460100c103a407000740020300c103000f45001c013a10b440c249070720a8061510300c0107860700c110048078400c1c105200b03446014031040c1e040d4030301e485084040d94141d5201d01701da622041070401e00000358801d0040144820302c50002040da2809481283e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 651543848 1250 651542598 651542609
    0x70f08090a080f030703060b0c03030f011a0315030705030a0b1f08151f060804050f030a1d030109080a1d010c0206030403030207060b060a05090f181810020f09031501 73
    0xc43c03514003641041c0d01c107503000818240506564240101d243e11b1000c2c0a0b204600c3c0c40d4000703542d03e0400b00d00701400180160302002d82c025030711501c00111001030302500e4000900c01c0c140c0c0811010f184c00030307003847c0366a003015415110340d03000d0341d06005d00b4003445402040149230207500004c14081509201030719000d140c516034000411100050107081000d0361019440c0411014100000c10710001c3d0246a4061800a5041c8080c881802400d01080783c04036101d00c019807914069030f9015203220214500400f1052400800300c00b50345082d0002c40f40c0b00d074001c0d1402da4407014500c0240c20350b02005070702c1d5104900e80425410070750090740e900340300e150000e28050461781e03941c1d8102c011390707c9540200c500c15103c582c001296120729002e05100c0965845150306d4001070720520000340b041b02c207654403400c40014a801c0104094242603000070100405c600c2038032034109540e2501010b2920018290b200141308214000c031703000a44911481141a554041c0030909660105002070248 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 651545098 1250 651543848 651543863
    0xe1c061a090f090705040c0f0e09040215091201020316020d02030a02030d0e030c0715030e1c0e0d0f030f030c050a0909021b15040210170c09120303070f08090a 70
    0x32510b8154400600381d8440c8078002214602c903121000305055440d1240c10802140504100c80b859a8011650f010400802e46804405251039000190141e10a14840500000002d030010307180c2c48103881c40142c3c0565500039541e07801d0600c0b00300c14000d0343c1c55207040140649100c100c0402c0c130100403208950101d40c021030602c407440032040000c0c4414141038856107c104040400014244036680017071001864403900c508121402400b031b2000c2402060054010000c407419445200a5903548123500d860700d591041d80c5080452104c0c141c14001400c1c0c0d00d1003110340402c05900415504180d0a01d40d828000c0480c1e018050fa6640038582c00c490110f230441400340808119580600b1f940e0382007044880800390100040ca041180150400c2104180c0d4000c00c02582001c0102100600c847e01d4803039042e140e6004540e00091000d00a62015900000c03494a9035490b459400601d0481405583da40d003071084002d0072001c8010403d2001c940740000103482e001c00405c410305e045030820361 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 651546348 1250 651545098 651545101
    0x90f0c15050d0b0a0914091605010207290f03040303112106060f0a0e030c0a050901091e05090a020a080606060f031e091005010e0103030509060a0e1c061a09 69
    0x781100a8452101c0242d013048001c24001164500da000b54600007004070b0032070700d00d418468012402d10012502c82d944010451204100c1c2340da0000d2110122207024040420b41a8000070104003090111420081003c0101d030760b00c240b8140304001c0d40194400d0314200850a80b000519415004103115050b1444548000811403000c24100c1070f409800203044074a030816500380ca00c0c03660007025008000603420003500d119400d0400ca1004810000c030382010b01d440c81c00c0d0000b4905c0c0014014450385907141c8200c000f071551980203501c0501030748442800f191500140c4260340307007688601a0311800201d800020042c0f00420307071902449014040c0c614100e07081d91010000da102420808010001c0c40f0f1a26983c11416095402030303950402400860070f40041d01c0040d11010b801101080058000400010b500001103582030441521510744800e01d1142c00e40302030301c1c00c00c15242c100b40b810003a0103481004100c04507445210741e03410030090240454010b03410004803001358000f04202c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 651547598 1250 651546348 651546367
    0x30b0601020114010602070e0a0615050c01090210120f050906070e0a03020d0c1707050102060112050102090409030306300308060a15031401050f0f01050306060706090f0c1505 77
    0x40059a0010040c0004945100801c10401c0c400350240c1c40f050042c3c0040d80240101840d090100e50070100d06c0c04148059400e04038564080400042c201050210000d10b454103901d0039004894441e800421103c0481d000c82c8001d04030180c420034840038a8074001c0084e030701c3c11040c031440340190070040c0145420f1f039034164161441c035280400a503006021002c0000140d84600819030380900c100502d0b804c59141000081c3c440c980307070400d606260000c020602450340d00081c0c60b41101c90082800840d840d041c14030b030740248628a42c0a030820f0600c030030301c0203141c4c06800c000700f03da20505180d051030182007414002d000e03d10080c250764014804e010800302c0d100707040c440d802550040010151955440050100ea5200950300000c03030788400c06070103100c4a042d00f40f07005103011740b50030710a030506000181c200000001001d05010700800440c81ca0303200e103001d0794052503000f80100642c1d5581e00300141d5400c0759520480c3e00751200180480c0c000150150300c64800c0840c1c403801e04200404 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 651548848 1250 651547598 651547613
    0xc06090506060406060f0816030b0a0b04080c0105031509190e071404060b1b01020903101e140a0e01020f070507030203060a150e041104020f0c0606030d140904020f0c0f151003 77
    0xb023440c51f0030181c80300500b500d6503460000c40c00043c5108030109644901e8685040d00741410301c40ca80d4180b05050003040000d1a00e1465444111800c4500c00481d0791001803a5813081600d160401d40c3c1072604051459401000401c40d05903894400c18001700b8002008100c00e59446016140883e00148071129243d0b102032880004042a10000340c1448401c001080c0b802400c0200c80b02d0064840004e0141d52194022000342444031410a114408840b410411414000307000e400d0f441c2d80c0d442d60001b50490a50660f680d85560010441d07aa02ca90300380f60395110f0303880c0016840790090401150b24914544102c2a0703001c08103141030a081c0c0307003c04102e42c29000800036140710340c00354480110799440384000d200001040740816124001100078516010300141198001e51019181c84605600b00300b08034061002c0310344850f0b46859000100303029000c0d01440b025506c0700460303180c96040700841c0c0b40861121613000c40300540e90030b8440070505803003035600c2c2c10360115400090001c6800c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 651550098 1250 651548848 651548881
    0xe07090e0a12170f0103081b070e010602030408010608150103030f14072001020f030f160b07020109031d060f0313021807030f141302010c06090506060406060f08 71
    0x300303400c1d515160103903102e031200762030b880101c01d0000d9a2200c0c14400700c0c9040ca28550001440400c4104560655445c40680d06c61038105508092503111109080c5401b000503001611152422581950b544d90029681e03400c68060010a0750034243c01180d41d280006681240012001c0c2c2c20110380d28644081c1e410741a01041d810411580c200d95400f901ca14030000c00c102c901c84c24040c0042e040d105000000203d41441460445d003180000e40c40c40f0070004103640c80311a010020350ba41d21300c83d5940750065100d40200070600103502081010b60358040d400442c41601035190710f8500300b150082c0030740c103203210750500d5030020381071000601c8545d681c0c0c00386a104143c5078038108540007540005a032504900014001d000d0814200f1101540c117000e9055550018042809440d2014210100f620001401c040c100095076149906581c8111030050071039400a00402103034806041140c1c0300c15040f00c07864020390804400041c1240b0071540f10784200c40582d195542a20f8a1070719a43c041d41 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 651551348 1250 651550098 651550121
    0x170a1a06011e080105010f082a0c1e0f060c030a050a0e030c0a0c0b12040615030b040f0302010507050408060703050c0d14090d0306050303040e060105190201051503010e0709 76
    0x52501500302c0c1c990307449840c80794000300380c40c0c103403c1e0361602c0001000601340000750400c0000075070a0143e400c81d10000b203140021105920809030002112030710460103481c030030301c030b09118071994140030303080d040c1400d40341407080c3e0180c90204c0a40395074181c4d40e5070162525040004100b000460300b030308d250711658204103c2000812114021903a140ca9034209001d207191a07005010342108010030344a001c001041410360fa0360800014952002c514980144007804141c0c0350004072803c5403c5104a1b07002c1c680c0706810a105041a0030072400c031080d100c108070003562806001c10f50450084003980d0489203044018800360b514070404402600018006801c07600c014003414000269501400c81c0300b2100c80480c1800d882c1140c40b00b80382070b06022a6006051410700d040c0120b0b20040700329000c1d22028081c1c00349607100d01004a80d2031048440b1075904001d401c0d4194845503042d08100e02602401440b01c1d6a50031040030982241d510006034640c1382c0c0314450801000210389c022021141 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 651552598 1250 651551348 651551357
    0xc03040e0124211416080a1104060c061b2006010522110a050c071205190f021f03050f16030c020312090705120a030c030815100801170a1a0601 63
    0x30704ca41040000c1c9103003513802ca480700013034040031782910382e01101c02c82d84001c3d10030081c0180941420200d07000d01c40c81c0601e0040050150f115000d10590303400140b41c2180d906001d9101106204004010303c41030030400d20f02c0d00188032504880c0d2800109941a18030040003105841905141500905600b00c0100006a00d801c50141705039580c0002d4103400701d10341c83d09aa107414183c0180d081500d50307000256510004031148010401c0001c5605160705007001004040d81da50408104010a8440c02940640110f24421090800c540a02080e25003500e080c0425100d5840c0d2242d04001101d80c6404200540c20012505200f030704607807801c400900540b0314000c901f03003048241072421a080082940016420001800d181c000e40c059401c00030090070845039260360040c1641d80009019081100c914007180c0c5044c145000103014420042607003441004103540134005c00000d115001d016510020305104400e00421201031540d4050041452640b90b070011401e0884007401550401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 651553848 1250 651552598 651552611
    0x50403080f0c241f1a0a120603080d0f0203060f04020306040b04021b0607080907031112031803120408060f0c0c06130c0b1801030f020c03040e012421 66
    0x40b0900c100c0d6a2110302129008030f091906010410343d140590b1001c800140a121003001580310040107103e030514480d1415a44401313100e030442e07070064008001000c0c00d00d088d0380081003200e031000420380242d49100c103208404655041a08174082110306541002c0071000c8036101d480d081e030040d5842800248000b8048100c00c0c0498226004040c0c0c1d0150380d0340c2090021046c2d00100b0807950311203100c0ca07191a00d49401c0c0903103a00c50155210003054101e440107505d46603643c2e00c9030107418130031540440c0e0f2101c80244c2000500d460301c6107100e00030b020b9521540b036019a8002110b0503107490400400540e12040b40c4c1c0702000070000d148140b100020b21040600300400e1241328001c1041d1504180c0a00f814200741d411090349034417410643d2010445001c00e5181440f0300c280d10074090030001141029080824007030310403c4d0741c02149000014002c1203113402c160201d410b880c10140d26900008109103800000f9601d08000d0021661070400800254015006d0b0710100d0159140440c0c0b1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 651555098 1250 651553848 651553873
    0x91c09080a030306080106080705100e01020c0d0b07140c1e0c190e0a090c030201030c0903170a120603030219110301090614070f0905010e041112040210050403080f0c 73
    0x30807054403011000a52242e40401848a0901035440a89099000b90402602c1c000010b1007460340c00041109125821320601c409a00a004640d0801c10152403541ba0040f545004080010304032041e4002c98060342c0c00e201e402c01d12106031070743e81d090700000380101c0031121081808121000d400c10050300c65451030000036141d8078880b10305140308002d00e4240da8105081e8108501c401040c60402c1c034a0701d00c812001c600071581d004122902800c00041d1020350110441da442400d80000d000050070300e0380030484070345800080810314000c0c0c4c0d0b0184110b52400c483c5068a10324400900183d01920600c0ca007681e41080c450708242c403882482e980b510507071300880c0c02e5810b8070900740c914a0b40c450404a4081c0c2d2120003070b038401b20b5480d1040c10f10040000140081515020b00c50402200c80c410846c103444650042c0140852003c80036251829090300c05410a01100c0881c0504d00c145801820342c1d020f481582e042d00e42c030018860600c1404000c81c1c0f12500002d210a0f01440b400c1d070388610 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 651556348 1250 651555098 651555103
    0x1b3006240c0106031a15060d02070f1709010e0d05120912010e01060f09090b07080703140f06190f0e10090c020a060608070f0902160b070806010314091c0908 69
    0x21031155462081050002844055402d001050510080204c6e400781c034003951a101182d20310304454000680301c6561b402d0403582c2c4940242c0003031012940880c15000002810054003a202d026070300c0007030741981041806403c0c02c2480d401400365020511446e1101d81843c0030300030217203000e00560071080703181202d10300b0364880c1503101119955505090007103464040e004805030800030f6060200a60660394000707055801000801080520800b0411151180d04a81043e452020004500b0300703015039504c906d0304050300c070f01c3d108240d54651840b0300c0400c820900d04440111681012503803404a80b02c40780712000b072403c403503102502804075124481d40b04400c07011902c0e40c001d00341c414007490004d04841071030300324590985c4550703c1081264030261100c8146d0b4031f019400750b290b40c0310109d803410025442c14000c0511039000200300c043c991200c026485400309a03002e209910b580b1a880b460048140e402c00e9444c5c00c5403c010105440000c0d4403000c4551a240c02e06109548042e010f0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 651557598 1250 651556348 651556361
    0x20924100806060d2c07140607020f01090b0403081c0e07060311040b03090309041a0307051302040f061112210402180c071401050606040e1b3006240c01 67
    0x809001405e030320680f4a840810481016010144181d104203840b640092224011108024880d44120f503428034a6446a07100740001e0030b00e1000c07103842d01d80f64604101c894010031040d00007031021070010406240a070207640c0c0e42d003101030007a20b965420b116080f4080c1c100c1416450200500300000030314222280c3c021889101d06102564881c45544200015500c0020003d00301300c1440c49291440d903404030380d080031100b088030124984100000b11902074043e9074043c4c0d034200f410f4100001e00d0340d0850104900c1d030311400113603401e0360310201118540b4000d140150240d10702145141c00214071185d10690420300041417031001d10007440240021000883e90003280d20000f050769020480410b01b50034651116000910080c40c194001c110b45000704d00c21210f0304207841021444208091000e0a200e44000307032603694540c24001c0e05160000c0043c1400c0305d40d030415000418081c44145076a020f90300041c89a1115103841c032200c030b210b903903041c070400c190304c01044820780290b400d01c11003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 651558848 1250 651557598 651557651
    0x15120414060f09011d0d03201603021002130b0a11013308060a0c050c0109050c0a0504150e0a23010e0c0a09091503020924100806060d 59
    0x42d04180740020205095407200769412616803040c03007480c10700078000718074200030030400d181c00500f00c81c0d580e030000300c01003942100301d81d200f000250101c401d00b40f03a06c40d00f40540c0a9021594200000600380b004c0b0700c200250040e4010507030606004d01c4107014001e00d070802c51071030843c0002603003007095401c44001c00343c3d991040c02d910b201920003011b90401001d400001c030040746900c9150441c002e8540400800300103804e0b90342c0110b40c0c401d500032030541c0c01d5469008020003500c2103900e0010381d21500e024030300d446031540ea43c000500d403801d4080c0c41c0003010309161400c2a246455803402d41540b000e4110708106854489040f407440724589502e10780c0c50981c9121840b94549015844865070160040c80c0c00c0c10104004440250000105411104200d400003081512801440000505270304000d5000140c030b000c1c40842c60701e41007413001c0805030682034030b991110300c000c120300020078030950f5012614410015a60386042c1002d040034001c0c2038800b01e00d0034089248000c060300181c001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 651560098 1250 651558848 651558871
    0x5040b070f0c05090f18010923070b0c0304090515032505061314030303040c030f02061317010c0509010f1d060304030f0e09060a0e040c050901080f0105061512041406 73
    0x41185014041b1888071400c100d04000304200c400d140c6031501140d206640c8000c1134402000a0b00f1a2001046050000c02c000d8100544400244a429480303034450300c60b800059041101040c80c1c803403140182e2a0245004000b0324580740c06010300900c54003170888020001c05028000200c6d1389a050050581c4c4452110000329242046028480301200907880ea0007540309104000008000165020030340e0380100c0f8040302400a440059054461000b0030003920014202c002050b81c10204045900d420950082c0b00108140d101103860340900386001f40082e01201d03604074a18000d52480d4072900340c1000100b002c840802c0400c0540e40203581c21800111411400d1418551100c0b0b0412041803c8400c00310170304205000404050842c00b900e940c2d0b01030500854104125510303180020b01001c0c1a607a0607680d110f0020b5114101f8446025a80d401c2100044052506400080145040c0c00f03450781403842185030604800c000800880384001011284007845000700b110900c6512021103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 651561348 1250 651560098 651560101
    0x4060f0302011205040b0402060d15030b070809010e07140d0c030f0b0f011401030b03151f291b100b0a15022a06030f070305010605040b070f0c05090f 66
    0x4041c0c50f5404034114140d031900c001d21000808819060344c1094044803825203c10740c08005800070040344400d605100800300c0004104400540413074803404440d00c80203d50341d00d002c80340307003038402071000e0460940082105101d1082c1800100403c10805011880c1042442e61444400e0784940c10985100118881035810001140c46496210703c0d08002d220007945080400b001c510036075407a8505250f114148416241c404000d48510301280c0f005070030f40b5040181000c0586111b0001c40d41e00311000c41004680d030100048041007204407031605401850034102000195045000810b02030f0310f2400b01c0a0307040e00c0c100148004000b02c1742001460840100030081d40900c290f0080500103c810145240543c011800300078030700401d010ba020254001701068800305541c02890782c8200c0220502c03030081050403a045c4228201d85040180e640c9a1505a070355005510803080382500410040d4001210700c4070032000180301d40c8500c2c0260751604005203e9940c21110019410207280 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 651562598 1250 651561348 651561353
    0x1018150f062108070303020c06071101230c220f05030c090103020d020d0507090207030309020907230703021c02030a033e041208030a0e0607050315010e04060f03 71
    0x10407803004020103000381500c0340e00700b03482e507080800c4420003410050001c168030007410f01a0f01210a0f241d01c050036107030755141500d03028140c00c0e0060f001b0002c540c40c10f003c411542a0b89495081059541000c4a00c603a845900a10040d40a064401100c1e508404240003d4070788060b8180500590007506243e07e061a040c23504e001d94240e125441181c2e2140100050b0729031f0450350600c65010360301000010440d041961034480941e014081061000a0f00014154180c0c06410304c14402c40e0b00d07148549442d41c0440302c41c0c01c00a9030fa924042906040c901c900d03c4400202110740c40390059030b0700800103280c501319031540c0d100c2400140c0c10001d203e181c09070385846404186503208e181449288581203250340310304404d0703d440c1400c040da401a030001112100a84000b400c20025800e02803402d0b2074445810b400039500ea001b0300b0b08060700c942040e60b0100d005441000f42d95600f80c00c507910118043c00070b11a4400241c10300078020105882502d460160b40c014041d1040191101d61030b62 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 651563848 1250 651562598 651562601
    0x1061a0f1810020a291f1e06110a05030a110115030c05102102130803030109091406010b03160309021810140d0b040305160f0218091018150f 62
    0x18802403100d4007081c21300134000c5c684801107681141c80c501e6200c0d028403004031301b25500d600319041090240c18101c440d00c2807121101140040c0c6d20140d46103036900403c103009558485c0f0006004225820500c0300169082c86115100c85000d01d0380004595a0340c3c1c0307a2480580280c540069901c00900a0144290b08088540d030703000691500e070a841d4001048450503015a0495198005680004c1c401441e085a031044101802811040c1c0c0e650756961150a40103001e001000c4501c0100100380030382150000c071310a8102c4a186000510b903546000c259048004007056500c00c0c035507a1003802003d600c1e28000350510031180251480c45081c41041e5102d038072041d501404000820b94400d6610340c481a050014141e0300544070381c3c1981300d9103015a00360080c40b8011440e03200c45c0103160306009030300a010b0990750096400c428546002410181e04843c08c507402c80503607114403484107910403d98008040d25040549d50b8100052035552300c200300303411240c00300303120791100b03145050001715 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 651565098 1250 651563848 651563873
    0x8040f051c26070c08101103010e061309061b020c0a0b04170304120302032d0319021b0c0406051009030312110d0203070201061a0f1810020a 62
    0x1107424151880300c05a44442d409128034203a000303001004201c0520382248501625040d0350b02030046041103482c1c028180d990760b20341904030f203200e0030910b0b0784488201da0710882e8161800c001c0d1401160342c9850910240b4a0301c210001c4159035140181c1c0089001407244243c1c0c2000442d0610303d4000a280092a011800c0075540c80f0782210042082440c180604840c2114190003440385080d084403155403d6020700c0d0312401c0381c040010103290070951b0110040c00c41c40400901c43c4154043c05078015441c0d42ea004034040c41210810200c1c540110700e05498240d0002218054580540314045c4882c1c10242c0b41c80240300e40c0030345945040ca2606002d01e0024140641d4015032646402c10b0007031154009200140c148480240301d0300082e259500314044c80c11241d00780300c0c0c0c1c403145022072400030f45c400c41d003200055103840300104044507501c1c0074040f44c0c44811201414125410186201e90f4880c10003601c080c40500340700161519030214151185945170058209503000d4200440800c50 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 651566348 1250 651565098 651565129
    0x10516051e160509060d02040903020d0f0f1d04110d0e01110c030f03100e1003300e030115290a09090915090606061116030201050f0708040f05 63
    0xc0110503207000c2d40882044000c0b5003048072080801d0700c5100118a00e08044c841c080d42141c1000c410034241034000540f1240d03884280d81750400600c1c9100c08850012241c1c00c0c040c0003640ca458200d1401c4420b40c54035201d21401040042c0106841c402036485510000240c45125150707120148102e000303110301024000000c14461804c40b81000c0c80351280b00e09959460004404000b054144007000c015002509604010000030b04100200318440c41c1544821a5140c9104c484204020802c0544c000d0030021109500025030250406440c18201c4940e0203400d5942e40c034004040c5d109902408004102c1145c01111045442c600043c0304490120b41040d4101c041000e000c040b1b03400852a81100c0050308002010061803800152002da1038406422050400021a0034880240e00500446002c1c0e04d0700d40001242c000d11079111075207032042d811802c040013010405540070350001d10403401d03108640d51600741c0a9492041c00c0d001a0080714401c05c4298007800304d401c0002200c00d0320034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 651567598 1250 651566348 651566353
    0x9060302040b030106110f0607050322030c0204110d09150b0a1a0d020c03031f061b11060c1c0f050c030307200102160b01050909030315010516051e 65
    0x1c2c10458009920b102c180b00d480e042084845802041240601100c884000d082d01595980d0500490003401d5030010754400403614a0914000422003844106400c00340d4540c40e45035103c00d95408001c01050824412200110108180f0f515020300f0310940e034a180c4542c50381e00c54142c9070386160301181c0781c1d420b05900401d41100140100b2661034880f01189403c42c0c0c400741d07250303070b000d000b94080c2c09082406004c521010081c840420504200c1c0a1156a046900300d0051790791402100c031450440c040b2000d6918447c0380c1008030f461005000d08000000d44403038134142200824038a804100106040780c1e00c0840403541c020341d4448510b03084c400307541c5409406d001c03408200a840e03200142c0a8000d02500c5020006035040514010441410501c0219103c1d90b12110910b20403400c40021a41050100700100f5149050b9509034080c88102004500b156a642400d12410602c0c0c00001d043c01010700c0349050000611107044122031041000c0c3c800c41418000001540540041240c1c040c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 651568848 1250 651567598 651567607
    0xa15020a05160203030f040e060906011d120a0b010305070603050a0b010509040905010b06030c091f23070f0602122505070c050a0b031e1528090b0109060302 69
    0x59400002e481020801c11141000d0030128800240385108208496071645804030700055030a80c2c44a2181c403d03a01950711840315547c0000440781c41e410300d08007440e1000340780d4110311541030001030f0002e405807040c11034004840039142c160342c5103000d80c0100c0b00c41c0c0c814a0180141541402802d4001c0c0c1190b000f4049840d0060019125018585034540a5580c4030711303440500400350041e00c1000009003086942c1c0c24041004c0189510181440380181e070446240000048200032841101c440b5549220140302407c44400038000002c0c0d04881c008018862080490a4000e00c200750910030f01e401651032494843c94882e83c100100415100080541054000d42e075120003242c0d1200c1618003540d07204007618144124100701d405c000d41040414602160421a2400a5000344501d48074260f40f503511540265100d80f040f200004828100655912242800c41c80c0346030483c1400780140000303498450b01c407881c0c0d401e50f00500c503840c2c80c5d050100c09943c2000c8950058603441c036055140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 651570098 1250 651568848 651568867
    0x406150216120b071205070f0e0d0c0e0907080303070f090509091209190e070818070308030c07050a11120111040e0702070506030c0909130506070c05031306020a1502 73
    0x1618086000a460201c400f40025030032445900c0e2a451300114000811203810301e0107008060007450f07034192001c11a100008455854401c410031440c0d5070000c0340c40c003500d0500c038404d16103400242101e842d034800c0c60000f0076110800d1000c2d40c0324100d15921200000c1d0102c2c0002d044500c2640401e00a100c200103200c0b104002227480c090401c3d540c44200c0da501c071b032280440d5500000702590564000b01901c0441c952680c034107401c2c0544401c1c0d070350822035160006954090025205180d0b0039a02503182000012021030143d503100041310285402d11840d034030f41034202140560115012a03008102c0d8904d45442e188102c41c0b4800d85000b040402c91840802c0c00600c1540680310b10b4030380340d0000580192081108202600000d071600b9101c0c00e014451aa158100c4085a40329100c3c06000a8440140c152011800b6801100404c220380314010161210340d0f80740400c0e83c0c2400300300600c1a20100c444030b01002405a580100081c46150170b158142c0c6080b91800a030860040180005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 651571348 1250 651570098 651570119
    0x230a030503180114040303020709050c04270b0406080109060c0206100e0c07050d090602010f0b06040b07060f15051c03140a03140c09120601080712080403020406150216 74
    0xd0300c0c0c94801d081068880040c0d1304400c080124084120b0006404000c150b404600d0008403503641078248603540720156804440d0003a409550041d00070000d2084c0700c14680000032402e400128000034080400c0300c0420151100c58000740d03401c1e9101c07020101007007101d00c5800c5e6415114805480e0500304003a404049800300e03c641149052440013044001010310111078000d9840307001c441814512060141061646208030780240d4a08841481100003a00851804d98001403046103000d08141299800c1d400c104025101ca55482d010100000c0b5140b14480246104c5116034614030712302410807030100c000a460300040300512280d100040e800c00300700e11a60500c1c500d803075203441c0042000c2b40100348154540c001351401505000108100100400c8549000e41d001003c3e41072442c0000d0350b0f40d2080c810061541c0c050130082220010001030251410322034482145400e540b900040c050b01c0340ba0708141224036180101c4c49542d601007001402404920404c01c0f0498901700c135802 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 651572598 1250 651571348 651571357
    0x11070515070203010f020d061a071a180a0b0105100504030b01151701030f02180412050c10050a06060818030f03060d061503030908190f02030c0a230a030503 69
    0xa051000c082001411035600790014048203521078011500c44001100f42c1c3c0c0540040e00c50403001c4260201c40c489000710410403142015044030688981a1b481c2d0700305040008002c01444040c0c680e0301c80c072606030701d060001d5882e450054002002550608040104040c031442a101c1407040401080001800308060300e070450300d120800130080101c011041e82c0e04491144403000e447c04d03204c001301c108080c0200c40c1500c14003d41c2e840c0000c00e078500802c85418400d90f000f81008002d00804110382e40f2801c0100000190002500c04481002e503800060b144140c1d1001c4600d80c07035040501c40306502403d40765010380303020000b1041d800980081c0d41c480c80780035007461115000000180d0300341c481000c2032403032a910000410001c1c43c900780070f090103042d6000032400906000320018240800040003038520103840314101184003549c3c0d94482c40c0100a408030303018001ca0540d03c441348e6404040328028806200541014114840e00d5454040341c00c1c1d115119044406060020a60000598 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 651573848 1250 651572598 651572629
    0x3030b010203090d060213030206130306051605090d03110a0302031903020f0403060b0d0c0801020c3903070e090a300c021306060329010f18050405010f0501110705 72
    0x10b030745140202034001c007180395230070181d00601d0000d01303941100d50810752103007200d010796020001a1903c151030241805400d440d840000d800380b10302580e9181c86519840d456210341450500c1d480d03060480e07400c04000110aa0160304049400342d00459004a1101c9080d403910f411440d2100300480341c489801540006003165a58960030340341e81e00c40328038a064950b040a2803a085e60f07a5040502d001c1d42c40840c0d41388840c056480d64100d50902d0006001080340d00c51070040b28107254100380d00c41c0710710441d55168142305550000514601261081c0e0040105a018003959060782c20607c56101e600c200100ea400300d02d1009252070701d544010b420304c0c10564a0a001601e07128000030303030b00c914500c011591003803800c3c00004085801d580041114078010b961590b4131100511300749907009880c04424080703a18080c004141c0c43c89011030200c01c1d9110304507808919103a102050440d50247c201103025450b0800c103211560b003041c40421900c4406004124a60a00000c105e9909490910 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 651575098 1250 651573848 651573851
    0x8100b030414190605220c060e180412110f0613050123060f0f0612060a030b01080a060e0303060a0b0a03021632150a090b0f0403030b010203090d06 65
    0x200c410320302e410300c00078620948410008000603100c0c10030314000c02c0180e9500300301e04640c000304804c410b003410759107010796004031b007010269180c0101920310041100d541980300641c10780d034046588807440d1480c041c50159601c4079046401102c003074000c0c0350b82044c0301003d500900b0640082c000c001500c590040c880250042c1000c0580703016400b502c28542410000d014012290100740b0a10a0080c0310b17000403203401a0050014040c0502440c09012a540021040201802000c8000040c5800c5403002d0840c400c40c0e56603072101c6201c14000e0304a140b094021701c02140c24090607000e035604203c90303e4003561860400c400016203512091042280c2c00e50042a000c1904d03000360b065880ac15010580c403000d4004501d84030714000035441800ca807422080c84014409036a100c404214003492100611800240c5001c0300d06d0190f000b010540c00b0354403200502700203440a41380900030700442c406a0701605040c60302405541210000c641107600500c041c0304241e451580704030040703401c900d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 651576348 1250 651575098 651575123
    0x30f031b05033712052a0a1103030408031518061207080d080103020307090c02030a0c022209020103050f10230402040b0d18020109170a060509010c08100b0304 70
    0xc0e003150a80341c103071a42150446821040141a0031211200340038802039130401c01e541e00c40e5110403246030511902240800004200d501d4007000e44010038150109003011400300d1440d00e00c071451030344102e03021181d0b000d010040c048a044c0300c40e2000c01440b0102c50425110301107000c41000e401000b00502d11600b0455000740507810148511000303011303204251403407001700e004060003541c002c0c031049000f441031072000a00c483e900d22415881c003d166019510305640810111030568181000341d0344194001f8150b4411551125603925855070740801181d5481e55000240807902c0c001c042c1203416400c0030810107010b0782d0720031901c1914603c030710080306805180d021500e003080c05500b0581041c40050081600d501c0030026007000e0403056010310040c1111641c0009a83c8040c0c0000d02140300758409010140e1030f202c582650b040100102e4102010a8407440e003612015100d611141e5501c00e40942031a0344903580d282c1c0520041040200246001030300001440020009003d01e541c840 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 651577598 1250 651576348 651576397
    0x3020310030f26030633040f03020f03030315011d060406080109050f0907060c0303061d0108071d0109020f1611030f060613050402030f0a20100903110613030f031b0503 74
    0x1941d500c0106c3c81c814180d81c40d25241e24000501102e9800240e21403407143c0c04404407484c00104592107000c1080b03180b08403400001c0195211501c0c503401400f101c3c1390071703107060064642001400c000c110035a11411503502d485800300c01c4542c0a00000001d006440403c0b5440c040040c0076400c580c91850a444081c0c203a09044004000b15084440380018001d0000340a4044d43c0101d81625000015922059070f210001c0001590740e10141d0308131000100100060700d5154058075203207000f002d03d00c1c030307104414040400c0f5410a8500312600620030003424514102088010b10301c03030510009102600301200010705100c480040d02898940f070700d00050454409005509007501e500c800c54440400e42c0c9820050048861074688001c03030a4101506207140c1003031034000e06003413515030400c42c50450702c1d604090200c10844540011040207032002d820b94949000e001980a03410300c10b5090800c1c54020010310807043e0707000314180340c541c51001290b404021101843c0c491031804450b9111003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 651578848 1250 651577598 651577669
    0xb0705161d011e1d011719020904030c0b090609011b121d1e0d08072f0f0f0d030b01090e040606090f240b0a03020310030f260306 57
    0x6401020070f200351844950f80080314138071001d050b180210343c02c0099017008681681d880480c8040c1000400245041e28054104098084d4000c0e000e8038086265800d035881c0c01003046c45c2598000104c0d4400401c002c1112028810091610078903420f40f118807800c00d030002c050110401080c06003070f9a44c0658440b039280311a14034074041400c81510748240070004124000b4400031410701240c00751100388071603e481500a20300c240f001b9162940040c220300c1c0c01500316042d41200301e910034000e900d04004e501040040132081e4200400400b100140410300c141071065091540050606184d000b06260b0382002c9480d0507550003902c4501d82e0342d15418203030060503c1d50300080100e840c000c1c90b4501c00045401c11b009440380310302c03c0402c180116081e0100d80312144070340b4144403414040b40501c41e1103a002181c0021003940c410103540d071291240404401285001c84503c40400c0d03c452544410310f089007011308041101038214a4401c000c2281ca020301a120740001c203000c0001501203804 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 651580098 1250 651578848 651578909
    0xa11190605031806010e1005030303100b0304060b040509071e06020d0f0203070f0606050414151014040b041a0a0f210e07080c090411040509070b0705161d01 69
    0xf403604451403540d40e08550801900140c80700c1c5521119504003103254200041102c2c052032000769a00c02072480e101a0380000d80001d00203c5441f43c49000100715036845009260003800d81c900940303c66458200c45041c0311403028008039015003440002c10400d6008142090110b04908050005420b101c0b01242548a071200081407030f411519581e09020039540180155142a241008980340e42c0c805011100800c5a82520424440c82c5440d92401c01d00e179440614406400d20004840b5411101365254000380c003c40040080802c00300204044541c020010030320b00c10000c2d1420200b01da0041c01000e41c2002032040c01642d84091140a100c627410400400041c0b00400407401e0000700152203a0f41845200698031828900c1c150501c0e002001c14004c3c0c2e0700440a518044202c0c0901008e0b01c0028200407490003541000030781d40d01a80c00a054403446074006d09070000d010341000712214216000394809040410b062008840400c0105d415144041080c00c0d040314610141c1504404 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 651581348 1250 651580098 651580141
    0x80c030315010f020c090601031a041b03051b0301120804210507080d1707021c09050a1403030a0e040605030106030c0e0a0213090b0d0f050a1119060503 67
    0x10000402070100c03541210540202026602c6070400442810200d980d02040c04030b071030340b1010132008980c0540c0254024080440f032000c00d818040e610b500024201d40b210038940c444c984180380c2c5809110383c0740c0702d0305601990308500300c0b407108103a1309410014001401127000504030121390307034140700f11901910000c005502090400e40c8065069858100c00e0712400c50b441d03c1100b60110f0444408502c200e80a1002e503205242d9044181440c06044400f0740f140e0254018040e1720a051814030700381c03c84644481c4c80d03207100705140800b44a901d400c81c1c0d04c000002801308a92041d107541c04802c984400d0780c0c624002d060b500e601c0000600030b194a40c0582d5240d880c0120010030031503d0300c0000200c4002c2000c001247e40ca1003900300c04c3c1e101d03a40c040c26903001c8034407040c000030f0705907406050580b0000c4c16050b00c007145c65032980030070036a075030040d211940310100d140c0c01c02c0403c00691170200400d0310f1a8201850707034068032030212014069203041c03050110010700122218030101c0c000f580b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 651582598 1250 651581348 651581353
    0x41b081005060a03241506020a0303020d090f08030906060d021e040b030d02010f06050402031501050d06030803100e0a0e060112030e0a0b030f010801060e0a0c0509030609011a0f0f0d080c 82
    0x24140c5600345038140803038a038170485908110890382d2243c1e9640801c01143da10307030040d000d01c4641d40c1d012002540110100865203a894184c00007040741c2018120242e846182804d41d6820490350703607450001c00509042c031402480705e40c0d4006844502008079200d18010141280403400300000c1c000d003005840c03ea030148200100c80c0d00303e41c0c0c15040118921103c03101000321507112000d0105034841107414005a06581540a1642d40f14500900800440780c4000421684965961890341e00944054040350941030341070202c81214042e07540c0000703040f00d003001003d00d100401500c1e40414420600135038413616282e4103141c0075000c0b0b8510188000c18807140304d030311112540038a030000d5810314041101c680021903101d00502c01c00e001d03146102401c0c42180e0300c0c2000c070400740003507a400340c1c1005010310100b181c4e518108283c50051001d9000400e24010f01120301c0ca9420b602c140c1240328200e1072041c501e26484183e240041e02e03c081c6d41c0481c40c00d6050030140050301c1303003980909491 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 651583848 1250 651582598 651582623
    0x12080c0f0d020c040b0d02031509070f090212010608042301060b0f04090b030f07030611091e01020c1c170c0703050d090b030103030f03050402130603030503041b081005060a03 77
    0x5a9000c200b00b4040b80c0104c0301040600c4032003007071228141e484840250168400361010501c1150600c41e0b82c1e028110300704861407644c5902c0d52000c0c4003001d50103019201d8000c6000c0944080c03004945001d03048031b10740040c0b070f440c1c135485140c50030f40c070303250140e601c45094090462103000c00e40222002d80010903e0710f51b500c402081c00b0000c1e40c0640728400c0303c0c074903000541c4150302e000f048005004010500a01185045032150b00090846000d1880d014508202555081d11000022500f03a41e40068810314206800000ba0820341c020101c10300c13400c2e81e860520a4584048040c00c0c0f07250300180307195980c0c019a80303140b8091144049880c910300c0b441c2800010010001017003840e00241e41c1e19012042d40d0303020b921115010a000040124131f0140c0440702c140d03c00d40c005540a40020525a0b24540d404500340c212110f5400940014800100304000d05c0742c05c0c405228810b41070303182070710f005107000710303184d26995003081c070403001900da202241003aa644400540078641180610390306 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 651585098 1250 651583848 651583873
    0xd0911150c010b0102010e2a0a030510050a1112060a0308160c060c0c030204090203100e071e27020c060a05060103050a14010506070c0830030112080c0f 67
    0x40c0d800c401e01d003102a43c01c02c060040c07103500c10300a05c010f880c0350800400650283c1c004802d8000c032108180f560b21010403101003425a80e04a44034011350280c00070305a0308017405100d506841c0003c1072401c5940c10060304200074a02e400031a1105001d11004920301d0321070344001481d0b0850340d032004c2d1034118003040c4412001a450064048544901ca900d054140e823400159400104034001038a604200ca07010030241c24650004060640300a050300c43c01c01c42c0242c2202140c00303140011600d075012001c20300a480d1174801e41c034054403200c484528010f00d8034101108601d08a0000c00c001c0f1202c1c55a4030f00c680864058442042c2c200c81074aa02e4a012070a21009140480741c0b140041d040001040d62042d540c464170010b046072451000c02a82400284202540004002c407040220a0b0f80001d541d04203000b40540314400b07035624022414010407140352900e200080300000c0d0000c00040141000c18090300244543c4600c00e6625403000c0d230030751030800020303003500b440354000c65004140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 651586348 1250 651585098 651585139
    0xf18030f071a0114010f030603020913020303070f11121903031d030409140a150e1b0408070e011a03060d03110f0106050909030a020c0d0f170c0d140d0911 68
    0x3a6513400380d0310408503426402044081d10304502c1b0203500b080b00f078000300d1450006000800c1040c1e0001c0c080f01e00d070020669031406915100c0409071940e0404004000b000e01d4000a444c440e510b040c3d000b0021841a402449244040014002c00381035654070184564001640510540c044510540e510fa503600e0450401a04c1c50140181403e81801c0010b480404c0a100c5c031402801803001300c2d01c80c0d605281a01441d110042d02c41c203000740d1401d02c0300301020401002800036050300c001610240e0301d80400b0140341d48040e0821602029000340b0381440e0701710581620f038452411500448002030b18241030798595110b14514415000c0e02c1e01c00e2200030b10540240040b00c10945060515903202c80d8016100d019922030f60700143c0084110b04010b18065045035a09030250748001c0c05a080c0d44c6e6109869486240f0b018110040855000e068910a0001421003040e500b040c09075445071a0340100035219000301c85030186c2e55107071a503003403180140d01c251072414094802c2400c00a140341070346 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 651587598 1250 651586348 651586379
    0x71407030915090b160809120a0209010902070f0318030803011d070203090102070b130b030103030906020c0907081314030f0714190209041110080f18030f071a01 71
    0x811012044464014454944035040707030204d09501c5d06202020540c444000070040c0f0a8a81107020300658030070f031b0b13100c03004000502140002860040b00c18810702000e60b00582c400a103052050001c5800b0030035031241c900c0e5140e45440c040700da019040b000031607100359580000c6c142110100012613000344080d614803820340b4141c4001c80c40c0c0d441140480e5644100f12001e401070b04442d0081080880700320180400d80f04030300d00700c802c00362034244000313094000364019400240e141000b045140c0d0103205c00805071905844040340b92504940141101d0030281900104050faa50464240441440c2c10002c101807070302030720b0b510194100442c0242e0050303c02036609140940c806400c202e0006007420b004845400140c2903030b12940c00b00400e010004005a62a200c908504c0c102c5607501214040300740c1454030740c0d098a0a28654608004000a10990300000c540d8400030559000105039004899500c041c1035441103030745088480b00400c0d41c4511025244c0340008540945d101e284d03e03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 651588848 1250 651587598 651587609
    0x6090605040311160320010c02031917040f0b07060227030d080f130f0501111b0303060a03120e09180f070b09010e040209060d0b0a0f031a0714070309 66
    0x44d60403807a040b0b200002c661851000420044c000101c44800e0303c0d03421104120103505040203410803041c0e4002c241007081e2007140c5026014100802d00c00c10004881c03119180400e00701e82030a041c141074075011011214001c80c019010085090002c02a4540403560030b0b09440ca03803106600322400c1c401d6950f140102c0e2107031083c000c0c2405400700c1407007190303c907210310300704005224507440d820390401d43c6c080192400d0794907600841c016004100c0c02d019410074100d280e03250f55552008900d2480c0903c0d00540b4040242e0010428404151f44010101c000c0d039070848044407141c2c880700f805445032001410081d8000d5201030420407203002000302e80030310050310b0058414070f41110140b81c0e11910580101c81c0c000000f403101c8141948980c01c40449400c2c0a0001850a01c130000042c003140c000604400919460707905914583c1008043c1200820001412205503411a6900c5403000c1405049079038580c103500000c3c60382032048200c0d00c0c54284079400ca0755180100e040060102e00036000b032 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 651590098 1250 651588848 651588853
    0xc0603060b0a090510020307021009050306070323060a0510020a050105061915031e0e0706080c0406030b1311210606030601032003100812070803011206090605040311 73
    0x107001c500600441d80d244009559048115092904011140e28200446021448103000b20401a2140803000091282e251104983c1364a0300c400c00d0700e0004020203d004041c1000490561a019040200f002003040009000c451303880c070002c20480c2e100c80e840994000d401089800394542c000c1a9041a1402940244030701c0d540c11041c00201100d4402182082100c5202004807035080000f80004101c113140c042400741e0013003c0a060b000c00801c0d01d101003561041c800f10890300400496004090a080041c0c051600c00021946801a841450f0030b01d40c6440c10f2000340c2c0d03500c41004510a25114003048104414004811150007102e0b110b4400640c0310140042c050741850243e1003079100908840c590f554810044000d400c24000d000711910124004401d682c0d2504091485200c16a01c80c10585140020880c0b420300034036407814800b03000304852800709406104882c151143d4102111420b1440e02d0a2401805c454102a002e545408140005c04d54007244090340504040304 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 651591348 1250 651590098 651590111
    0x9051b04050c09030a08030c0705030d140708010e0a0b010302040506070605180f03070f0f021809011a062b110304020f010e0d03030f09050a0c080610030309300c0603 73
    0x400424441c101c9803661503031117a05c081c40055201402194020b41c1c2c800850705003015aa1303102d20b107401001103c680d143d110300b440d21100516480b0144e00a08500e048901545040c41d804214903004d0010609a6140e440c000060b034001d40448009000c041c04459440301c180c142140141001c0da00d802c3c000000100c0c00007503500000d4200b2488543d07134042d6151204c10799640c881450f00010407240300c00e070702500030091b03519802c824a1000a07400928254502003d01d242150211214400685e5a0b0a0b20b008161184000d441c20f90009504480452041440d192298035029500c0344c030990501c884030341d01c6048000654040d40c8280c4401c0c852040e0400107485440d41c0103441d58002c1c1c002208a40400e10076004040c41c80d030b1503140000c0c1c00095894550070400c2094040e500445050700412a1107402c210752070b03000c500380212050701400c654009011a0076481150940450f00705440345c410007442c06084002e2a40d20340c158880c1c1c1c13034580b82d030382c1052920031440030034034080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 651592598 1250 651591348 651591361
    0x501170d020312100305010f09020111190f031701081c0503060603070c061b021b180c07151a0108070f0c0611070605090318030a21020109051b0405 65
    0xc20310010030040d0061800c202402d00c01d900e010b0390041c84181c21a0741c810000000c25020f125041540303210758004907180e400ca0002420501c504011700308240e020351980c0d40d000c00b035090601001c592142c2c1e00a148003060400312982c005d01404103a0b0028010000107001c180043c2c0341c102d51102408003003080e0722220301520603000c100c5407682c00003001c10000c1c401e035200390070b035441852007000001850308025500191100010003907002586c44108001000c54014625083c41101143c4008226000340d100084588000d0040c0000341c2000c12500c003000341ca80202c841c94880381501308505c654000c40035142c03040f10980326012038949004254014461800195040910344a50030080c44941e200c000a085c581c406801d030140610280f4001034450164034051060b8030011610307940b00540803040701d01e0840c40d46209601c184030000000e050300150150b00e16140348001010452451300703034054441c0d101c0080660240179003000340104286401d0902003c140d60810081c1d0701d85 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 651593848 1250 651592598 651592603
    0x61805070801021c0e3d0c0c02010c053a030c050f071a0c09030601090e0c010503180a0c0f090608030906090307231302121602070513050117 62
    0x1400031402280d0103c075221140300d0700c0e002160340e60000070451b818403029145040389100c1d101101d10440a192141c4110344401c140d20307107585a0540e004004040d15040c0c0684044580380000b4180440070040609214082c00030003140505586a40100c80700001039552101d01c0c0c150894000d02c822001c005180c1c4680700b80014002251a21450941c80d0318039600b441d0400b8074102c4d00900d422804860500d4166045402614005070345500e9003010b4040500b03101058002c200881c1ca00700301c01030102000251400300398070070b0a01d543d07261905c0c0b0340142d0040c00c01190759114403a0007038010400044400b050103c94030401940c0602e07803181c60000035101303540310b00e0304907500910041c02140741000060008400c0101164a0b86070ba4440401090b06400d1040700700b11040842d080e00c40c2040040e00d1802c40003031104514243c0b40102401c0310319800362260001d100744140c0c0c0c598042c0204031b010003a01c0d0040c2905a00002e0b17107983c0003d041d090051100c03409a44203c3e17081da2400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 651595098 1250 651593848 651593857
    0x80408011b0507020a06080a021c05010f121a0a0609020a020a0212011401031b05120c01030f05040f0f0203010e01021810020601050607200a0e06010e0f0a0509040f06180507080102 79
    0x8001c40c0305c03545002411120000e0160a47c440a5070070415601d824400c02c01a0b0041510b200c00482c056140103200da203003806c50740c0400201d40008140b44000f0702d8068a02812109400780004580c07624040c01000f08883e8005940c4280f00003001c2d0306013500003594070a00e6208840c280461484002510b0aa501d03140d9481c0c404c111000040c40003840c0000d04035006900b002000510507030b2080041c10b400200c2440c0c81080c3c000c1071500a0b956850b01410b0124140d4003805c1c4141d003071a513200100d040700c4a001824505034003003400e0440d9000c1d0071107e1580c084800a6403a02704002d4644990948015064440c1309a0311045403d24000b0500604842005003e54108265501d40c43c0300e00182c0d84100e04100300c10741d0241d405646180d0045c0c081c0191801060320b81c41c01c00005041c5060b4055468850350800c180440300c0d0340c82c0c80d0b8034829610305640804903602c40340340461700202c038190000c0115082c40c10070680444101b4150310201c1c003c0f8101c2d50004ea030f80c1d042c035080f07108 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 651596348 1250 651595098 651595103
    0x103110901210f11030d090608010801021204020d031110020d0509060108151e01060801080f280302161403060708040503090f0102030904240602070f03030e0607080408011b0507 78
    0x90080b010b0124010340c10000c405401440140044e038070010010381080a0340350802c0218078203110500005600c04006800740160038021840d229a01d00d01c507001c4980100002c0c03240c5400e21001e01018440e02c401c03035245104e907049510715508021700c00040d4200340c0c648258540307044000342c080000080c42030b04036820f0b03001400d403103900c0e11488016010000d115048004070040c00350110000c1818517402040b09aa030300388254140200142000f00303066004059602160b2803d0740003034070460116641c0744103902406103030001d04d0b0590400800e00402051030111420014408034203841042d0b00034402c405035401541d503003409498201c3c0c1a01e007c0c0040c0e0060020b800d4070304100c884004495030500460f42811040700018060719103182d20803000004581c81c02e03090808041040c030103001280050130040e803d0000c80c0c50104181d10010702040903001500805460f840e0441b1090b9400c030b0310741d070358403615840401c0c040c080d0102d410740c910001c0c40110540e035100b901615071032503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 651597598 1250 651596348 651596399
    0xe0303010f0b220605030411240d0b0a080a0b0c070c051005162d02090a05270606010f030902220e070305010e0d02010c050f0711090103110901 63
    0x141440c0040c019500540e100e1059800000f0018980c04060881c07040204000c0c0d076010b0381ca14003485c203000b040c0450b4040d41c0c007910074581440d481051030341151005581c900c080075100c1001d806d414000d019480c50240d089009002d020a2a84020486420403030194407070361019200e00a00f480140300d803041c007605050f0f80d04005c0c4600d00d409102c4125610443ca8802e013841203140342081040c08502040392840c51007031072448962266070302c0c0d140d104807071191004508103580110b411030b000140101081c0b80d49000240300b0418111800c0310b0100410f191102d541a00d910640e81c0306d00c16106140070403000c2c800d01d074019110340501300b03140343c0c09401c00c0b014034a0038050201c1c1d1030b14034200f0380e01c6685403c84080e608000b0080000214064400401d4007442c4008490030400055030950869040c00b054103403003a0006d0448180c124251f422a0340c0e0400c80c2811308a10440031100e991140d0158000400c3c00131000c202070a484080b11160035a0340d80d6007008a64550032807840140341c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 651598848 1250 651597598 651597629
    0x1b080406020906040f061e02060105030c0d0f12091d011206022109070302150c2802060409060602190201020715030b0303030403031d0105040507350102030601030e030301 75
    0x56031a005041d110381d014050500b8107844030400141160140c0050001a5040031a034007440203510101c46c0403607160001d0700c041c5d41410080784d110300d24103000d0382c00740140d80c11758410068103d2900800359000340c484c132500c0e44046d00003082ea0b004d81c0f00c1e40c0c1d88404848200b1108607907102c00d132412503160320f543c80000e0140e40e903150065040582d0301c29061800111039580007d803c40da031445107001c00050b120090540c030420a18207440414002c8c0c461080c03101b04912103000810110b4000c0054003000130030700c20441c1504903000410001d42145001c500000c030145281c000c14103960b80c0d5001e8a124660041e03441e513065407081d00190040e44602010072152400c003030040d941d4a028903000c580107a0910201e440c46c2d000f40c408500296441c0e0303411419000340c61210742400c403080000c1c016804d25440312542c40d80c0e90302a540340c0992001200b402c54030b410710450407540c07601c08910700d403580d80070301503000350400c0b03a00a010034205281c5c60069071380442103a043c1c0320000152081d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 651600098 1250 651598848 651598853
    0x9050604141219210e0106091a060c0f0d08060103061d0403050901031512020406050a08030306060319090501060812040b040b0a021213031506030b040209371b0804 72
    0x12074070280103c140300d00b02d000c031403004007100e06040c01d4466011001c42c0c03a14400d0229401c4400650003522282d240c80038820511050103d0b0845520048595944840c1007915a9040c0400074050300c80e14410b2007030b1012101d410000c187e10801090301e08200655441c580e18059042e0610420554030030b0800080000340600c0117084284410b02d00015005804d000c0304401c0c12580e0880c1d03010030300d80f0002c10118074040c00fa040281100345c80c142403c9250200e00d9079640400380081d4410785020002400d100003408460801e0310542c4414406030b850380c10098002c18150141a4403409020342941c0f101d0300e403d0482c4e00f00d032052103189203403074074204113202d6075080340d0010300450041c0003a06058801d105c026001c09501d00004440252552030450703421600d00b09000142420300c00100301080840d081c0d0340c2e016806960b4011541e89100c2d41c03070780ca90522444802c80e14050300c0d008211103e03a958100148502ca0410081080c08800001c040100081c0d050009864100003800 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 651601348 1250 651600098 651600127
    0x50c030a20030406090f14010c0305160b010306021c0b01050d0b0f04063b0703151a181804081606110c011b020c0f060d090506041412 59
    0xd07035140040c906618095030781074090542c0e100f80d01610024012507130501c850b8050104031402803015801180107495920000307062100c8000000c1c060100100b001030203030b01040b115080ba941d10142c401040e41e16441d00780000e40205040c1c800c0100d844d001c45c0c05c01d20319071141d100004030503110b00e03080c50305010804020749811520160811260245180140c5583c022240540026517640c00509180000c00109100c401d031650002e211419450a501650700111a040b01c01842d0100d00341084024848150700268407401a0031002c6401a417600400e0000c0c0400007282c501020507028950100524049090300c400740c0d0350501070124000800740d900420f40c1034243d5010f0320030f209041c1c0b01c0b4001c54180c42407009840d040044d81c1a4040001e2245114000c0b07081c84c0e00d0058001d0340402960f4802010341c3c0c500070b0802c203d010f80241c3c0c400c0b0588558105c810030038052450545042c0380c583d8001d44c0d00712038986441d07590000100e00030680412081c0355121140c2801d0941c0360440 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 651602598 1250 651601348 651601367
    0xb1309050a02040905030909072c01180803040801110702032e021206090717180a05060c090f0a0806150a0e0403171602030301030f1a0f01030203060106050c030a 71
    0x68640c841c150701e240050301d46000d0a0324150040e005140c549034100280036844500030600c0041007204070320080e4418001c0d6070184400b40704641100348011660050794400021541038070901504000040c05810020083c0709507402d1500911031041821041c15841c060820001d40c10b810903045c2d2180802e0720501c0c0702403020002a401910611109090308a0b8403044546417828030700d004001040c01c01c04041e94000310350f4540401d94081040e050f118080000e424214804c0070100b445010880400100c2c0039140c014091301d116003040b070056401c50341711032070a5001d0f00004255000340d01e00090944102c800f1140507100e240d03200c8405040e000d2100300417070346c0070780c100380c001c01c00515100096200394402d464208a001c0c400601c065aa50000d01d40541030740c5d9140e1640301c1c90703404026039044952100040800300f2040c0740100072004c40807003d5040604070420400c3d25100e48160710b040b81c1c000e5042c2da03000d0b600c42d07000b12418803600d0501d04050f80104110001a0711419411 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 651603848 1250 651602598 651602603
    0xa0807060b0d140f0d1115040206091009090c0302120f0a0f0501031a160e061c0203090607030b030705090609060406080f030c010b0f0f0910080303010303050415030b1309 75
    0x401d40c0c0c440d990307001ca040080f100316095602a04a0754410783c810400c10305400014100301450f20fa174401c1c22a070f103022180400c80e10f2001c2c3e4020504644840082d1038400d41d00400c0005042d04040001349808001c0c86190585410034000302c038914001d2017100c0641c0040039401c006641e135510320314a864030103020603501d590b48904941c2c004141d4801d10b8061407003101003c45082403189030039900040500007030726280c0310580c0030f0200d03030300007a149140741415145261542d12041f050200400a0050b00d0000b900020170400f1081d230108400e0300c11022910204200141e08081c035540d25403078002c3c5504030854030302056240c5044d14429a0000000b070020070207603140c3c01e0550038082c043e001404c0b1540f0208022694560038040c1d040e40b441c003620818a103015001c009008244480451030040301e10750040740d0400000c01d02c1c0c0d4041d201600c00c580c0c1c0d950b5a440c0081051744240f184422240c9945800d8941a12900070b5400064004000d03c0070400030341410002865a503904 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 651605098 1250 651603848 651603859
    0x224190c0f08031906150309030e0a030f02100903110405040501020d06060f090503120403020d050f0a050706030c02150601030e0c03070306141006050324190f080a0807060b 76
    0x19000036001268100054420140180c507410f2220312810341d03104c071580d01d000c1c85040c0714041c0031005c8503154045a98100d45070210b1142c0281c00c00380da4405440c0d0105030800204040070080c469014015039403a80b09039010326400508d054102c1e50504a4040200b00528000d1740720398600d0650801904203000d080014908221020030030300f194520b038008800701d0a0b214010140c0e541114120005000517030241c9000c00700d07205003012910070b500000344520020500c1405100d01000070703440d16116803044640302513080c01c0581d40c0721034500c00e40c0002070900400c203031558400f1440318140c106c804030302c0c03986407180c00c01503018088030b007100d802034401c0c0202800580e50800c4400001d5000300b100149041c2c0440900b50341c2c200080c000030032142c4080c410014a54410101e07913006410b107214032035000805900703140c0c01820026041e0301c100040801e0b441d496050003010b044031101d854249410390740e00002c5840b2801c403180a84507001c01e2144002195480d04106a8164000e1a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 651606348 1250 651605098 651605117
    0xe150d09050622020108060d06230613020712110111040603050109060e01081b1f0f02010605041130090a03030605010e0a03110109050913022419 64
    0x19510445000d0481641c150b8424410700026600c004804011010000b906100ca800160000b0b0480c0d600540540d0040c007000d1200b6043c002980c0c0480c880a6008280386030049280d40d501246481c19110700d44078407546001501c0e01c0300180308072542c2e15840510f0f080c2c03002d0001000d5464400203900d0f65960354072402c80e1060007155030000c0c0040c20740c64130001130307550425070280708480d011780103d06100007050060062074070014500f003504002c3c14030300c84c4010b268030100381c82e0300c4840307034168465010f00c0c03048400390303041401e44070140056802002074030b81d0b810410003543c002c60040b84101d0b50030841c1d4008000300c4c0300c0021450480280101c04115140b8038128544002ca92102d80e07a003200001000f0075905020742d00041c038092030800d208401007030014001c4d00251000814200c00001100d0099000f04442401000002c00500c001d01d829190200038000c4c94208038451441e00350a1070089200c0c126861070201007010b064100368200c00341c0d56031514078003007010500c060707844c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 651607598 1250 651606348 651606367
    0xc0402030a0e070815270a0f1a040201050d11040503070e0415020a050409020d090b04080d11040b0f0322051e010e12090103060504090b04020a150e15 66
    0x210700881241030300090010000c89441d0401007540c01c24022a003000039040309031105800c1c40c83c1c0007041c48815603c1c411008140350440381050303600005a01900c10034100340a00d0703140136203000b4081c0c0a102c0c1d030625402440c0a20300d2040b034009010940502801074800c21942c80070080400100e50b9078a445e40f1000000d280c5a000d41c049051205590100010003150040e60390075000c15510560420702120030250044c0500d008210b0019400700382114000b48541207900c2c00b58020030310f404213040038205031240e903000c2ca03460360401e0b007481c20122072400c07400200c60850b003402504600b030603a8412039926643c00036204c2075800d0700c2c2c195074841003090741c0e41d080d02c0680304500922050100c0c0e40d005801001c1c00e04019072036450300c51100a040004181390b040c0305200001960b40e40065030050300100115040035802501e040b180f5020002c80c0e020040c09540203c80880c10aa5140104503041c141c2001c00c00005462064840d8503040660a840e240d0815203032103410034407a035 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 651608848 1250 651607598 651607601
    0x70e07030608100c0e031c0c170d0605030f0a0c1a0415030c030b010c03021f0e030409150b070201090909050c151306081006050927090d1d01050702030c04 68
    0x2034a241c0f900e44d41c0d031101401c1c450340142c104c2d10b40180941c00303050344442d0300c0c03030310307044104010003030000e00021801c0070707081000c5078158400d00d06414010f1910b071885c200700d54000303110300c1c001c06000e840350b56048190940006260341d880da91065106048508125a501704101401c0041c200b0900900021801c10380041d00c646190003a0350380003c000b280b0781001426160b41c08400c6040c0032004e500c0c540400c6d03010910a40355074000c00111038001030364240400404450b8224000c0380000b040106d118199074001c01c0005401403009040540c449a03a10036520034072100901103220302c00208901a801d070016240240541d0039103030303a2900302000c92200c20220b070400d5400031001440c0000341140741195400307080309203000a075500d0455001e42c0509040c4c01960305100010a41442c03a94076000480d002e0390854000d004410040c1040c0500c044003038400520902070800c20200c0c0c28403c804400314803021081c48c03e6201588001503030282d1011200f680c15004265060410703071285d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 651610098 1250 651608848 651608863
    0xb060f070803070e041a101205070f1205060306070c0305070803042a060e0d050705030d02070e0903090a03060b060d050c0a030c02301c1406040b0102070e07030608 72
    0x190307a5056807482c203800000d21503400148200c0c46107241c000c000c030b0b41840c00e000155088000743c0300d044480c3c10035441a0790b21001d0740d0342c0504140c108004c100d040f5502900c09910f20b29603480700001d1054040c40c543c20380c0c60889295426601950008041038070030740d104140d6501070300b08a4034081480e21001070a07481150152035114140e00500b071034001862528542c01003000c0444610b9041140c02007220f0b40e0000b4003445021040108428850140030700801040010115800300383c403a280070392100190700c510001e00b188500001c4901c10b0120880f480008024084400300c0d0075942c5407002064010070081e0030030014085520040464490903000302e080d40201503c602e06c05400605907000100d0705800c5401c000120000d0221036001451401c001c603150410344140c89444240d9401441c1020800420500310101c0d8050300c2e81c407680034441200e102255a030340b58010b11003502d024001490050b80040010000740c6501e0586540281061801051803561040d119103407042 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 651611348 1250 651610098 651610103
    0xa0c05120319020c071e170105040308070f12020f0c06040501091407032d080d020702031605061215030f01050a05150307031104090f0b070207270b060f07 68
    0x24000107020300c582d041809070600c24245007080d85401800b440454903010300b80f1500f03144040500c10000d83d00425100700c0b01a222409030a41202220315019001c8c1c00c0c1904d00390f0208110001043c4100d11078084d040d0340042075103840c0e84005600107084001c2d4072050380c11041c00c1c01444901480c08062107032500a5000b1800440c0511140c2440708108000755514807560380681420030000300f8481c1c000103401d101b04c840c0d03c04401658052242880300030710041105c10b0004541414203901c1d405403030700747e0080e002c0b11502c042d84542c280d680700c458007035543d10a500780002c1041c100444962036208588441c000e40b080903080c0030078940600c5440800c850b944400801ca200343c0544200e0380d101d4588041803504e5400b9201003511030000d408060300c03501143c11811aa5101c9822884055500c40f14000301543d0b9030401003040a025160744006000d10000040c1001070384c4042c50144038070080300007400b480d800310040107201030161b49402c40c006014145000f05000c0142032181d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 651612598 1250 651611348 651611383
    0xf05182203020a1203020c0a0609021c0c0e0106050703080402090901090b0a06031a011215060519060e0108150d0302150a0c1218030e0613030501060503010b061e0a0c05 74
    0x3024034007132010780b4a040b0010b080510500c400341d1081000103100808030381180d000505543c0c0d50000c0307070904c40c45503065000e40003940b0140c010450b8000c111011a080c5168000e0180d032280e0b0115868890540050001028040440d0142c601280400c1d000981c60000040140007aa03441d020040111016000d140d030784c200400074069424590b4900500b644030140e00d03503051908817007000000342c80103024400d19800000d040581c1e68041c10103048001c2004007140710070b0b074500c420300c41a4082e280000320a90544656540101d01c028012655181c4503e40b84913154184406500f05074419411481501c400c44115814060428058010a803022921004030360020700310000c01044440102c0c94a0b020b001c1030006424032040f10307070b41841c00708c004100c004001045030140b62801c040c211002940001004015446501154420ba000b0300409805100300410303401111001044201c0c4500c0e03070240c1410507001441121040e0824000d02c2d0481c5d01c0c0d051900604081060608 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 651613848 1250 651612598 651612613
    0x40c061d090a02130603060b0712052206170609010b0a050d090503040305010b0306160305060121052706040210110304080f0c040c12090303180302010b09010f0518220302 75
    0x540c04c40500001034052414203000f02c500c0c1c4120030245110b107400c080e01c0c084001c409999100c2c8110704481c01c1d0a04844c0b154121054403e40b014410000d116a0012031106070046051031001c00d0400d1041c032000b00003140d160710340020141c66600400c1558100030003001041020112807042c40c2c04180640c00440d1105c1c15031828508480710072031003610030303888031040140907410b600c612074404038a1300d00403c03a40c840303000580d8901c1c1c254605040c81c0080711560070610000750b203c68840c40b03c0d50200c0260280e060500614510141e002c503406800c40c0740045d0141c1030203c100038070313901241703000040348034881101d070304540050b04480e10503080b010202c20303002000c000b088001031003101c041142c0f141d0500060015520f8008100a464a4200c3e940c180b40c040d0b44445034045041034000300c494800e00d0001d0080c15000d007100c1c40303030403200c00128502c101d01001c5016a003000d003811816400a5205a000400080c195a56000c42c019108030122024000d01c20320b6100b50001c0188 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 651615098 1250 651613848 651613867
    0x905040c121401081e07030b09010218010503070c0204110f0403140f1501030b060a18020a02100b03062e0b090f091b0a09090e0f15040c061d090a02 65
    0x5039210100c0c1c28005510400052210190108580d1145c581c143c82e55640602010301e010b040c40e0030350780054003c009001c200810b800e41900140300d070700c801c101012030803c1d00c0c0700152850b00083d03c505000510b00c0034039000601381070380b103801d02803202d0401e24185602d072007039110142c1c1302d50411a0008140c8101070800c1508001a110021a0030050080d4100c4141c4116464605102c007510000c4640d010615030303120081442e000d00031604604c41da45140c413007003002944c40f0408660040c4a4502110200744080c4250038103030200602400c207a440350000700d203154003550045880010580103003030b03008249030303543c0c0c1c010b208480c0d4241d00d862048040208400140c00454094080340b401c10407103000c031080701404540790410745374440d20080001c40f410034458006910080c5440d9100c10b0003c80001d8603038058860a04030350710000040c207030214030081503800501d05000d42c2d0091180074010003c002003258800340d403c3c08812500f0002d60400020345000c0e52305c85d80010003508 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 651616348 1250 651615098 651615101
    0x71206020c1b1c0812070309060905010b0f01050903030714120d0501030303050c070b010302011d06031e0105120c040c17040b0f010f14060c0a0b09060108100b0d02100905040c12 78
    0x24011070f4511405803030070f199110315400c0d100e40c0852118880d8500000350916011b07034014000d05800410401c0402418640f4900808060117054030600030b10340001660341c81201100d96400018001d107081c50219030f500c80d120f84900c1824a031a015065412400070400c03000f50841003000740000c2410351650802a04448004c1c0c40081100d00c10405403010a003500185411a6821320303020240740c401e00a281e12241d03000c1c101c41d074441c0c40001440b0760024407403540301403940c0349022078543d039aa62082005a42d4495a42c035041d4112510a080300d10301070307102003407018146c00d00c14112151030038209460201203500f03d9042c01c00c50705000e14030255034282030151000c080d02c10b0420342808002070500900200e1641710326800590845600c105101383e6405551100c00b0344030303030b0401e150362a03100c031800d01420403a07120307900800420410314028003c00144c0944210048020740e02401484500901c1304003e02100180000b069102d034461220110296540d1a0f4650032894202c0c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 651617598 1250 651616348 651616369
    0x4061a0d0605041113051905070e010c021c06020702030f030313060c090b0a0305160302040b0904150902120406110405180736080a0210050d0b0303040b1903060602071206020c1b 78
    0x540c440e00d070004100440c0d410400070702b0040303401d00f0800a08481803001452000d41809103c0120075410000c00c01c105264002d480d035240300300d041c0d82001d030500300d0081c0e981c0800c490401d4819941580b203000b140f60740d40440310840c1c1c1031504c000d4541e101c0e010701843da07008118100c00079603150100412aa03030300140307008030301462600703500d050301e014900301e082c0c018035800320b10a960b036500e1100c109004e400088020300e000b1f1825500d41999006107603880208840a40d034040c1071000180c2c0c0006008101e0f404e0750002000000b414110040c50104e9000042c419414800c109a584440c0028a407401954060301201c4030061012500000300710b440550180016601c20a40c60006a8407070ac000e890380d03625440d0864561040d04046009409916400c1d50140400940401c40258060003048820f40c8000c4007540c508500d00c003102125014403508006801c248828450307114042010115180200005400c102014448900b0310a82944007404641c030400c1020903400c040d035202 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 651618705 1107 651617598 651617641
    0x14061b010207121103032403011b0f080903090111150108030301061b170c0a060e060f01060207080c0d03110109030804061a0d060504111305 62
    0x540c001d50040005889104003419009119800b80395031501c0320180d18020740c81e43d0703a0400b089200c00911031201d0002054564a00c48540e424083e0201441030110030154010024a024004a1029620390180804481040700255010040c0d9090301c8080c02c10809036001c111425090140000480740d1403800f40c0000f0441e05000405103050320559116200080d254642c00c451015900b100240824410403a444001e4181d0300581201361282e4219904484c0740d96401007940c403e108500c0455002004014034111510417842c0104a14009440b4484c10034800a85411081061900403244036109000305480b41840e400c4004414000b044101c0e0b0700d2900509029081d1001d0b50103908100072079403401b403081c006103000c4500401004580030b980d03a4074805004010f10545052884662181590b102c49807c0e58444480d0b40000686180130f503810781c100c8100800304d = true := by decide +kernel

theorem cover : BRFrame.Cov 651438848 651618705 := by
  have h0 := BRFrame.cov_init 651438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 651438848 ≤ n) (h2 : n < 651618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
