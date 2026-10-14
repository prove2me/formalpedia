-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1951
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:16:34.446989+00:00
-- url     : https://prove2.me/submissions/fd62c00a-a401-4a46-86d4-ae8e70597978

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 350719424 ≤ n < 350899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 350720674 1250 350719424 350719427
    0x2010c030b1c0201121e0c120515040903050c01060b071b0609031e0c0f0f0609050a03120908061e0a09020d0605270d0e030604050712030e04090f020a150203030a0c 72
    0x29103400c205818080381c0306403c1b0301d0722a001304507000f0501c00140080029000c200b50398066507004040800f0f00e004401164810000180601e8804500303001090040540c107402c00e1203480b0040640307100706640c0e00c85602d89202030320310303814082c3c020814081040c00099032000010090b41d03032040b2840e281000025460301510300000c0005c00082e24030f20b002ca03000616a030300e001181d0044e140310f040a03403140000d84803080d20340201500645442001c1010468628000b11000854140107a5003034a0301c5030182030000440d0003200d50000b2030ba074034154650b8015119408a01d5840411150205034001500120f0034200030b800c2d41d4940c00881ea190821990791740450b24109001c54151032401d12084d1a071440540e1100800c18200f007452180c100131440c644515030000c007411303603a030800c5d01c0000d2189044400b034040100e00b200118094941d80f1501d01142d0040c0c2048070031010601c1044144001e03a003107184d01c49042450091056000819203402a070344040114049400c00380 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 350721924 1250 350720674 350720681
    0x928020d110616020405070e0f24030a060812180906030f010608010905010e120409110d09050f0c0a140f0f18090c090f010902031009060602010c030b1c020112 70
    0x1040c0b5485500001da01ca440000070303c2c980b821030701c01d48060000d40c1d503c80301682c10040e808003c50700031822415030201440e1404916a0001d20004550f46a0440c00760a60194104840325085180d681340c0601c0703240000c102c518610001c0b84141850003036820b0200312840c40400c042402070108001190450f03030280103c00a0200c07900080040030f0360780c4482400f030309014038144e0795540780c40b0f00a40c1400700401d6601c00c81400850760352809103407000302402810401e04200010109001900f059030712401645005030180340102080c00c4072103810b608103115191503c1c400c4451800400480d202240c22504000c0210340e02c1e4968100d0b4008280c031092181800c03030740329a141003d060b81c441445a094002c5a00004403600c901282d42400065a01603030711005002420004020112141d001954002100282112030703541c1c41050314182c810b0384d040400542d4407444141440c560501c00c3c0c42034503008840701004c813894904049401143c1c0c050217810480800098442e9520380e81 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 350723174 1250 350721924 350721953
    0x3080108070e100902371409061606020d0504080702011805011b0309050a0e041e031709150403021b0a050a0306331703190305070c02060705060928020d 67
    0x1b40700d945401120000c5c0c101540f9880d082c080b51942c2c8000c51031899800c269211542c01a00542c500030054034a4a040e2040c3c0004540c0c641c1c080003480340c441d00c5070003001d028a20480f1102c0d128522480003401d003031300480f4400e1444008402c01c02103680e008041e201100c1e40f1142c0c0c01200c1240742804c950141d900d0b0884c40d000012a10009080428620010310490040c0c00e42c1203400080310341c1e03041c0c03400001da025000508002c091451144240071640e08862100d00700c032175000301c00c41b080048502c2210b0941c0580c0044008010300904500019940c01040307442c03200003820b000008d5000d11341400040c100f16603c0c040050b074a0700d240c482a998015a0891aaa05c0303003032009125440c100d4041c29044412404003e02d2407d000401c0d5140640d00c0517542845000d050b000710000e0600034020b004000b820f052400141e254080141030381c03400780003e00014909807010515240c5000c00c0342a40a15003001108070010b40345441c1905a411110340410038500d0070000008513051 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 350724424 1250 350723174 350723227
    0xa020a080d06243002090a0315050f010501020a030210050912030a020409060501030501032f0607060b030615310e030901020607050f040302240703080108070e100902 73
    0x1000e0900e0841072040c0f0307108011120f40c1d00e43c1c0081a011080828102c0c1c85580b009804040340c00e0000001d0b0b85401416058402030606d42e00140d503525176040d1a40452246240155141c061001440b0282d8506001d42020300040c08a02c61607a0003d5940c0f070035025810703085a840c408501444802e0282005100d4103480d4079850b82000c81004000750f000b840f500c07a140b413800400281c554028003445048a801500c0c83e80c0906000f2a101d21603070810b0b0560094407079401000c0d4040c0e81e4603002c0c1881c580181c0307000401c24590014185400c10161142c20152a03040041085680c3c041b201c45001c41890008074140039640ca5912001102d24085414581840760610070024000082c20040100742d088841039254010203842d1849034540c0380000ca002040280b0160424400b0100040140e81085403001c201000244040d0000c410803400558840010400e4420401c90440074200c501c6089001d4100529071701100703400f600c01c00e240540c021802c00d600c150f46d038500344d481c55040d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 350725674 1250 350724424 350724449
    0x1701300602130e2a030612010608010507110f0f2d100504110a14010e01140c010c091409130f0c06030b0a0b13050613080a060c03050c0a020a080d06 65
    0x1503d806880150049902069040310543c001c609540c01313000c002c40e0310f1010000745140d500c40b00248580038030750307210440480d0340714040010544401d105071807050200340e590000c070300d2020100904140382040708244a5100b40f06580b4200c2007c5100c1c52022141130807440c15119084081e2001584000c403c031a9005885802c02c240302d580c0c015900c518842c280702d490b255035402c2000703c48481c42c000c600302825080c4003014117501070a003d00d042c140c1414010380380503035003029030712643c00080d60b405140d4585003030120a5070040d1012000d800c01481001b044c442c03500c007069585500411f81020041815040414040480b04403010b040d0060b94080d040e81c5c803040f0141c0a403403c10f007500d0240f0048940014100c0513541983d261030401c003d4100210300d4182048103d401c00b420f505040b07220001c0c00201c0c580f00b0040c1101107449200701084101c0100c03006000c0b100010280154050200aa0200c940d40440e040c0b0b075075a440b0354050748681c1c01c500e10310300409031a00440d009480307 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 350726924 1250 350725674 350725679
    0x4150501030b07030b0103051005150c070b0405011e230d1b08060a0602100b030f071d010504090206090d060e0a052808040603020a02031306170130060213 68
    0x1005800d0074803c881940f010f100100241004504440c02103a9011a00c03040490500c458505410f00a08900f50884107600b4010f0a031126400d1000a07031143d0258070303002078100b00c40d50b000004d0001a0b000c6030f20100700385000c1e11002d00264101c01103950750101e81540007102d03920313030000e03211010300c403c030100404101c4001c1c01c0760000c0201c117130701c0c04100c0c80400542540361800e4007a06803207169000d003091140c440a04c07000741c2191130b42c01d94940202c071107401e003021003080400010a02ca41c1c14900702e1460840240003a4010b802c1140102d0901000d0005a00d95008642003c03406a910f440c0304001401c0c84001800041c01c403100a00440e1450002d0240000d081a69250001144c10b410602d04111003280108203000070072801e0305000402c10180a54042c0a0b4030b0b802e801074924103c0c684c800441c0d0303a4600d070810b60200e0385040242c40d034124a408418050180e915055104050460491007000300d41490280310803e46141001003000e160180d540c03020303080903014411038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 350728174 1250 350726924 350726933
    0x1020316150b1f0302030406060e0f041523060d06060b0711090f060d0c09060b0c0613030e190902030114011215031103011d0c03120f040e0415050103 66
    0x44030103040c0079003a801e150440819141c400010341c00040c60303041142e045155900f0030760180d00014020307528540c0c0e0b10800519940e605584c42d12441c0324502c4003100e80350500e09944007074840341c030120a4900c0e004a40483e1004070204d08945001c05041510395a60394001410020300c3c4080101b04604007880002d01b04c0b500005400038910803001010300c0b10b40242800400c4000702c404401da034421b43c011400303d0900441c90140f86000301c00740c600407a2200210b900f55030403940851146880001e56000f80c20061059a40181140008911204064a004007a040a19010f505c9401c01d4031084070000c3c088914100285407841c4155107a695810403001401b00c100f0700e05000c01d42c0c0c3c4100d5400740d0382c14414842d004030380c04a02d400a50558a030032180004042d5800c1e0150341c0d8244c3c1003c3c1c00581070542c500304002400520669101d1001c0c141040503034030200c007080704244908c101004a00007543c0139241d128045458682c1ca5080c20181781d01c425080690684c5081d00100521 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 350729424 1250 350728174 350728193
    0x40f060503011a0604140d0b07080403140909040b0604090c0b0703030b01080c07060209150d061406040807090506030a0b1603050f070e0d033c030c0203071101020316 73
    0x44808400800c1240c1ca0f8070011441440124409688407404110602003d440c055001c0d510074005032201c07900c000e2035926026900b105407401750201c1c4460041004042d840b141070303c800310321520032074203051031407002c24001c10b4040d000814007000640080c0e242e4840360300c02c01515810501c20340c0d803555201071203049a4040002640003c0c202600603a0550180030118002c0c018030f01a036250135400e4640100940158001503441082985010300d0030064a001e010b07130007807501001509602d480c580130132682440b5400360254100307100422580b00042460380c12213200d024081510759400d0002030411914040041c1403c8101c07003030121180420940c03400c1c0090f15201044075440d810b8002c25241400c844482c001864454080b17414180b030142e034228244641001900c40002009001d5141c040c0260b585a400024020400c00d11000ca955040c0d07ca06c2d040810207240c40c0140203440c1d100c1e0050151940c10800c1103181c407039200b0001c8a0700401c040e0680300030f0180602d400d5140 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 350730674 1250 350729424 350729429
    0x1803051905090d0b150604090c09151b0503070b040302070608060f0f06071109090c0f12060103030f020709060f080f150601120207060e0a0b0f040b07050c010b040f06 73
    0x105000c0409000103140698121600040014015a500401552200480c0c000104094040c3d4041900002c10751160030142014128194002c40d02c515090002024846a54048441039001440326205035070400d4910401c0308030540243c580c0d82160605528501c50141c0051295102c501000301340f541c0410004151f0707510b503a5103189030703c4031801c010074802107040c0668041c8400200807a1440c0c113000038000c0910448491010146c08c3e00000d26000c1c08032400c50442d0010780683d4400e1030b061151851100c01140c9c6404105045031410f0358801c0c05010050610a4410108981c5802004010000c025250003030002036100e01c11a80004600e00ca4460325104140c1c840680540100b15441003c82c001c1c41c00300c2503520807004480801c411010a00d64a608001d04008070f2180d00601c401c0c00514001000584000d150840340002c0042c50550310f00905014030001039403600e4803941029a62810b0b903110f548a58800d401040685000b81d8003629254102905407883d03040ba104 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 350731924 1250 350730674 350730697
    0xa0e03040b07060204050127060806011b03080a1d0303010b0c120403210c0302060a11040812041e030302030f0a091e080d0e01020606040c020a020a060e15090904030c0303180305 78
    0xa18070b16000300d0140e0300c0401184254480c0c502c508c2400007030b2144240e41c1d8001c805140c943d8140d2a03108111a41c1c2241900c00d80005400400700140d0380b2190055024490103a820209071040846c4000d4580c00103020740c81d10000700007910000c801040064001c001c3c0c5065009650b641c0d40d01d411048200d140d15200c1c444551002c850708103074003401c020b078a41501a0090045a80c81d980d0020003002860614a103184013032101103455081006012824a8004011951681000e0b000354500b044003200521108281c401400000d90110540d02c0d4144c40c200e02a40321540f8020950354546543c200b03801800300001404016070721820000c0403107211000381e41d41141c00b4542100c0a07c048105070703000d80d0120000c52083c0c14250b00441856170644195010b40c011540040d140c044641c0c007600001304035000001080c1342040325862207895480140d45414130303410200d5900e110040000d000d02c081c9900c0d60302814020340204084100c8052114a00e1205150190080c0c01c00b002c6601c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 350733174 1250 350731924 350731937
    0xa0b19030201030b06030402090f07120609200a1e030204180c1e0e0d050f01020307080a181e05150106180e040b010e0705160c0905130b0a0e03040b070602040501 71
    0x5070117080210489004580140401e101640c60320041154204050075200812448803918180c2d0280c40c41140c026148600012544698209501d29a005620043c1c44c18181c204548123060ba084640083d072218aa40b040306180c40003202a0024000c0d940002112100d1000300399030b03104186c0c00881e45844507201c0c413020112045460180040383d56000700420301182c0400003602d401c40000100c68455401c9034401c42c05407030004c1c260707001581c010010030102e00070300429041a0040003103100b03888054600c501c0640d284e000c2060b20118840c0240700c000c0301018244102441340300402d05280700c3d803480e503503500c03000145100e40d240c0d5501c0413003400c41c034040355111090454038041c2d13400440590081c3d0804030b80814140c00640008284201080400c400c241c00009030100e890054602120041c50000c0c9807040e20300080044101001c00343c0e03c500002c0da03441480d900304411441c0000c008103901d401600d180b040b508580051200440c21508204a070f8004005440c0300303907540d5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 350734424 1250 350733174 350733191
    0xd05040602010507030e0c120109020301020d092307090504030c02090c0901110a050d032406090620061b090d06050406140c0a0530011406070c0e0a0b1903020103 71
    0x44044558031086140e06801440744520123140504a6441e009000d400000703402c9840d9000030308991040b01d6a880d125203900000d400d202c0f5a08500415140c541c41000c1040810b003046c58031000d15002d142d0056680c1c8000c6400c1c11322418000c1e50351a4050407031050342c20484029480c5030003c4012a0024508202c0360703d0601c00420740385060ba900c0001010440a800740a030041d100c0c2c2800701510716a148a1030303d0b6400f042c49803600419441d202c155140d824050300030a480302200e50801c06800504801e10312040c0010000d1340000202d002404851140c038002e80d440c0b041d4440c0c01c1d8441a030032455401e000d551340c05240581e22510003001140e0180170700428400b41121103001038203050250714000b40c09180185076070f18600c1c4d409a542e4503001c103514038565a94416202101e84103005000f00c0141d29180d0103400340c1143c20f541056242e646408000100740540c0d10148440c1d8003058200199420506604200070a10038415082400011070241184001d9001034203024a1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 350735674 1250 350734424 350734427
    0x1b080102070803010312030209060409140c07030f0c03050d2a2606060906030a09020306090718152606100506030a150305030a03021e03060303030403110307050d05040602010507 78
    0xc0362074841d4807240840c29030786180c440400f491211601101031540030000d030342555450384000c1003c0c11013148006101c524040120000420052100c031080c1400c00142010a03002a90384507504000c0c600344152000c0da1804461134041c030349174030a005082c42044080c0d0000000c2e140d060b00e07014880c00310010b42000742155031001c12903005940c1a90805200c0c94003000014060380408080e02c0180b03801124004100d4075881140d003610413956a001610452606214568020320301c440208240c03400c0c451440c141030300b41501115584e43c1c88421911810542d0002c0f03000300a04d80c20030400b00c3e4100c1c4c0c0743d012084140601c0d58540614400264007951408000040d00c102414090031544d03107448074001000182005001042507403c0040010000c1000b403500025564015855145000b09012002c507101078640c41508284100040c0c0e48002082d85c1c0e11981614214031040100f59180781144202c02d000b425a00624458480c0c6030b030808010021960300b40d008004503540c1010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 350736924 1250 350735674 350735677
    0x314090d080c032a090306040804090b04150b0a1b05150c0c0604030c02030a051e01060503060609060603040f0812100b070f03030e0304050405040605060f03190f110d1b080102 77
    0x221003403c075010001d404c250300b0107035500800c001601c1100900c0c080c501c0002030300c1c0507812102126210340025007845109014003a41031007007001e8030306004905800c5040c8124001c01d01458034a000040b1740c02c0e04092080e4900d80d440c074003040011140c26810700b02241c0301c40f10881c10100307500b00c2030046a100a005030880d226100d004000d00704945903a50111800a5455000c1e07916100303031005800851014801900009201c400c040c0c0c00540155080b82982d849500480c03082d04140204081a10b401b8100340c1d014070111a115504d5440d8078000e40c0309031084001401d10b210116840c0c18503040304a88900a41c2446403000300c9582c0c480b05280c4502ca082d01c010030140c0100080d40002e4002e4102e26000240b850503a42401d80700d074007080403100c0c212015a602c0f41c8031414059a400c00301d9070f14240744c10944c00f03421042841039120340e1030481505c0041c030078507090031000244140300c80b032424004401050f24031a01070380e0406845400810401005070214180c0c0021203007014170 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 350738174 1250 350736924 350736931
    0x150a02060f0c2205031006080a02190b0d0b040b0406060203160c090e0c0f010203031e070905270705190809030906121905040f0609030314090d080c03 66
    0x500034046a51140480380c500d050140c02c2c034900c91000d1082c0006240c008000203002d8445003410b00300d1516100c10945060b0b44084820b0810b49084802c1c00300c00c00216540e22a140c064442054480c0c0007540040e4042141e03003c001c50100100d0142c403500d090b40c10050404008039000c0c40440700c59001c10040307403400d2145101582c000c10188041596450384044a180500d1400e070354559694a04419100c0c17124070b10302c85030030000061140d468200340c002518102031000b1825407034202c1003405800307440c84071144580c04020003d00d015104900c07074400303000003410075821b240c440c10780c1c010218662740c180e01d02c00090800048007103105074203483d003032218120380210941204105881c8000058680303c4240410054a005521411b006101e0565200408021031504461880d09034030221140440c0508010502000c14220002c2c501c0c00c5030080c800080c04c1c1c41928058008040c6ea850b03031646030786044c00b000283c920110349446540c0d017a0b12844030540c2c4149281c0705030301c403c8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 350739424 1250 350738174 350738177
    0xe06031606030914120c060f06060a2a140d0c032a0507061709070302060f0d02090d08031503010b0a2903010f0501120b240d060e06150a 60
    0x10019180b00c0e820421031140207084001128020840c16070070040000524561948001141a61550b082081e44c0c0c1c0700e100c040c0c06901d40d00b40500064030303d10403a14110204601e982481c24441e8030721509680041c030b003008484480007240340100705020000124000c40c0070382e800e2092100c0c050801000401e5041d619205503100c4078507100210fa15600e80305a94260211803040003443c100000d001510081e200c180580441035103c00d080c0d94020180304194012040400c0141c03130300030a07154505010155252540d00141c4040002d01551490941c040801c0c0301c42800d000c11000114005c9441c4074907405104110800d1500361505543c0046d00520551030410144210708440d02070840c42604d54203c540124202c118560030a030003c02000d0016a003c00c06581c1045e0b0700c1420041d030600c00d000f8041c0220004810190280c1d8554810030f0600c0050780c41c900c00000c962118400c20010040140c407402d0107182840708070f41660107284010341c0d034005a2002000d486085415 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 350740674 1250 350739424 350739463
    0xe070f050909060a150b0f070b10082d0613030315030b06131e0209010e09010e0f06040219030b040606051314150406080405123606070b010e0603 64
    0x4080b0008000c1605c0b0544141070700d2140d0703020880f8072070000100500c030346464038261542e00500308800c0000c0d000d00062075942c0c0c3c140b02048070300340101d15280225401c120b03c050060f5540c080d1403681a4000410310709000e0001000303040c0040f00e1440700500d0095404010410000403401010041408042c00d00e51900e40000d695180081c112103000b0724400000c164050001402203a1140030079140e414190013103400000c80d640860540d5800804560482c03c6500d01448856402005800e0002c250300764800501552580d0701103c0301d80303a001c0640b01100701c01100050040a54154041c8a141410302c0001d25900c030704c055510003000b010700342c1012840c0094801d0070f201d480e90101d400c014180d00c4042240010030250005003041c0e16540c415140618009080800c001d40e0386004550501801030900c08400601000c440403000180a030740b00d07001030890300200514500d910140014003202004005280c1604840301f002105c0d038a034962a08241e116940f044841270035658 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 350741924 1250 350740674 350740681
    0x9060e06090d0203070b1615050c03040f030c020901080d0801080102030103080a18030807080711010f0914010c0605011401020f031801030507180b041403030301141207090e070f05090906 82
    0x2000c0109542243c401400c80b00007036900d0f034500c00c540c1c1101c4c014540c94030500740b911003403000341c8140c9500c0942c9088208080c0c9000324034843d0b43e020207030005e031583c2c4080b8031900c1094002c00900318841d400406c0c0c02c4096a5400348540d64440c9188003400080c84040001444401402902c1c1030b00e510a041d41d042290b203040031100511503030043e44804105600000209907460000c090140c080d2104954031307e10790a000d150a0a007112260400c003402c0440801c0d10340c4079010400350b800d1101000c841d0000c90004039000340007058050800340c07a20000159240910704859800311080e029220700000d03840c0f40719240c1c040c00c2d207e07180c29200300100d04041e600c030b58007180d0b012800741050f600d132881c01111955907107510b030030804140e00002400d1040c08041d0148041da80803c90007949558108110070304441c0b840c00306240982c4c1c01c00c00c1d440c603015040c801c1d8009400c04850810820726002000e0f0342da45074070701c110031018407485004a03a50404601c41d920945500004000684 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 350743174 1250 350741924 350741929
    0x306011b020f09041509230a03080a02030a140c0c010b100906030b0a08030a080907120c0b0f30180303150402160b0a0605120d05030a14090d09060e0609 67
    0xf07402442140c0440d178990002c0b001204511811224600403500c82209140005200e42c0050f5841c100640c0741e80010a2500001d030f1041d000780c6d0151140001503100e0b110007030000003605608006144000c000c808200603031001101910036081074800034480003526000b131040340f08000c518400010404c0d40280300c014082c4d00300b155442809441000c1c02581e0303106080c2180c01001324400040d85c2d0109124940300e042100741b010348a82081d48480320301964403001c1d903170018851000c803054080345003040c2100000a42d0164440c0041b1100740081e0150442c030003401484a9146520804011075942c9003401c40c80d020002c41c0354000c5103513031544d0780002d0140000031201e692081d002c01200c010b49000d5416040032074401c00300f28805080101483d010b41d010344d003001e130060303010300e00d444905200040c035583c080800b814081e030f40380c980021280262190a0100400c2c0204000f4421150300001d40c808458102c0e075208444107032a20411901c200110041680c00b8909000091031407 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 350744424 1250 350743174 350743189
    0x6010e0c0d0b0d0b01031a010605180409150212070801060e0108010e090c1e150f0a0c1703010f06080f0702120c0313080609190b0a0506180c0306011b020f 68
    0x1d80002c03c1c01c01e0780407296440342c03d9188240c20403102c50240032058150b002070503501c039014112a007001810015040c5c00340c0d400000d550000ba210321340303030104c81042c0400c3c800350245003042c0344000e41d42d60105140869070b03548144c80030f00000c0c8905000094091080780c003401c00c00d20581d1a0b0403d6443c104180c0c20700b40c03000d401170396180a5801c03a40b01a9407240c0003002c49210003400508040f10b440104010301d141c010041d02d0088003000400c64081e808801c41d1004bc1650401442601c0f503401e0526290300f040c001904001c50003c004030b103880c00401e01f40204c450943d9102e10f1f581e40d40041641d800401c0e0390400250340400f006101c0b1070b400a0180a8403030280717003124101060040c07030340e2039a861b42d809002190001c03420301400203414009000400001e2142c100400c5050382e50340002d00008080b031840d103942d00f010410f1650307018402c0c1d50b0b140e102d5240d041c071401c14100119480d4415560f0ba0b020410312220141810740e0740030319000313032500148111800700300c100a204a4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 350745674 1250 350744424 350744441
    0x1080109050f01091112011b09050102280311030d0903050d0c030e0703020105030612012f03090303062101050703051005100e06070f0210020f01060b0301260c04020a080906010e0c0d 80
    0x1b99502da828060038070b0b80500301d49121701c6403a554000313203a140c04006420030074401e41d0055030141c512000c03017084040403d040c10079581440d1911412120141080c1540290f507103c200c1582441c469a003070550160243c001383d20201c0c420007441c507242e20154119040d1556201e140e070000381c01000513600800c081c40c1d200d10090104140784031030382483c50842c1c1850521204030900300c0720036004444001541295142007158481c40e5080c20a88542d43c3d0000400303c511880102a40c0c444a400d20000307a51a008464020b00650419800180c0a482c088900d10010fa03650350002460b40784c504900d0159420b9503c52240303440ca40014008a640200c00517241f000d400c3d1252001030b1902c0b08101c46240c0503074040c00b00f030f0020107042800c0d84c2c002da02040c200e50303044c0014002004114000050800e81151060071403550354501810b002495002c158050301c081000d03010a90804141440f6a20a03000d4600603a2140c240c4900c003081900c0c82a900002400444803651140e0f014104 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 350746924 1250 350745674 350745709
    0x31b05062d1615020703021f18212d0207090c0206150a060e010e28081006030b150328110406080d1404030c030f02090f01050f0112060e01080109050f010911 69
    0xd500d41000c00740304000301052812034507102000702481e0004044801c1c9052180d840c501030803654100440d80d5424038250803903003242f9012441803030900d40204200702c0200f0b07100c141880202c03001304010351901411035a0180c1649411814030781071600084c24026203080340c03940d0b594004480700440d03845800c0c92807103800c88000d841000341d280d080500c010070121045040b841e01400c0c2001541442c120011f030701c02c0242000d9040c800600c501c0800390740b140d81140001003540304240020b103030a00c2000d442c02809014517060041a64a06403214a00c2c064081140810040010b1000b26110341c03080a6098002c90b0a10020520405995600910784800141400d403683c84a0310b0701520380c0e000b00d44030311040e01c0910842c1000c00c3c840780d0118150404585d030f98507010100752952100c20381c4504000040ba25103421040c147c3c0030002502e0801d080d0701e450341c2c555035000d0080280d0351081d00d45203d032009400c45404140a0135003003aa00001c40c54124042034144040115981707103a91 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 350748174 1250 350746924 350746931
    0x121a0918030c0109050d020d0815010c0f02090406050709050102210a050409020301062303040b1501020114130314270f19031b05062d1615020703021f 66
    0x120415404d002d4158541d00441c01780800400103c00a407610480c11001f1040c04101000c105980c0c1c0c2c2100368800d18102824500480410351500343c02141a07544000e502c140c500c07080c041800038a900003071060017651070740040c0350745400069903958041d80701c40340c070000c2400b10400c030444004007a110140480c10f1590810317407503d10450503030300260420000242c1513044680008003e980701509060050895407460a007621107143d0008014007860541e0160481420542d01c00d5014a256400c400d03426001030070702040d454001c008200d41900002c0c0f045048000a0f0705881c100c4080e1050b510800c441d1042950b414100c881c0b02d11440c0d6405490003020103003e0300e80d1045413241d81c0003176a03101084c50541c03070040d04910724040750920200c11004103004a0f1030384c0c003c82d40081c000e000319100400c0b00b2010040c1c1011503903010508408041404400000c4070507441c2c3d0b140b071186961b01220300c80c22234224101d000d03400001d0016481a12041c00c028490141c181442c0780c00003010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 350749424 1250 350748174 350748187
    0x150e150112020d080307020f0106060306080c040b1201091a07031404110310060b0c07060801080706030f0207050a05060a200304080309010f020a02030901020705060406140a03020705010c121a091803 87
    0x1380d0a500111060310140e01f09030700c0d000d90f4140070302c80d560150038142130400040381400d004070350b50080024428041c0d81e0340c00300e4072150394500e41c10501c4039610030b00900190034185462124805c0342c1d0480c400000714440880d00c00f5009015000158500c200b207842240e0707a98982c07490100c10640c81c19054003034048401120f070030320300540f006041d0302180140c0d11564900503d03c7c08041e41e012100b0025203000500082d0804201d20f02100e100345008605c440440301c6400080c0306c0d110008150344140498601000030104a00d0b103d5454070a04210303d140003415100d456142c0c400c100080142000001e00080e0680051a08200740d0000001d141001c00301110403a03000a40c0079015030320100340d400709587d0421100b0b000d81026180d890605103040c601030b10302d224203401c82961600c0400c2040a85110790305032420706400a0080c0103104a060020746a40c0303005c3c60416001d420b004510711540300088206140c050041c1403524542d0714203020303110404c0000340110301800100600d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 350750674 1250 350749424 350749433
    0x115080a1b080403170705180303220e090a1a04032c0a1e06030903270509060d0f020f030705060f0d050f0103120311070f150e150112020d 61
    0xa07214180320703900c506885080030304004e0581040000315100301000c40e0700b0000c010b50300c202550004c100c1100d00e040919004000a4298000c8020940300180c03020840403c00c4d6124a606040b12405554500c0549548980e5616040b249401070000602c1c500b000300b810a030045405da000d4020b25181d07110b09480101c40755621221180c80c040e070034a1521040003460005c0c0990010a032440c4464050f205140081d000c156151040d0740625175545280c03001d040c051002607188000e203248160720b0941f0a00201004c0c507039402000d01405051001400504041c0304026000d90041030004c2a0b06140e400c000b40e100b80518260342600808200241c19102c05010745450b11001802c151170307040c0540381a0803120000c20411071072803030400400c086201101c003080e0b5607801d4900800c810929652041c900c0c4030f01b5400a1010b10101c014038103024101c1003072442184e5041e01800710201242540303549142d421960309605a2950040001c180005408443d6070304c054001a400580d50303c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 350751924 1250 350750674 350750711
    0x12060703060918021c080c030a020d0219030e0d06180b1e0c070303020a0e0a12050607030c120506030106051c1704350106060507030806090115080a 65
    0x142180440d440c0c440034410300c500ca000d40480b4100705407200f4400c80081d00001c0d42c3c081140141c041c00340e0b41184490901a12500321074030b10705400102ca9442040c0c40d002951115440d4940c80107000703603d0703005030608225007080411600356a84201c95901751040264007003440700b04881c050703601c14403034441150400d4a203015a0181c0c119604d1032070314001940030004500544151140f8500400450000e9881525031041d090314005072105020f507001c0e00c8402006561550103000884001149924901080c2c0d45500c10000c7c3c40302500c40303087c140c0550300d00082100104241c0e107210000440c843e403186a000f9001000030941580d29070118001500241e440360144501105070f4080c88102070078055041c2805000f2880e15140c0f41d40c01c442c0040c0c00400f0651264180841610441c601194110350007019008101456440c00c010341030358805801240030503810000503000e0b02c1c1c003000e540e0407500541c0ca146511030034160b084031030301d00080076102000da4078802507500c031085a6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 350753174 1250 350751924 350751931
    0x18130c0c02010e0d020d0b041a0f160207060f0e0d0c060c02100f050702061b060708240303070201030c0c0f1203060e06030703021e04020721020304030c050f1206 71
    0x1100c003002114280001481c0856410300e81c1e009003c0164000c00585400d03074100041500150098a26101d52a203d41c1c14907900000e8108050380e107050202448200c00c5c1d0600813800b441c0100061018000184e8030341d40d0a21694011030044402800381900030708800c0644c000c010306da12441051640c4140d0350100d183c002c9000188201c51036800c5051140f880d0321105480d0501d80c1d008114014000e00600c69040000d0240c0804a01546e01425134050a188220001c044d01ca0751f00d4018002882e510f0304403052780703520300955104c00701c1880220f0060036101c80680a1480d1103117940055000d0205040032000704040d0150f004085454010740c81c0c03a03144620300038218000c240c0300007015070b0221782210303a51001407014480c40d130390002018070807a0350503034504804104401d407081c03901c529002016002400000d40e44200500002d0740c12055203958602507440090a0080780e0b01c0c001c1d40801404a15001c000f440a8a060a0351100d001c2c00104000885441e0f08011401e040301034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 350754424 1250 350753174 350753177
    0x11010813080c0c0a0e010b0406120207050d020c1c17070317010b04030b061e0409050f030f04031a04050a030302090d0c0305010c080a1505091305070608090606060f18130c 75
    0x40641ca045131501c8007103400149803500032452654140660703500d4903c01d61280405101c8444140000340b030fa150140d807000b9401000703894071020400c0c40a5120b8145440395032107106205841c143c818040c0320252889138203c10540c010990001c46400168080d080c00c2e000c0c4460401407820141d0b40300c00c114040c2c0011580c030703520390f0301c7c40c03a000750042405030402e48540c40e000340d01c525030800c1422a83c0800307012a000b0901c4002424a1800d0070481c450035a03150000080034440d000c0b1000081044a01c6661400e020020250102400031020340b4010130940102803688080780c030a40180031256801040e2620b40c1120741c1d500c6d17002c0e50380ca900c100c400740d44078407640c0c280c642c001e641190302051010301409001025070030440070340c05034082c01d849240b00c1408599850007803102403401c1c41d8800c0480306000d480c0c2c103000d001c42d9001c40742c40000c0c0c80707040002070050805200f590711241d18072a0b0182040720300844202085040c11000e900300b410b40030500c034081c00c58041d483c0e095030035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 350755674 1250 350754424 350754433
    0x412050a0c0810050c030f060d0615060509030f0a0308271903020609070812130504050c09090a020901081308120f0a110403020d23010e0102042111010813080c 70
    0x4043c403003420340b40c0043c080c1780b002c60140b00b0013009844401c002603201c14119500810f200540c90a03400811145880040b881400311010504980001c014080b60f0002c80c100c444080150040559030043d20700028000f610007800720b44101c0360501c481d000c04140a0110495003415a001841d0078500f90502201c128080e41b02d2007410b806001b01500511110040d02c1d0a6050017845d5a442d4406440401d040780b00040310880100100500405004010010300081c01c01110b00d041503041054414418420b103004103401d01c0d814402c03540000b0040e101c1c00d525035103559000303061241001052b5210030042042d410b00203104034019100e210b00a000c0d50f028106000080d04580c445207680709004000c020500c003680ea10f4150b986401e50222800041482c03200d860100343c500105090000e6003012504d014403001900030b4002d460303070420041c11842140d140c285034901c880c6405008098003450210807035118a08140c0d000501c114503220741c100320380d2101c0c001c3d0300411003041a03412 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 350756924 1250 350755674 350755693
    0x80a03020109110d120815031204061806080f1b030a05010603110903071a1306050301060e041e0c0e0d060b0306010501030e06010b070203120406030209041b050412050a0c08 76
    0x440803d43c0c00c0e5400c05a03001009481c05541e125200001c000521003030010180020754000c601d00307180308000802905584110010b0080625039070007c0c0908004a41c8500450850050903040300f4101d44895071800310f80d4680e045142c11075800608500c85a20240320542460720280c4025402001c182c68001000c0d032601d82c00400b150311050000d12075607010809211250703800142401910041200c02e0141a1050003496651188101009801c2c2d00c01d03400045494000e00654121031035a110310304c841d044030041000b199a44420488a4444081c500010b80072550060100d62080e00307200941c007501c0030018a101150000444986440d021842c0144c10b0a210b014014a42801c060002140380005641c070381c5014003d5540c085000b1a01405541e8108224800840c2021038036640c4d9444060040180d80490344d4240500d01307103410040d05401c080c0140c09081601d80d01c403030070141080142036203800f6240041d030b01c2d44540760306400404c441c2c640d010000c1c07402c5002483d4089 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 350758174 1250 350756924 350756933
    0x30b150a0e1504080c1c0f050a0501060602031303030c020d14010605130c0c1412030f061018050d1704120b070c0c0303050307020102070c06030b031603021507020604080a03020109 79
    0x10300b40c420700d190404007440204486040051008a1800b00312040300072110311210414100a59480c0640800c110700035038420301502260070709200380210002d1240039116803040c1d036241b00d003200024039010510803c2020034031805402070010f00c010803000c014000f82d2510103c0c000c8240321006565900c8100f005a40390059106403c014a00000c0c04401c50a15001d46034291852020340410003c950240e410f000600001000042d00c03401141c0b01d00305405903500ca54011951a4050764110000c01c041502441c0e007401c28014240116142d01c0c1410705000000d140128221000e003100710b68016100300d494050005019118543d0000c0000c50034541401e02c070143c840c00620600c00c440c100801c044500040540e074040c107000e41e0701c0d1a0001d08074028429000c1c0a0300c0400c02c41000710300305606070003000116104504079400100c013800c3e40c0c180a6424400254030040c20000402944540005480d0590008109a0400d5900c3d0318603401c000b00c89004a0040c2d6503800020100b1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 350759424 1250 350758174 350758189
    0x1b04180e0619140c040b16050109030507020901060c020a260a0f06060b130911070506090c090622110c0615091303050d11041502031c0b0105040303030b150a0e 70
    0x380144038103510300d0400c0c213210700441c03007503014214602800060b40c9079440c80190001c01029032282c000c001c02405820014819001490102c2c4220050b000018032540301d1085000006c1c0c00030442d10410303140800183e52802c5042c1c140000800d4202c400c82058418806010410b00407004024400c06d240341c240122051500241c501d410180200d00c6d03444194214101900e03d41280055851001350000b030460081d560010058407440e810004031142c041907081c0d20001c03d68a83c02d20341c40d00c00400c00c900c41504d0504620601c0240448c2c3c620a0641041c00e0f414003015400b0b00e4824041401c41c20220200c50702030001503580015100307402e01d8080664401d0b2441c1c80e00f0b080080c50b5800510f50311079454005803550322800c080e140c0e80840d408943c000c120041500c2d90072101014003030346030303080312510304a502114500f40c2c00c0e0003904c1c0124014010160343d59898981180d0b0150024545600c24540140048107203801105039440100b0415401e500e80c401c107a2404002c00044 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 350760674 1250 350759424 350759441
    0x610021e120a1d1017040303090f06020c07090c020322030606080f16030b041b050a080d18050d081b030327070e010b071a04080903061b04180e0619 65
    0x1e040741c02182401d9540904c44001900800041700b00c1e076100c6040c02c50261440150190411040c2c09090040100c10b0b40200400001c10050b5a0440e64900d42d00f41180c0c031160482c0c0160b00308018a000b045109080c413250005807803c060011901d07522080111142c90300109510781c070800e0700b00d40121003048160401d1040b004143c0c00142180c0d1540024040600001c0c2420485141c1512140e20001c0d078402400003d40100780c4207507254501c50380c47c004800c00350042040c4024004a000242d003a0300252031001d0004091590f11399580403055102c9440f0501d0181750103004080c2e46030520007140112080c400603601100151902c00d50f030220011240c0e4568802e90040000500d950305950450710a41010b5440d0b6910f414005c251800441e40d100f0046601010001000f541e080506240e0f42c1c16401c640599803112048a034000b81440440c1100c03505003c20800350007241000b040c81c3c030300254046030000149440600c4c01308151082d110344041c650744040c400e071052107200703003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 350761924 1250 350760674 350760679
    0x3020609061648090e100f05010915031709010c080c0a29010e0c09061c05010b03042117070e0907020c1e010908030a08040b0610021e120a1d 62
    0xc2403c21a96411454018401d809040340c503100401401c0c01c0a000300c041000c0d030341a083c80b00401601d84140140b10034025007000c1441c0c00760440c6204401095642940c0d030245880b00c14801e88031b120301550b0412001c050400201458034070000b080503000d000884440340c02448403200914204071003403800300d07008001c1e01c092498100b0b512820028541144c1d003030543e416007920340d080d00140c584035000e4001c4e00040000345110820300d440c0320b8440c42c910020303001c1003540d0721400d40800900c81581e0151001c1000c50b050030500092050035060181c19041404202d040c5035010000c1c40d104503039646c0440c1c1c150220742d0003400c00c8445039034401518400303410f00c403400380006a08440a4001c2119000c80035075141080c0c0d000d0701200015080100840743c0354060300030000c0c00d4410860b070440f481c41444000c1145414101280351075058150050241d8001900c034640c50030360041c1401c11944540140340160104c444000d01c0300c000c083d0b481101f66480e100d15010030049080ea03050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 350763174 1250 350761924 350762033
    0xd060f080123090a0609030203040b0408030d0606090e011e03021503070e04051b07080409050907030c0801020406090b030916080309180919030e060f180901030206090616 75
    0x100342c460110b44ca0b18855401200003400b036007a803c040b40365000c3c80d0803038103124000041c04900c0880002c0a001413900c0c40f44144090340e254141125a180d0078032a5000070007000005018042c0d40300300c030300b0032085015803018200f5500c0d000141c802c850003030303200d090720000018060290390141401c1c100020a076424003a505010301404c505a0840c180c0d5403200790081080c0d410041481d0841d00184203d68040c860742c1801e4800e180c58000030300c0111b440011600000403442410b00941d02100c08981754907044c940f424644405990004100303c1c194001d0701c0044400c40c11a06020020306568001141c4070403010081c042030001d030044c0e190040d10a0810818501400120260038407100b001b844c8064100f440c0a130340513144c0a0750700d40e120314049010075842a13114050b144114107040c125865821080c1444074410083c00080e40102080008040500341000201029052104000b1100055440b50041800e908000da49811506020103880074802100c680c5502c04409209 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 350764424 1250 350763174 350763181
    0x70b070e060a271a09060d0e0f060f040c0e0c090d051609050907090c09080d050d050c13060522030b0105040501170a06270605040b07020a03140d060f080123 69
    0x508031046942030a0001c8000180c40a80f0b40b2140203940c011813110005000480440601276100c200200c0e8035000f921811001500c0d104180310010300a0760045c0001c3c0034242059a4070804400c001c2200b2001c0208004180c8207448800f1400c0e4100d014002400c014840000341c007442c1100c691000c1040c0d406c000c1031106407400030032007030215044403034002502040b04000b6103121109511401160040c45801010140c0010040c450011409002c001c15a01c841d62040346029050034444940c01d040024003026014070020580c0c589581c00c01640000c001051618100407600201d03000311303032100100300c01d00b0a40952405041c0c06100c00c00d500c042103078007030782c1c0709081d0710003801c41601c440240c1c040c00c908111200400c1c9203650741100c1e199944c03c1100c040d12091b01c003140d01d0074120000410b041c5c40402c420b410141d06681e111740b099480100c2e4a0141c00100a00301030a42d0740e200010703405041e0380d540004100c0c00f00040b481e1101000200c80043e003070f020455000000c038080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 350765674 1250 350764424 350764439
    0x1a100603060806060d020d12050403050105070f0e0f011215051c05481003050603030406110715020a12051309230709030c08070506070b070e060a27 65
    0x43e00da022000b640c403601130000c0c1d80001951001c02c2c441c05443c0d08202c04c50b007034405038000700500589005800902054640400032112117440a80b4000085c0c110000b0100c5458540d03050001c45c24140341050b80c44c404074180c01c089601a00342e581601c0e005140422450401140c040005104990300c2c00d2070f210b458030b50684609101180e6003030b90f8034501000c07515440d512110440742c2114004d90840b045216101c3c02c40039032501a039403040c140070012113015403090040c14450100680a5800c03d46170100540701d01c00000c0300240c41e8002c508002c5095080800d96003d00d000d507034002c00308a0500e007450020b01180c00d4641c400c01000f00402207511007210895022254034010014611421080d4201c10b206100c001444d4026094240051280c0c8683c0e0b00040d02d005070a001d4030913030b80380b190343c0e07407600244503441c0c01041c10301041004c500b54a0100303602440d24200700d840c80c9100360000791325a02c83c082c1070740829100703e07003507a041030521145c010300303900c90b01801c0199040140707 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 350766924 1250 350765674 350765683
    0x20f0d090b03090304080a110f0f011b0c05181e0708010b0c0115062f060412170408030a0605040203100b0d021218010c14030f0606071a1006030608 65
    0x40c100e4074010002c041600c81ca070420454001340320700003d0300e10400c3c6500c0c00c7d181281052281a114455032250303209140b400e002103198071034050b140d000c0c03110009082c4020b8400c0321042900c40f20407030080090346840b10340202c08506c0c1154620703642c9207400e0401d00fa50091841c8051012284102007181103500401094191849004210740b03a000104050707002d01030004406152500ca08000111560480403151903840700714030300842840c044103044400c41c807010000c000b41e030259010801203100100320301e0280125181c041c880c828148440c500101066408440540000040000c1403400d0b22842c0c02501d0115415461130801011100000c0500d02032420041e500007100a0040d4040d8120f800c4000a00b841007050b20f4a06920355a0800d140c001c0d070025400c21540c0c0501e82e11030340035101088100700b03480d800c5891f052101440d81d08010086508000304001e00000b00f10100c0b020522070b140f4034001501031411800c00a0208425809101494240b06042c0040c00d000b04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 350768174 1250 350766924 350766929
    0xb0406020d0f0c0221030c0c10020c1305040611040b030a05010f06170903090301151403030715020c1509010b040b010206060109030816020d0308070f091401030b1519020f0d09 77
    0xc034484420303902c1c250700810b80d05c8881c142c5a290321001072483e100a5000c5035940c616142142c91081111002c04140d0b121440320050704d500c8120003031980f410030950b40c0b2164010b8020000001c1d078001340c0501314031503849034112481c491008401c20200b080c881c042e0740d026100d0020250070325450520042c2c45013103041c1022945064050000303400c40700c2082907440b6090010001c0c400042c03a02201170328201a8010b04110074801071014145086c00411507001c0d030340c080700b425000099000203000a41090751701c1000c0e409540c040e4030030340810380300d07140c033409440000140c02c015141c00c21040b250701005130350542d0004ca08016880c2e0300000040c0899401c90351559032002858084a4000328041c0d00a6001014008441c103040d40070741c0645c40341502e501c4003084801d26400070384489a480c82040b00c64610b60344c50a0300c1c0d502c00d40203001d0209000d455030005036020400c44440343c01110105641c00007007241040d1060381007112054140180c800380100107001d160007440d044507030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 350769424 1250 350768174 350768179
    0x30903120a060e1501112d1902100306082b0e030606041503020d0614010b19030b01120e24100303030b03070e07170106050c0d0305071101060b0406020d0f0c02 70
    0x20313080781c1c06607409050b14004840c0c60f1029901000f10f42410300c0516480d8030310107190f0002505005410174000501000104030310714031076481160f2907007000100c00c2015481b1040540311800060050020018112440d445940341443d4010700c0034425021071a001d420f40030007000308501e80031034502081468020030705450108000d284d840c80c4c0d00d44400240c2c0000e4100580740b031100c09210455202c81c0c0d070148048070400c00d50b661201b1708502e0707001e0317403400e10008400c5d0112008080e0290b80a240a41d10606104018014054112046454901003500b040c1c0100d5654040140c44020b10003488082c0f100d0311880d401d01140500e00c140a45c00f0080504d9960388408602c2d5070700f00110720080026030342c81e000d07618140030300422800048101c0c2c0d04c040c07550400403960501405c250b51451b0a43c00040031540b000307805c00c9001d000c000d03200c0070a1081020040000c5202800b564000e004001c4040303a440740b904200031310380350074400e403081003001241c94281c0a80d0700a180e031032180d404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 350770674 1250 350769424 350769451
    0xf01170a0506030f0a050a031b151a03060a09060c03111b030c100f0c0503040b0712060b0d05060f06091c0809120f0c0a080c040504050111030903120a060e 68
    0x4002c0464541100c0c0a420074a40c8110074010042100000b00140c070103119a80782840075040b8115407a4078281110020105860404402400c9a5550010180000800418149c10100300c0400d082c01400d5410148003921641c01c041440303842d0007050801c14441c40c00304002031390003c000714280900711084403d22030102d143d00c0e056404005a82c0c1a240b01d2064440109004005d480181000c15a96142604008a8490580c00794056030b2003150020711150380d65484844c1201d05101c4d010111011903507800c0c01040c00c0c44058081e004100c851480082c080c141401001403440280c00c07403611030601003100340211340310160b03501000405100300126000c510300d0080154000d040c1e80c560406170007140d8080e40c08001808020012502d410340e1400605c02c81031025154003400790320340940c040d01c840c5138181003036805164002d00400c000206681c03a44408041c0d60301c25a071034101c82e070000c0fa0b440210010f811109030803103200102040740350318100318050034120040c1015000300e907 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 350771924 1250 350770674 350770681
    0xa0204051e010212131a0f0318070b071a0405120d0213080c01020c01050c280b0a050c1812010c09060807030c020a110612010801020406020c010216170a1509020f01170a05 75
    0x2c0120681f40d000c849074000b0368a916007110b9203880d80041882c00280ca128071a00043c403142c000342100c0065800c49078000100e081580c09244072030005d0002c0f1018400d0560041c0403074200d401a1585c00c02256015988030340103510650401650f800003d155000a9180d601170307a00011000c18140c0c080c04c0c004e0303d86a1703540300f150914501010020600e1101583e0f00000b8054104401103030744034006109c5503859a0200000321641115030a801020810840d1506040c440303100c1c01e540c00041642c4010342094424030b085d9a50b019240340031480540c41484681d03044090168411445d2608100d07017004103d0003981e48040304c0c0c0240000c5496450307024182c640e20119129150800c114000c55691480514000e600c1442000018001d04080024940c03002c110300c1000005850412401401c03d88021721070902080400464810040440d0008070300900d1068951068200040c02840c00d005100514000000241c104000070b240d00d0103250204590a0f00040a00000261981e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 350773174 1250 350771924 350771969
    0x1207050415091d070c150902060d14010e040503071502070203030a0f02070518041118090106030b01061e1202040b160c1a0f030a0204051e01021213 65
    0x2165070440715501100c054841c5585801424100c1298140400250141c0f488800041803c1c400e032441c40000b041c0c0001d8501290710344d5051100340c0034040d000504411142d00048070f0354131160142e050252502c00500b0044500d1103118010b20b0140c071811014a4942e03640f070340b81d1040f0f0b200240a1550a401200203052641c1554900b5a001e0b007160b50b94401c400c00a414186100d8203c03005118070b040204141c1030a040a40d403500c2560f900303041c2a00c952759229201c003080442d45801040c00d00c040c0e9164440c0302c14140c016101803000040640c21410701000d288016040203050115800c6a022200c1101e80900c0d0542c1e2a032038400c0d14502c1c940041400f074440c5070720100c4445000700d0030244c80350418184c55034891040c0301c030814007039481c40351145102d500340290340001c001384110715214401c2001180c4c419040b4030014034040d225800a080304491001d5813101e5080400140e9a41d40c04000030041201c03141c00c500d0400b200c0b200c069400110078002c0b5840d01c03501103500d203141d4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 350774424 1250 350773174 350773177
    0x210030e0705101706010201060b07151104030813050d0b0109200d020c06240d03050408010203070809010c02010516051c06081f060f032d0b060a0503070b120705 71
    0x400c801000404040f0307549200422803007400c0403040d0b20b07541c1071003c510507600521074081140c107202486410101183c0b6606181c40c03510b101180d41e203417102c0d542c44d03002110740000c0020310303c036142c619228040d4075060050b690054025a004141c0d83c5100c00204540c10360350f80c1118942b1101040900a5101c002c000760a004101c080385800440d0a614024898002c0c0c8500da01010481d1a20381d29100c044613290410849800002d40740543d07030361241009030207159841c3c040c2c02c100d403501e561280c0040c00c9900807100d500000b401c0100b8803001503020b000d581340111191000748060304000e0082c005400c810380e04601401000600364200260607250031040410f058800c0203001e075140080d680310f0340d1070031001d0340c0800d85204c0301d030a14000744128016181da00303900c145194150781e5044001901701d207101c6004600e0740342a040128a04401144041c031a40350044641406018880142c441d600614800e404c030080a00000c0055016a0300610010344c6c07000054440005c183c030075 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 350775674 1250 350774424 350774429
    0x804030c060e0a03140f0604140c0312070602130b040306020301050a17100b13060801152c06060c1c0914060f0307050c0a0b0f0a0501232b0b0709030210030e07 70
    0x10b80511001c108c180300008850011103a0754800780c80f2104908000c040d140c10f804800061003c04c103000703400100c2e4036580640968170124181250340f60f02e4141060381d6030010b510880b501a0000010301907410071414040c0244014044a40041c0c61010480d44403010014540c09039980e95800c404aa681c1d004060252024010f042110716181c140c480d001e000d22603072001c0501c4030706600040112260745030301e401a04910300351540d0711a042803c4000305010305801d41c003d009001440000d401485440803442c4400d825114154030038102900c106520741c0000b01e0001420308016013a1141b20484ea940c101d1710703401c036035240e4807608156201d0281100ca40710520904115808201300501000e002d004903c3c034521440d6249030744070040e50002d00401250380c4154000c40600301104200d0809000001c14003d200c0e001e9150b00c40307110a00c801e0f43c40c0d10150484201e42444019060141c1207181c44ca0004443d07400d40d000b03d50305115060307088080503035070110101c1a950901c0034901 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 350776924 1250 350775674 350775703
    0x703020f1204061404030801091a06030f0a06060207080a02010302090a03080c030409050a050103020109060e0111030a02160503060402031e0102040317091003060503061602190804030c060e0a0314 86
    0x4984030300015910703004100702c6040f00d026107002c0c0c08001804610921900c69645551407000380c1e800d052501014110512240f1b51800c105804500555180c002540c8100a41031128003e03241208135802036410036408802036402160742441030150204000c4941602800e0169480902c0340100304609030a030f1010303104c000007007205107004401000810465031252402c1c006600c8004a102c100c0c0c5007032100030b0100700044c0040041034014003403203e603c001410f0000100f511012a5800c66005d00328020040c1c210804c903c210044c924049009043d0680003484503107030550101c5c0c0c0e5941389905171242409050440405603400f5011603000c1d5900080e1012640c0c13101c01c00b195290090300312070f03114003010b40604124901c01d10a150880b003000f001400c0c5500c80030350342e404038100d44981e001140281204045201c89a240c4100000c1c85603c030190345501d1424491001d0100d5085030082101a030311751034240c2d443c80024420b2704e4000d00c14840d0f40f8514103026141c6a2138104120 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 350778174 1250 350776924 350776927
    0x10831050a05031c0204080a02040e03160302060907090e062a0c2d0d08100e040c030c1502030702100c2009161e2d02100b0d0b0703020f 60
    0x4080041c040064940c0c02c88051510242c00b06640c1c2132010781c062402445402e07480307502480007503d0190040c81c140003002d03042c0d034607210100400003403080302c0300c10540140c0c1c0302200380304c4c148108203d5603009040384441000828082c100580e29010081c0814925a402d100094401246400d507000045040130140365903007142001c050704d5410f01c01c07c00108241d607031a080d0403c42000168051003484d01b000d00401d410480301551401c6020780810800e00e0b8140c408502d5901c00040316016902a041722003040e403441c03900d1003111200750402d0b1040d01c0000700700480144c00100b9588a140c1c1298035105803910118120342e010b454001c050210081c0d8107040c2e904038030b1180c54207200700b010341c3c0031101a507500246240c0c1c0d144000d42c2d200000c100364030b4600b5000c01c903d0b0000201c00503150a069400500b0210b131070120401400b46604001c12184540b1550100490078407815044424010407641400003041116410700150040c0300210004000903c00d50407501c0c801603c0b515079 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 350779424 1250 350778174 350778193
    0x215040606051509300f060108010e0102070302070b030a020d02030c0c010c031512080c0f0d0318020109030b040501290112020301030c0b1305150a030b01083105 71
    0x5020701a00c1c80741e10300030070019480999201c080402c80300d0140024001c0200c0c0c42c2c03000c20079000340700c010045604500c2c0045c04803134a04c1e020b0004a40c6644600d00a064a5044c2001d403801c40c0c07915207803120f541c2c1c03042120200180d000300700c0004442e0b9040c282900c9545501261000c0c2c443c00060100c1d4501c0002080f40c902d00c00c5010381200380c0c0707070402000182c04510742a0110b480c1e4103c1350950398200d002c02c02c00c1228801007401c9841c40f40c0d00301d50504440040c100c0c58410706035521505500140b00c010110343c1c2c1071060f01041d8084003c02c10821341190006402400c0a00000d0060401480018103119013500710000d04516403080300001e481c403a81c061404801054103d00050000c0d4122400f6003080c0242c0e8144c94011554100d603514003030100c03607194051144c05500b85010a400981d031b5442442000048041d10809a522130032004000c084a039620341c1e45040c01241414440c0c00c443c910401240600c031407800701940c0400c4403152000304d12a1200900510440da0b01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 350780674 1250 350779424 350779433
    0xe0c07030e0a0e040510110301050613030807050703200f040905160e07030c0801050303190207091e0b011e0509040e030327030f0703140f0304050106180911040c021504 74
    0x3c00d00c50380c0203100752481c5008143c03541e0240d40c40884400800c410030700041c8840e2414400034a040e462031200524400c2e130381d0341c3d440040e4001030816603032031304100401c00911100d90521070003010a2401c201c900304041c00015180e8410842c06401a540d4448031400c00ca4100500100c0c18503405c182003c0c25070716000c18981120848038900003a041441c1001410300481946042c2c41001f0090350400032a01081e08505c540c04644601314810003800185a901d203114034402d50301414000c240f402105c209840540740707980c190b9410085200072070098410a98030080c2e101000d807a085607a50103040009000c0e0a0501c09010640000030274003a0034034014129400701101c000030421807401d003840c041d40f24091b94098481e40d403000c2160301e000a00c105040801082a0008241001f8658aa62469404c101d0f001c8a550707540ba00c06001c01d4500c011030f071481111708030007031151541c0c955818a00c021110b15450059490b030300c0d09003040d4020300c08800d00840b40d84981102e0703e4141030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 350781924 1250 350780674 350780699
    0x80304171602040b011805060a1e08070201181101080a06051309110a080d0f030204090507030b0307150504090f1407170c040f031b050411040e010f0e0c07030e0a 71
    0x70128896407074099010415400303211906002c8a03880703041d55109141105002040d40404511001c0240c243c01003440c402070b1fa10088510401d03984c640115151000c0042d085841c21513600c9542c50140c0f0411300080c070701070000f421b4008203203042450754950000f40c002504458100d80d610681c0c0008129000b11103a0140c2025401a1500000b114242c020b01c0f0744e4199600a2022a400990200321000d001d00c004694a207020300d80180707007580d203003904800c8880c16a001c000094032001014490b180400c406800340080d84080000d940c2c104101a299202c0c40c0316040740d03d40c807914100c4c542c40841d404020014190b0240c0b901c280391aa80c002d103618600306400d0a501342d00b80101c0c40d0100030b101500d0030389440c08444643c090458640d002d11918820b100c40c0c3c0302c0030098020456468a01820060340c0f12490015142d9040a084141c00c1030141c11019080314980c00c00c100c40f07406250240d4000000003101550f609243c2802c6480d0302030b0381ca05540201042300002040080e044 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 350783174 1250 350781924 350781967
    0x11030315130b06070807081e07140726010213030b0f090a0809120109050a0b0717040c06080c1b070e0c07030f44090304030f08030417 59
    0x41e80c0c06803500803480e01900322028002403c3c0c200c5024801c450006a4500060680324010701069040c4010184c101410640c00c405000d18104081115002c2009044031066140c100e54068401d45082120a00c5c801c021381e400110b045a04030125000360800394102c1d58007920102003103030703499140d0402645a010a4409a400c010418001896004081050b05509a21284162608074544200150f071148074003020f440303540c6c502413500010b0301000700c075151501c128121070062800110141c0300c12020b40a4402000c04078040000285202d07030000d05884e180c0c100760305903407140c4a986030740340600000c00301352020343d00c0702e0440c50400050420031a0140f440003052075940c3c4001001a02500c01c0080118028025041c0300501172a4007000c1030348010300c80a030f10440826514440c2d00254040300c1030000e00800309801d510030604136075208000100541c9854070310f0341c0d180300105688202510b0b8a1700800420104200e03040e0720840c02010221303994552041d03a1500304c55240c13a2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 350784424 1250 350783174 350783179
    0x230d05060a0e090604081308030a0806030d0309020f090a06080706030f06150e040e01020c030703090f060203040503031e07200a2313020d02040608040c050102120901030b0111030315 80
    0x10000080d42d00c103401c8064032550b8104060a420303110781da9143c403290440e00500c10301d04800e481c00310314003a0802c054002075002c1e0765040d5890500c3c070149400c15200d14202d40805050110010258850398920840c2d41400c1c0c9068450b07035504150321000702010703040501d0364042c0000004906034550014424803419070001c000c0d01d680c0e54006081d071546105010045001004607501c2807606034043d4000707036026000076250560341d104140c1960701104085010400c618018000700e00008400400743c00355000131845c2504141c0040ea903402094000c481c500d9403484546001520001981c0609a2203800703804440300c202e40c1080b1110301d06082c1030040821102c00100048440c0461304901148814269940501810701280d90708a0395080c1500b038080004418685c054401800240103130f40e00c103400790030503180070030450826621050440d884070880074032001030003048031030f6041e0900f00024900c04402c0140c480205c071109a12150001004200c03490a44000e00401407004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 350785674 1250 350784424 350784439
    0x70302010c080921010509280c09150905090304060c020d0f020316140406050618040b0607050d02061f06080601120c0306080f1603020405061219120503060907230d0506 74
    0x195107030141d07038031404c80b0960200c2208d0b000078031402103101d821a14035401694000705441c3c4403610281940c2060301c0403141000ea582d4200550034107840b07a6a085815407020310320f001d191100080000b040600064854009600720300c0400020780003408445501070280c1340c540da9031480d4400300707064a218a07814240c456444542c1072071f2500c5090191a4010f0515091415144843d40000315484000303030031950310021800c4581e034950141185030b10130790042ca501f5000800003401e0200241501c00c510451100708043c1c1030100ba8244151400c504d0301d40950f07034417040121102c420075120364014600c3d000c50b0841e415456001481a682c0b8142240e0013070080b585020b90f540c1401454113600c00b6240400d10051070180c0000d60440c0004211501c07a004c4007000c5170070181c4d00c455500009a06c40110820800c041720075004c00e1116041c8030303082d8609480130400d0710100410381020030180b05001c1b541e40490300034501ca81846202200d849a05c0703a40b80900801050310042d00ca10312 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 350786924 1250 350785674 350785681
    0x90d0b010b070b1e0f09010b12010b01090f12060515040e0a03020c03030a0903080306040617010e011103040b070e0303191709030a02070b1317060615030108070302010c0809210105 79
    0x80050001e080410b143d04c00c080c030f591504031680c1c4044000d000e040c050b540f10440c002e0b05075a0450b0041c40030360500c00008008100d00000340908030329a10800c0030031540d02c4100071440a100b03c101f100d6810500100d84e554681c0c1e6a140800100385000f0f078054030f03296035110300210018003030071194840c2d0210b0320104040c0d81055540e004010845d000518890020300005109201a40c1c00c074102030f20214802c1c1d280d07201c4d0031050141c0d1803031110760b0b9510404038421800034002c0c0894a418100750380d145d81803076207407003140080082250081c0114000c200c1b0154a04004507404001c40388844050380c5a03007880203011811000f80300d81809904c2000c225100e60200c101c0c0c482001507001010101d00c0d190103c00c0c140c105e00b04483c841c000003000011450f080291281c4a44001005030999180080c00c201e00880203881c10001e01105200510443c10002812000d407502402e0000300c410a40c0f80c5480c0d1446030080d800d030003140b00658007011100b411000440da4107690001e11441e40c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 350788174 1250 350786924 350786941
    0x50609060319053301060503100e060f150717030906011a0705070905220201020d140f041202010813020108160c1709010f030207020a0902090d0b010b070b 68
    0x2806031121603241d0410700302940e00e4214280307440c007120302c81c5003a01d000c224120180700c52045406180074100b10390100d2425829030381100c2038091724036800c1941c15428032103110312000d90302d0701941720a40480703c08030700700341d0f645138440359524001425880015041c203164540d507040b42400311004241e00c000008491410b006a91181d4410310040c82980e1030412038002040c0c000041d40c0c040e5004000318808600c0c14050712000e05407450303001c22103081c15010f04420403441e49000c4110440140a040142c1e404105600018020301e001d4031900b00740400c0700c440d840350350b813069808880001d000414900f05590382d40002e000b40ca4194141e45d9071300c1601515603c45200034006003021000502c07801c001e1211241d22503051a09042c5c00d4841d503101048001d440a181c641c800c0d012400f08000d40c1d01c00c03a0810841c01900e070030360428601e40c0c08229440c82c2805007801c000c0c0c02041e540199107810b102d100c0d00c0c6130040ca0f44202075a48400d210802d0384203280c25191441504c000403400d9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 350789424 1250 350788174 350788189
    0xd0c02010b030c0303120402060313320a020d06020a120603050109050d090b0327060f0f100e01140607021009050a0b12060103050a0f0c050309071a0a0509030a0602030103080d0506 79
    0x40c10b420140d01c0c0ea40c1f19800c1103050303400100060540c8903080c0314a004101c3d83c0b02001e544041c0c4525a4541c0880e4210301e50300007407031440640c0241d00006c401c100586842554652090388050050b8171105000001c4e00c40000c8185d0903002e062800354000705100054000003407150044050b01c8507203a4000b4200c404824601030704240260030800f08505441500d80090701c2180c08603401032120205445504240c0191070203808103180e0014020241c190392115604054503808400640e8074200482c001e24105108441045550550102003a200c20b0111001d10b0343c0100070400d500b2800b080078000c0321132402410b002c1c140b581e0012032189004000c4850000060030840b400780d4072030004402518000b440000310b170303889000c11807400a480c080c151600501c2d0b00c665031280f810340305241c84e00c481c07940100405030b102d0023220703c3c5601c884101c510101c80f071320703001da0342d42d014030302180c03420003044001030001c0e01c00800002803080c420090403800143c0c440a0166454240c104450b1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 350790674 1250 350789424 350789437
    0x519030f0f0e0d21050a23130e07020d03020c0d080910020c07060e060f0301030b180303090c040e0c0d14070308191209080a030b0310022110060e040c03020d0c02010b030c0303 77
    0x104100b12030b8040340e0f2175400d031504044291525041e15002480c4423405a41980e030b440402c3d0025600107200c83e068040c844000120304030b15045003811f10100c483d9903180b07031030309251050040503801f050404000303004441c00300700110f0066690741d0080d250683d80d525144a207100045405246020b40d24207001111941718841451504603404d50b207580c0c9a900014010b400469040100c01aa2007014000703948101c0300e810261604a44602c103200544151844100040c1c0000b81c06c1c80b40d96079540743d01500c007030304114003001d0014186d011510b0f0003020b4001030301001c1c01003020305000d047c10380504070f040740d26560822a8180740d850305003681c00140340200b00740700074460540283e2080e844005d6900004089654008102c1e41800c202d0b40080c0c0030500b207080e030100b200c05500b100301c0a01e0b044516440380342c042030314000c002071803048400c00d10341c0303d15284d03880a40c40500c40e406803041c10048044c1000200030660011303000344500e0a2903800781c00f840314904554034000c07003034822 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 350791924 1250 350790674 350790677
    0x1080906010e040803090f01090c2105031207170a0510080a0b0c131802070204050c0c1c0504170607030614090c2104080301030519030f0f0e0d21050a 66
    0x1070380f100d507100400da8100600d80f400d035105030a020032801d40c0900901c60300b00e002e10f49541d90182032070485031401034a117001940c0700d008814181c00050f000001c40356507420410001040d03031a82c15045400c41600800e03014050104810b20200c0d8034103a00550154101a003240c004a944a4031503071100f90b5040085c00c100b2001d07001400740350404000700780da180e110f5004108103849803c80360810100c40071442001d0b82c0482c286d81141064812190030001c4a44c041c2e0410006542e070301d80c0c80d050280e102d520905012203614040d4001c0d01500c001d040421255a582d00342034171202c1d03803010100c41c50303800a4280580081e102a1400b40006000c0c80985100080e5440c0034080103640c0c451a180c1103001f40660340c140050100f0100540500c3c4290304c420355030b500d103003090b502d000280b10b50600f40403120112440000d800440c16403e212007800c201b540c4268861095443c89521680c040d0880b40b003203486c1040010840604092003003901c0b0b40050521003180454650189c420301e00d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 350793174 1250 350791924 350791949
    0x10305060f040b01091e150908100b011403090321060f06070807080a0818011103060d150c030209181324020711030f1b130204150e0108090601 63
    0x5500d090a40101ca43c0540c1030403d01440303030f41c40e0a250080c60311035610724004117401c207090103600d0041040c10405242c1d460520429070074418400e44038540002d4842449696040c258940d0340140f609161781c110454250fa10303880c02101301d81d140c0d4000c00f00e092000c04040070700d04c008070310580410300811000d0a1054001c442c08140709080e03018403801d0726041c0081c00720000103840e07000108904112a543c60b0200d00740181031005518144c83c02140d07990410003600129041441929030003501102c00803581c088900740054010b69509040070078504107807051891507095002821a101c06039020301140c0c00211603118001d0054840904201c0c07220040d0f40850f03650031194040380d4274081ba80e4041c00404425004a034404a000c54a48500c01c042c9007461500348620382b26214100040c0c05446800100b174160130403590031283c8503000d10380d501c40041c1c401c2d41c151005010502403a4101c03034503030803020f41920340144409000a40c09800154600c0b408a143e5040300e60342c08032170 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 350794424 1250 350793174 350793199
    0x509061e010c1a04060b010f080405060a0c03020705071509090e070303140c060f0709090509070911040504020d0f060510140a0c021306030c122003010603020d08031501030506 77
    0x1101e14440b12103007520811441c85841c11411a0a49024010345c821030000601c81c0005e000545820035030070340c600a01003031001300400305101040e034a0744031044160001c3c0c5246c500600754000d001303111010700688030f48200403401241d038400c001d01600c001c3c0c4030340ca10a65110107071800c1d0340001910302c0c86504a0001000001d0180001883c85400c0e400c4190a14200c00d94440c60243c0c111265000040c0350014007286a07000300c040c1e0041c2c052920300b4001403400c55180c86d03441e810380c454524076540d19001c422420040405803405400c006005659402d209640c82c005440d0020010443c58501400000c0c9840d00081180c021251520b40c0c01c044103169203c110f0075080314040e0f03824271100261040060340c41840c1c01d81912040307140001c41d40e044d41401d40915056402882c02201c0c000c42520202d018100d0341d940050460340d20001c403840700004203004d006107600003904580400810420400303008007451040700550400800240d1031310045003680e1095500c2d680000160102 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 350795674 1250 350794424 350794427
    0x60503030f070b0705070f0c050f0405060f010c14031204112407020402040f06020d1d010203040506070c0b0418050604060e01050405041103060a0c03060b070c060807111203010509061e01 82
    0x502e98060045e040080c00d201d06a100c980350001040c008480c5014804814001d51800f2a4600c41d5818241c4040050b0315050010500103038140402c42e0502c0756a01c00c4030108496044868501101c5209030790300c42c0c0070034400d00d020b5603080e54125050740c00c5401c001c00c6401c160003540c8503400300215a405480c1c50710001c0c4072a034427070101660400d400f080041303664400e103c0d40700014043d6a0003480744021580e0001d01d09481081c0504041c80105010142c0341e0340042500c05640f001c50b0000d6803012a450030401000941e0f006c10306805020800045080300410242c4203050203000034020b0350313079220400c0100c0741103010340b80103ca010001440b0303e081c15400554070500c1000211240c10404001034a403600442c2d01ca4100c80e00c60002c0b0610640c540514001032400014203070515051b40c7d01c1d10300808060040c082002118000620018464162003444c8120a000d48801e01000c515204580d8024050b850240c142d0b000810321074205200c11290b02d4a0000b2484c4528001100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 350796924 1250 350795674 350795693
    0x3b0f15040302030c07031203050609060a06180e0408030108151b1c29060304020f040207020a0f03120807020a031e2001020903010e160905040218040b0703060503030f07 74
    0x4150300b140720500521003410020032520004d0b5006500d0024075100c0320700300406031003009081d140103211880a00900341c40790958001540c45a00702003650140307118030030400700c03216400107146881200500c1b00b40031420005605a80c0c0e00d5040c1ca000d0200341c203450a4211080c0d0f448141d01c1500c0f81c0c241c7c50540400d018140200204105030f88044d5071040d050290350080103d26000490800c101c1d5101d206d1000c1b11000000a95200e4258a0240c000640074044800f131103000e5a00003520404560300d00071080e002d0105210303280101368483c1020400f44d070004c000340020038003042c04240000c6c000070703102d001c4a50564820741c02c0361401032600860340759440d00701c0911079141c2102c00f6280c607500d045141c0000507800140c44140c10001c1501355445d02190079a180c00281d2503104000a58003400e050f2038003c2e2001c00c3e0342e00c55102154418008500b4002e01503a142c051200b005121034201c1d00400740780d030f070501c080b80d02d4408043d141d115280405079000c1e41041b1290010380f4405 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 350798174 1250 350796924 350796931
    0x60207210215040f05030a0801060f0c080f0705010e0708010b010e0f0303070311010615020a050105010501080c0d150b0a0809010b09090a2a06050c06010f0b1b013b0f15 74
    0x21281c104d0759500d944079465a0440c542c00c1d03001c1500070005021055100321000d051100e2883d10341d903403000c151206a41442400e180a25410000550b00f060110942000c16092640c07030407607100031756400a0300c6c02006c00132a100d000038010000000a0700c1c1c0392000445c1c3c1840103029616100141e07509032084030030344400562075529104001070700030f507010903500100c2468000d8004081e040ca401c500b140d00503000355050003050b80600ca50a03004000b514401d18035600700140300c040b808009400d0554684c880800c0201c0050a04410769101251a0190030918000e0080d910076004004049078200c03007130302032030b401070b05400702041248800d0140d13801c0e0140303c80585920410685000d002d60b030803c802150000540550b4030504001003030050008003141401d003410728500314080e105a041b20303010800410101310010b4001c1d80620118032000d1030741555000c005408102c0304a000211034a4000c9080e610150300c44041b0f803c0442c1c0386254050454000300340560451202c015 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 350799424 1250 350798174 350798183
    0x50306130609050702161d0105061e0d0608190201050d020a200601031b05010915052a010612020d0201080414030706020310060f3906020721021504 65
    0x3100000b031500c1051241500130f64141d030160143c414503001000c00c180d42c0d070303000c496032030505846080241c0503600440d05440f000c0764541c0d0354403031a00085c03118003684800c43c0020103001600115070401584040d0480704040150354068080500c10801182c12000113408140108584049071032264000c04911502d402d0030703410090394107005030201c40c08e032a101943c0c1e4400c0d0300600511695600185448158204c0750001c1800c00c800200400040d00c54420700b02d90460700c01c07601602800c107032241400347d25580c0803840507090b9003600f00d402c0340c1341480b030350b500e094408100360306528a0204000e40150580202e0081c9900440f9040c000800946199525544450341203c0070b20081c0000da001d8500940c480c01d02c51040302c200051540b00c20280b00b101c540e41380d0002d800c400d1004407946401c03150200400380ca501d140041130200400c005240441000d4402c000300c0354081c05040e40500c0301e0350740c2e165103000380c00d0f26145005030b2070300568000b10500800ae00c0039443d2a50143c0310307 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 350800674 1250 350799424 350799431
    0x3030f010603021303080319140c0405040218041b090f03030903081e0a02030915070b04060b130f23011206020f090a1214120a14090a0e0a050906010605030613 70
    0x1646c40740c5c880340d04180c1d4600d00f1b2070403017820060f540d02e2034051044080076241e0000403074203140c0d401844510a500c19507000e15008124524010402c2120100068001d8070501030b08508180400240710101071510214418100109050748400680e01c140d96140e1900207200781076440e0840c880e0800c450142401c0d081100b0844e00c9035441010f004001e08940045841d081c1d904200004403614081c3d06900760b4041c014000440c1c1110102504690131402c0007441c21b000201041030101a180d030318000c142004050302c0401c003150711040c07030340038602d0610212592407401d45010610a01c17440d00c004216400c01e0f40411401e600820010f001610100e10300100e45011801c009072961103101c900c40b035101c4030b00500143e0074540c8040c410190180c045e9085d0300c10600c0040c083c0c51144410096412001e89115440f081200c0e06800018500c802070f6035030703124010150800b00c1d14032000b503090801160701010001500c0d816503001c0d0701c505086580d54000e0007101c070b10070840700460648 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 350801924 1250 350800674 350800679
    0x30409090c120c090c0305151c08030705070c0f06020c130902040603060b04050a110a0f210203090708010905030702040b0f09040b0105040e0a0b040308060d05060a0c0e010203030f0106030213 84
    0x402c4420500350510800c01101d101d40703415000421130308640781300414503003004108000e01c9000206000300e10012200c0c114140c112226080e80c101c0000c000511801c030000c00e03c140c46800c00d020f420541e00c0f91071105d00b1139840c0ca080090380d004510a0001592088140701800d04e4404158221740106100c00500308903940c000034107440040d8010f544160f500c114400441c14a406000c0d0311408941c02030252606600404801c3e00c143d00803d0b003086000000041c660703204100c0b4070580f42025050303105210300110313114025841a01d012086102e107031000114080103010709420941c100c8041c505014143d000d02003e021031044450b8015050316030128079998009860b80214041d00e40b40340b4960504042c072040b100c0e00c6004d201141e00480141c00090000c5881d140d00c9585031801034041d88a64011840c81480c0c4900240140104420800c0c4d120f000e900200004406235035584803c83c400c801640c40344800e0781c070000c0c0c070010b210052007502d020743c00801c1c40700e000c0000040c5256 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 350803174 1250 350801924 350801939
    0xd05040303020403021003050f04140a02120d090f08150606270f0118050625051c050304080313020a0f060e04050c120403081e1303081008030409090c 66
    0x4008440480c00300340d01003414010740c03c186408082c1960f80341001c11603070a0000381209100030080004000802c2c0d00401c6011040c14841c1c82040c5502801c42144440607880315510381250041200015940314400140315165401c004100c400040c040c00d040300680b2191000090004c01031504050200105008002505507004134002003003548000070540804101d005448050725904001000c01e900007444091003800d03040703601c200c549503030b0b595108800407416000da054400390504041e10440505c42c0204042240c600d03480302c012225841042c050fa540d00050780c001e80100d405000013100404800306948080380000c0241d0b0350700c3e641e50a403804490454102c100014640c80045500e82801e014a513000030b08018218104440001841482d4100402c0a004c00c1030384800718840f6100c0345900e100c0ca41ea40e40c40c519952514148662800e054140308800103140f1000060840c0070f0580c40b0030640e01804065440c2614021042d4054480c0140a40b050000007800050340c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 350804424 1250 350803174 350803181
    0x2270f0406062c060108221704080d02010e030319090201140d140105040c0e0d0614240d1e02060d020a030603050f010513061e0e1617070501030507050d 67
    0x81c400c401d0042d00f024400e04180e4100030024000c641402406030611418094624640300f114070f0650383d4011314282802c201d400f81440d114002892100010007103036102c0041440c04400526030001e10443c1036441071640e030b07880300321794080020f00710507c980031140075600403101940c01450034191a1451210b02d50303181d4440e2840040d41c2d90307152117900c03101000003003040c01014101c401b000b0304410480e0140146110400e4244562045031489081280d19030184050380d800c3c900440c0103141003940c00c0107030b02d0f50024020f0a440355551040080c42c151100000c1658481e18400d40c625650110070144500e00c80b080764410028030403a10040f03001d01c00360070481032903940851928a14200720f8103080c07200c074494803983d0400341046450b541841116400740c0c1c3c0203d0001d1080b424400c0110060745118002c1e0f403850409000201a07040010a40134028011040f0107100340d0710b0f450b0160741c140098001165812050b0200010360003503020903032011880c01c107a4604640c07207540300100c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 350805674 1250 350804424 350804459
    0xd2d0f1e060509010b0111060c1207140a030c09050607120f0e0306100e0c030411150409020d09060b030307050c0f040209030708060406060e01140f01090803130302270f040606 77
    0x551795034084031101980d10402c40c0d100065204d024040034240034043d90b01c24811103c9552910000b1000304a12902c1071213489008010f01c620941ca50034032007030040c050140b01c0681400030b0190703400485d881c5090f4003240d10300c9910464400c4e56405800c0207541e0405009040c0061240c0620201c209071410301c6483c3c0319070807a40240803601c1c2405c1c48440d01103006000307405041403e03c100f000041c2000442c4080c1c90040301d000b4400c4c1c1200b280b2070068442c3c0e07080840554004a00074920300e2043d08410081c911402c02440340480c0c1106040d41c80c00b52240192075135119440c4e038842402e006c4003403103030000064409890320449a011a280183e141d00c000000c3d0b1144d0100410b210052003000c02501402c10028404e51504043c0e034002c1814a02c0b003482101540401c0c58168003a9802c0c00040100c0000c0d6511100504d400710380d010017900c4207030b00803208440d4090054800b48101901280301d00483d0200e5250703401044540e140051003111059550340c00815440b0603241306011 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 350806924 1250 350805674 350805691
    0x1b010b030601060302070b070813020d030807020609011107060213050a0f06021015050603100806010f08070e0c031314010207060f0b040501050102120c0c0d2d0f1e0605 74
    0x4410568009240c60300c101640880c0c200342c414820032002a20701a070f1b0b02d80111181c5400c40550b1103c11003180e0134451403400a40c0700350003401400030140c00c00c802c0303403003030b00503030261032085e6190b01002c0cac26031320b008480d007910403000c118a000045282c2e0140051004110040704032580351000318421342c4441d004400c1c500305031302c400c1003025410880c00040c050400b2081c4103504984140c440c08a0540c007c0c10710526011001500d0110a200b0381d0000300b507000304407485940d5440c041701480707101d030150300217501a2000200e404c50340100c00340d0092903490307480c0f851a919030101a1800d08059001c560106901c609007040d50000d001500d5400d005000c0003135055007400c0700008070b84121414500550620004000d11b03a004a1140c0c0900070f0b810107159141c00082c2d02600303100450086070351046403013245000b440303900d0070305a010b500401c4007020600721385414290380b0389090000409001d00c4844040c0010000c1c9000800d1150109400035420019910041a11400c803070404 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 350808174 1250 350806924 350806931
    0x1f060f090b0703170c090303070807080702331c0b010c080409050f06040e0706050f2205240906090604081b0a050d0515070e12031c020901170c1b01 65
    0x1382d4035031a207416150400b2205d941341d40f60299a00200e9106d01910201629010b00894143c09100c4002c084983c2580e00404803c060200303640303a200c041103449e013126090205a440a8020a564001c80701a02c81440e1000000b107502d4403200301400e1a00c00040c10004000803060001c3c1441014201a0000c071102064910301406c021200450040405125a0502002400f02c07040416400c0542d1590301c0c105e82e4079114085083c5061241140c45080c800c0902c0c2604008180d403100c000030398000700c890b00409031106c2a150740c1c1e8503200d6003402c03200c00c0403c07140c500d80c0380180042079045006881c0783e0074196500005802c1c18004420f04424900c00c001c8040c0302c0c90b0010340d031300140a003110f04141620040d201c850b03490441054030494124801e012807503050055942d6550000010714050140c2c2c110b0300d0160b101e80010a04c030040c00c2c6905a8501d1002082c02500c42c1250103035140c4500c0407082c64000410040540131604c1c000081182d40901e01400000c0000d41e0031940010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 350809424 1250 350808174 350808197
    0xf070b0601030510150e040636020405031216120806030d030e030901050c070b030702030a0f1d040504031206230a05010804080d1e050f1f060f090b0703 67
    0x50182c98006100340100001340c0d8003070020029500d0016040f07105440c000980030700d0302d00450024440c41d0850364085940140340f204484154541480705245809c99165481100a150040e80664041c0030b0749500300c44060241201407002401e080d80c41d54040905402860725124500414040741d6070000344104100b0125060800612644554030b28080110003441c0148544034000d01801d00c0c1000000240c400c441c1e2410850000070f01080c800c2e072aa2818240c1d00030350749900c00c0780b140707000c580c52000710030945001c1e1040441110740030001c020520018020031000300002482201404800302c01c1e20344990b003030b104a8000d4951091000d00c0e1424080d42901d2000000d80c0040c85160801030510150340c0c032101d05a04290b01804003900c48210004110203464040c1e880e0b62445403400301d0900c54091904164000c4d5004402070380300e502c0322051506016a01c1007140765032044044200042031080361000400240e034501a06501d85a1607a201a9030055905030005140c440a1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 350810674 1250 350809424 350809427
    0x30902090615040902090406090f02070b0a0911151b07062a020d0f240b010507050d050a110f01060815100911220306051605030f09030f070b0601 64
    0x46400c40701c00c507800e003000e10044114400b20303c2980603004520f034020603108601d450319008080502541c800c1441000b04a00f02c41b1300035000344005550900d40d12000c0340d0829007520030510115081801c00d00c0d01d50402c0305004121940c21003040d8021010032002e51104205141d080e49052294090300e03410389011002000200140345403802200c20005585840394101403880220758180c52901d1042c186040c91402ca84040f03a000c2d1010010354415540c42c10442c1c0e40054640e80c0750810003002c49031100465081c0a8010b004080e0b81c01701319012100c502a40286c05104414074100c4103124003040f005040003120600602160b45a4405001c14981404103050020a02d520790005260a40e1961962002e5100b400138180c0e03900344041403405c14208844100310101e42180d4002103c14158461444510080d544c00e4076000c08540d8440788c40400304402c940301d584090660712141042440d0f184041c01018041c0703c100f010450f141200b4002c0c18400740910000308181c80c11000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 350811924 1250 350810674 350810689
    0x60f06080c010908061303140d0501030201030c140d050408040503120903070504140403111504141002090d0809040b0d030503091204030c0902090102010b03030c0d0318020306220204050106030902 86
    0xa2040c140f10001c0828000300c0c0b00054940c0c0d01c40310a03c100c6002c0c036000e041c1a06c000d1392070f011500344c2420014a1120b4255181c0065040744c0c404c0c0d03403c01ca04010600116035a02c2110f10800321004104450742c0e0313281290304425000350094007494581960750300028900400042115035580002c80d201d001072400303001e000002d1100340d900344400c640011103941c5000d401040242485402c074041091000c04124841920344102c0031480e9070b041034100346220f002c18a0103912a4401d00850a1400040d4000d4a03840035024001081112442c0e0702d24030b554000b900c00b5a0420f640e414440c055544042c41c03030071643d000361190b551340d0502007a501c2c100306004c6001040500c0421080000854620003501183c5120000585620107200100d000d4044038080c030758103202c0850110024580402c000c04000201d44080044200c89604003940e48900d01019505810110008003010074210500040c2030700800c0400e20041a5030001d400c84030280c000000191356060220218200406d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 350813174 1250 350811924 350811943
    0x5010e3d050a09050705120916171b01050f18030601060c1202060408032409070504170f0d181d010e0a0209030604141009121e0801031e060f0608 64
    0x50113204528204001038098403660318514210300d403000c0082c0c901c040074080410081c1401060142c1c40303130742c0c0c00344400c058000181075080e03001d41c10301c054402c40c02c04080c3d0f18800e0182c40c0e060601c1d100080c07404180d0031000d80328468517102c00340b048a50368140300782d1740a4400c2e510303408400800c3c3d092440304600b1402e825010356100da014880840c00c46001c1d41d0344030f50204d250582c00c0c4072294806c00482c00540580790461400000d12502d240c00074082c00949000c001e200b000322074014002c40e0740304020024081c02d5048032590364006882a441a0b0140a00403003003041940c0c6c070008042140b506075a0041c11281450044c041400c84400d5035030003030410300040d41070260100009444039070280c0000c002c4902c0441000da0a081408032000c64a80d0050070444610325007407120152480039042c1c000942caa0703003281501100800354860103000c075a500c803550307030a43e66817002e05000c1040010780341c01101038202c0041d0150180b000b140300e800c100400d2141c0f900c92030728503002c24007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 350814424 1250 350813174 350813189
    0x1f030f020c03220609140f040207030201140a06030c03060905030f0f0a030c080708270a050105011a030c0406030b030309041a09060109122414010311030105010e3d050a 74
    0x180d0401c881e541c800d020506031611084c082140b04401d100248480245107d4a5000b60001c901041071580641c03019069500589098066513914030440c000c44507140030080042500346014000f062050b448014802d110340e003201c0c50b12022001590440c1c000280d42211500c000450705806941806202d0f029005d43c2060a07141c00d0043c2e025040396801000301841240c000000c02581c003620300d40504c0030341c0c50001e581c000e242c2403c166010703000c24002e0602540341008030f02d640d441c0a004403882200f01801c02c909060030710707004030050056140c0d255071612040c041c00220b03544078801c08146c0d0240c2c0002040d100340030018489226001445203043c0083c1c1c9a04100a40320800c42c0104294403c2201000b6401c031400310001030b90108440060310b00d8013105403205428100d2090507280101381820644511030b017018241d4000340109088559404007040031180d08442d107003a8004510714005144110000ca210702403009101441900544041000310f401e15120007030250028 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 350815674 1250 350814424 350814487
    0x10f0f09050f0106050703020c040606111501050603060d21110c091603020706062115020a1d0303120405070515120136020a0305090a021f030f020c03 66
    0x15903916002ea4605119000511900103404007c151080c0441c0640c07040c0148100941b94440c80014810321030382d000c2c0400c5200d1b41c00000c3c584660401d6550403980020411b6265642c0c81e4140500300c1141c1c08112286440800d1002400c0c2e100c40b22450a110181e9840c280d082009609134036081001c030031940101d448000b840511103030034401410350401420007580d520b600c0c3c40d19400030001907014100c80380c0c0032503820304065194030040114500504580c02100b500000040807071040304c1ca500c011602e0200302d1000b504100e55078004c0018001c050740c1c10480d512840040b0074404403001c40d255001046c1c02d00c600e1410f0103030200810714140555041c0200c40c0700c08210001d041c02020700c03102c03944403050480d0385803550042080c041d06003106a2112034404c2d0070041d4022080300d0011070308000000d49291400940e4000c0e068006115103c104000780c1400411034000001404140c2c80d4810071036a9603150000700343c403a184400440d550350340d0000400700109000c25000798100d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 350816924 1250 350815674 350815681
    0x31508030d05043810090603080d060e070507020906040902060d060503010e070b370e0108011d040b0c130f080f01050c1b07090614010305010504020301051813020405010f0f0905 78
    0x1406440c46184c0c903440a030078505882d1083c1e0800c55200381d900020307159042c900080204061031001e0031514109410610840340c4540d04185c0c0c0c2c2d201250550f000034030034072001025145c8030103100d82160000e440001d196150741c0204000c2e51040b900081d0f019101c01c820415401e007440b58508680050b006411140e0501c0c0d0200494403991002c1c0840c4001d84091010041011138180031103001c001c1c200e1301c901006030018014040c1510503601141010000185d038007038a406102d0216540340e1124201c2d5900c2c3d42c2c0060104000d000707079071a40414031003c20fa24112488072009000d480b0000b0030b0355031810f9142403034000c1c7c0858900c4144d0500d828813403035183c240c0c19070b00310174044081401c0026000c4131030340c43e16810760300c0b00c0c14040c00c0c107800080d0680c5075992030a040000b03984c1400381d03a03200ca043c081071303101c00c1c03007800d4100405400054491440592a5401c0000805400c1c1c50300c0f5503130000340c2070700c0302a000020440c40c00c070000c000001040d4141401003881c9072041c40240f070f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 350818174 1250 350816924 350816993
    0xc050c03010c0e040b040e03160c08031e0d0b1306030605011d060108040302120f0406020d0309110607030905190e09150103111f02010204050f01020a020d03031508030d0504 76
    0x303001c6a10385001355251502e012083d07031395401611001c0070382000c4030b440d40803034000000341e1480300d20192440320b00310030003154500010045407841400e4a081626951305044031401950000e1a02c2050b44c2d83c82e003000381c81d552911105624075084c2c660100c1c501d820b41c203080d011a041030b48160340302d01981503014454550112100d61040090900c1c1d07417169204e0070b00707a04102001d072801e014940d0003d407041412411030040c00c1030340c040d542200e0301c10101c86002d400700e07a0700c440d01804000a900c1c00c0300c1c0700d181942c0141003140c031915004041c5961340d80460098918410301861550003d0401d00400000c40400781e4040e80101c010714012107068000c0404000600010380001241040c800702c680752a11111541c0e103092102044c0c070111194028000d4000c0c1c000c2a10409890308048841d43c400949850b0780c603002071040103c10001d13035058000340707144152a180d0100000000034404e0042c0f0240829010407540428980391502e4012602a60305402509101c1452160480c01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 350819424 1250 350818174 350818187
    0x31506120f02061e0c030a0e22020f09040609061e0b03060d0609050a120e031204210b01031209211b1509081005060112020708040b0a0c050c03010c 65
    0x80d010348a4569415184d0704810041980742d0a00e00c021100040300a5816000030062240800c00d5036408003800008040103003104000441c180020000e446a20326072115900806c040300003900380901c1e040315480070134180c0b059640861055946c802e010000d910281a103a03d05c84c00f0320b8000e42045040401a1b05140405080d180c00340150701030703590410003a54844003500c3d4200d811904032411529100103138006ca00304a0340000c810034030200c12030400260700a2403101101d64a41414102078140c10080203a0480340a0303000e0b51158400861201c800c0940a540110345082611149038005454a10140d00a00c890342c106a031781b000c0342180e00e509440081c0d000d4800300801810b1102c008090409400c00001280c3c00071546c44665085a80d020407141d403102501c1000c628101454201c65048403214045000696801c040c0da440d80d00134600107104040660525488081341c003a907070020520320000c922603000039820b00c4010400301d42e400104400030b201114080c04024500c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 350820674 1250 350819424 350819453
    0x260919050d08250224040b04090c0e011107050405060310051801061e060c1a18190b0612010608011d1c020712150c0e1c0c0e15090103150612 62
    0x301721a003038035041411300c602c2124010300ba6030b074200b610f454407880c03084002c04840d6031990104050540883c481e50140c5805143d062184014025840c0780c8018017010301802882d044d0300d07000d22414004101d034940702e024007900e9003d030410414102142400d0846110707400600142039030225960242c0c00e82e00c480300135690145001c5049103c40d2800d21581e01100c8007017110305200c002088207070180214031001d01003441c03044038001e1020204840c80728a030190043c244c40b000d0b034009849410210300e15601000c800c0c000080031540c402c51700b421039a0031044901541305102d80460b5411b41008404407082001d0315000c508104620b020391380d080c091203820615580d001e80e85083c00148001501d8000d401c035014801600b401000a02248000600c0d80c03044900c1c00c500369412191805a9451a5100c20283d458904140800b1545503004001c0222001900c0c9040013507195240210300079403259034012024140501120140c401e42e80090840d5440d0b20f54500101d107080c60719101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 350821924 1250 350820674 350820709
    0x50903120f0c0a080903100603080a050309030c100c0801150e12150405030703180f0e0c0702100905032a1e1c260919050d082502 57
    0x664501c0e0115805060054404452142c000c0c039100b40107004004004000c4000200c0550320070f5503e00c62034a0440e4114000982403500a0040c0c1c651603005500079900b0090b60320417a405c2190b80c0c81d070a0703d05010b144d183c10741c080d240d1440400d0360360082d080c1030140401d21041c00c214004200003e00070020030030628803078013511140c000500e500b8001d5802030900714102c0c41c1c182ca41420100c3d41e80d80f00140443c00540e0709403600041d995948880c005842c8103020000c01c00b40b03030400c84400100050b2001000c40420044480140d540b502e8451548000e038a46a802d00e140038101410710782d4014208400c072009880c5180120110500407052038000c80722410880d020f2001c403060391881c8092140c20000113068403007000141c549892020741700e86030040c82e0407182c0101c401c1c80050511181040e482c04d00c509030561401071000c009800361025040911680e0300c00088025503549025180e00c0400036845221501a88014417012140f016806040314680d020582d0480401181340 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 350823174 1250 350821924 350821927
    0x41a0105030610110102040305031209030403050d26040506040210090501020d1b0b011e061701050409140d03020a110604110d11061b060601020d081b0702100c03080705090312 77
    0x3c68190250080d1105605090000c40d12151649000766480e800320010341620009000040c0404000000300c0341544d51080c00f4080310300791100c1c00e48604015003101c030b01214074801c41207050a0310941840c8214041c0001b0040c6007014014460741f2100e646001040041c05801440180d800040107a40e048071072510700a0500c038205509041114030900902498102d400010400801e0400e016030340707405200c3d80022661480e09071441d42200804040e84182507004102615107a400348c0c011a004110002c9d0280c07c50b50183d040000e43c1442d0030111b0341c041b41041245903c42c4c8292001c0606400030821030510791100314070b0400c9250524441c00c0403681010400c003240702e819541c840301912321601d07288008400e54010403068140d038054403629000a0f07196100090b0909040e60984880e20f113519030342242c0d1b003401311144001810010800c07003040107889170341c08a40740d081c2c1e0f40d0b50351410146604c1c00030180f030030261116042000622160121307039004603103042c900c0c08040086 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 350824424 1250 350823174 350823199
    0xf04050f010b0d140702060708010605040f14030f010e03031008070e04021005040f030305120a0c0e100306030f0803010e011a03160917010f0501090908040b090f190302041a01050306 80
    0x300602107030743c442c100a8120134144003500e81c0004860340a9081610764030041c1c3e0326160304581d107014a1007a01c50041c0040b03c02c00102c5184c08106203124005001c1ea5621112075040da0309540e5082d02c2841e0590001080100e5444c2c07100000c006080c03a00c010b0f103e4149040c503156071070320340500084c2c031414029110700000340c0607408a40c020706420318459181c0b96603040141c61904035000030384914a2080020715011214860907034020126210516518140383c24400c03111218040c1c9824503075901c0021011504608a04400603c03c240d46946c960600c1c0203550f00350410303440b59a10000a01da180140f01c000340980398404202c40c0703480c201001a1b5422100e5100c19840b00500728018005402400011342009001d0001464207104030391b0707595030032811101c02c10000f8100d01c005001c107003e1880c40c074008084222005000c192a0309030000050504400741138000d091001454007001142800d00444481918206110b080e0042080c0003804603c03004203a0b510401d0a044c3c0d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 350825674 1250 350824424 350824447
    0x200708120a030b09010e0105030606010e100c03021f05010306140c040e0c1902010203100e07020709021804180506060f01050f070203071701060303020c0603010602211e04050f04050f010b 82
    0x2c0010f803c1e0042c180301042d40d440c0900000701c0020700a40b8002d020719000140994095043c2c400441400b4100c0318907548408822610810000d9084046004441c20840518140041c40f03032058200840040c05515524040c4200c0c0c020704941c90300521040200440c4200140548080b1010507d80d07808981d40d62900608500c81c0344801e1500a8092001603c80e9505501841c0f158400030140403440c2d4442c0f4a6602444c4111840c40041c0d0040c9000c4c410807040750040c10443c81d204140207400b0442d940020252908514100c44034080386030002e09000080048071340140c019078103500c1250701140001d00b540f041c1002100c500c47c2c00a5400110f44080049400a0142008912015018200b264040c060034802540140700e4018040c14070729003641213038120f4140b41c00414014090215141c0d41218076100b10740ca800040c817101c0d1070040c411050000c240c43c8681c426964504010070800568100c141803409203142c40c040051000e04482c403a03040d40c0d483c401c0591a100081078 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 350826924 1250 350825674 350825681
    0x6060e0a33090f090207111206010b0a02030d090b060a0603112a060a3603111f09060f09031d060717040312110a0308101203200708120a03 61
    0x85040e0702c442040000510803600d9014001e69407190b0344c0e20078042c001608201c4410140d03840d05648c1d40100b00100710002c400b8004107101300f0385005882c00d040c1d20040d40c07022242c00110580340810318004006240c9002c90381d0394050416410100118980f05810085d640036070001948804026100b030043d4050602c00684414048400c030b501510b0030040c240003420022800c1a0805060050b100607204400c8014a40f2448041480c0c4034544940f800c603280307000354201d01c0701800344054000118079800103000341405000008a628105c030710b007a80071204901c6007901c60300c0c940040c20000030342c4841c09020740da0f01c07042201611452800095032a10807850010900c8410290030040e0302c4498015004176800f840418240001442d02a658a6003c80100ca019003000342401c00080c05107410303075008401069008510360b1940c4450410310030100050b80071450210780c0c0518050410300003000c1500340005400414603100800395146556070760780c04018004100303501c0d120300c60362 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 350828174 1250 350826924 350826929
    0x60f09030501180213090203030906030408070804080105070207091b1101020c0106140907030b1f0203090402070503030603011a03031e0f2107140f091306060e0a3309 73
    0x100200041a0100340c12895405115402c9004175410f0032a101c0c5010180b040400058001d00618a4050007808004581c0d20050046075400c030180b00309008a00c1c614081c00c0038084680001400381404a001303460b00806502401c941400e1801981c103a021000f01c2d085000520b040c00005290300c40c4d1942e001e4003503900d08400c1c5610b8a8400143e074590700c00d14105101c015101103001d902d401e0011815148401d000d160040104c13840c2942d120664491001c00c41d646205480c141201c202c00141a40e2101c00c1c241c480d980003000f0b0110701d2400313210f4805000111110518110214000320303840e8050341c00112820240d00c032182e4548981c0a081340c0c02e540505c0a929591410104421407549640410612858140d0300103940300d03008100c540030088001842c54144541464400c0040e44054400d50304075000d9070540140c501640941c40151034a42ca4002120395000c1c2444034605c52917016600c43d032039401e00c04a05143e4a14620f19006001c6208140c22a01003c185c0e0020460b6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 350829424 1250 350828174 350828183
    0x603021c061b0c0c09020a0f05183006190b0109030203030a080106142d13091b05070b0103021002031b2a0a060318080f0901030507051201060f0903 65
    0x406581c00943d803100c41500121300c1070003415081600c0712004002c80c091071ba80013010076000018180384a0164015082c542d964140c0b1622844510002c00c15000c50300c0d80459210004100038a00c00701c0e0790044244204007038004045901d402e40d44d01d504402d04541e010f045039505c11504c456170348507542140c05541c000e0b007181d50b501620b00d0010845107091060b440041c044664002030516520100d4585a410040300718113060700344112586680d402e15800c11941082000c2d580ca091041c004100a14a4640004141c035102c0b0f0256000b0708100c28950400004100c003074000b40c10514003d041d00d4058803280018250083c0a81c5944684680c8010b202c2c41240004071a0100182440c41b91441044000060039a01404800600f0760316015900100f042800e2102920a522180314422582400c1c1342c03046850b114500f807a4004500f451440200103450072035541c25026950700b01e1000d14000340f80481500441c0c003001010702070b01040210107000350020904c15a045005503410 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 350830674 1250 350829424 350829461
    0x180907050d1b050901060e061318060f0603020906030a020c0a050f0c03010606050f070b07050f04080105010302040c090e0712020f1b0c0102070f060332040309090603021c06 76
    0x1810455041c0b01c0c19000440801a840c1e80410b0ba424403c01c1c2504807100358440c402070010b5101000500d030440c554881c401d001c1010000b408120034640162901d002520002c0c10f2401e2850090f60240150032240c1454010094262107880b010200c070342c0b00700c1e444001a20354092101040c145a580c840107050392154400d82c0070301020118140030b0301c0d48210000c22481d5605c240645090260002c0620070410500030400819140386406030700c06441d1030114a0145107130700d501c5050301b0980104400da95110014421400c01d41303d00d003200c44140c10319111f46440d2100a503130b0004020f0070300040000345034044500c00c8264068412041006141680700e040440403009010001c9008000b075200360140b5109950002c00e101080c1c46000030380c902007904144003030b8080c0c924504a107050340404011800d00300c03d0000c10011181f00303201009258102030070018240300090f005902524070b0710404100503610b0b00f41001a00884080b00005010181003110040070b04101c0195400d54 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 350831924 1250 350830674 350830699
    0x2061804060b03180106140108072a0b0612030a1b1e11040b01050301260d0e0108070212040e0414010c08090d110d0c080f0f0405040f0b18090705 64
    0x30302c4010310b2091081c3c995002182e940003200509980051290320301c0201100d004010a51041c3c0d041580302c0c1c0035080c920107004a44500d009040031035403c4188518060030450100222003441a8101000312000d1201c03100500490303440b441080c240780d09000f110501401c501c0304003550b100b111600b00d2442030f00c4402c00c000c40001101d880d00704031007110588807803160901e8184180e003401141030b9251400d507820070480a400420203520028000d0610303d081d50041c004004401c092485a80c450003806907980c0098a6031002400310740540d0000c00c0d81847d100b8502050300d003200c843c003000100680ba40e040c094004421010884155404e001102c1c2503c0c0d0031032400e82c010400310007100d5038503020400454105642d003025040c2904480d0711400e4081c0300701c0906042500902a05241004001d90000703984d200301400f02d4010000f040401251825124804803810125010700c0210008000a288c00000398900c1d01c0c506102d10200ea110340c001c0290070094040078100e0700003041d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 350833174 1250 350831924 350831939
    0x1109190509010b040c0302070f0210030b03030c1b030609060a020318030a020d0e0f0a0308090f03101b03060b3c030103020411070203060c030604090605010611010f02160206180406 79
    0x20030a03031154003403410a525017602038403a1007100c1006401c00d103281c4036200d50350708002000c08090f0b02030003007640f20703010310640d95801c2c8010701c030300800031008218510714078034503044810050720094400d13081070040055180c004a500781d4005503100f0010f07581c2c0c0c0c071148124032022008288075501e02c00450380d21941500000e088207400910b03180d03000324903c5401002070484003070181540100e1404000c1002401079400340000b904001d200e614601603000c00f00785070100240703107100301c0e5071100640d40074400d00c412070710301640c4c240c5014044241041004011407003134070301c074080c07981c0020700550080104417180c04480c000380e00350100724600f006030324603290401c2c0000da00c20f6291049500380e2000f60412200c2c1c50703a01a024284a50301c1813403961698000609840d0816110360900b000150140b05084c064005a201c40980004c9805000c0c00c4820f54098038a020780b041040d410010380f11515154210f031304464540c0e4038920400216094005484101e82003400d180c400304520 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 350834424 1250 350833174 350833181
    0x3030213081b01051312350415140d15051906080705160b0a0c0c1e0204141512060f060402180a06080a0606030603110919050901 57
    0x510951a50801141c4400425842c1e5020552141c080d80c03401805485550250307001e414100108541c00848075036660b4412401161700004aa4445110900c5c455030300c00016012002d9504c2161441e8015124102c855188102e014008001085903034440c6090300c290203d04a003108002c249072101c41e10b0100c10050700d04007800f0705c1d21040612000c03807607040000007240640d05031079010401a20702902a504c98401034056400c00c00200000709240544144a2000c02d1041910f051a403034448140c4084031080b042c01c03401c0003020b540e83d00201c9c10850785200d1440040c000100300c0c407000d04c0020000c007190a50344800080c0c2d00c2c1003000325160031914101d0168140c4201041c103528103030780c54485404992003c40c00d0301c980c0200344a03050640c00f07402000c00c0700211001d07226402c0f0004858001c15070204001455a00401140d146035020366401030840d41001d10050b81150381e140c2c14440c1c0307030303140c540140140350000d80a0902e015022619440110080003281070000160303000e07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 350835674 1250 350834424 350834437
    0xb0d0f0804060908060402150f0409090b010302090a021804020a020f0f0705010e01020a051218040f060303110a020102070504022532030a0c0c21050105070c0b04060e0a0c03030302 79
    0x8543c516100107150400880e841c1d204550040090046200c0203070400e28a4200c216200304940c028840401c01e0b6840c0e1050501480c0201d0544141c0d40c0f4520400018490040400048600603c0004908498801d062581e00001c403400350b00d41d00700210803850f21500c040561860b101e1b042204c03074503183c08184001038582c00e07a81d010321280014010390340c4280901c0b004155a01028080b510080c40d000684801c80c14001d6481c0210b00c030348002800d54000303002d05940320f42d558208008042e0806219007001c06098050540c944250300080e440740642c1c030070725000c2c1d5000200344040310400110144580c101490316513814195080804a080384085041d0b01f4001c5402e4001c0003504492840303034003900701001540350209001e0300301e4001c80c4e01d980460301c0c9400d6820204240013068506000711000c0e0344070781200685070030882d003560b002601a00910000603612000301d03104c01c56950388250844004514202c1c580c06881c94101001e001a00c00080403078007004066164005200 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 350836924 1250 350835674 350835677
    0x1c18091406091603050601020c0904080a0f09050f090612030a02030c0f07050d15090b07020d0e150a14070b040803090105070801080c0d031206060203190804020a05040b0d0f080406 79
    0xc2641c4000c207222100300140c9124560035040745115120522a8203e558007140c18419a00072030500e00c00700d10590016101100c03901c80c0450780b210202d50002da001c110742c0b10343c5800c00c10f030780c940004108910110210b05016040200008903030303449208122140304145002c07641d45d00c25601009489410500701c201542c0a120030b00d010103103001030803c00b9103900504408015881e40d55000c2c0c400c0108000c05c00c40e42d2920304941c0401c8609500a202c0c464030740240034401d40c5030500514043e450000c1511851701c641560111035026003c0d242070700040d04081c03245140b103006a2206000e0814014034160900381040300b000540c0000d0344c0244000002072026441c2d04505454181090007560800c1d030101c0d00980240c942000b0483c401d5000c0c0c20070340004100014103006070b90040e000200564400070340c41000100907a128040300700a8038040025080690020704410524800c00e807049860306200789050381c50071240350001d40e201124000c481c00c145010401c0b500244220030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 350838174 1250 350836924 350836961
    0x403140a021503091009020d060c091d0c1603021f0207110d02030a02040515090108030918090c04090c0902030f060a050a031e0609020909030712030c021c1809 70
    0x114003102c00e05903405800c5080c0503000c40b1404244510040c55010342c142d03480010515084041401031099020341d07001c3d0b0740c542c2016401c1c01c1054148002c00b0b11200508c0c00c1034420443c981d902c0d041569440d0b000a90004030300060f46c241203190003013048140c920380300d11003030b44003540003154020100c0500c50340d520280c140a000030411146800c0384003035003640258100700010705d019404160f004441a103800c0c0400c840c2404184d20345002d820100880e40001020013888c58110103040390101d02e0855120786107080e002c00c03a181d4511300da240f8082d944480324a420455616a078001030021114115100e02d000c1072089082001541c040b80240d48032000443e035070074000c034080141e075000b000c0c18044011100d2030307203200f0790034800076143c842d0340d5042400141d840c00020760003108000025134442e0201d04040e000000c0801da078000381490300124480a94002c10240d248e43c00515030000c05d10071200301500c04059110b0320808802d000400802d0720122644441030070b00d40500540f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 350839424 1250 350838174 350838199
    0x60c01060e10080a0f0204110c010204030b06030325080418020706060e0106050a050c0703021c210f053906060a0501053703090308060f21030403140a02 67
    0x3140d0201c014020f0210740d400c0b80c01c64002050b44a0500c601c3c05101030400244034031080641220741d04034506464250350001410014030005034026500040110042c0d8544900c01903c0302c070781d1101c2c645450060400e251200103200c80401500e0052180407410810300c6250b80030703440203501c8020b085070036618015010848030a2206030905075601a181c1030b00e0607000b208150781c660850781c60308045100e10400440140c80b0203901c080590700003c146890030300c0c80d1034484801d400f240c0c10442c82011031031098ac006035204421612000300d0341899a41d071092600442e0082c3c0c1070b2091802c0d03600d00c4130340c000102c48a80110449500e801c005481054442104205070030015218070b900091080c0024080529407400d09002c000408840a03450004c100c0312502c06007030b0704c00075804039588650200a058102c041070754881812903280701010186000103042d404646000701141c0112039041c1641c50003001105d01554100711110850400c1d254030b0303075039000700d80c404074064604004607 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 350840674 1250 350839424 350839441
    0x31c0f020d020303060103020702030109051204030c0b1215010309020d1202120c0303042301110702090f060904060213030c08100605091302010806010306120f05071517090c060c01060e 81
    0x1c41c07441e000c55003d1450f641354500114040e4000d460f099901d0b541e103814050005104001e400119080070041c2500d50385141000d64054107154444c140160041009040340e1400120b4554816500507031004018240e5004030000c221003080250420200704a04042c814800d0741003401501a5003100c040001c1958070071030700e014000b05480d4690050000c6000a09100350b00c0075502101ca492100b420312102d0340c6400c0d907070040140801d03020f0006800c0f0550501c01d030301c194400060313001c1c58aa41012030101d9400d0a000b0005043c80d5070104a080720210520002002150484101c0c0710f501c1d03c4080311622106406d016542d80c0d4604400000d0b03908048504910903442c01182d0442c40c400d40c0c0043d10380c1880101840d04059548030045408504031002d000594080d80182081c00300d5071070503510b84880c0d904041000c85139103050003a00d651012a100b000484400003210035120102e0641c81d10084c00d00c8941e02c5140417400d105031080551080049914a01c032061494913900079 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 350841924 1250 350840674 350840683
    0x120906160215060607030201091b08010f0b06120406060512060f07030e0a0b10050a090b0405010b030112020607060e06091605010f1e02250305060c03090a0209090309031c0f02 77
    0x1038907440b0303080400000e1032441c0c00300203040130501900020404111564850281e07011030000380765890354940060212000034407444000188000040182d014982c000940c103010321624030b0362500020001034104000d5030414001490041c0c072640400705280b005a8640000b02c4800854140003400101001d100c0d00800403a100858060300e4000440c0e100e20030507200082c100b820350145003100041d951684c50440e40108503040d0b0000307006004404001c15200103074007a003420041880140448075404c080c2d403c44590403582d0f60b031b45025500d010030203004103c44680346c1c0e002d80c2c400c200860401264100f0050082004000d0a607220380c019520a10001303614400501c2046616450040c4401100b11400a0340110303000c1c03401e8a00100144558099100f03d034643d07c080400c10402e0401036940c0100b00d10301c1850451510503029651741e04484006403180c4180d01c08620043c0c41030088800f148400b400303a81c04c1090f04294080d21005443d14400081c060204070041c0c80d00c0402c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 350843174 1250 350841924 350841943
    0x60302040f0228051e0301080d0f0e10030e06040c050a24030c0c0c03121103030115050a1709011a0f01081503070504020309010c110d02211209061602 66
    0x808000040c003d0030400c3c40b41e211444420013400340170405006030f10303400b044140c440c0407055403c9503a581001c1c10340d0f08007002c40611109202c005e09161003a550002d10540c0d40020035205c802402d0301c500d0088000e00035500044104e4095101070005001646101809459054403944002c0342e40c1d03d0418a0030600603000c07080001d50780e8071a002c1c988a504900d10540d1186813510440c7e5050f141c031842541c29034421070b100c8013a00c1034182170a4000200041003a41003000d10304562500048000c5a0b611403440003c100d000100c000c071440c0030309000307070716128900085042480c00d01c280703500030200f6060102d6584030001d0000da803490b2812480f558010107a48201c0307140c172030001030142004103040b070b56454061104003050740e40341ca2014521800c48030001242c901102c4102405814039841074001c0c036005400e00d0104507800243c2141075a100b01c003400715500841444208901605015404682c6000107001101078002001402001c41c0c404041c012000c03034106a030780f0091700 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 350844424 1250 350843174 350843197
    0x70602100b040608030d0c030f060b03010521030a020304080613080702040f0609090317010509060307140102030f0d09020406060801081005041b081b180622050703060302040f02 78
    0x121541540c18003a00a401944400780020034159100c1034480d0950300a1400e5100490b0fa60a0134006c1c103038140200000900d0b1054200725903410114100c41e6072105014a42c000c9111a0217030004100112155040b00942410f40b6223525a100d0001c2d00d039803003445010002c0c490200400c91071040c05101c1d124440d40302c015249801400c2e420f100180465581b0320780165550b1000180f2512540900040d284c0300742d40d0510b00000ca000d40344c04182c41a0401303400340724414204040c903100000d031501a909021511041d00342402c1c0100e2440c45134420348040070700041906404200c0541108100510850303050040742e80740d19040301d4500c401d200300c010541c4070708013008032030013a940b1440d001030040c096042082e20080084a4041541d44003810591140c01e2440c0c524100341c428000f41d510071034480118403038103404441940700240c0640c1c481e40740c403c0b111040c071410140700700c45441d406000748160f180228001e03000788028441680617605100095010303c0300c6108403032000300300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 350845674 1250 350844424 350844433
    0x30a140f07030e190f0f0906031a101503020c0c040908160f0611030610051612020f0601090f0b040b0604090c17040f14060601080c03130c0f17070602 66
    0xa52802c65a803442c010f203058008011210403018100081c050304040d10001d014580d0143c40c1131500b08102d0703d50340c00321515502d411130520006501c400c0d19560303815000c2e000e4a1503120b800c1c010744140b081d5032140440c0c55180200540c05501900a4810301400c0810340e60303040114014481a02d160203001880317540200002c02c01d032120501d400611354002c1c440308246140941d00e4104441d07248207041c8a902d00402000010305d481c03030f948411348549203032041c208180c800c0c01d14a24680010004c060202c1000003a11551081245084410b00a411200075581d04d0a010006220500e44ca02c6180d003408001840d40c2800c1c081e6202610010708154540b5207840094001018030380c0c0c50f5000c02c000064200c3e91600054a081d001c2c9001d4004001c40000c20f140958400200300d0035482d00f03070031410070808542c1c0c00581c00f039800039141900c286c3e0b030f1780e5425200c2a14240e0707000003401c850240da0041410006802400d06860000c41124244151415420707039407902c5101e8400107030311 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 350846924 1250 350845674 350845687
    0xf070f050a12060f03110a030c09050c0c100905121303080f0c0f0d1d0d02011d03010603060b180c0a030e0c130c030f0b0a030f0c051002030a140f 64
    0x418001032194581034034010042c0d80c40e0340740000c141d59007a40718001e4001010024030900042200c00c07403a4403800c80d11543c40c0c03491980c446c2c8c090300d21803140c4910541d5400c006801e480000c4202c90b5040c241d030b0150740c020705800c00840010464490140c40310701c602d1018841d100301a0048074000101d0510010241717145540b41000f5610032a01d01d045400148040d01d00311000300030b504043c044e440080d203000d1aa120008021500f445036581c9900024144904540c0301c010f00d15500c640c0a182451300d10f030348001c81251005400203202d4156192100c00024030480c1d42c080d1041210484554229840c0d41d5850030891906403455441e104080240300300060080d0f01185802c28030b80d050340e00c040ba0940005809c845011032100d034058075480e41038910355041c07007104241d41c3c0409c0c00304041c0c190b2501140100394240001490384215004070400d00c0040383d804802440010440c100c2e0007a0640029100c1e04101d41d004041031180001e0b103003503503c4d1404c0e05e082281a81445040c6075 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 350848174 1250 350846924 350846927
    0x50702031b0f07030b010303020c0108070c08031f0b0d0615081807081608010510030c090b060405100512090304050d080a03200c0c06160f021512040b0f070f 69
    0x201145505045840744074514820b68509020010013580a10110400c035851030501904000d4544403c9042060705400c010816402c19403114400760001040c80d265911090f151890b403100003e0315085000800001498480d00d02c01041c802c076011209110040d580c8040240b400e076008459000b051003003001412074000d18014130100d0040d03004948036a641d0341c851505140503d03940380a0030b5625101400845000d000e100d4120b00659100c0d8512803071522030855aa06a000d41c8c00c074030351035118a02ca90f13a00c44061ba005020010038500c06880071601c040c080c0c2d4000320710000d5682c8c040c40040d06000300801078800300e54002d407403890b1402c0340769160300c403691040310711506041da522020b0328414030108000c40b00c0c884650f0700c1a595140c58006a2400e03292000c0f803803060030b00f006910280103d030000d80c0041e035400717400c41500546510005d2140d00c25004001c4454801140520f2054201c86003580280d0040440760070580382c2d4140b05015000c110b9107440400c0043c00c03140c0205 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 350849424 1250 350848174 350848207
    0x41a060d0b0a0306020a020d0e0d03020a1401060f09090c05090118180b09060105090a020703090b030703021603020115140603152106160809101a06070b1905070203 72
    0x8004000c03083e240c0d03846004030382216030828011381c08600008071040e00503400311400481190720010886055030025524040c81c1001050703a10407805201603507109410000180545a020051990322905928010706201009445907100c13800002181d04002400764107803680416102c03a0000804100c01c05070480c00075481880b40b140e048000070861090009000703900690182c60554034210401400b03460282600c03105510401050340000c2d0016405001c0710003100c45144c40b6505c000f0158000d004450001481124240d400700030950706620080c200c03095003c0c039803649074840c4030303910f0a0186a88e58a0f0041030410100c2c4003802e01c40351100300c810340103200051000212488918501000400c003846900100500a441ca003800e0140000580792a02c40020b1505103003055070b0f01c9240d40c903041d02a5071086951b032132204607402c49000a0000c0e00c22684d8074801c0ca00a4042c02088541514111081c0400220b52400b40215400340c181c1d0350096050030009070916451 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 350850674 1250 350849424 350849441
    0xe030d080702190b04031112040e060607080f0406180506070809040f2f070f030c0609080a0e01030b15090120070b0a090e040f080304080d0509010b041a060d 69
    0x540c03043d070f68800c0e08031a03010000918180308010242c3e55080502e0050418545070403446020342089400102004481d07040d1812100c000d0030110540c0c440b0004651144110200640b2030350300000c0305503241400c040100b00304c0d1011764a410b0703c03036041c4801020078000e501419520100402c031101c00301c1c1400000d096032030002000000c9181300d00c111841200c1b00c0800d400030851185a81081d0000344041e100d01c2246440d144d145815019555001102c190110042c01d010b000c10507041072088a9010804035a80700791001d6541c0ca60080240503045000046800a800c201c1c0304039403401c00749141110580d0b8400160f04012070b89005540300090b014589040f1492406110b0301010200000002402c1854270607640d00c581d080010b0130703010a5003054501000780000e000c0007944045101030030580000340903440b6102c501d8200740314802c5048080c031260914040c000d0049043d4040c030070400044804200b4030000620b1001080008a001a80f00c0000d01031003958074a181c000c40e15 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 350851924 1250 350850674 350850677
    0x3070806090708010f0b0f0d1505010201060902120a05131e0210032306030a06050a14010b070c050103090305370f0c0609030905150d06140d1b0503030c010f05070e030d0807 76
    0x148146140740c0c5c0201c4074189c040da02d4043d08100100f1103540c080c410310001d010106002e501d01790440310a4102000c0c05080c0000c0c065980001940c000c003c203500c200d443e036100401c006056404140200311221341e58040e4401d0309500c013401c1e0114006d12071456103c0b030310024030510340810090781c010380c1c6d00100029014010382c4007480001d02d107489040d203d00c2d0f20b00d0000841804c0400e0008130b4520581241940e140d0401240001c10b60034503002c0f040764024a400700320284546412140390041423001c103410380b010a1402210f02444001c6914000b16100a500b0b6185000c403c440c0c0364510301001c00070030040d40d004004640300360080240c190103400c0c0000d44a9560300810308040e510f640460070101c0100701d400e00e914480c02448010000903404600c02600030000035071080102d4401090302d01007140c1d922003c4a5180350400410b0014150780d1100d0950300802e0103031241003800c0500c1450407002031007a6004840c0902041009001840302880044090340c040001410440 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 350853174 1250 350851924 350851927
    0x40b15010210062301110a08090a0510022a011d040e0708030a0e0a060e01030f060306050a1a091b0a141c15030818010c060203070806090708010f0b0f 66
    0xc5108050003031030000d014404443c0113038488140b10000546507240c040c1d0400084460341045aa03000440c0140c140d0001c14140d940ea00c0c000004081d00342e10303480716801800c0c1048140701180c0100e00e00501c00318241030902c040304105200003c201d031a00200b40425443c0700c884a0760003010940d50f0610350013800000c0d2241225010340d01d030406981c0845400e90002904480c0d0301d0b48610b01070004041070700d0038a00d00741002400307404c10101d019160304043d42c6071041a034619040d0084402990401c90804c400c1c18126051000f034088136010200072040016140c0c81410b245000078440c400c80860346016824000d02606141d101c0310900c0100080100710100d9105880e0051401c0924a80104440754500e491042603c80061404036412210401000491139540c2117920840780b180c3d00b9011404088010ba800c900c0400300600010b03c0402001041c6401035645070050000b1207101c0c61554070804111943c0001340144440141000b20070008941c21802078001110701c0b00c100ba = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 350854424 1250 350853174 350853193
    0x7020301021308070f080102040f12061e061d0f011511060c030a06060e0d03050a2c0a080a1109040201031b020607030f27020a18020304060b0108040b150102 69
    0x3102c40361615045080c0e50342000d10100107104512911000034000c0b900290309040c504010785658810b584180305000066402d081c003007080d1503208000000c49164040d40710310482080d0380040c080e078098290500c01c880c25000d5001203820403903220340c140d154401c815178200713080094080e45801144c07040c00403160f103801c200c0006224051058540310641d030348a2410381e9812083e103e040c0e0214061080317400ca200601d880e4a2300541c10b130364040c240070f5aa0a60588225065140c0e044000030140d9030b00582c82d00c40c10340c04a24800c00320101c030035088164403440110b071510003c040007810f42c80c4a1589141d1801c3c120191a80540141000261070500414400c10015100503040040e04084100450503405204030224814030040c20000d04030803e034008085c0c01124990008529842c0e07014003155034604047c0054072209101d4188a1904d450f6500a0f4000741c604444080c102003003881d80394850002d50344a150440c450403025110701203000442d4072a8070f4454114056150070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 350855674 1250 350854424 350854447
    0x6060d1110111605012f01060b130e070917010b0406060804020102060f07170c040f15031406010c0f03030b19060201110403030f1202091c0b2a0702030102 68
    0x5620340c6151510b0541c4460080351a00b4052800740f50440b4000070501070045076444210000840030240d00158440308aa1aa500440210044404940c00c110002c038800c001d00000c4c0c400c1c244030700080911103880d010502180101120008002100e400d0308103c80d5414244d000c400d0100d290000403003c4c1c0580118059070b00d01d801050100c0c0d00a8103000846d68100841940a0321005440d0103e041580006112048032802c0c00c1800c1180d0000c10200c05410f022240240301c9049a0f1950316034404072a100c5005901c40407001c280b5050400000405505800b4032070b00c4140d40d0600703900b5896440044166900702d007601055680c410400700740e1905401d021850400c0c8c49030400720351602c030b0001d00f90786001d03520001074402071004100081c0c101000003105074040c00c00305030145503034200e81d00134082e0340d007007a5100200c44a40303d1011140040c0004040c0520254409541c61411910791641007410540d404040003c10030504c0d8020390140444520007000585403e00840030b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 350856924 1250 350855674 350855689
    0x2191209020301090c05131a01110304080106030b04051209130e1f0f0b060f09010302090121050f13020d080c030f031f060c080d09021c050618030c06060d11 69
    0x1c0888580c12446170500c014501060201007143d50800300740300090108800c0c286c0a554600d4171814403500b000d1501301c019003441035070702a000c03a10007000030303540d80c0c105414404800c0ea401d68807070054044e10700205519008483d07018801409540d020402008580010025031841c01002d0250f0804c5464400100c181ea1045894000e008281e0894684101080b41c161004a610540c02044003002e1214110180e40c0040c2090800503103030600e210061300c665aa5001c11040c456616602c0c000c290226030005000d00403100c0d49150355503a0390b001110601c44070002a40c4a000c1001e8030002403201070052011880c1d40007580c7c00d00e42d824110340d1140c1c006a40310381140d414a00e000f80d4000081c40300c2c4c00140958900003521010a4030f84401c50300c202400441615102d1a02c501903444010001003000515066400588800d041c02030325840103a401350340c0c034644010003c5440900009450b0780c0c0e100c40d0048c207119150f06003002a03501c212141262008080703004102d0903a907550 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 350858174 1250 350856924 350856941
    0x102161106191206181a0406050a030209130f0f03090e010602100c02031c09020f0612010e0601020c100c0c05090108030a11010f020c070e010501180302010f02011b030e0f0102191209020301 83
    0x1101149007010800c4401c5d400b2401d0410a0080d480c010707003049207a452b01c182d0700440350150f41c2c02041d80c40303400e02034080c000b0800c00038107000c0000e40c01104101403640500103181c082c0e03842450490700c0d040328500d07014083c0704540050340140c0c0c56006100541c3d001c00300c080142d004a0b49450781400c0000aa07841d0101c101c000c05a644400d4020b500b040c103400006840101d6030185044180080c440380601c0601440b61039602a070005201c5034020070002030141c000800c900302c0007000400042c8000c982000c00c50b0b640307074400000500c5040c038219143c1a16021005981402d5000c03100312740044100e0b80f1800d203503403103c1a845200c69584003c1c24055000c4014000e440d0400b402c20b4991803041c0d000a0400c80c042c1100591100424030071011780ba424a4140e072802803600d012405401c80a10070207490000100a200c0581c2603402000c0d418007890079241d41e40505c5640714203e0040002d489100311168080c0605a4828600b0442d141d01d40c0c000020b00d00d000741c02103401c44e0941c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 350859424 1250 350858174 350858219
    0x308040306021614150c04050904140c0604030b0402030f0109050c0f2701080f12120403050702040e070501110c06030711030403150203150f0a09020a030603050102161106191206 78
    0x403058524900900c117156001e0340940380185418a07141c0403c049c0301d40104041c0200a030b030317010f28485000601c84100d0154005001d26203460b1282000141d200c0241ea080388680704030107201125007418003402840d01d4010010304030364105c040500801005002c8002d600424694140d980a05102c040032003038a10150742103965030520a14a141007440c0e844001180d2091103082d654401c030a00722803005902d402600c0585d101c6150589450042241c001c0d17006080c00b22004500030000b440070102d5800742c0e9842152010310034000d80f2003603031507044d0b9082001000040c0d0400d020304240e0660352201012a460556240c80321810318030b0b02c2e4220400c0e00d40010510100a94811406191a8040b148100c0700e5281c00700094454005100d90300d800341e004035480f088180a0790001009541280095648101c0803140d11a8549160f004955001400ba01e05240d410a401070300c00200030b0740186201c2003074482d0240ca88403d002c45000e421500d64101103074030217420780d28542040d40b1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 350860674 1250 350859424 350859433
    0x20705060c0a0204050a0c0306050306040b1303031d0a03030f1e05042603010503061005011d04020412051020040e0c0d0c02160602011e0207061b0c0b0c03010308040306021614 77
    0x800d800406449d8035038007083c4698000002c0c800030824020f000341e0030417405218600280014942074020b48900c0c40b00c00185084050105041c14001c2824103c00c0d121b564100711441262006008071120151100300a100300b5982071508162540a290810302554030603131000039100c80b8000d04c40d60f045691602c08804801000717181420000543c00200d2006840e05081c100700000700100111541542682c48450025a00d42c80b43d0341154080e1070f0502c0040400081410420307902d54a00c0d001104403480e0161000c0080d2688082e2040c040131411407a00d02403422445007428000039249552450081010612000c00b034460381c7c20f01080d507000f40c8080c40324503c480080c0100c6074030503420759040401a07420300c006150012034280d05c1550058407094103081c80340080c200410380c02c070f41d0100c03031084820842c0c0003001040194032580c3d005640b82d176011680c0b9941e01082c0300040131824288401d00018015030003034112803855030140301100e2215101c0e109442a03400000505801 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 350861924 1250 350860674 350860691
    0x30c0d05060301110a18030b070201060e0903040815040302030f0310050f220c260f0702030703020a0b0402060c07060806190f050105031b03070f030c080403020705060c0a0204050a 79
    0x1854021039a001070704500030000ba030075001c900c075858070800c82141c003008000b030000c2280e40462000b003000703141c00021082c15498001000790003401d075809025520245c0f90000340c441900007085034103a41c003802c09400c02c44081544611207042c05030044040d400284400300140c04080c0281d80b065411140d5141c40c03d260909118040d02d0801109001e802007054414902d007401031032400306101002c00040034103d80008480c144600121080200e18010b80540140c40b105c007068024800d1001c1d51440f6100d50384240c0e80d900c1016002030141e0040001c007000b240440d80e031654458009885c0514010800c903509040848070341005022510f00424410350741091031640800e00c3c03200030b001c00000e04000e412402d01c000b030703c2100e040007000030000300300d04d0030030052028241d00d07141929100d0400300c2015103640d1a4008000019181640382000507100e0010b490246d601038014006450514040c0b00301d40d40000c4503181107101300b640c1d400040c0c4030341c4a80c40c0f2408803100300050848 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 350863174 1250 350861924 350861947
    0x2070501020d0c180b0f04120503121627091d060604020909150103021605010911040614010f03060b0703020304170304030302190501060e150103141003031112030c 72
    0x710803040800402150000c8103800300611440384c4180c4008580081d155084440c0e100d4940c4960b8000301c0500115036080d5040200000c05820b10391480081244642c1e01d076220b0b0105034100a540400180c400088100c0d8014444007080015010507941411181c0714010101a40c0e080c103882280301c40c1031030840380c0c90001408801e80086080381d00754603000449002a00c407203005131081182400350400c0d10f1050780241e04a03603a1480310055000b49408605283c0c1c020100750348252007030389001003c1c0e03006281511500068812101492054944600044815028003000c0b036042c9a650340300840c4030b02c022009418550300c02d074025075070b490a09060840c080c00a080010960380144801d1001a030041031440c552699446214101285418040c0c090501a4001ca080e0303003016050003030b4100900036032079014200b80c07010b205448003d01030085404040b40d48400030b200302442400041e210340740301000e540d1520101d8000c1d4101148004469200b03441c11800840005040003150 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 350864424 1250 350863174 350863181
    0x50f010e0313030308060f090c0307170c070f0201020723031c0503010312050d140708070e0f060906040f0902031006020307080d0e0a0f060c020c040501080c2202070501020d 76
    0x1051040181d07042080303200d0242c1c81c2c440103000003002d202c0f859002583c03e84405002660898004003030460500304041a204245e000343c80c59800514600b00c0400080c0d1100d403400c5c010b40d0301500140c40c0010503200e4100c41d03190684228114080c9140000b481c03131a0002150207410048422440440442c0c1014503010006c0f10003012407007942036510350580c0010030b032030460740c00103400310b10300314009011525403050700441c0800710320304103840c8010f0783d6080d41e0500c074101d01e480d82d406640f10100299005427480c080036901c1140700e40d0076080c50411001908107840064001c81c1440d80360500c4108460094100c40080c0e903010003045507a8501008403c001d020900140d417614519444002d40d51243c40291505251170711615402c03140704114128002d90852010034100000b031401c6000344c0540b000000052058010710304141c9054440c4038100c0c2c080300000c3c14151050014005060707a03124034039120a00b4250103280c02d000500003801c51034410300005954291000004044 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 350865674 1250 350864424 350864441
    0x309131b02060405100e10020c030d061d0a0b03010f240501081b030c0705030c0714040b01090905180a050d030c030c020307060e030904090305030108010c0f120c03060e04050f01 78
    0x1c550000040c0030204401003440609040041030114030b016038103600074a80012518090f5100d81300241e6040d04040c0400a440d405000101c240032a9a58000e400014051100c0404040024002056103000c81798001883c08001034008101070381c0ba400d1880c200d5110003d00000d4145480b8031035041c40c4554000c002406090030241e481d41004070602c1d50000070300303004884850001002c2825820940f040d80c404c1c40c0e1220849950b10040300100340c030341c0c00e5840346410074106846012210314050041e201c1c42e580607568100400c2c9017099900c080c00340580110300c03034071141e6110500c001045c4141c510407409080100070000c070700d04004044070018070448040614081102c09066408011900c100e80c00a0700483d04504050f9494250710070704501941c840d00d0103c2c40d008264110000d103040740d16a00c000c000103498075205490385c8448455500005280003590540030242ea800348140804600c0d0020b43c0507103e05800742009026101541c15034000c8102501d50f0000f4040c83e904c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 350866924 1250 350865674 350865677
    0x120501021c09050a0b090a060e0f10020405010e040f06080d050a120209010f0e1504120c0e06060306060d020c01020313020418030503011203020118080702090a060b03060904050309131b 81
    0x390029a07242e1513101d200b02d502c003c003c00404404504c1380c0e00c0c00c000c5060600d40094041001580b222401c65076200036401c084002d0103120240d040e43c000901c2070758219007041e180c0020308459001008001d143d070841c601c4100d55920808601074200f000219032002e0f1549600780d031a0030709900070300200103000b40386410a004100326801070340e022242c03901100701c0e030070200c0c0542c00d5030001456008001c003640c1200d0002003400685400380c20100541540240c0ca18496562914001c5840410854605030040d004001140c5142801c000800d00c4400303003000107042c00148009242683d0054901c20200350319003c02105501d07091103004458002c100c12409030b01c0741d90780e02400c03d003c144944003120341d65012a905060007074100d4046d4900043d02045540c80340d10346581280c100e008180d0080c1d2001002800a1101e4402d80d41501c40007010f20b130440d0751f288108603c6040c028000c54403800300307008a400640b542185c58040e0092203402192028404000106030020004c0550 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 350868174 1250 350866924 350866931
    0x8091006080a151805071509081902031603030207060905030a0b0612010906060e070807020303091902062703160612021305090c180d02060d15120501021c 68
    0x400358200003002c449556100900c0820280c2100e025801030919148004400100c0202e0808002c0082110810b40d68800c190192141c0300c40800c85621446018040f00c561051a1034542c2c41c069081c00e8840711f100900310340d041904c1e00c1c50240c103492941d2048015a00148041c405203410003121005490160010400181c05442e6080c030a000070b051180030f00c40c445407004945c00c0c00c1d000100303201d81241c014407a4603912840c5043da120101c0e0f00100080c0301d0404205010310200c00c0728042c5030428001c03c10f240da1045441200030500c00c040364000c008111807400300030480d04001aa41290a07100704401c01c0c0d070103243c00e04482c14040301c5440c207401c105024054201c1c8510b09050070300c00005031035005500c1690255000394004c0e070340c45542d0700100294804104001c3c26030030b12155004020000607800c0c80b903a4010048002c0d442102484520f80c51011a400702a5001c00d111044006035a190003080e14407086950079500c076500080c10001d410781113000a4035034800e895081 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 350869424 1250 350868174 350868179
    0x180e011a130510081f0c110a1212020708190203040e0117070e09031c020c0d1b050312090d030902130507030f0e030403050609060606040e0c090613090c080709090c0c1208091006 78
    0x22342c8030350154030b00502c00c62101010706031a40c07192010784600301030094210340d60101400c100c0c1c59038100c1101080320040001c403400080344003009850032900005c6d903200c1140d0800f45003a42c01040c41c59515013501c104900010520300500f11240a810402e0145d0f41d110070985100c4601d071880c260404000e4010858060252000114105100250300e807074220b2550300030050044c052401b001900c94031010502c000064407800150b070141007140102c45640160317010640c1940c002c4500a5448400c6032007541c61072040e42c003c02c1c0d201782c0078500000c03030031400c2c1a02411079102d102400800e9102040c140704015003000051f4000754004001c01d594903010000500c24880c500070201c521008401069240c03101109442a030840207200f1512202c01c0801010310321098801d0340784031400c000d038400046e40500d20140c00390025540c0c3d546128100f01012028220070312110b42002808200800031a05004503c0c2050400d543d80341402e042c42101d503460102e10414008205250070400c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 350870674 1250 350869424 350869457
    0x10306090308180c010f0c060c0305061207050619050904110c1203240307090c0e130504050c011b02030a2108070c1506180e011a130510081f0c 63
    0x91300301c02d400d20703144e00d5030780306c01e6801c0ba10b03141c5001d0000c050714201a401141745415400080c414002030712a0b1403007290313049500d0380e200e0980c4549608060100302e0b2040281d480d001015841c851414454070300743d000c1c004501201c600413840d0402c11004501901d5548e0300744445040340010441040c01c3d0b04180302d84100d4645100c2c41104103050441c0301c8086c03a181031000740001c280094003003141071807180000c0c008181400451f88903901c0c1405400e038007141481800d010756004801007050500720001034075203075940b404486030780100d103801400503030b406c1010800081c440d404480d54403c204980007070b41c3e04000e01280c10310183e4003c00c448590302c140c0074020150000700b000c1c904404024031030b000b060240c006504103042401030400e03001c1c054001c203080c040b030704000b001002c560f00145900030090564a65003c46481c2c801c51160751190001508441c500c2040074003d0342d148103e518026040d01c4010314000143d0b5080c02c040028802c002c069006e5041004402520502d0b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 350871924 1250 350870674 350870683
    0x2030c010c0c0e07020a0c1814070e090613090f0b010e0103030c0f030e04060306020c10200c070506120f0105060a0801350102040806100f03030503090102070b01030609030818 77
    0x191080300f1030b610340094050b51080182c0b80e140740d0000c0c10007408136100d5030b040c80500e44000c1d014050b20305154404040328050000306203d05034903592000110384840811407000000392106512034042c02072142011030a01c07581c2ca036944229001c0c52445110b01e081582094146d120604804800c001003000c00d40100180540a43c030000200c0c1051a501d002d503041c035084420b40da003151030120040700b003150301d44c0104440742c4502d04503010f1021144406080e9048a605121504c160080b2450303440c84c00700c01341c020401c0500654503e19150300c00f00750b05801c5854205007443c112014046003400d0500903c0c0940402d480881c41d2011a00d070103001241d0610a2004078120394030030f480030039482009030702d03101210000310b0f03003031803003130708041c1c041d40150064a10034001e0703901181110412300d5640c03084a540310205022580b458409a5694000404074181e40d50200988000540d044810a001c1c0d0320030007000034a60071078200140740320300003003d071500e01c410052100c900d00000038 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 350873174 1250 350871924 350871929
    0x9091a0f180c0d02040905010611060f0705090f01030915050f07050c0318030a17030702010b010905030703060902180405010204031403180405060a090207063603030c1103130302030c010c0c 83
    0x20b41a40c1e528000c400b140c0c0284115030040c04400e05d0a4000f2a800d680449501c242020300307401c8a20319100c0e40014444d040c0b0581d0180046481000800c80c4c40c05c0c40d0054a60220301414005204085519807811031107102000310007269983c01004904107406a15035004517485c42c1807403c01302601d030666980e00c12220100c4040004c80000d2030340b65403c200c101203090340038803050904008407017051642d402c1500e24030f0155080443d100855403045240c6400c4440040c010140c441ca95144c400060080d440107036044654082042c01c00303480004e046028034415000143c0e5107282d810204516060704100380381c0e42d042009120300341e030444440a55640380072200000c1c40d407a00310024103003001e00d501c0411403500100350442402a190300c10b007800044111000c014070400112a030b080550040d0900b41104242e0681000c64400c5c0d20031a5101268240078803200c0d00c24000c240356804c5802c000e200380d20094024421401e042c80782079003003402801c20014030801552408003045407070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 350874424 1250 350873174 350873191
    0x30c021b0405040804150c0c060c020306060922030f080f0105060d270605010f051008010e09070f08010e0d110c010e030a0206031303080106170a0b0109091a0f18 71
    0xc2003c241405100ca084800a11240c0001a40c01c101b09201421001945900340d800c0810111300144181c0500303181c041c1540d0040c0030300499136400e0b0804c01e040d03a014014559200c410030708401c14584816001000d1402600d404031100801d02004200d404020180f146a4002a00401c16522514295088100d0b902d401080607402c10603022041c3e01d0b101c1042d0a280311040c180c000348556a40080d058440d01c03641d103100e041c1c48100380220108600001c1340050b00c20001081107409040742a6081003481080d502c1d241d540301b001540000300c0782c00400c2503942d02d150b84d1003585400c1003200c603460308500348039000b985a40b0140b5140e017400c02c200c03818402220000c0c02181e40500c0045000341e801420580c49007171101d50960800741a2101314042040312001056590190340d44d101c01400748046402c441c1c0d103c5144202610081c031641e814408050380100300d03800740e40160208810f0340c40c00c56480710264030401882c100f10003021402000e4081007422311100440346180c1c0070041c0e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 350875674 1250 350874424 350874431
    0xe0103060c14040603060e130506041209030c0b0307030b0301060501051b03040e01030c080d05160f020105070614100902090a0306020f0403050f0604060e030a0806091e0f07030c021b04 81
    0xe03228140d48000041c0b41450b4101c00028010608541640c40401510350a05040660b41e0350502002c6040c0722058011300319500034070020300000c0c0011440200c8101914024080300d95030380d5100b030f00f0109900250305a44010040000480d0300d4420010103840460090120a02d0000003070820b102e8038001c401040304d0f00420f060039080402c2200c0080040d0b45440d02030351380d2800c01c12a0481c040c05283c580740108450b9a00c00b502c24015118900a0400120700c10f440995607901588160314003203051003c02c1c80240007081c0b00d8072642d078481000421407802c2c2d14025442580c80c1420350009208544144240813064680500d094180c990000e001030b603c10121040c000680a10341c8000e145200c0d019810404140105000d40528403a450911107003680c038607841c0c3c0341c2c018140b15400041c081400510301d450944480c5401c00750802e42c9020035034107103100390f842d1101150500d2143c0420400c0c40b0f60540e1611a00c10944110b01c050010344080300ba41d01c0000d200225a103211760b84 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 350876924 1250 350875674 350875691
    0xc040f0504020109090c1b0f030f02060c091311190201060807060c060f020c1b040605041802010c030e040e240f011202041407200309150c033703060e010306 69
    0x388141c1f54580c2c4100030300d50050442c0c1c0c0b030310044241c40180100d00141e240f0f07040d84201c500010344a8054140305220700e06108004040c820350f0180e00c2d400746191074881c1c0c04545c41100c22401003440704459600521500030003103019080d180a5032000785c42ea406020100f00d801d900c07a0020100650045000c240102c0c1b042f454030180c011000e07403a8045c0640d0310409a8103241e40041d41d05800c05440a20511307903503d0070481110018682540000c5240c0a4140107621030b03c3e004020302e201c0e0810501c0600041d006c01c0441d0301c240c41e105c0659215442e40d00e26890110010f001e500c0350765600308854584402c0038a130305801803003a42200342d01011100708554540d0400c0c1911106013951348035610306550000c0c030158800f142900e1083c10009041c01134030010048030345601d03010349091409910014a40c030700350300075004401503000c1400f401040051000c611070701000c90080f1403141d03a130600780c448e864020703400642040c1460900100544548400d0180c11207400c01d000092192 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 350878174 1250 350876924 350876927
    0xf0702191503020c07081f0b040c0e01030509010f0e01060f0803090d02010f020708150619140105070309050603010e01050918060402060f310e01030f14160303020c040f0504020109090c 81
    0x1d40c1c0200c01c447c029581032680542101d60b2204d1101071080f001d0000c0f0300080b00b8407003180c030200072003000907400c07030404441540203420031504400302c1400099480c140d00e021804940404400c2103850751604410006400c410050501034000c5101940c500214000010302d90b84036148002d06000d45100850355240c02030084e00d004110701404c0d06c550403405403000700400720481c0c1d12031051081d4460303070582c0410b20b21600190b408411420b03c072000800015605504001812001c1045110020526403504005103000304900540860305506000400000e940010044481c42e13040c1c07074107000b05560000c0c140d5045901580d4459980d5030301140702d00c2902c5075840b400b4403045a1001c402640345100c0d180f0710150806100d45442c4c035210307c03040061000030303c00a042d08a0340b04140c008200b07184610042040300e2011118030828071110300c00c10740720542c42640982c01441550599080c580610001400104000c000320301d003c0c0d0000c0e2418402c0c2c020061080e40d209107040c0020f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 350879424 1250 350878174 350878183
    0x50603030705030c03070c0b030f010b0c0309060d050109180c0b18100f0906021b0909010b0a090b0405060f100807031d031b010b011416080f0702191503020c 69
    0x1542c0101c10340c0d9580d900340705195602d502645003122203080103e400101c2521040a40c0c0c011380c11a11144d0680e40f07482c4403a181c54202288400b2a80070402c8900341544e2080c0040001d0303842c203080410990315050100c02100c056616100c40c0c91482c5810400050740b0703007442030a0712500c480003504e8074503800482520400e02010650416034090709811707035941044104c854003010f1b0f961880596102c41040746c0303035400c56074460381712460b07804060b40314503000f01c00f0307540110224000a4036596113000150460300c654400030156a46001c040c1755401c00e0b0243c280c3c00700e801d550484010b070f240303c041442c030780709243c64200700420a0003280e0054425040321110342c14070181d00600004c9041e09507166848062a45000c4d1a0b94484940d8400103010343e200301da03016180c9843e16008a0f2841080d44c0c40170200625448011f00c080e40080c03040c1d800340070350840307155095489146500c1400900c0d0101d2002c245002d40d904c0c01000099814191120032114a01d005070315440d1008556141 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 350880674 1250 350879424 350879437
    0x907030206040b072d0222020406080a0b01030b0a05040f0603050303100608060901081e12031003020111070e24031c0207120201020a170c1002040611160905060303 72
    0x111a0002d4001048203e05000c1c02c07030140207101c81c100448007400280d0010f8581c00d400d92a0f546504e00000c05442c1c10701210000c211641c401c015000c100300f0285040368060b800c032401144c101014072840c199035100b400c10340360080c20100b00c9808010001072181c00c5511070707544a1501c0c0c1843d0740102c146030304003400655105049a459041c5800c0c4540300a55501409d00000c01034000200c00b03261005406040340c006c2c0c00174108000b4103600f680b40004054040d91254450808200d02c1840864002c41c03051a48003a048043c90461000600c1104d0015103861540c0c4510b0041c002034550341802e81d0042d104c0a59058000d90200b405621003402150710b50f4035004a141010141c520781f04000040d10084c2c2c00c0d10003075900c0c1e141c04c1003046c0c1c55200190042e441001d03003400180d00e200742d5942e2400c0d55804039003401020440b051034007480c4512881001d40100d02005101d4100d84d483c04003012041c003030085405103000a489030001c500c10b1305101d5446002003000e685092045904 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 350881924 1250 350880674 350880679
    0xa060807080312190209120606280323070306050f0601020f0c120c1201150f080303060f06071b080d14190c02030303070c020a05102f0d090905070504120b09070302 72
    0x10b089142c142c04239110201290781c140501e106c107500031085441e2407015901203540e011100d62140c1191500d04210030303844a540a0b54144e904081c141c0d0f2004c000e0781c0010b610844004c9141d1507c403001c0743c60700e00c003d800c07181135600c285c071418100c1c003000c0780282848609485520100700b64040312454421590b00c80d07a0803422016014196031b1041d002100e030020341c0e184482c95144d0381c43c4d110b4800c05952103050150b4100707101064503440c00900e060032070300700180203500300b001c141c0f1800c103003000090000403031000003502004201d030240201e00b218002410b180030060782400c5031187c28400d110b14251904941c3c900d90780d1260103010802489600903044a4403031a090802400b40d452340c03501a0720400c18204001014038058503580e2543c01142e640c004541c1a85a9a00080c01c4d440e4110260688540600400c228200081c44070f0b41078035035601c3c2c52545000700620848102030040300800000300410b000002d50740071492044c542c040c080030480e941d0030b01054184405904000d5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 350883174 1250 350881924 350881939
    0x204090525090b03030c1b0406150c060c030b01020d05030402040608061612020a050a080a0b03011a040501121707080d0504080703020d2c12060a060807080312190209 73
    0x81c604041d000c80c1d01554a0a07508105901d12a010903541303000702c10501070719a005004011800542c42c0743c40c00c040c0c10140010860548501307980081c034190b0003501001848240c0540e05004480c000c140c48100203007001c108080c1d1580000351960b504403007010a0040010100d411500e85611413030091494a0943c2c50f1410541503440010502041d004001a490480c2d82aa21302c14403c50344c42042d65150f580c07501840c0a0142e400c000300618108200d40c1d00c2d000705569403028001d880d920300251103040e031510880c0081004a40060b0011031400f40ca0043e003100141140e20743c250203285000c00291165410b160100b054420b1000d42e034031844c00d02040c0000c100301280640b060910a03020303200c5200c8107141c1110508090b0f01c0e85199038440980c00c801501c20301c6510140d8980c06003820380300c00385400000d403808405444950741c0560f14a81081940002c1c01b4400107171440101642c41d001703211100501000c00038002950002c0c0b5226045140081a8102c0b0340e890005098030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 350884424 1250 350883174 350883223
    0x21201050906070207170d0806011e12060e0609060409080403060e030304031103180424031a0603030c1002090f030a0b04060f0908180f1804210c02040905 68
    0x340d2901e0080d610000544a0a900400c4940800c01d00400e000100d0001f42240d000c42101140c00c080054020307414010041e900c41c0000b502d102c9451f69204050300c9d190300d0f462484000c681225600e41c041010700041c0400c0c41040d55455001c250851021600070075821514140a007862150f039000410b04c52600d511844044000b101651196009846034042603106480b05512442607181519400c445000861120300d00f952280601016001c2c400380450505240484080c40e650030540380e000c10640074241d10810350074000d0b403086059000d5820201c3c078440c030701c1c0c1e20311000c01034101040c4c01181801c0e060310364000d031307451007a8001d04684580986040c941043c0384159810f981e00c1d420301000310401030850091100341a40100c2481c9031612040d492003144d1510041160300c003490b149583c145507950082d420b80400d50032801101c42c2072500d440c580742c1c0c4c040401020700400d13004c0040070181d0020b01c022038807501640c012410030b143d45002820604401c12007440c0c00d4801100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 350885674 1250 350884424 350884441
    0x302040903110d1106060603132a080f07050111101802040903030e10060b0403020603090102040509240d0807060b0d08030a0902030f120403142409190b0106050702120105 75
    0x21601307007400d440c15512a0344400c02030150620017107590107403e1000d03140f07102c0015040071410402400c424501c00101000850440241500742e00c0041e1a40c040460f0b4003245130188107007802001e003401d081088400c441c0d801c1d502c1e15140640860021303a0b450145081c1110503025400c0b03150700078410800800b140ca00540100418900d1302c0390751181014001e068042c070f01c50300003910080b0b60242d041c50302d19420045154001000e003000d5540038000003074140c03640c1d8143c0e0b020700c03c458000b035058410210110415000d40d881c0d00d214401160303003a0b0205a60f11700721032803507400c900017040e4000c1440200d003100791001c00c010400840001004600c3c44198821780000b84210140c61712010f02d03260071707990340040d44001050703148100802c01c0090322280483c00810089803e13070701c40d440341559a10001000390320b0f64001c00c078207008018105905000da81c5265100000ea455004007a468400e02410140205814000c0004200f4155900e60740b040170100e503600000c0c406407401d26103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 350886924 1250 350885674 350885687
    0x1902040b130e10050105030a090303020405030a12121b0302071a04080910020105061c0201260103030f051c02180904080903011d0d0c381e010302040903110d 69
    0x2031541c0b1500401c003c0744189520340740034022a80169501400c5440d00070001000b402e0b4400d08800703261342001f0000d2a03403800e018241c0418080e03c81d0300e41c0036a01c814040c0850001100100d100d40c5072902c184d803030b040070140340408142940303801a20f40c01c1351715040c2d5403d003e14025a03c0400722004000c204408900100a50075056604095941a07254185e0a0f0340043d5801e6030f00041e1404141184000e0160a1080500500d0325400301210310040d6551524007100c5103404842c8580184249034000d800c040d840869450564980030040c2c0b400f5022518000c68403000e25000501c1071520400c50b60f80d001d1041005040c69045c3c200351403c04601da104496480c000d50a1040000d00303080b02007032114440344d46401034060b0440c403607402c0389c0c40b401640c41268013200f400c0720403895401e0010f004286c444030303404540c10819110b000c0003103030344010711041d02c0e5410f070704001268481c10f14005d811a0f605440c085400e1040b03190a450b9031100c00313040c444c0c0d4810101803612071684031a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 350888174 1250 350886924 350886929
    0x1d01030906051003060f020403020d08071b0305030901031805060f090708030a030e07080114040605070302040b070318080f07060318050a0b0406050604021801052b0c110102121902040b13 82
    0x5c00401c03030741800d04990030030b0f07006c0c1344406175202c041c2c4079500000c40c00d90002094410b110300903200d04070703100074812074908180d40c2095401e40c1c0040b40da04e9035940c2620031491030811045d262068001030b0b40d42c0c0c9980701c400904d006031448130300c000b00b89810000c211150240400c00166030b154289140000c00070124064440c04034803079000b00050340c40d8103220748070140e01c801c0348664817680c49407030301e002900c00035150400f09070f03080100065a4403110050001c040c4a07580d400918440211a8042e0244c103401440f042d82000f080280c141c84c0000c0c0c414101e0300c080c140072501607110100d030328100d240e412010f04603004090107501000b1919520302d10880c8035440c10080703600c1d220180b0049014102801c449200009440e090942c05a00580702031960110030003100b03620500001110a011101c000c03810340c858001c001e07031907003048402c420110103000071810034038000c0328200e9688000c0d01c2c0f2803403a07820204a400b0507107660100c9026105110303640342e6134014003180c500100f2051 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 350889424 1250 350888174 350888183
    0x50a020106231509060a09030614010b03180c0d0302010207170315010e0d0212100f0e1902060d4808070507230d08071d01030906051003 60
    0x45404103110b0b0302d0ba850244600846a46160508045418031410100c500d64a005005050005509a0b40c41d80002c120404080d51180c074441d00d149058825201394200d80c841440c6508014006080c602c41529484880700301c1d21480e08800c802d5440c18082e0991520303402c06481c0040f02c05240c3c0540040401d503101e000e09948543c1d80f030103d0319080c04161143c688062005902c0300e107640c807035042c065034901c0c010043c0e11920107a500103029009211215900c540214844a013407100350b10034000320120300e00050280034501d001c03440e19110648034950042c001d081d4450255210341041d1501008a4001040340c0483d546281001007540b4203541c40c8641090b02942503c03480b88074490440c0701940b80c031081716030140020f40f840399004113030380104002402500049140032903482e4111658149540c02c5440c1540c609080c042141e0b041c4c2c0a200640c020301184560040125882d62003003032408480a09210048002d4641882d01411003030420301403001030806090580e040320301c00c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 350890674 1250 350889424 350889431
    0x3040e04020907022814250f211113090203120708030403120e0a0602040302030d0e03060112031709060f1f18020c060408030114150901050702130c050a0201 69
    0xa9000490392214201500c8502442d170b40c004c5040354034000304c600315aa200f282011148040b502d40c1c1490100603401403d03022500d025501d00c44000380c441000a045070000000400382080045003440c000031820150031314080c3c000505100e04201000340c3c8003001003601c00c801d017002001002512000800764031074010124414208a81032045646450741328656905556542d1420f88900480ea805010005d46540748030030390301810300c41c2a111512811005072518114010b052406038040c14403000e01250000628607030382c00248007070460700d449140c00104119441c0480f0380308503c0115926106206040c003c0c00c14001c5001c43c40b980340b49064240030766070b020701e40605000d400111070052411940500c41d03074414641c1842c007484c1c0502c02620700040c00e1001450300074221000e40ea50000407006001c03020982c2c4015004002c100c40d881c2e42030440407507406251090788130050620000007040d00c115150000c100000c102103182c2040b81500311f25020303200d90b1044100c138005518 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 350891924 1250 350890674 350890681
    0x30c050d0f080a1802210c0a1a07050c180609072a0c030b0903031b070b0c0a0e0d060c0e01020a05061b070605010f0f1d0402012003040e040209 63
    0x1c9540541d140806503600e80c00350b5150718801030014107102011a4840680711000c0c0056214120071041d94107410017055543c8074501102e40c208494000103c0c403511100e002081440c45a202c1070000e91182c0048555603249407914500d0b18403402041d0740c00000c0303801c20307000010030608a24891403054441e81c1c0742c0c0d65240c01c212034440243c2510310f00d051500c01d005100d8100300000d0320030325100e4403907080340356107945660300310181c00c9551000d1648004100001d0101d81a039004d40441d02d1081582010010b546c1c076030040600510a64010303001051003000039200741000104904058002013010b0018103004019013030b00116240894400b8048219551002030810001e40e0094007920060700c1359028200a00010540503440440500c400700200301a442814020100e0400e0303000010310b04a001c0580103036542c455441d055000c00c494100c54000c03002c603580250709107802c18140c6140c20102001c0184c0b01c20204031840003090100b4a102140c2a080c0514000c4903001003580c0c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 350893174 1250 350891924 350891927
    0x103020a1e090b07050604020a06020d170c16031710121403070c0915050904050309191203051b03091e03100c0513060e031209030f0604030c050d 64
    0x41644424400a00718101c0e12101c1c910120001c040c01c006031500c0e038038141d658006202e142d0055002641d594000c50180400c52415003121301c010510750001e00b4888440460140c1040c202c2c850006816a203400041c100b100000c04840c150b10311818552000e80c11818002c16460200c189418810700040c081011100300414010031550401140c510310a0b1907500c04550448441e21444144000d108035800281440481005040807450014209004030016203621000780e110900500d402410300020800100c1156618142503d11413079014041c202040044015440008000035002c2140c08059000c030041c00381414a48142600200c0000040c4d1684a00354082d503001c10210b500050103d10799800358a00c0400600b40c615000c019070440d0305440c5080d80800006500081d503490200000107010090500c618000030301c03000b00c0c001300c0e9407103600c2a01d0b41c4101d18081165051139404220015110203401c080d203042d030900b450060200c140d04e00c411240c0340142c280010116 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 350894424 1250 350893174 350893177
    0x1404140d02060c09060c010906020c060f0c12040f020a0e07051819061b0b0f011706040209063c0111030f030703020c0f071401020d020105130b31030905010302 70
    0x54030302da10f5107440d01108204200c032541c89020b58003003554803200c000c40403030051310180a1600000c0c1c060040741c07414400510300040d00400c2d000701c4080c140924000640ba0100e00390384150b10910b200c0180c0e01c0c0b8000195243e64a034019406036800500700f1a4450303215018100d00c4442c0003540200000040c01c0210101121841802c904480c0c4400c2000503ca0300c00e6601c03001d000c20045125070015110500312520484580d401e4a180c0700c010042c44911142d18050025154050441400c00354001084440007130700091054104141784850000c800711190140c4118110f2500d0b4000441d840101070780c1d40060706400b00c0c8034441200c04010002c02210903070701d0694582c514603500c03c0000c4c0d009400401e8806110310400d4210046d03030b04200005801303441ca2000900c03984400e000028030300142055402d04590400040c014040f98a500954129501282c1c41405948107084061685080c4209103000b14000c00c42c15080c042c29542d80c0085400782e03803410882c41d01c074801035059 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 350895674 1250 350894424 350894431
    0x210106050a1802090112061e09051003060e100204090e060f0702030f070303021603020105180102070309030b060d1a1f05031902060c0106030813060c080f07061404140d0206 76
    0x8200b801d4000a0419860340245014a0141003280e140b400b440392500490358541c00c400151f000d242054051551951402c0e8010b000014051200d4645004202c01d18001d611005001a40307842040f4040c02003400442881101d0b10411500c9582d00c01d03030070025001e204010f000c3c0e40180b501183c458101c10b51024420003190f00114502121402e8814103035000a10650030190b01b40242c0165080209071911818082d50011500e810324500d81f10001200d011800540d038410400040001e41000030352046981140c084907131541c0f0200854000c25412000070602080504541c000a540780c0c03400e1b0048042071004019070b821081400c83c210700c0c50286ea645030703220030b0b015118440d050012070b40d1548041c20950030581032101290039966150000c9400290200e070742d4202001ca500c246004188902e45081005501d1316002500c1c81b80301c1401d00030800002d800003e02c0039030780081242010600f20b215062605007001481c4480506a540b1240955010390b00c43c244001500e501 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 350896924 1250 350895674 350895689
    0x1c02130203091b030c0603040303051506040f03020402030a0f1b0305090610140301110d06080f0c0108060108101d0703050f1603022104030522030305040b0c010902210106050a 77
    0x507208000144140d660302e9003610264148100105e9011075280e00003c1c6024078440d86000c1f0341800c00c00b45180c2d0038101004254080c031001e000400180c3c10f0440090301301e98050f01c0c0143d594840500001c0030f0400b24410b50b001c103081808180561828089a072030020180c0d0303040001f0788484035500d4480200707540281c5842200c80e0144081c600c21444440308034001000002d01d8408183c1e19651608120518100c2ea41d032000b0401959900b40511810700d284240030b07082030707104c1e88006030101e0b00151203a8108408400020a90210f0781d8109000c0c00f01c80c04118204101c1c16110340401504844000c00a07040c07034041401400f2480c5043d009811036000c151494034440c02c110004c1d0440e80c00082c00014a0340f441d010079070481001c81c0a103029903126a0303580740a00010b01c01001c1000702491101c0c40110400c0800d5108003910143c6450b5001d03195545d00084006001d04944c59002e503000413010000304064602140c40d000c464000c0c00240611941c2c2c01c100940442144900f07130703 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 350898174 1250 350896924 350896933
    0x4120309021503131209080712150b06070503130f05041803030c0203040e09030d060f3203061003060605030c09041415070306031a0c180102010b1c0213020309 70
    0x10b606080e0a020715884842c1d91068076280c0c21540b540c81c25070f400707003001001150716030406000001c0280620b00103462501c81103158101e1941c2e0b0100c64102444d11229050782ea18007000c1c0355994242243e40303140e0042c040301e8955200d50080c4941d0403031031040202c48601c4600000c2c01e03003003c0c024a208070f5a80c3c8210f842e00c03401600c05402500f2451003000444c0020000460000300a10f503090040701c4070001140c80c0d204c2401118112222904080c0100c60350303040802c807500c291300c10a030f59600c3d284009200d8103046904548038003141c0c0602d41d854041c06c01040f110b03451001a0340c040304d0045005200043e0740320245a120b109508c0803681011000000501003483c1c10200c03c00300c0000f80c100c819000f8400e03021030f0b1801081d0b50318800252030300410014041040382070544200740c00041000d0741000051810700380320301607618284940c1c00c802c1200682c000c0d80840e254000281003189820803900608004e8105d41c88124460718160600c40c0f0003001502c01d076445484002c0003403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 350899280 1106 350898174 350898199
    0xc031d060f09130e0a0809040f050112020a05010807050f03130209070203070b070e0f09040c0806011503150b091e031903110c06030c090d0503040308030412030902 72
    0x183c8a50402c030f000b07a03580501180f0441030940c4403226541d541c0101000c90050b092070f00940c140365180100010b5500700e002801d854040c802c4501c03914660700c0c1c03401540c0c0441d040e10704070001807080c00081c40d0000d9030030041d504006011040e4050241581c001450140c086850000680010409a0401200a0030705030845045d0a180e214000c144021511400c0503451803441880f0f4440800d0a204032160f0b07110282001e42c041d2146980c40722034140c002d105142c000c10000b494002c100c4001d42520303a40b00241c0e58018091440c0c80c42110070045400810303000c0321100e03200da660a8001f070380c08008004a40d0002864500340300c81509015080c455141940b00042e004405212002e0356280c04507a0300641400714281c03200c1540021410340c00c40c8260040079448001804000e204040c4003540c480c600c91a08904201d008513801c170300341c07200c4580007500914a031496 = true := by decide +kernel

theorem cover : BRFrame.Cov 350719424 350899280 := by
  have h0 := BRFrame.cov_init 350719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 350719424 ≤ n) (h2 : n < 350899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
