-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1538
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:27:58.40817+00:00
-- url     : https://prove2.me/submissions/1435c592-b54d-4973-9c7d-fa16a60d4787

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 276438848 ≤ n < 276618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 276440098 1250 276438848 276438857
    0x80927010b1b06012c040b0a0b040219030f0609060308180d0501090302030423010c02040b040905010603060f050c0a050d0902041112160203070305040b091516020414131101 76
    0x41c1000c00300400c0010300801ca401021780c0100c18100740d101c80b41c0080300405480720b841505000118007200c0303900b604070a100c5400202240e2440224005e40035404402c002180244543d07000b594040e0040118800c0f0840e003041520341b00c82452044409901000c0d0001d071051180b20481f007410401d080c0c404c0030041c0144090405543d8040c29241e4204080300103810114081241c91072201c03030703050a0181552108080440040001c1612010900207845070740c80300e0b100086616a58440c80b00d007a00301e4001d00600392a810300704c0103001030214140d002d901c2c1200260041d0041e2041d07030f0703584181d03980302c5282c0b02c0303208000d03401792040e10020384c0d2041e950b495032048180660002c00c1e03030f68948241c0944514100c8590801d040400381c48005641003002190f002070303406801c80e015261400d4403507494170f0005010403150048190070b420807035400500c40711501c541100c0d1448051013120240018120f802503105440740554400070284406107551001821010b07071800f1200b810302d007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 276441348 1250 276440098 276440137
    0x30609020a050a080703020f01111f0204081005092814030d0203040605060a05090c0a0810050409030c0b01150e0909010b041a12160308030c04030c03080927010b 71
    0xb0500503d542c4018199440050100f0440c1030400715042121005d0800003204412518100d07240c284416100c070321004c00380b01c29151401207506880283c404502100d01c83c05640c44407800a00c0709681590043c402c503103911045c1d8858164941280d400001d140071040003964540d60391714580341d5a440c603404148543c41810b4030510240d4460350040002040b641800c0003440284483c6800c1507025011072030404c0050100d01c4104d07170070010305250507601035070340e600721820342420f40e002554894200507190741450350050003140c0c07080c000c60000e4466682d40300c028070202c4020744a54081117400e810b00302d0600c3d000d0301569010441f507002054241010001030115031210070840003195003507541e11030a00749400107940300c0d000c4200404c2c0e610090103c05400c2d0010303100085c581c14000000802003914001641d0081d42c4c0102c2c200c45d21502e03032500c403055804c84e480483c0511740340c2c03400c05006175004915400c403e40118070001c840c1d00b440031010b0070750300139020002101144407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 276442598 1250 276441348 276441359
    0x6050427021215040c021207140708060603070e010503070501030c03140106091802071502071b0b18040519150b13080c090f24040e06060118030507030609020a 70
    0x1040a4a40707040045420b19090400400d500f22201807140980d18200003201c9450700020b0958050341441e14003600c4152511b4600b4080860340b128100900544100083c500c00009401c1e00804d411002c0d80c0525032200b4800c005811309101d4950f15900145003000954005d81c0039403001d201b076140105000324082140300c000c81007a40101d00150f10000200081002c0d20940a1150030006e41075250600719215242c002c0d03040700700b00c01866800100a4100401300c50f620020b0a00a19103920b144e51b00d140b8002203070026440040040c000303c0c0802050f10749071107520700c00c9a410a082c41403500740c080c5000100760103070300d091040c080481c000c40c1048510020f0442e00e080c81c212410a1807c1c946101d080c802c0c50f00401d4080c845080c144008001c110784850380c415000c0748000c813124903000440c050300d03c04a15150704a4503040c500c4903440800b155861080302c0a88881c40c400e01070385952500682c07680b002034400d03003245c0e4051000030829084845c400340000c24151580e519032 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 276443848 1250 276442598 276442601
    0xb0c0304031e090602070609030b1b070b01090f0b040c0507170d09060e0c030109020109030b0924040c050906060706020c0c06040b03150f0f0d05150a060e0f0106050427 74
    0x1c64940010401c2543d0801c02c0070750410101c0301074100b500d028441780c2c0c9166901c12001c54090981e081220041c20f44001030b40c56403064a103e42e8000d0540e0850303580d1008440020000720050ba01c1072410b0030180481400c1600410304032600f9680c8091604100f501c458903518000c02e038500c2d141200b004402c9484085005030140360380103080020fa241400f9001c60714041010fa4164041e0341022800300150f80c00c4039500d81240d070804241e0f01c02d03036030f00d4000504001c49007041c1c00100780303207410500b455100705800a01c268850728460f00603685420800a00c41003c8420391b40c011010441c00300011080e40261101d00c02d142c0c101c1d020400709200044042d0032a81241e200404040100038420b10a064001c1103220213980310002c0c2954000840c0c10403080e0711a1a00901c11070402004004040041d800f0840c01500c0320f528034241281408050041c0c1d00c81c40c0d0f43c1824000120b40700c010304400380d50481e501a150302d8601807801840c0305181040840040c010812003040701c0703565005 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 276445098 1250 276443848 276443897
    0x6270601022a01080f0f04140a0c0f0e280906090b01031b0b09010c0b090c130f06050103020906040e0711120a030606021507051b03120901180b0c030403 67
    0x10740b60801c40e0b11507241c00102100380040208400c00041e400b40840d405109400d980c200e070300150310030030204400070aa40b03014030780c020050429420344400641c5020b04078002c02a2105202c400c140c50f203582d0030003410f610451000642c03c00400301710f031403801a6580040c1c0e07424895100030500042e180c40d0141c5101d802d80c02510024010419107083c04a042c010300c003d44107241c90241040411070008000121000b40141851025804150a90010010076480344002403440303d094844050043c06401d02164104c0103074100100890298040d00a4820100d0068402810a40b070a110240203010142c002001e010110841ca000880c050001c6d210311800703000e030746585070b000742c10080890b8204e5001c013007103412000c0350300207116403600b00ca50000c10500d88a901c600e181c01ca0310749107100742e03469400544030000321014000c0b20503155901c100d4900e0001c0129089000d00400c2400d4000d80c0149198950000501e00c00c000101440d0080d00a1401c1030b00e00d051040825442d510 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 276446348 1250 276445098 276445153
    0xd050f0105010f0303090308180306070c0605010b04030822030f03030228020628150f12021c060207140c09010602011b0e030c0402120106080627060102 67
    0x4a40000a291000d01846005003040d0040180342c0c2e18544000f0105401d502000f810844005002079070801d01406ca51214607004003502c0c0706043c0000080c0105610702c00885000d0306003400050f00c2d1024400741c40403241c0188001c2e182c400401d12a0748607002007003142820080f07150000c40450403240070024050701c20b450040e0788030380b1030040e840792480946d00c50b2041441e42291540721075020640b0b43d004103511104c510010044204481407415032a111810079107000850304a02c8015030740c1c541101c1c0e00d05405d00b003494450071003200c490070003c80a0f42200c6030700c000c500c61414900c01c0c101440e0148200500f0110556503605071038000d0703005101542d114000326042442c2004100e40141014002080660030400c50450025022056101440303000c3c903004040e03803011302c0300d0401001c00030802c6589040810600c045003400b8002c0c2800120501c00141c0182003506001070b151100da840c58085610b1a402c40c40840707001402799046001d0140c001070034004120850301c4210307 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 276447598 1250 276446348 276446353
    0x907261504051504021503060307080d1d040501061b080d05040c060e010e01020d030b0a1703031008030408060a05071b050606030d0314010311010903080301060c17030618150d05 78
    0x92504060746080038054650f00210189000d0000698400000c0c0000384040400c10f52243e648600003410070000d03902c4441c690050155200589074072400d0300c8080103410f601010490700749000e000c21200c00340a458040f4154640c2281e41918611071080102e101e20200d500d481c4110741e03410251481500c0460b08030551078007d11104c0d0b0810340110040500f881d101c8881c80d185e00000756103604542c0b440381855680c034aa4422600c6d46a88000a0100a100b15500c010055052550b940c01152035248848034200046190440801224119280e0900424a40e1039440c4a00010304002d0b08441c00c1c070459208a0520840c04007903a060140518041c040d42d1800d501458182240d0b1646d850401d450102028405018804441d0540f41c00918450400c90310b000161940c4d004c07500040d00001c07000c400050042d07130203d80c0c00e02c0c092203400a42c005140c80c11003002d00d80030036101623a015022099054442c1c040c12155940f000b80c5920080f0050301041c0031404000126805980c9034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 276448848 1250 276447598 276447601
    0x2061308101d01140105090c09060705030d0e030f04030308061f09030b060a27090506010906181a0d080f1201030b280506041d060601020d020609072615 67
    0x200140341000c0c481c5042d03000a010308184440329030b0081d4030500801e88507074020004100504502401d5688807e00a040d00d039603101c00e800c005503250031240404801508007181140342000120540e249007042419407801d00b070441e038054519400080c09540c0140038005440f0147d00c3c15422600c030806107440306014281541450307141c031600180b101b8041c1c00c5043e002c20104554001c40001c6d0102c1c418110000c1541c00080c0b0701030025424003804900c40d02c0300106030070070958031000c1110501c03860303141244072141c0340e1401c0da144040090784085040048400c18100f100746003010f1885680e41c2c4d0704c0d045120000b94007030781014203840c58200c1240c005004002243c2c45580d00010581c1d00c030240c040b003000c20406a0112500c0101c0c406403190007190560703c1c3c0b82c01c00818804070008082c921090300402980c0c0d103800302d5080340140318030f03015802a40e0020030f099000300e031000b01038860142028440c00d0808691802400705010307240036004121003d220050600000c00e00c1c14001d03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 276450098 1250 276448848 276448871
    0x60504050106050f0105180a05040219030e060f0402121203010801021c110301030f0303140703020a0323180703080f0c2116080d0906050a23040206130810 68
    0xc480043d004a401140000d0440703244e41e130000300384c071000c1c502088122105140c4001150b0f00340e080350301164009002007240100a8500c502c02c200e8903005036003c03c41098541500c540d00d100644495842e11a071a0106015091000b00c0e40740907109402102d6600080e658020000d80c000d0340f02007101d0b5800700d0200840030020071140e109024000042c0102d4140868544030341c40180720003014254800d03820001c02d4001c0d001000030b036200196805442c500048050060341c0402c3c404400203141c10000c101020304e0f140400740c2c41601050121455076104015000c0c0d10440f8032050103403045400000003d0381c45d40007002c0813101d412405840b1115440c21a282c5480c03080c0100030600d0444401640b8044a0251482c8140b00200c00c101c039003050400d0401c6200713400018080f18180144c1e80d0030700042c1d0704150700414140303000300314168541c502107422800800441424200c000c01003030241c034200740940f1003110600b905015103039460624500d0401510042d804680d101c1030790024 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 276451348 1250 276450098 276450101
    0x40b2a06010515120106030b030f1911060721020c0a080a03090f06050a0c1112010501030b13080f0903010612030f08150906040f0e121312030c2d0605040501 69
    0x71403c80b0019608101c1c10100c01d43d2003840c14041d030001c041d0ba03039546010726075040080c040c80406030010748011555900c0c1c00300065510348070a0b41c0c2d03d10f020381283c0290a103041100c1c078a5401401c0300c480403a54049480d030010b41e03412080210320500085c3d0546546282484005000c100300400d000321444c50042d02c880c0082d4000c00b02d031500d500301000456003200844d000e141d814500600385500300d2409690704440b140c052a0040b15a0084440300241584054182c038000c1560114a40c0c0745003640e8409184103c0007421040e00384041c446010980000d411700150050020405c107483e01c103000c140509054003640000d0520700c1c289a115080019550403469400c03001c84101e0182011411103603000d840140034960b54883c0c0a6110926444804500061400c0d1075410300d03236150328805a0071500b624034440c0c0d90b03004000b550510300c81400580643c5a2648540c1e1030803a00e03180829910044d4580480d070408102125800d2240f1900d082e05200b01d50002d0f00c1c0c03d050901a0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 276452598 1250 276451348 276451369
    0x20f13080a020907030b1504260d0e090c0c03070503040905090105150d0201021c030902040e01050f041509081204030215041e0312020301032604030305040b2a060105 73
    0x40d9650420211800540c644820055001d0202d0601207080441600807a5149605c03c8a182c3c08010126001c04c0c0070384009188084041e9011a881b10612021262922030704000a031001042d8403880c80c02090070141001179000702d2505c5420700b0724804c1c13051107045510500e0219819080001c05118102c003912840303400c00c003444001c112901d411404040035141c070340340c0144110800c403038100843e842001240307500c03840c160103880c2d00102110050701038210034604038855803d20104a0b04180140f1030b480c0314034403486031401c1e144c9885d102c001d4170007545103d030103440d44c455840d000498028001005603c0710781c2e0030001705240030f0600900b0403e8032003240a071072516134144030205000001d090400d001c0d0b69000e101141d01d9207801d41e400000710382181049030002c40000140107036503110140384100c2c8a0464a00151040d254010b84200d01008000c14003d01c410f1090302d1b03540c000340c5003001e06100240c2c030807207030740c4e410045264204240b400d25520170001803205081c102e0355003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 276453848 1250 276452598 276452609
    0x2010c120e0a060207060b0301090507080c041506030b060c0106061214130326010b030a0c0203280c0209041103010605100e040e07030b0f15010c030507170904020f13 73
    0x1c00c90714403041e800c581c03985200d1001420b031540124900d0140708280c1d10075070b08a40018020401080e051030069240c11700307031042c07040e01c0c0a49035280720581018081d260715200f4000445071198101a800c0c0c0c020803c02e10b009400040901003040040c000340b042174064130310794a851840180790700030a0150b03001c1900581c61800c08809101d4042c02c030b9140c0d05030a56250600a262800c24035000b9145600d036201082e80c0c9541800000b0b501501c40d00444c00341d40300d4202401800040e2070213036074911a030b540b0b2600c6482074050110500d80300d003119032580c11441c54203400c8100c440d00014540c1c10195400d03115840c142040c0c080c81d1030244118130051000390354468004007402e00c05071540a840b5100c9001c0d90325102c0f000d850714020301405c0c010b1030f4030142441c0941071802c0032038560007041721540720011101441c00d0f529030150303175003d5500341c0c1540d503586010b460380c0d5240003080c0364446c032b80f480350000d1000c1070750784d03603940040d01c0030f0288654002d03210141c000c514000c00c0d4155004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 276455098 1250 276453848 276453851
    0x14070f050607060b0103241505040f030b09011b030b0f040b0a060509040e030f1c06031110020f0d0509040b180105060f041d07021b0618061902010c12 66
    0x81003640c032071205895000340c02500c0021600303410001a00503241d08100540100c1590b8124180c00c5a0580e070709040d0751884100c054171090501c000d944900c160701418a0b100e4240c2c070200001400c2c064010b500000314000416038011640410031046651706120b004603440c1c41040c001420003a98024801d441202c2c00c0c44400200404150303420fa0324064201080800561820307240c9464001c072102074080c5080740d0f9203869281148600f42c2000c40c03d04040002e8900400c03c04071540158020f4942049845100172209820400355000d298226000e40c01000804022a031080c02841401c0c43c45464a9030b48216050401044800340c050143c420204880ca08100102e04114641590710a40d04980d5800c0824500107440c040c0d07030300c010842c0c503085080c2e600005900000500503c1c03a07070204c0b82504607414040e840c0307000004066402510900016440c06042040396080c02d1b0003612203464030b8440142d802d440c01c0001c7c044000341c0c3d150b98240401d2075008115802c100707100c000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 276456348 1250 276455098 276455129
    0x30e010e0d1e05010b031c14040503060c090d020a0e183d020a05040905070305240109030206040308070c1517100e040b010503010539040807031407 65
    0x2d48600c84510380c4101418030103050034030410040c1c250301c4074030400c0c4020100d03003c01100540380c00e0001c1c0120300b510700007246a690081864003080c150380544074014050086a600c920085040b80c12004107540d10506203444030340581c41d00da50b04000380c5a07056070b0003880e01c0e01100c44c807425a4204402e140e81d80c0000c4000440c1d0150a03c05003a050f100003c03010140f40102c0304c0b954850804001c205141d10000381160000e401030000c0c022501d85075001d120b40e640d000d4003502103441c03c0f51400c90414207001042c030205030880a0241900381418030818090320ba401080c000d4000340c00032034079484000b03803c5c1d0900c9003c0585034001d1501140600040320300300c000a2901d200c9140905c01505000081041030304140c40020251085101021103032a040c18601007016003031140a00952238140032401c014604008070004580c1440c010582d1486104000c1240c903800b814185821804d01001c0b0340c85100b8071100d001103004400a500d402c0441032183c1c10b20002c0c0c0c0c84004c45004588 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 276457598 1250 276456348 276456353
    0xf050705130308090d0b0f0907060e01020a060e03130b09130618050a0f11120a0b06071506090513050c0307050d06050619090c02010f020405090615070204020304030e010e0d 76
    0x410502607a900040084d00c0700f41540c003064803400c0e4040010f040700c5044040148160180d0381084c860640503080305c507900c0d03441000356004000744030b0348d40c01030300528034071408290301d074011019000005040f40c0c030303000c4c0c808030319406070070315820001c01940001103034031052038066240e04080c59002e104000d000e181100794022410400d01d1501e00350307190b030000f50009840d544030b4050980b54107024850b00220180c0204d00b5481113000903019804400440c510820764031420034551400340c5032607d40707012901c031304040c00303018075600c41c190b610360742c0125010380a40581401a42c0c034030310041d5200b0040c0b80c4241464101c0703001500a61081300100025914040035020998000c000001d85448020100e10a080d00040700c1500a2610307000103018000d5a00c0049481102ea0080044000d10000d110980c480d61103425884507035440824454075100b01c1009401c0e1032042410f00d00416a170119040c0c0e041110182d0100d0008a030204ca60751700041d000392055805c46080410341180d5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 276458848 1250 276457598 276457627
    0x130804080c0a0e0642030f07210906180b06030d0c030c0b0601030b030a0311010e0705100e031f020a08010503160905070905041d0c06040303080106180b070302010f050705 75
    0x34100e041006583c8000000300801c44100d01104014401c01c030304990b5203103407031703d9160b600983d5042402801c280024502902c0f4541440c0900c0b0001c210300d03441c402e540c00e170101510f084001682c00390341d582800300c192407074a51040d00e003500c0780c0c0e0468a03926110003010700701a140c1c4c13107600503c80b1421403040040d0380000c110f00b0059008004000e90380790680100c0040c030001724403e0301441081100814150002c0d600c42c2c1000b541e100a0081c0e050285060340c40302000c1c8601c5411a06012011402038020089404661400380031034035040c00750100c09002465680700345296a60001d1600c0d0100e6000c25a203000d49410b600500c0d030403048c00814080b00c0c580f4825400c0310703540c560110300031600c03074050000105802402805865410940c0b520310084400390700b022441044451060b60510307030f0030f46007100d8154032008000c3c2c2ca406400e69140c55051a123055012580c540883c01e00350340800740245600a070f0001800c0500940a40d007258006401d000511006000260390203410307 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 276460098 1250 276458848 276458869
    0x20c0d1101050d02040302060c150a090302030f0c01021309150501030c2106050414100e07020d0807090308070501050f060a0b0d0f090203300415030203130804080c0a0e06 75
    0x70720b0402c1c2d81e011001c41c1080240150b40000b58007032000205120744000018119940140c009001c0066032a0b480e9000100c60116600401581051120003003041c1d01001811181c1d0140001500c0c0035421400b1480021054010503585a81c030041801c80030011111480a01420300b002c00c05031407850380103000302e01e80d900e151050345d8182c3c84800107400e20785c21140c02080094803c1c84100241041c1e082c1b910003c5903000090f0844004c00246c0d0b44a034020b550007a80d95401609204051020440d62080014059001e12840d140d0000000d02400700070036960b8066400040c2c1e41c10210081d050805002c6c12041c410b4000641c280301c0b000580701202d00b80b1004a0000400d060b501c0000d5025090b6440083c4d414015840c0c550b040c3c7c82d1060a540040c0070980e01484144074880707101d107823802603004031074541808400b2303103080c18000e1b4015500b008492980051000e0303184e40303042844c1c0c82500461140d80204580c07090380c0c200080c1c00c9010b00600d645134407003031800e88007082a4092 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 276461348 1250 276460098 276460133
    0x806070201142a0d0603110d03210e100903081b09060c10020f120708040507050d110a030c150309050604030c1406070c0b070e03062e08010c020c0d 65
    0x5403603540f01d01c0c00c0e04502520307020041103c0301c0c507290403000c0c960350300174080f030302c001d403074441e80c088400d581441d26100340c224140e4981c554080c840c0c40c4d200050b840c0b900d983d40945000360349607016031100608003d0401d00f140d02c0e01010804010928004280840150581c6801442805030a44600451041d0745445400740c480640700c0b488030841d145070000c1403101050b4140300240b40002501d2440090202d582d2501c41d1078602d8440f298102c40c045012a8085c0040d00315500a0240b464104000c1c090140110000c1c1602c5c00680d000440c3e65589901c2202c40d1701005004104002d2820030000d02e41c1240d050402c4200c0c0c1e191251515010700603c02001c20210003252020400c2c0724142c91601d0301c042d022601e40d0b05e1b0a410181c807404c0700c54070546024480800250b4068801d8101d5000603002402500150b01d071100848188160b41d146424440c1020315400382c20503e8100400050403171000204200000e002d01038200036600d920742d400307502c800c0c0c0b8240220382003460381d448210 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 276462598 1250 276461348 276461371
    0x207090c02012408070e04150b0a0504150501020f0d02070314031903020405011805031009030212070c031b060f0f0e1e0a080d0212090a03020a0609080607020114 71
    0x6200c010101d00504450054204002c071541080040c3c1e00350740280b10648400c0c02c1110606034070781d00c0c840d0340d100d0211030041c0302c00480455065083c1103a000000c3c8414060f0040300e04a8541e0009015a00c41300c0e003807294000074100401c01980d0401c11600c0300d0701404054900701300c40b24802915840c10340006450311908510803040d024082044880100c201c0c1400d4031038000e80100200130703500a218803030000d859403140d0941c00c0c0c0184507000490714020010121680c8050000d0b016001a280036010360181146403207041c803003980181003051244029060b0541146809106003100c40d6106280c501d042e482406603030741181358001020b0349410850400c6428180071148607940b001c01c16044440c0b541402403103030403224008a4902c0850340c03081e04035181c840322541c0340c61000c0c0380ea00603403200780568034900e0742c0d1008080b030100141c54594400d031a034011840703181b00ca501031000203800000400c8400010320070740744c116882e40700032320220094042900303180034081c0c00c040100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 276463848 1250 276462598 276462611
    0xc0f0614070c051207080f01111615020301081e12121302031f0b010f12020a0c05010e0a0b0705034302010227060f03190e0c1807020709 60
    0x3400741c01810082c103009020b207401408291800c3d8a03803105d80320b00c0c100e611803000d15030b0780080e041c09002c0c007100940490f02c1c00c140c00100d00000740070a1040680e02c1c0d990030440b05200e14a180029806840c0000051240c644001b64404c0203407441d6140b0f0000d5008130880c00f1f81c1458030380458003801c1075070071301810b40d4a030000d2000d40d002c801240254980325100d50481002103541d505025400101010881203440c0801540c00040b8803040030002942c182c513003414841698003801d00305180385400d260342509940c1d000d08503800114142c92a42c440d6606000b0081d082e600130754400320f1440c2c41815400d205010a0740008203884d02881d06030f8000616142044110a5501c03503198185000291101140007038000d6201c0c0c507100e2844184069011400c0e440b0804805c8560001740441b4500408100c8241c800d070806020b54200d40c5181e000d0314400600c500032018a00d84501c0a44000f01d5983c007000342040318042c48006001106017000b40d49074012480100300c410351180800e01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 276465098 1250 276463848 276463853
    0x9030a061b02012a05210f0708060109210c08010501030b130c030204020313050604140609010606170a110304050606040f0507020307030305100815060a0f0806010b070f120c0c0f061407 81
    0x1c0380103a494803806100341b000c40d81c13401000414010b01940700150141c40030744035004d0807034140900302c49442c04584100000c02c01c43e4000600020400ca43d6802843c2c4094036648070b003000750040d40710710040d0b03458000520034014030300743d8660030500c00040201c10000f295208000c074055880080d1244c1d03170100014525030074040d46190f42c2035110050300c003e4601440c1c19806001c0001e404102c4e071040c000003442c810700521031401615129241c42002030b9a405183d064240010901c030070145d2100150804404203002450290b40720780064039062610750207100843c2c1a00030300500c594140814000610f40201c200c42c1000e070586008200d1b42d882d201100180302d1a60f00c04540340c411410504190346d41c00440500460085446031040ca0361494041c44407141805000240c0c1c200800410035100c20000400d107503407042400940c40300f09901c446199072210691940030507640e0040302d0420841c1c405e00742c00752499130281002d0f68140134006000126408076003011000c00201c0ba401e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 276466348 1250 276465098 276465107
    0x3040f0b0705070f03060e122104080f12090c04020a0801030f020109030b01141302041a0c011410060201180b06130f020a051b0c010507061109030a061b02012a 70
    0x1600e01c9103904c1d0000c99036460104020b0503001d015007254040c00034400d1001d80c0c40c07000c50714400300540c040c45c0114100b0080102c44880504200c0741c0c500d082011541c82001000981a1030326403200c03000340d603d41410481c0c1040303c120307420352050740304225001c1123603003040c20903040d01d40081c0251918916480161030f50605a04040c03c4145403400009464007807100700c0c00a4541038510400c04174100e1820b0043c1d0285025140c03001c0034034078007103142c4803681c005048844101000454150284514081e002006480904807680c00d158103000380d51b0240a0f512102d00781c040401e40c041556202c940a42002400152107080ca440010000640d2a00111401c4020581c1107540e511044d501610a40c010101c00311500c401270420340c403203480070505a501c0c000c1a150145428080d588a2004010501c10598811b40a020b85801c5440030050f11824900c80c000000c1d10034103003504000000907902c80e0504582c1840000c9500045000c0d00220b10312002070407105a5080c200d0554 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 276467598 1250 276466348 276466363
    0x1060f020f0a141207020a05090c0d14070e0105030f0126060903030f011703030f040212060412030e0304060e060705070312030230070f0306080f06010f0803040f0b0705 74
    0x34441e12556000c0400d03c0000080c80102c000e48804032010380c01001c2401d8014040c0300380295101e030014104015504203201081d5000c141b200606140c801c1c40441c0d1421698140740042e1404809002c000104d9003020b15a140800c007400c1943c01c1d4a400c3c3c0170318290b0301050181450040c06a62180f100800300e500c2018030060706002d4646134a060380322180e8a4100302c6e04000d0746d2907c4400007800480710540400e0801601c00618a141e50368085041c07216800b4004982008084100c146070703501c21b2140c03500591040005818140203110000d060f2500e040381d540464004000c1041559041800348410703210030341d005526814a17090007418004283d2001d004a85025040300e01e5650581c01000d03000410b007600b102c000c010540b0089450100280200e00c4c0003000e022806890064814040e025202d1a01180a944030501c0504003581c241c00601e00c0c0c1c4c480001070100728080e00610010f05a41c200840c24680340c40c0c070048804190748a056810000020740c407051040a10008 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 276468848 1250 276467598 276467623
    0x110307030b0f0a0602161a0a18320303160201080405102a020309180a062d0e060604030210050d1503200105180102011d060615040e01060f02 62
    0x20300b03d035840d04040d4440071000c080d205003c1c940100851000d00094140f0700002080b4801030820100140c1620649510080582e19980000c4001115022000380d206404000d414000c040803051201411441c112010141300340c0042c40049a028859296034031416024a480e82058a890070942c0c00c0c03810410018900e90f080907141c00107281d21051103509142e1925907042d07038005422040307886c0d01400002c5680102d10444500000c0004488980c021000c030340005040c80c1c1d40d01a213102000d542d100d60198000d109003c0c200c10248807004030082408509041315031070000c00048262085000c0284918641051001c41922507019a590003105203c00c0020807005101c0c00741c6007a184c401155050392451401e501c0b100c080e003c80e0300c0e030351060b12864104501307101c10611034240e620000341190360f10901c481c04070313100b40002617001d00100e02408540c10142c00b44000188481c00c07045464604000030821550481003070b5044850b140b4148030441210381d01242040c8441100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 276470098 1250 276468848 276468859
    0x2c19030e0310140117030d05040809031f110f0a26071206060e0306041211030d02070b0c0f0f0304060b1306090e0f0709020d18110102070504110307030b0f 68
    0x4984111215501001e00180c0f03518151401e40c1e682d610450b81c074400c490744c044254000344a010200d031207607040203410602c80c0a00c51f003015440340c003191814000030480107801d500004001424440c0e031059041240c1402100b07440c0c6020300c1d02c00e040030702c62002c803182009025003100720f10317480100b80b404444801e4404034410f400e0100005020308200c03204d510906103440b0002410314000d5084250700d1030007402810080e075a64480202071100080b210092080a0706000008001070009040c5140304400c0140c842015090003130b0500c1000300131422404c4104070301d82055074400f040e110142c4400701d51507546d41c0c0c2c0c0e1602801034010b200003147c024a03407111240842c40d1503081001900d40030030040200048607100301d944c4114064400301c413604a007009001000142e001061043c040c20b40c080717096107002e10581800184110161202030248000c0046981c1c103205080c014001280c09021200000d100164180b201070044800d2683d64800c1d4045d41d00d543c110034460440060a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 276471348 1250 276470098 276470113
    0x60a030c090b01020d0504031a0405120c100e0a0b040b0c0909010b071202060c040504230405030408010f02120c09151305010e030d0c140c0301020a032c19030e03 71
    0x407007101030140120000d016000d02200d10400034818000d440449412940d001698006000d58884a0b03c1c041c1c4140e425014901e031111481880000070201c4054840c0144817000092480f54112800144801402d42000e5080c00c0403c06c9600c4041d00150000c407a050b2a8854040788025032050400301070300007100360300010b01544001c004e48001801440140c1203021f400178100d0700c42604480d003000c0c024007030000703208a06080c0e001c440c00f087c0c006400103039810241c0c224410450102e070103c1d00c0764400035003805061800c0c01141c00103c5148020350a001c01d60143e0a82164020400306040e0000f00303104582e45c0d02c0341c0c0c00b0300302c08083c00c0b0a19a185942003811070b0b03410044c0a43c44c086101403018001c40d0030002110f400780360a960780c0c08030102041d80e6000413500c451803090fa0901c100100d50314145d80030320027002440312540780010101c10a4a642c90345994946400b448041400495045d100000c5485109080c0581c14801c95034410703d002d0710064500600c05415214081 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 276472598 1250 276471348 276471359
    0x6020c0f0901060906050f2206080906070518130911100801141c0b040c1418042a06091502010905150601030f020c0303060108130305160f05060a06140411070b060a030c 74
    0x140034030527200340755111080e591320f100d070fa240c0d6104240e50f8417000882c100800900021100d4103040c0e40c81c0d000b0010100c00c80038030002410360303a8103401030b40c1d01c0c2031880d009c1d41580f83c00b145010b9415020300304214198540071801d0a0b09840d00c11690007480c0413055180c600318102042ca4100d80c1c0b10f5103002c20743c10a030810390482200c90013242e44296540c82541520b00e003c0b94a00014501d006980070955155078a101c0c440141810307403001300310a41e075003001c40c10f43c400c0500d001d051640c0d50403000b146403410402042201c1d000d44006d69241c82580c6001c607a000c99500b5000015030700e141d80c07544541004030003c15030700d40c2582c82070380b0105007103000f8035002c001580180026070b07400e0003d0300d0b505621400b45403200301c000c02140c01004011003003102c800503182020301545e042e00307000c491501e07494200740f8200c032601d210a55800062116894202601540032810b403410403561454a199007040e1154041c094142850240056000d99902c10540040c5070300c40c0002c00401d0f07544 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 276473848 1250 276472598 276472657
    0x4030f110d020a050106170309040902060903060a09020301061205060f0c040f030602040503070807060c12090e190c230d0f09030c050c043e030106020c0f0901060906050f 75
    0x203c2044940d5401e20302c0c000707008074800262a001d0780c4603001840c600119242044003c01306544d00700c0e000042407098116559080c41450b00c2440c070f8180102e104013140c4101400c4451680220410600002c09c130300104000088032a81301c108100c0c0516541c840d01031005503405035038804643c60041181c04410092175401401c129541641151015a210020140c94801c20b020b46800035803540c039a080414030300798045141c00d20504010403065142d0300c0c03c480001c0304580089000003410102c0e400101c00c1d1040102a58040c641a2400340d0100700194003c00d20701c10b94043c40c0b1004c600b5000144955200c02c90100c2c00d980c0c10024000c2500c0c001d01038051900701030b140c0c2e025186441030113041a0003075204d6602c4d4032b00e034a010003d02c005218030381500e01d05082c251b0102070040d4010561402e008601810154006141e114140c200f00400150410324160086010318010015a42c0098004081e56042d05105890703d50740400c2550714000d102e400010000c24101c100e80320b000741e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 276475098 1250 276473848 276473863
    0xc060608013b030a1409060a0306051f050a0e04140403230a090504050c070f0c1a13050d15060b0d0605042d09020306190b0a0e04030f110d02 62
    0x42c841c1d800c92203960707004240c0210750ba41c1d0009400c0c0e001000f1030b001c030328400e0107000c0c094211442c071241455560404541242c00040d1040042581c0e164103210500d042441e42c0d4805138400ea410400784100035006115014900c00307401031003080703c1c2460f0b540c0c0c0caa400c21400b0495181c0002c41510300f80c140200500e071207801040d02403000c0c04100800c1d105940403202001c40689417209a030f4501810701004200040020954180c28054180010810b0b0505804103001d145810800360a05a00c2207803450304890141e811601002885000c003001d40c1030900b154001c4a036240544051309200da1100704c60701413000c0040c0341000106801c00c481014140c0c0740b00c0e40741d0070407000344c403070091008965124480d00407012110080340901c400050241c25852004040031034114040c2c0c2c04070340b402c5000e98101c03040103c55510141075100b036220b030b0240940200d5110714164540003032510180800341000d810000b178002c02060090242c1d021818201e1000200c5071008034408000b0b4880f44c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 276476348 1250 276475098 276475151
    0x3210a0807020a03020601050603150316030212030918070c080a0203071a010308030a0c0513060c060c03020708030106050c031204050109020a0602030414010e0a090509060403121503030c06060801 86
    0x321000305800a100040000781198160000e000a900380401c11405400083c01120303200210200d411040c2c03405d004450000c800d01140c4c00749a03056104200c0f4070042100c46d0704151b4018040040156501809011400c40e000000d65180c4c4403040111110020300d1406080c1b002c0c00180100384d0f0360700200410b4018056110400e0240ca0441c001d46485000c0c440508129424000308005040c0c95105040d004135500b0880e284c00c18038104c00b046d0481d02d0f4404000305a0180380c113801e00c0150b0084a10140f080d1808500c3c14119954056583c00103005400401a000c142003035950810022600c0c0100c042d0f1400c1c04500e400d00e05a40a0404200c003203000e102802c0e00000c0c050b00000556007620044052489102031001c01140e2210721081c80030360014411000140b0f104040c40342a000d8810079000d000145024100070b00852945002c81e40c3d040d160054060710150340380e0f0300700107883d85071600c843c0d84109400c112028001795040f8144030b51a02c448403072001c600540ea503034150b0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 276477598 1250 276476348 276476357
    0x31202120306010c0f02060906030f180604030e130b120703051203070c030c08040308030a020307030c0201291804081b030a0519050c060906011a071a0618070903060e0303150f03210a 80
    0x1c04cc0050503440341c4050b00c3c003c003c940e0310201c002d42450441e08424004000035000035070a8030020004944d101070164142c007980081205205003c001c6c440d0400020f1000d8004e8614201608014406401248042d007080a015008410401c0d41c81c101c0d801103401149140c2c0768200440c20390000e44c001d40e14100864500301e805030011b030040c042d0500c0103552004003821402c016525210404500140e03c1d80a103044860a2480141b80d01c01805140915a0b690b110700c5031032031181060108600c001980d51040c8030342c035040381c0d1003000c40300c02c0c441801140c1c03400800c4042c21303161802040d030209614000d010400a55210015126040311031403d1100004840d95075500203a100e042006813180c44e1120070704010301990720011b0b0700614082d02000340d102b0b201c12080d08411082d01c0314070001c1c0340200c0c2003080c00706030f000d0b0a503114140c501451450030400410f11a0015010450740109280e003120180d03560b0070701003401d00a0507003105903101d141200310140d460f80864911000708 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 276478848 1250 276477598 276477631
    0x501030507050f220e0c06030f0105090705070f03031104030f110901060e0a0b03071407030215070809190c090603060f1103041515050a031202120306010c0f02060906030f 75
    0x1407410280e0b054055504d41c1c0403d0240040450710809070000441e1140240b0940300359241c1901c0b0b4400440c070a07402410001d800b5418041000f1008001500480411405001e11310109040c40c10030300010303601d030500040500c5162200d02d803d004a600c0a071034810001c0e00d002c20301c00702400c242c00040c400c546200e030380da880381015201140304090f003c0d0000b2447c0c0050041800641c001d42e002111410090411000401d070000140e1002604400507001182c0304000c85064028054100c840341c2017912031454005501c0342d4841c1c0e01c0b1150310980741211140742c18032000109200240c041d46500b409038907120305110028060410780034100c10b240600d1001009680c40907280515400035041e240403c005000070041c0180e65801030225080400001d000e40d40e50900ca030055126000e0040300d41101c05010341003581e05900c004600a0070000c0002d280c0c0d02c0b5140b0300445a111240c101c928481e40041074287c022011000e40120000060155903404805168801e1060145900c0b80 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 276480098 1250 276478848 276478879
    0x20d030501080c010e04021b0d020105150d020904170414090c0708040b0304030e0a091b032f1c060321020714060d110307030c0c211101050103050705 66
    0x12035209100303150641c0c1001da100d8007558070401040707045050040c40542843c0018403030344d2454100c01c031441d00641c02150700883c2943c080c01040d6110440f1940018100f0b92103001c0341d403000c0c5101009110f051004002400c000303205004000c100218440c0507103441e00c1c1c44400550008202040b446001d1000000300500012021242d00a5002449506280c07401c4038002150300050012000d004e006001c070355142d2180140314004000010300403602480d031080d0000d5480c1c1c041a0b4600301030410220b801c880c4040d40c00c640400324006404403035000c07521090b119a000f0511144a00848000d038400c0c0245641c02981c281c90051003d0f400d01c5104200b0100201d0740c0515500c0560000382e0108107030103050310302c1110a00040d04d140e14154200340031100b1541050140c5200e0000401402510360341840b80003400240b90800340040001e613100ca140040b0710946410f00703e08070590140b4131502c201e010000d00c503040030007889256102c0c90100d0700c401090040a000d0050030303030900c0c1c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 276481348 1250 276480098 276480101
    0xc020d3f140901320c070501020706050a1d0615030a02040f1505010504030c050409020a03060203070320131701020403120c120302030112110609190504110c1002070f02060316020d03 80
    0x4d0048010401e2008041003c81d00000290007400b00d0410807043c0a42c0010500038002400918460000001c461070000a16800c8070200124020380003820420301c00103003400103405030850360f0150050400c000e5540002d00d020219000290080d01309402c442a000454201c03410103510500e00b5aa00ca846500440b1240a0780c030018003084030400f4100100d0034aa881031502a0019141070002e5440743c403110181c0e0b200355080d00001e651051590030700c144400c6450307201c13130542c84680d150142d00d40009030350440c0c6015040e00c102c41c415501c14a948258100e8000310390000c503a130001d5401003805081750341c8402055075550001c0081c002494441d2080364140c5060003402903024046880c2c1c0c106800c944000c1c507401c04000c200d904441d0b61070f1002c5080d03484241c1008603110b400c0034248000e8a54505182c08004000d1280741c3c012840400c0c0b1000d0364031034800058440b42181420410301c4000c0e072002c2e4002d00004103012241640411400c4241120307000c840c00c4680003a400c40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 276482598 1250 276481348 276481391
    0x2d091101050c030403031404030f051c0212040b18030f030315181602100510090609060f2115051f08030d1a0909010c020d3f140901 58
    0x302c01d03400801c02440080c1c00398000361a4414a03040f4103040688a60342c4080c640361b0750350207071003690216110b4445080c10081640ca0540e00e44050020f911141401180304d000f10b0041c0252007002103944243c00b13150603e031004520008007144c0703800c405c000802e6160361098480411100c5421101703512030400c0320507600650004641d948050355040480a80c0708940c003001c03801c5009594080c810044607001e1a0302a01c501a103a6864a184c4036480b0210f0700c19074032682d40e003402d10100f0401070003a07000e68022902e200140030b0250f0180441360441021408005004403080106004a000c4a07846188100d800040c44280c254800044410494040c403e049060348200720010b100700c0f10f60040041c07005035060120604902c040001d010740703000c5a031031200b42c2d507407a02e40122650400040001c8a103d0a2040e880600700f008409100f11704598041c0c1b0900080720109200961402200344080b148000c200c00390280340a007942c4070090f100c40442e5820801d544441809001424 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 276483848 1250 276482598 276482617
    0x11704020607020402070201210e0d2c01110304030302150919080c0f07080c0126060f0111030d05040524060f01090317040303141602042d09110105 65
    0x742044001e43c2040060341c42031904904021303c807140e004c20201c9100b030183c00d00420b0580071070000c1e07020b8140b920340281c400625007003001c24800c8242d15034800745980404080420154a0a0701d45030040e10240c281002d0030006100010300041850b03800300b040c46a031420b1210000702c81e11042100780c0e4481000ac40101c0da0003e05040a0001d010180242401c0321200280d90003003a0b440c1c0e40309e081c04900e521401d41c9401901204d222507074842c0d07811080003601c1c1c00c100d404c18141c420940c0d00e07144c01000c0e24000c080101d015000caa00500d00984d9544e10402100d0b80d404244840001500065600b01c1d507a03c0741c5120615581c50420f240c94800d102e45000034581c2d51410100301d145c01003035041d54140110000301001058030658000c1e4041009520207a6451943c540103003034031842c1e406510204003d10910000c0c220705842502010703011200400c00b10b000400300004031031100e02c1c1d5107204141a5440741a030203941c2124a0701c0e406a510b40451080d424010f4841e442002d100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 276485098 1250 276483848 276483859
    0x6061509030d080a0b04111923030604020f0d021902070b07080f070501051e0a05010b090907030e0f0a0201030e03070b060d0f0503070c050316080d050f071a0601170402 74
    0xb041c8840b4842d04071994408800720000c10a0662a17021a04540c07810b0345603201c149001410880350718000c02400100545498400002c6508100d03403040e04a00481210361400000041007855440c1c4e016141240151220181d603090307602240e900a50041240b0341d1000388119041c10414000f0617410b00300c61400042c1d500e030115a83c1c80d00303110b50040b0032200c1816401e00c040004a0024805d6a10403030504500714402c601a145d00240054000d0070021241c0c02e06006201ca002c209064540101d01507941c40c8040d150320307200381c3c043c02d40e500d0649c2141c491b140c441203d07990000f513a60900d5001b038a013007069101d002040e68892041342d1000d0203e5851501141171420700c14421b000a500801c003000070755181ea52074900b5a480b101c8240d401200e1400b040c442442d00b4054248810920503031444024640340080e82c503601204840c0301400b5002ca11629402c0d0008215807015500a00ca5041c0d040072190759040d1207015102240040d1201d0045000e038022014154040c9800928 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 276486348 1250 276485098 276485113
    0x130b1510032705030d0c030b090114010c060506031c05270303040303050c07090f140a0c0f030c181e0605030c2209020c0a02090705090d0204050c07020306090606150903 74
    0x10210488000b081c0103d0781d40c407007042480488803061140301c08140e042d0394086180c1d07280310108215000180c00040380d4130441030726200b0350782c2c0100201000540c08180400c4a54403440045d040c1554076200d5000d05284584402041e54080c001300000001c8080e02c6c21416003694080703048018a07668207406620070401800441e004074007502d1003400340400c0300d100e140c88545d03d9003640c0c201c10f0913543c03242c2c94400c25007141000b4402d0941c0071100d298108040f010380b2200506250095036100c0915540303c0003203c0d503a00c0f07200385c10308401a00c440519403e1b50303910112417003046002031650040201502040f0309125108403400354140e94041e0341031140340000c59103000c280d42d150744000100c0f4400021a0070642c0007601d00e070008034018240011040c0103000c042d0b0170041881c820060308001001d0309070fa407001c3c135260568064400090383d698145e00542c0b18442c100700a58144905000c109400800181207171280c61300b40c90001e40c1074a4005001160302038041600e5040e0403060 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 276487598 1250 276486348 276486401
    0x160807031104021b0f070902071a1504020a120506040e0d110709110c070e1902090f031203010f0b040e070305090a15060f0509090c010503130b151003 66
    0x240d03180d44101c0001c000510b00f410407000b00c00c3c110300c400078805003600001c0301034029243c180190001800503e4065161003000e603a20216500320380c04821056200401260310500b211100303114004000d0001c540ea00500440138203010191013407111058102400a01e040c103141c050100c680c4940c80c01400300c00b081c06001d0710510264410f2030020302c542d500006030130b0b40e24010110f880c8400544e0321b40c0c40c03105810f000e0a01c9002e0700920020500c2c00309102c020817070310020307042c81c8003420801601c94a06038001803119002200081d031510480001c408010001c00081d8102d400100c140d001007030b43c0b42c2c07002d100c030300943c0b15681ca03100d070000018030000d01035004281d0007070480060380c5014402e81d0b00c0a807503003c1c0040c41c01000760341d00e1046c0550001c00c4c0d104005003d0840e0362482c60710701600714607035070140306000354100100071002c500c11000e6120700500d4141e01980412051a0903000c3c840d40d402c0d10b510701d5125040fa0754040781d0590091041ca040c0c094907204c40100e410004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 276488848 1250 276487598 276487613
    0x16080316020907170705040602100e06010b0706060503070f150201050105100318020a0b0322020604050409080f0c03070c05181812030916061103030a050601030209041d16080703 78
    0x4044400380544d01c00c0b4004000c0c41031340418819500d644625886a080400003403074411060750380c0940b02e18004e0a00726a2000040c140d0444801c03202131951000c440c07400d4005051250f1051b5018450320300c010481d0701c8aa40450b05031100c041c00d2440308004100120b00b81e0303d0070301c50176070054101105104628440d0704091601803c2c0200040c8a0005034003041100321158850a80ca040c040280715607047c03040900941e22652030b220310055003c6800003140c40c4568400d1510a175580d1349050100300f9481e099860855500c180785860700b64808001e51030358070043d011283c4901c0707030402081364940700160100380440202d0300b424075580c07280e07001d002400e01c4e401b0342414803550148541d0540071400070751040d030124028006d0810703c0100294800e000d9004032041c0705a40d10342443e40c1d0b0000050740d6124000c40c0d00800c0c603480302c40041e03000744940551241c00c0f03030074000c0091080000c48080c03042d01048004a803000110300e40c03c4e440184150013543c0007a0800b171410400328589 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 276490098 1250 276488848 276488851
    0x40e040308040c030b13020f04060f09020c15010617060406061d040204120606030b0105030c030d0305060103020715020c15091b040e010e1c0201021806030405150108160803160209 79
    0x20300f5241180c02c0c0c90303840380f04520f2401c480c0140c1e29480c401440e01141010314001ca4040c0c1e007910140521403c203000040018010300030b403040d650f400306840f042c248e820404c2c980200030811000c0f045503100d50008100315820a4034116490510021481c0c40c200792240b441125a02d546544010030710900d99410300780b010007401d51154003880003040c04925030001d43c4185105040028034035181d407412600700003050380128440c2c1c00601c10410030791400706511811001760301d40090306030340b2200168000c1c040c040000d4000500e4000714003014425034010005048110100c40100d01440185130340304030f0866000049030091101c00c00c80d089400c0c1080e01c02c041c01000840ca01c80a0b0410740d08446d542d00d548841c3c0d0b0322001c128070b014207500c0d00030f285d80c4446100039032030144800c07000d00c51a1080c40781e044c050180000000c0512109009500c83e9036104a84082c07031356940c004855480520800c2c21145801e029400501c000d000002c80300d05400310309040c10003044a030204a0701040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 276491348 1250 276490098 276490103
    0x50f061323060a2903191403070f11030d0210020702060915030103031d060403022704060c1b17031801020301030f060e0a0323040b0c070515040e04030804 68
    0x84410088485841c144895442640b604000049450180d40340e000c0030342c040004001c14403941020340d00d003503c002c03410004e52090300e04412580c3c00c0c01c3c80c220f02e9103444075141400c00c2c00041482810042030b2220301030010301403c00e00d0751865001d0105600c07030602034584000b692160180f0a10071501e40c028024041c0020200e5050040c10f0300410010f00c60720b08541c0c3d140c0c0c070000042c0201904440e01880c00100d108094591402c800e021a203140301e03e00000e03200301d03030306160b401240441500c010906000398501c0e2166040920b402009000000030a0b00403c0b088002c558480f4001980101d901d5000307441142e0300e030038400e4100d005a0003d40f10900000d0405203800022100340006c500a5100d02004601d021f0700303080c240222414034007209541e41056011101080c0d00028800703000b1600507500406041503200108644610342c07000281d10342c0810301348290034020841d0030842e0b00682e00c95101703080500303000c51140300d10700503041404081404100030a1044440b50b40c0307c0d1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 276492598 1250 276491348 276491393
    0xf080309150a0c20190f06060608150409060f090308010f050102030a080109020d1805060a05010f0b0306130f150f050108071d01020a02090c0d1b05040509060619050403050f0613 78
    0xc00c00120200300b405c0141514004200c4000c10200003040c801c84004007920316016520b4242040e030104814401212a80700300e0f140d49420050242c240d205503103001c0742840420405000b4980601103020911484160318881c40b00010254000b004444001e0b25560340c1081982c03c0021210003900954181c0c0300603543d800d08580c24282e11140711000d0390048005084914001030080241d8805030020110700c21a03010030029001402d040d250001d808560903144c2e80a11041c2d10000c1c030400c40d0302c901c0c00341000c1a6a00408411144605032108101c4002d400e6841c1d50054170f00079416141600068103111540d0540c1c900783d203101000500500c161032042c8029000210607071400c0e16010300017040068006c000700c005200302c0c5118596101850310340c0a64140141c102d005501c1403e00459120000912503a00c5804413413003450109011000d103003d040008110360858013048900f4807403004104a04c4d20b0004010744145514941700031140705983c1c03511280302001c0380514060 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 276493848 1250 276492598 276492613
    0x150a052b02030703140105090a11010302090f1903021806010203040608100f03080d0f090308071b05010608030901022505010c02060d0c020606030c0103050c0d02070f080309150a0c20 80
    0x1a42d082c414100158094000d20308100c240c1c13074a81c2d003140e001501503411075106041c01c10008440e1300344500003150074200142c50703a4401002c41e100d429403800c490b9001548880c2c84220f115401010f50a0728000e41d01908201d040351a1594015001d0310054050703401400304201c514400d20f0300c141c0c000b081109018501d80c1e5038181c86079869075604220b880b401c0216200b60090f0399480b4040121020710418080c80810713032400b4100080c0500000100044c40c0d001182c500b031105200307400958080c0c020042160b031040030580381d8000b4003800f80180540a580030842c042c1d420755100317924140321103070081480c050040d110052a0281281c0003078081c082d60001003203d100d0724007034200e203801a141c1841c0480c1058100340c1008030035030505103400284201602448103440400d0440b08006941d08803c0c10902d04108030040d00a200800c004200070a0700e0700400c1d6601d1404140bc0140101d448a003100000e031807005c49035000140d9204402d8100780540900c1100d01c51202c803d44a00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 276495098 1250 276493848 276493853
    0x311011205040606171c050a050c031305010201151d04061b030507021e060a09030207120807020103150b120703021e0405090906010608040809060f03070305150a052b 73
    0xd0341d80840e01624260703600c00c420002d11200c100038408501e4a00c1c0503025048564542e01d089003c0c0e4415201004000b0030442c07007107401032049840c14182041100e440d4010000c0c9000401428001c0b58019424440315502160031401000b06442904021700003406c12000c0e9144420401041546c005480c0e01c44040302e840e00740f051030490b4005a402041c10300d0700300f070064a081c0b02c59555007036103c0341d0342c0030100b140d101080b11368024049100c00301c0d5402207410100e240c410140c00c882d40e15020300810070304100c8e64800070001603100f80c800748429408900704042403061072083c1c0a0700d0071304215039068048680010350303102c02076050040c1007460315480070408a254014001100c8000982440070f03103090309881c2e07444003898004011541c140394006264081c00340c0010130340d281c0850f1048585d541c0d0800e80d01c3c21504a4140303500c078542484000d018050036540c0400c8400b1682c03900c4580d09012100b90700791a0b02400d000b210039240c00d10316038605010910f400244000c0702c01d1000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 276496348 1250 276495098 276495101
    0x607030c030e0603160809060717090a12050c010f020708042106110403031803211214180105070e01051b07030609020a140a06111e0d0f05030105060403110112 70
    0xaa900c5c801c1e40c142c1040221015010003070181c500d0003103911101c2000200f90740017540d5203416514107010002074a80f44480c0c0e03e0980765445c000c10085807140d22020166200001e4030440c0c00100c020703c442c1d01d10004a034101d02c201440079000600810047c81510b00e94507082c084d401c00240c0000c0081040c0c5c4512045407511200750903a90070004040003495801040041d2032039642020b04102891669a21418040d504044894080480398600c1480c043d0103400d513030b48501c8c1018000303001c1c04012042454421150001940a40d800740360071403c0c1449044e10803469a191002c8924038000151216013100c41420381e5400c21902901d040802401100700540c0300340000b14030140070740304002c21031240c1c0e00046486030070484c02c040ea42c0c0d55501500d040711000e0804508459010b03921a0901000c00d02000b00141c0c482c2d42400ea50304002000e0703035508030b560354081c01504e0790102181c680c8420310541d507210b0740034007040c404180b5501c1c0380d4000302014140002c207802181c91a10 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 276497598 1250 276496348 276496351
    0x27011e021c1d06120f07110d02061e090c09090703140106061b170d0212190e070f051302040812030f010608160309020a080f010e01060b090607030c030e0603 69
    0x1520b42c124200c0302000502500700120350443e2400d0903c081c4241d220780654008225241c03041c1c0060103e580c90740544050804029108240c8100142c0c0c0780c0080c0d82d40b2300544401042c52120340b03d040c0082c6000c00700901407880240500505c510020800000700b0018003421280e008003c0004000741c00e04d140c01d101c0d103400b41d0000c50844e00d0004040d111301c5580c07562a8140c3d0740c0920320720000358024078000f149480000000d81b19840b441d0303510300034007034013540c4845c1c1800901488852548080700c03c2a0f0030610100b804402c0d642d101c46515040d06110300500e00e910340c40184030368580980e480194203940c0b00b0040c10b150b56880d030a4580300d10031850604d410310000600020840000246004d446c00e4201500c403410449480d120305c000b500e00c01c004140e41c50380100115980c07429400010000e401c201c50f20b00c507412165074000d0071000c042021039860885d000038004545010364800c1c0301d000b070640d810906940c500b524038407950202101001a030a00c00b4086a80e80350265 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 276498848 1250 276497598 276497653
    0xa0c0201140d050a06050f01020303070c0606050d0b04050607030e0c010804060207050601060507030324090902040902130b01090909020d02060c12070c090c180b13080d0527011e02 79
    0x41180d00700f0404004c2158002e400c158007825049031a214242d130000204c80d0095014a40307640c1350185824030b80f00601d403e030899030380000454101c4017400f105072450340c083d81c0030b401a685191191a020360848806860082d17072504443e580840540c01680000d03405402241e016103413500356a90541091801d0300007402165000c5601c109159140c0300d030385000c40903c40705504980b1450944507000c20640308080280751280f941c0011511142c01c1210415400380420001c41c140080000180c40032941090020b803000c0c90001d4004094081c4508180e00580108240c08160302030100030791024188104921543c64048040e004210041a400340212200d02c101810a08110160780403e2080300402407601c820100d0641005a6501100e440095681d5a628004542503d813038007036028a40754000d04c074130301a03502d401c1300080c212041130138803a02040c0c59491380105010004003146d07000882c1c1c242901e4580c0420002b10f08142101c1c0121180080300b0388072007082c1240700424 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 276500098 1250 276498848 276498851
    0x6030c1205010e0d030e06010e150402030601050912031c092a030f03020c090f0f06190b030406050603151e070c02030f070603051b0708131a0304031407080a0c0201140d 74
    0xa075211100500c440341c09022400c851000700d02b0048a80c1501d4503651003618801e5500001180c442c2e03005900b142d144030005002842140c4078880f4168485c1c10100006142034072500c20800c2180c4244580341d030040c1e1000003042843d5030304e2130304c9100142d0327440e00d0212503090301e00100c0400c00003255098803501c00d80c000c002d0480745d0307010300c00003075070150060050108280900842e54035038100154045019030b019071400d15944801025803c05130b0081c0e041c40400400d00040c4013458208500c00d507400e808956550803c07008000d034041040705c40e01c402480c0d102c031591100b00803041403500303e4101d00d003850809150f50002800c02041d030300000019804140700300b22564060080e00e0b4803100160710f2444028a60f140000d01707128a800003000c0c0c80c0005600c03103040c1409144640a000c1d501d155170302c511030725880030040794030544041e2301048000d0f030304800b500702280455400982c890750590801d81304c1681510181a0001d0407814008410040021030904502920300344030840320 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 276501348 1250 276500098 276500111
    0x408030313031803020108040f06020d02040b041a1215030106090c0e03060601080c0a03090c090905031206040207020105070b13080c012007081b0f0a0c05090a06030c1205010e0d03 79
    0x107014040340340755502c1d12203039203c214081001d40c2c0c200d44800e900c181c021810008802d42803070b003a0001d00c03c201000c0b800520220f4081003030390464001e00140c4015a19a0a800f20302091010050041d03104680201c0c605800040e1000000700d031080907158040c0010a029803030700b8604054500f43e00950000810ba81030150092404101c1c00381c2280003820580820700348110400d055100b0901c25034103040c0ca40680d8400c000f0f40441030700040004a804111034482c81c130b005900c07a44040c841c005200740020105581c0d280901c200e9444940c16103030b40e407802040759100f01251800501c03200c505c80c80f614400004c64026801401d40c09500c90000451074403c1b0102118400e21556030030314828244040000100d4420840d503044021041c902102000321900750b240c001c008030174403003030b020350041c200401c8a80c00041c8180c035002c0780c120003240d503001181c904541841c4006020594021000c1099035040a0a03000c4035020302d002041c20600900c1e03080c5400c0e20003800400003035983c1c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 276502598 1250 276501348 276501353
    0x102121303020f01021c290418061d060c0901020c120f1b03100e280c0306090303050a0b01020d05090102070509090601030201080c03040f120512151201110d0506060408030313 77
    0x2141c015088a4008555044448403950050200b00b0721101070269549d600b03020441301142465100c01540a1011700009224041c0301030a1805c6074a0b54660340b01da2004105140c1009054402d00501a402002020000300400c0914020360302400c480d070140c0325065603402020311041c604d0303901d44280421002d815a05143c50454140c001412084c5418102c01c144400818001c0403a03585842c00310301248010020780140000041c001c01c5860440300003c208081c503005803203c103009840400060781c4080754041502d0a24030750328016000400450b58060040d000741514402c184101e885550302c03900400c4040d0b506841c039039050750246d0700400071580c0c0080a03030361100117a05810b00b9401c165607402010101004000e0103039056882c070742500e034414801c0c3c580b640d41e4101c42c10000d08000402c21080f803070554807103000d180c15010000c0242c0301400b5001e05461200038003450030f0118070210f0010301015005d80e0740150208800100714100300003841c00340301144501c030114041d51 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 276503848 1250 276502598 276502601
    0x16090b18030c01020a080f0d15090e070e011d07090b0403060e0610030215090f09041202010c0f090e0604060803070506070e1801060804060906020a020c0109080102121303020f01021c 80
    0x80354494110750050b0315800004005070140c0701f48030003407080251100501c031380441c01b40291796103030b80410400704000156030005800c6219601c45210550300120707221012500300903004d00136400300074941c415903070502c610b060740c15611000c1031804101c03060b22910380400e03580c0668802c2d998681c0700c00c600c484440c418800309400c581c00308822005145550701140200300b5400658a61a801044c0b0484503180c550403084071701d0000f13080d0000e900c0c00d4542005a46500610400158600b85c038055a0034040c4403410080030064981401c01440c3c00344c41402484c008141e5508141c070352a0004070040100042e054903441070001d07202916056074001c02ca581d41d050842c1c410f42c6010340c500001d05410754600c2c103480c1030b882c04102d03a0f03075035003040c034064102e59000038100c1e840020307040728980d4042107074441d9407000d0382c0d00802c0315517412000d402e03030190500c044c0381080d401d070100d0b2040c61030b1142852450b01c07a0041e40c10388212448005d08907006040c4841d900009590b03000100700e0769 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 276505098 1250 276503848 276503863
    0x3011e230312090a0512030d050a09060e0615062a070e0c0405060f0d1508031b01090b0609060d0c030602090906010201020a080420090a0902030d050c0616090b1803 72
    0x600300607030304010200c00018414080c0e81700b0a4050600900040381d0743d401401100c0e01a8071149003448035003000755140340140300800c4281d550503d03041440d5003801002c5a003030302a501c2101c1c0e00b0b40d000700400c20843e5603880340300b10b0210104207143c1c2846d0802032480080508000c0400790190615241ca81040c51000910034081000c0801061015503501e20545001c0f035034810070540c444e6840c000e07040050007103a0001c0c3c5804140ca074001450440000100f80760700d801130782299042401042d65098941c0510b004041d145008006041420030740c1040e0b500c800002d05034448040552034800c2d9a60301500242c1d101d80d000615080fa504020842d190401d0007031008514115800c1c0e802030004501500040010008060320b41c4c070482278600b038035036001005080c10b8450500c0e8104100510030310004074024010400c03061a1140a013050f01d190036002409802d203507464060115084800099110921202103c0455890001c00103040141030030203034442c0719045a8200340c6000c0030b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 276506348 1250 276505098 276505123
    0x2040510030327050301021c0c05040f051212030c0403060c0c080307030b0604080d0504050406120503040312031506030b0117091f32130803011e2303 66
    0x103140003040080e40c0529525043c0b48032445000c0c402c082c0020000c403200b03580e40455455030000c68000116800c000b8402c0250300340800410546c50303070050940c2c0da809140305164868171031403420841d50918a07920381558003400c0607078141d2406001c410750f407a0010785a500300c3d00c201003014010402c1d1881010701360022810015022101d0ba500c0301014440100071100705519404001c8050700c840d810b84001e002050291488200b141034001d2080d0014816188144d042280004d09101542201d4101300d400c035000e5468203003035844015040e50b649442d0702c201940ca803810f149200300c170010711020302040c0d82c1c0441c0501c101d9000401186505a080800d41e10400c14495810030002c0c00b14191a1103905c1615030a1406001d8401404041c122600512003002d035002015404002c0103905c05850b8821000d46d01c0d40d10889a000c80b40c0700d40102810f10410040c0017201c4205113a2900c0c11500b400d06610f50786035241510039460000140c00380401300f0340f1075481031900b03100e003030104c0c403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 276507598 1250 276506348 276506371
    0xa060908030a060b1602100c05030c1510050f0913060204030b0609180601150207051302040807171218040c030c02010e0c0a26031306030c0c03020d2001050103050604020405 76
    0x1121017440e205140c10700300001e100d81e10301d6529000ca50f015100302e180d07081c0c01000342c0ba100e49003194115282d0000c5407411209986c07800000b4038003121085100165a4007801c601c40d032034101c0c010300c42c0040c400b400480c0c03c90402100f1800080680c00104081d510500c001d401600f045801d0148014024110100e01164420984113403540000d03d1411039407401c03502c1080c5040b20b9020381c01d00140d0b400c0705410a031058405d011202c1c0603001042140c44d5a01102c1c503003903403207500d06034140342440e24483c0d0b5003080b00560a01d903911b002a040030120007400341c0d00d120501c0000b03012503a0b615900004207803600f0714188610340a11480c0c002201220103011010f80010000d0440030803070103410080c0704410305031001d40d400e400d00a105a01c104040b242e0382d00605404c400a0350b4607201e03010000381040e0407805005c0c0316010038030419a054006141c2c060180500344c0b040c0e101e0510082e5150314000d000c4041e05001d0043c1802180140060140c508050041c041502c80040688100300c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 276508848 1250 276507598 276507607
    0xe01030509030a08061e13090c080d120f0b040903110c01090305060417070b240a0b03070f140f0304060509120403060203071806050d051012140a060908030a060b 71
    0x202d4001d002c071035001100b00c668581406140501e86c40c3c0d040f0a5a0050b007040c03164142c0b41d10b01c100c1303620501c810390003080d040c0800f90b561100f141c8d0b40c10b40000d8450004200013043c4010700e0040c0c01010b82c0759040d600110b2100d960308086001c6038007941080c6c00140d80c1d042c3d21b10140c40184410a0010707006e107450640b00d0b085450b165130b25007000c0d10003070822424034054030348462080140c0f41565800300ca804240d05040e48801140740c02e060281141148401d620002ea2400e40207110854090820f114110b6940d5003003681d5820102c1107000500c0007070401b2412640c4044010060b2400d410083c03500da080030f0605c082180d0004107921030300e601c9500000c00381000d24081d1401c503640402d001d030744c80e510348c5c0c000c464540051000b02c140003110742000c228035401801410610308081d00070040c641d5256804400f0030081c2c480c600c0700515a403a01c1d40880c102d800f1303110003503111000300c520004d12a6500300865407203120a66101c907020080c00207092003800707410028014a0000e6003072 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 276510098 1250 276508848 276508867
    0x12040c0b2808070f0c0c050d1a060102010c080412090b0c010614040209091303090503010204060903151b0e061c1b0806030304050618030a05100b0102070f090e15070e0103050903 78
    0x210f08202c0380a07045c0100d4035019020400200e9106010b03000241c0340310f080580c5440e0000d000c4c452608601c1e084080c0c900011000d501c148580c5900240580c0ca00b01961100e4850050302d0105010410130000141c50101c0d214546800818004c41400c3c000950180740100b002521a0010b4090b84100d004002c01c00c0140e80315034115410820000c504080c0000d146016200501d140e40020740550003c60005462500101e82d4030450b80504a1401c0c2c0d417115898010803102c41c921001c180d0104084a07807440b0388140720025a814000c0e00d010300d0421510100070804407407050540780d051b1135050b94003022900045425006986003851915410883c0c0000e80700c0c0514040d6038044d44000c91005100381c580c0d420801d0018000c1c0a544d84c1034514100340361074154800c040d01142e41026800b1609510003e00c080860f9900e500d4899500d0130080300d0300140c0301c40d0509070518842c00c60750308803a01e81c15a1807401100c05403a503a041400141c009010f54070300801900c0c3e030b80c009004d01045c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 276511348 1250 276510098 276510107
    0x5030703210c020a11060c10020f0d0207060c09060f051804061206090c1a0304060203090705030607020d090b0405030a030c06180b06030f070501020312040c0b280807 73
    0x54455241c2880050010103a10032407055022541c200001814003001841c0300e40c0100701e480216001d60049400c0c2c0c2903034418800c65100d102034028050340902c400c4a00b13004030341e0285c2481080103203030a107840345070000442641c1040174203030781550ba02c01018a460790408040c10050006061140744071001000190503070060120b0ba07208403a0800540e80c2d540e66030351181020740000c05820f040508181031180041a8580c003c0b03da180081002141141d02d02007042c03020404a000640f642d51f9130b0303079400003941018120130654403c014000c00c1ca65010300c0301622490342a8024404d10500c044000d0150445038041030750050100300500c840c0e02c0119407010b2003601428680725404c8a454084004d09852a248400ca0124042d100c2003107130380811180609812421030322061001443c03a511010349216990140e4000c00c003030180c000703a40110755131103801100c2e46802d599591100d1449a849010109108031100031064006910f20710b0310600011180307411440307458800e5010b007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 276512598 1250 276511348 276511357
    0x60f120114010c140a0b010311030705040218010324060f0305060105070c05090916080115050a0806060111010e10091401060b0a120209060f0714010c0503180f0a0804210503 76
    0x80c00b00e08004d5296048060400640c401139500c050201d580d583d41e41403205d003196071070645a2181c040c071a40050302c0c0c035050003a91601001401e003800d884800d040150002e01d440320100c00381e440c00281e050602046e0600000083c071054a650f0003030502d0800060403100010310300c80c10310030217002400200f000d41d003014050300c80585c0d04d19865100c40350558981144414094071038080290003090080064110b02807882d0102c07503a071882600c8a042003903a03000e034041c4040c150b001000094880d0310461205a4590070702e40009980c851100d10716050100c0c080361614800d44680025042049219520340c0b45600540200b00543c2001c83d9500c0c41d1003140040c504005424062182881d0640d048a0301e000c03000300015507600041402035003940020400356143c043c01407000714484418000c4207056038551740c0d1980b8654480900f03803420301411035440050b104050400d4201c3c01c0420030440c41501614056840303501d08600420907143c0c1c00d01910b0005907084d2000d001400010036907 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 276513848 1250 276512598 276512603
    0x902070b070314150105070b090f0f0109112404030b06090f160e040f0e0705010807020d0807050a030f050a06080f010608100507031b0507050d0c081803010b060f120114010c 76
    0x44a59043c0078004846c5e41c01101000341c8041d01800030300c8000e00001603030f00702e4481c20030143d55032200f0300c4120314200d0b8040c03200601601500c1c03100955a18107400c101c59902402080031154001010554540340c1007074108a070503a20480511071189000c0c1e20352036014801401c01c41d0700f0315015040a01940c50000c40105100f0f03118141d0003655926005408440d00011007000180803a110050380e03143e541c442d140c0803503002000714030ac0d18404a0400e807000301b141c40d010708648804900b1141a8030048001c3d040607a03901d64000919518025680034500c290b8010800c0f50038180064141410103070282250780c984101004101c0d808100000103003280d010000c0c039030340e401005902400900380c1c806d107040c1d80380c101c3c2c880c039603004000b034010f09008104840780b80c4c0c0c29050a60fa06540d0a01c09080b030034003803014908166141a480c10103140140c004034244841802142c40741d080038100d000041c0000c03a488440a9000003001e00405101950b80c4000883c0000680b1690411401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 276515098 1250 276513848 276513871
    0x4151401081911030417070308150d0b07020a120201021318060801020703020d0905090f0103080c071715060406031e0f0f0303020301081c0206071b0503040902070b070314 75
    0x142c1900801c940c2c41c1900c00c0c07a080144425a0000284150341d8421a41101c941d500c65550f450003400b054181c9003039a03410349411000d07445120310402e030104905c40392648000300740080c1c2e00140810401c680104101d40051030300310f5040c032313006a20201043c5102e0071a03106100c18048000031100b201d0884602131500b82171312400400b1000076210319003054102c2c1d0300000d480403c0580c00901e50002c0100e03a0b81d08081207403503c041041c0c0810942d2849402d0340c0b4040148003050a032001820581d102c4c0b400c64008964503481481c070400300b80103191407608519403240103180401d11643e8881c908440400000d030841e543c0040c03e554850f18141c1c2a01041d00b2802000060a0400c1c1a150480c0100c01d031103c0e1441c00501951013402040c6190107100624030708441400f841040384d1070300d500a08400c2e502c0d404203c450b81c10541d59807060b0020f201021000c26030900003440644a030f0300015036200481c4c20030800d04040500b449003054030381160030b4910b0480080b142c0c0c120065488 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 276516348 1250 276515098 276515101
    0x409050601050f120303040503040303120c020a0605150901150f11030d0908041d16020f0c0f2101020a0e010503040c03030c02060706050f0402040501050316030b07020307120e0415140108 82
    0x1103141103c0c0c8800d40e2184e0300c4008144001d02200001501c00c9a102e83d0310030109003090a0a0021758903086c410f6805a8408481e2000040c40f540003d5880210704203401c052801c0c001c001110030000ba4000c580f05980d482c800c1100591000c100c080c440f0642c100a100007880c480015681d10407400d0742088155505a140c3c00c020100044400900c8c0030500c07010300184144840c0f10b10441658000180c905060a0b90821800030842400110741e0070040c2006200413024000001e0061042079444103c00001d1007002e260344180c04001690f00c400183c07125000e00015020b0152458560f05001080c0200400175500041184c21341e42d2600d0416040d020324400314a050044041c0204802c4c1042c08020340c0e00218880760b13201d28000c440500059a840081c1615003203240502410403c10b88020f001090300c003800c490b04100e00f841124508402c0e0707200c0e00100518045004001005000b4103200383c5442c0c00396440401d80c18000050441c9400890045030885508440c1031140040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 276517598 1250 276516348 276516379
    0x20916020f060c030703141521010c201c0f0e04020309150c2502061605060f090606060418060302101106010f05060304240f09020906040905060105 65
    0x32031001c424030901141c01c40e00b401549040c868004641084c002487c045190780350030702418440f40201c044c081d201d032845116205009035101100c4031903000310041014001000d00034803441100050a035142010455007150030a909030b00108800b0719036100721540c82500c1c6030b070440381075012124103110b0380700c0c10200c0d001e4408202da02001d96110348040100308003c0300c0030448082d44403800d840460203940320000c044042c090040c8804000240094010300d160009003182c2a0038002000c50742080d00e100b62504c4580d0724000d04449540003075041c0004401505481030300110000c0103800103103416004601c02e400340d44208400c03014100d031303642040605036011001464014107492084004100081c1000e42c01003020b00043c402d000002802595a01e03410050f13440080145186840344d0721001c012180206200c20416a040382e002d92880d524071428014005003000890304070b03020300400c54002d13801004107000301e041200c207200054001c034000c2c0c10b41f81d04a0340c8118010300074 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 276518848 1250 276517598 276517603
    0x3020a02031606030c02060c0406110f0105040609021005041202010e21061603020705030f090118080d0f030506090a05070504030606030b060a0f03030504260105070305190902091602 80
    0x86000c0d42600a12079200c010300040e500040c00d864464400f440000600403040740e482d00212084035400c0c42c14042804007911078882105451800301c1116881c5080b40641400c464040d241201c0c0c1c540d07900d01c3c0204500b0000c1b0810796105a03410050304291030b095440001c0500540000d04102040288200c9a41c416240c0d416005031052000407105c5504001030341c0380c80c241e03800c00d18801c841c030b0128603d070700c030b80225070034a82d200002d14180714214810310215040110f50714148490204c04d1035a03050100c0b0000c00401d43c28004140640e690310002c4c010301c541030301c58810141040c0810501d51580317050950003c110b024000f481e90b85103407044425002c2d681000b0441400e0810010a104025a0440c0114411106112881c1e45c80d0143c100b81d0065203c001d010600500040201049041000d017250405601946030600003080c84c508690302102c103640865079600502080101c3d0710b428000b488910755041140446030b80004044840c0100761800c005003940c181f05150380309 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 276520098 1250 276518848 276518863
    0xa08030409050c162a03020607201f030f2f040b1803060106050327070f0909051203010b040506030a150f080610030b070507060b06041206050105090601090b070302 72
    0x1130a589a45100359203846010403560580c035820b000304901361120449841d215007021a81c1c010141807424800350750b0301000500700c0060402d280b2400f40c400f0340c16200d10320b0b0f11a2541d035000c28a02d4015154070041d00b00c80e1002002142a440c0200782d808402d207107c411904a80702e6000001300081400307000721103204035001401040740c0130405c1107801d0028001e0094107d8102c064403403507030f203c00c003c50320340c0401c4803082c1d00100e4070000403d08c10580b25402c40c06000c000151050a5141d12180e030a24072140e0029120342d42c0d483d092024440207200540301d042c900c00b40c013481c40d4508598415076004500a881c820100080441c40c80c90b050380c081c80741840c03250744e8551034966410004404d21060321070107a9501801000450002441d001801566400361038008542c4442d42c2c02c482c2034025500460f04103607a480d80c0402565058080d20041c0fa22811a200d118683c1c135086043d0b9038183e001900982c102c40a205d41603070812101c1003550712101c0c0f0305440b20304905040345807459 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 276521348 1250 276520098 276520117
    0x16030c1413081015080a050303040b1b04031a0a0b010e06220b09010f030b01050d091406010f1401020307020310050c0d151a090d02100309060203240a08030409050c 72
    0x151407a0f2a60303104058211007201220aa5449005943c0340c24050315401203031780007041307074104100040c00503144811321030304505040c90800a6035041c40704000b06501682007510045100c1408502402064043c5a071140c14054280001000c150000c0c0c55020048616481014085003a012400c6130701c08400401044a100342800c83c2c2c0e801c1040c078283d11021002d07001802d00c07d0717005250b07400b81c003a030f9100010603581c0518040c0b04185e00c0d0000c0107050001c4408098540305103c070310004028640c060301070035801c613420602c0e107901c822200407801c02180c1950414040c50015079004103c04c0020416078802003990341d94800005100e211741142c44501c00d145c0303041078070302c051000c581d0350590340ea55220040d8261701d0003203240e090140c25020303a03001c08507030b060327400500f0035003000350000030a03080c0801e480e06c0f243d49030810382e00111407149881c030344910610701c00c2040c8004070100d000b0903100b4a20b468100801c45840b0700c19800341c82e8500da160f202141099500c01c045800703014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 276522598 1250 276521348 276521353
    0xb0702010b0402161b030b040f03090b070b0907050a0b0d0c110703080307030b1206060d061b030911010906140c0715030c080604060503030a1808060f16030c141308 72
    0x380407070140c14013040044015074590610591950140c0200c0c5840e10580341c020107410f00d1551584e907120307201084840f084040143d00d1800052080090010f000007511074500a001460042103036440c14855030302c101c1c490b036110401004541043d9007190411a52050089084000f280f010344412400d014059198481d006000041c08001e8010354040e100303560b010300c50442c0350010400002d40d6050724280c2c0d40c10920120b821031034040d10102c1014454200070400140c03c0080b000381c05040501c01d40400c1e00e8004841c2040351302c0e805a68060f00908012101d00d003481002046008050100d42208400050b00300c3e440c03d0800c0302c1c100801e20207a00c01121038041e040200503080e4a500040807401c00008203200c2c2c5068000c02c015608040e00442c2044450b000440b00070282c46011103050321814000b06008000780306a0780b042d244031501d400c19003800070505100106512410701014a0318444812403a44030050b08035140102d441a038407030001d24250542040039a0040b0303601e1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 276523848 1250 276522598 276522607
    0x10239030301060c0c080a0317040302120c0f060109021317030d020a0e0f01030b01120b0d0212070e0f0f04030507080d1b0f0507080d020310080d0503042307030b0702010b0402 77
    0x3940d12282400ba5117114200521641d07542e101e0155a42030128030003004a80c203004038090852201544950185c082c1c030440e1100d0400c0540880654403009811040c1d40001041c245a181d003040344500412009500f18540310404103040c6580c905400390945100580c9082c101c03041041060b2809400032200440d66141c40ca8005042c1482d8044950f024800401c51100030b98080e2050750b10000d4180c40e07200c0341103040301c0e0300ca0003040c9500e02c00d503210600c0110b00003d61034148480c0040283e2800500070a820481512907195005103c150b5846000c020050601c4140b410103801590509080703459603040e00d8044202e001d2140554030440c908001806c0d5140320302462400c030003040e101c02c88078880c0c4810441d0386103d141006080510100300c00c00039101d8030f500640d0301001c1b0440c080304482d03c500e012801c082c00102281c1c005100481030105000308054801c940600e0150440f08014a1402254503050380b0301c00501011a03c80000c1e04203030003034201c44107030329008000b150354 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 276525098 1250 276523848 276523859
    0x12030f0301050a0b120106050a120608010509160312050315030a0b04150204030308010e0a06080f03090a05121504110a24030b030a080a020309090103080d0e010239030301 75
    0x194000b44030345031082661400008103800c01c2c84c02c540400d407803d0b110b011a6800d02100780c800c0e501075050039040000080c0d0f550007008141c403580300070705640800820541010603145103031582951a14001901941e0200002051520100303070600301c0b400c219480c0e6440301001c28031810040740d055014011042400200040898030500c00c9104404030100441c2c0076080300c00701d0056000080124086500501c0803614103031181d6070040200b00d0100b0040e880e224914100801000002501d40c0040f910002d14a0042500d202900c0190b0382c00480412501c1c409a65662a0700500d00754071036400030a042c420400180840c00c00c1c00350090200c103271342e55600320a24064486103048000c0385c070300050403c0e100b0700900180d41402001824615442d032118580c80d4080300103141548402c1115041d01d84074084c20a0085004440c903d40340d080c272907030b00400e540d001d006510a46c0d01c10803560b100c0c1c2801c074540100501c4101d081e0104031048a030000d0500001c546400050321021000092 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 276526348 1250 276525098 276525127
    0x703081e0405100e0c0d060e0a080a021006080102071106070201090b1305030c0301231305010c030b1c022112120403020f010c080c030a1b020c031b15091203 69
    0x3c1803010600304840c2e0584911283c8400d400d426080d070080400c1c600f0804600b0542240c000011180140c1c0d072111403a964404095101266602c0541c00280302c03000d5080040c4210002801444021741c54107415548410310f140f01c40100c00c0c0725010100d032101c03c5d03911803642d4401a181c025521a5a800c188900b981040990300c6106e1080c442c11249035040c0c241802000e480800100d01e01c4484400c00741c0b4007042000060504c81c1c109080344402c00460424083e010f5641202e4500085218000b001e0001c1000c0c8442818000c011224408006840c2d2001d4900f401041d80611005120040f08250030907a420000070a03412000c2080c002a502c08030740c4502852294088404030250780390050b090b24003600f5000046445040011b43c5960040000d5501084060740002c3c00380b0051104c822a5244015510059004003204543da04041044044010701340d031022541002c00b500040801c075842e4540072504001003404801034840c204000810002c602c00c1d00e80324030070548801c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 276527598 1250 276526348 276526363
    0x9060b040b041a0f03030f120f092e060e09010501090e0604081206010302090d030f1d0306040615030503040e04061a0f010e010e06130e010501030608030703081e0405 73
    0xd110360718091035016186828401c03a18948190b55801a199588008000032480030a83c6141c02d800b007004a0102c41d00d0680040650104e20a0101c8590a005400140110b0018040450341e8049e1031218105946069410f43e00013120f03a880f09104103400e0900050b000e030303601601c180403290007403265010b4103410031410388803808801c0003682e00c039100081d42c03840280c40107040c1900c2000448034003807040101690060041c14007500d40140000071a03005c008600741500051301c40f50110750159800025000c10704943d8080341820400c400c00262130745005003008200c550342d680380710b9800418481c554019078000d401c0d43d494668845001070640c0c03084500b21941490441b1803041030440e4621000803000203000c04512131207820054908000400300f1138107021014a00e0f60b503680c4c030b20006008031012070130000c0c09030380307810700c4682c4900c41a0426030605080000a01c01c7c158004251220740d03402d03107840302d0360b9110005044441d15103550740c00c00c0d040c01c04003000280400042c024 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 276528848 1250 276527598 276527621
    0x30f02071505072f061e010e070509121b012604050106080303011815231201050705070c05030705010c0807031b080a020c0102010b060316141305030f0a081902010f0906 74
    0x131445035564005546c2e45001095100f00361385940401071016403010703040300317910901c14200a03281904000000e0109850390036101c4096000b42080503410785807012100a9003003e00b0041e4040c012001e192110402c0c3e4172001e84007218400001d401c1c4242500002c0041c403828081e241e880d61202100c0c2c4c032124180481040b0681004180e030b41c070840c840f02a004030b402d00c0b0142c0712100000d0101422000030003448a600554010f17814681075002c3c4600c0b80070b403580d034036900c0c2d644a09290031954244d050380b00c58825001200700300401d907007040e8080700e02a0701c02c19240c1e69812901e420345028403070108003040c0602000040701005008001000603a07084d400b100c4602030948012800e907115076280c1da42019040c030120f03280c1031082c101c1c54220b183c42c2c141001c941072042d0100165070096612010a01e03ea28070820035801c0601c2180e40c02c19000000d003415020075190f4048512544c04040d10040e20707020703c14103480c401e40c4070381c00304019402c040c482120641424000b412107221003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 276530098 1250 276528848 276528853
    0x13030b0f0702070f12080d15090b0a1a0a0c06060e06010801140a031202120f0403060b0d030503070c020d0b0403020601060311041409041703010801050403030f02071505072f 76
    0x401e61050001070b211080790301980100c10081d0400507074404240592204845031101801900d001c0e084900440d241900c5034018907030b000345007008460684011610881c0542c54940d018052201035000800d20304410343c009983d40c0304090f80c2104c6980446401a09491605001003442e40c0040d0915015034401da031408a5030744c841c1786c9110801c00031000e05911031885201000002d40401d80e07403250045034015141c28400c503041812980e0f20105211900c2900000d080c0704100305445400c603021403e070b5100044268a81d8040c100b40710203000351062040ca41c07060700455960000f03030f0703400a9000e01520080d0070607160103581d40340c0a0141e070001c41d04066040c0489403080c4190342c00c03680a07524405c204001c410038404814400307001640d02805092805e50764202010045000704252000020745240c40c1c10b0080485070a1200388007900d00400c25080400c10601f01d08036003e1000100107507548a01c4004d0310b16056121480002c1c2c459a41034805259600229842c48000d9200303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 276531348 1250 276530098 276530101
    0xc0b0c0601090f0209031b04020c030414040e070302030601060e04061703070308150f1201020f070c0312050f09120109120c062003040b0a02071b0302040b0d020a091113030b0f 77
    0x32641c069014172200603806501c1a0382c102500d821a1020b07080010001c2d01c01407500801d02c81803400c5900a0300b0940c02d10500092402c0c29041c01c0c881c41118508001c00f506165045034002501d50906104000421042441002036503039140c0c0560020400e003811044d0012442240c00c1c5c481e00700c01800d402069102c00000c1a0788087c0007885500c500c01030008858a44540400040c0150700300440855076003401101e40482031500108005400345441c10342c403034a9854088104c083c1e00081c10308003c420302107182000030613415101044401c50b0a008540310500302d8600400002e50023815103e524400ba906d400d40200d81d00b04014000e6005222114051031340b00d140140c00b50201c0017804c0104000340c04100418040c039004249040e000d440c008464450010280312200c041040350203500e030400840c0703003c2c40b9081e4190015030b229170b25030456800041e15900c1e01e10800c030035545c54203a0100004503141c1100c00441c410b0626010003600d9040510341c0910890b0001e000c001c0000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 276532598 1250 276531348 276531371
    0xe0108061203041a0c010504030203040f060207062001020c0601030b1006171f0e07021524010e0a0e090c0f22150302040f0b0a0b04030302070b03040c0b0c060109 71
    0x841c1c0320500300465004500e064902181500300c40e214480f226682d950910040340041820302826010300d0291303000710389172802c01c191214000705560003c0150b40c401141040899044881031092212160183d520821440c21550180c0f05440b5280d005010f108000f01c2081511240c20740210700c46403510282a813990802e95040340ca02e091003010860321070000e00412040040b060f05500c1d83c02410741000e41e6005509426541552020007503085049254a00045c0c00d400c9940240720713400b180c028403484454400e40200500106040010b42d80c03074007080742c50f55074144000749002600d280032481c04102242d111810300c68080c1c85060b0f103805450342c03031400000c1c089140503a8556104140000c2510784004c02d02c0c1d00e44614482040d08000026a89a2180c1610041c0c225008540f44807110300f0003200b0909900103c407002c005000c1031001c607500007000800e41c1d0604000783e980b52031341d060448102c80c140c0c0c400d070141c080010f1403007a484400708103503040310042c40c003e204d2016001f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 276533848 1250 276532598 276532609
    0xc0b070816020a03361512050408090d110a08030d1109090f0604110703020a0218010b1804020904180b0105010c0b0a0c11010e0d111c26070e010806 65
    0x340c40900010000b2030205c40002d6650113000b4002d2522914909950394016402c505994680c42483d0b8556801d10705240203400c6164003445102e9010100a54a0700d50344950003401400205e500a0703640240d00b80401c01d1a12112031201c1c40144400c0d01a641c0b4980241d9a41c4940106159079003070501515440c0c07600703002d5a442078001130032031125640c0d104000701076210041c50345911546070501d140b0037480f00002420441e0182d409410010158010b02c10b40c0108640c142c0303030f540c0c005030041001100c00d030203464100c4142651240c5075540c4c0e8000802a0185120456007d4500a5680c034185030009403042954840d130070321b9400760b981d2001900c2d81d036188400505900c1080002a401c201c050b400340001240c2c0d8200341c080c2007005a060b601b141c0c480b00c4001000d1b84401801c0d01c065400044421401c0c0b1210000d0800308aa0703800e99050326000543d640902032400c0b004030300343d1040301904201320550f0258050710710b4441d02c014600490301c5c92050101c2d40780d001007041c07403c01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 276535098 1250 276533848 276533863
    0x61514030105030d110109022706030c030c04090501092a08071206091a0a02030a0609090816050304081c030507111c0302070503070c050111070e010b07030c0b07081602 74
    0x7405821611500f44c070584001240c4056090103551310f80f00100181d44403a0f0002c0030040c00c0b1040040c200d422401000d9003200585414403903809403034282e05554001511640302c02090703401013100c1c20545041405040e1807030004204503200c612440141c248040c6a0788850800d600443c0920f580c0d0703102e141c80c3c024030f009010b0601a840ba1810208400e5000400707920310885142c072200340000781c08440350100307450f800c041980010a00211813070368043c072030103080c0e214001c0018440c6541da50450b807040c00c0381c10141c1e126258410080c0300090003614018001401980e90a560348400c0ea0b10300c0824101d4040840c1ca48808140c0c502d100d14000342869038224000c01c100c501d0b40c07903107040b405e240703410034001c05408001c0000000d605001500e0b4092065108402c9141084005480e0003520b8805c407009a00c16902080401c920b0301c0b0540c112031003d00441c0e5250b203d803c00f01e40c400001a0060140083c06d420b1203034280d440454035105003220b594070030f001c81c090070040362101c00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 276536348 1250 276535098 276535109
    0x120109060c08093d06090c0f0903120c1e05070e33061308010c0e0306070503040602070f11120d0f1b050106030510063c090615140301 59
    0x400d18680038101141d4074002c0f00e08010b8080c1c00d031984000692800c1607507240c1303000c0d0751903220441005070701001e00607400350303041034204203140510a64004013052040d00c006001b180e030102d20020205d0180c92400380054101252000555845524403542003c00c18211038512543e980081d417400c03d2192180202d070b00c500000c10313006180d0081540030101c041c644507020b00c10494060290b80d030100521036a02c00d407944820f014138000035942151402e801030030a00025400c44400d0f0355001c00c409131320402c0d906015031030b5180e41c1040ca0090051000007851090000b440302e040c407040c0d0520401c5d05404465507480c0c0000f01e941c003501d030183ca031031352400b0a030385040700c0d03007803500610100e01d002d14000b08000c0c00034420344070341f400d664281e48182c81980082007021120080c90280700b02600c0d44000c0e101a100301502c0003952248601000c03856240c080002a07140855900b40000402c10480184101501c8280e9601e03007450300300001c00800d520700b00480408400c2020f030fa04888 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 276537598 1250 276536348 276536353
    0x140709110a0c030201320108010203060109050d030513090902091602030a1d060403140601061107050405041506080309040b09130b0405030c0f07061710050618120109060c0809 77
    0x426001d0564031401d4880c0110255503d071120725a1112544a00304104510020281c0d185051800c500c0a502410781001a00c1d90040040114698010304000226034080d66120208811400d0890b40c80c0100000e565895961034000600d2a09a4014411950084541358040d440b49008a005075607900c90390401350300306002100081d070284c601c2000c0c08071103003000c01b180e1f8401e01c0042c0c1e090b03002d40c00841d01040501401c8030039601c1041030a024050608080c01c1440101707211030341e42c00191140c948901c0c3c0b9840021704024284802c00e10410041d6001e0001d59164043e554a982281c0c103e41d02651400c0c0c99038245107441e61240c3d001e015440910348500c1c0c8591205404084024001e4a081c0b004000103400c0c00c0040180020340c21004003d01007032814030900403e00c40c407400301c079102500f007807060008000011844c3ca080b40e80031500a51750310039031104a40304260610030340d64042d40601030a514240190840180a84205030422880111010644280d41d06031946042ca9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 276538848 1250 276537598 276537607
    0x312040213090b1009150614030a060816030b060d1a0a09050303010f060f11061f090f1e0e07150203040e1810110d150b030414070911 59
    0x509006844401d8210300000200d404900e5841e07036003d02c0d1007500c2003c2810007066040190345100c2c07003810035507010010b5089074517140c007000a014011611591040201c0000030a010a0705c81e44030000070034030302c4156020103865540c50300c0c0000c0030744001e0380c0001c440c000041482c50044a8440384030360140b55961007003001c072902401000c0042000c24415500c44510011500c20005503000700032203100c3d03810103030920700c005003441c201c209000f09102862410f03803d202404604d0b240d00c40428010340d440d0400c40f0343c0c15643d01c0b0702640000789032850252142c82c00346240e0001c0407201c0340f2401018282c203c1041003800c803100e84003008000c5d00125424031044c2c00320116882e080342d4900c122800d0985482c40c405074000251000e145840702007090580461060007045036021180004125501c0300c1402e1103001e00c1084a04010a0758610140302441c0e803c01010015100c02908139899140616183c80480380c0d400494105118451001a240600340a25110003800384402407c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 276540098 1250 276538848 276538853
    0x2040617091e0307050f0102031504051504020406020f06060a030b040206030a060b03070f0e0109060e012d0503060307140307050f03010b030f01051e0411010c0c0801020c0d0908031204 81
    0x304100609592100e000b40c50351880c14145000c006021080d150014540d980214500280751031004001084503034011310030000021441012000041c0081c0d40110741aa15000601101c002110940d90301a1001c140403d61f40d0340051074070751280402003121034a0721403070f0400c4100d1400e0300c00103150000c0340c80090014100030028640140b0424408140c0305d480398500c00382074108548605c0040c80c020f1105a2055000c01c0000186100b82045002a07040c1200102840742c4031b5015410300034106980c950b444901c4042900c504200e594407003440d080240c008055900075600e140c0700f449001c4020950403c1d9001e0515a00e900500400b0454a04414041c80302048424a90316542c1c0d81d50075200303528103012004c3d18021450001900340391040118085515101e41200745401c107004020008a42e183c80794070784882401d0010f4503080600e42022071062513080384000e9400466505d100c0d1000181001003603040c0d031550004ae80e02c40d2809552809000f01400048103080c012902 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 276541348 1250 276540098 276540137
    0xc0610051005121501050714010f110c120309031b0604030206091203060f0402070515040215090105040e0405071703030601090b091c020f100c060e07050105120a180302030a1101020406 81
    0x9000e0103050203802c0080c107445238451021040c00e0188941d44540c150900b4040c107200e259003420006101e00e040400c0181c0195548034000d03a0b1004801c03000001c40d41c1c0150401c291070303045005031489515641b003c841c00c1d440e403205a500320058803500001c15683c010108980f60f140060101d564190398500c8200000d0320303180414150065420410140403840a104001c19205040f8004205081c20f1042c0402c1074044070005070810b1080c02050503eaa009080318106c07a014841c40c0d940c1e890314140740342070010f158021a02014000c0510044003408000303103205040036296168800e82d01c031f92809040c49822401d541c088642090951025419403600c1811800076003030840000b180000f08500b110340310002c0f004540071082c072a00f081941d01a002d014200040500042c1d403520700080d2290181c0c4810035140e0502c0d00004e80c440c0c0190303010314010120007951541c9120f6601300691a60b00c100488030001e083d031000070300381820500841d0111b6410359111281c0e0048138403900c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 276542598 1250 276541348 276541381
    0x204260303131e06150b040803090415080a0b0411010305070e0d0f0804180b0a1d090a0602070b0601030c0f080109021e0a030221041e06020c061005100512 68
    0x16000040040065110101072403d00281c03441684001501680311482140820443d400ba80b000f1908000a1001c59000300954070360610641c2d0108030103522190b52a070420b19074016030101e00c111350380501031014501020340142e00840b0000307101070316400110240c4c1e40443e204408180c002082b41402c2c10a0740b0380c8100700b0b014101072080c030512652030f16030a1780700342d0105004000300524011080d041c0d00c203030810200d0484104040600d081c485c035100f00f03200a02c074441c6088010000300c60500070f100d580d02840d8425421580e840e201e10340800d08000c2910001e001038900003140c03000c680180e14610080c000d03134440d190141c8ca8060150040c6d0310214021410421360802a0302050749800036201d13010712074901584841900f146041c0302940d825014070b0206007141407001158417615400c1e0042c18603580b01641c1421810300078042c0c440e940c0801e10610441c400c01070200048031060050b201c0440da003c41520320114125002d002d29800c00103000721100101c0c42e6040c6112684 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 276543848 1250 276542598 276542603
    0x40c05090402030a021905030717060a020919080102030a0f09111c240e030a09090b150304030e0306060f010512070c1403040e1003030e0d060b060d020426030313 71
    0x391311803407540c1e001c00c4440c81036107200480710040c10000e0102d80340a02002c40540946121080e41500707002c48556180d40282598200d158001444412903c0390740041c1c040340300100080e04c0a5558050150003035101f10707010b00d0710914200380c0c070780310b4a05801116146a00244045c400c0c024180400100e0344c031810000d14101618040303c40000e6042c010900d03c0c0c800d00c400400039100150501044d214442246c420f07a0300f04020044505030004c803174106071014414000342c0074605602080c0340c0039020980354903009000c0100020940d12124129a0103000d030140c03042c6c0d1b2034080c2403100026000c0185404100c1c00c2c000b05c14450b0a8004181e482901d074600000d0040068540861031560310060950907000054144821101b9404e101c3d0010001d00b221002c651642d00c004102030030760542e0300c0c07190b0300d507880c024207102c02908804085403000b00265500d13600c500b082c400070340c814400c0481010b0b00802d20b240c02c4103245801030740449050055490341c2e032400740905c0c6228013030701c04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 276545098 1250 276543848 276543853
    0x1021f1e0207020f0402070c0e060103090605090a051b06070312020702060406020d08160f030e100f0207050c060403031e050c0607050405040b0f01120c020109080f03011805040c0509040203 83
    0x800c115001405200c10403a480c0d4000603a0b6588900510004401c2e80705a01d0040e4010442100001c80e0808030360115880d003044004551107240048019220a035070183c881805e003000d00100301e1011441c0c441081c441c1040350000c030304144402100c808100341607980641c0030b101c03620203c1d008841c003204c0c0001d47e18005190240070780c005509a0040c0d00070b003005a01459503491300d590000c00041d041128240c1d00c2c2c2070744002400062034034405406240405458001084040c0810400001919040c10301802039001d05825007000303401920302600c042c490700420180c2e90a02e48221130039139401d681c584008049611000794098101400c2c4000c109c020003a100b034400c03044c0071807401400315644082d0381e40e00d44010030040ea8040443d180c400c2c0e0003c044040c55030b800070f000f50b500b100030741400302d130003100914141e00600c117244010300300d0900040e2041507105203000440c140e034041043c0c465090000c0c0420011500100e60080010000c80020301840c074160348a1980544010f08 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 276546348 1250 276545098 276545111
    0x150f09120303010305031b070b0304110f04110a0f05090d0602090a0e011e092a09080a05030406030e03030903090d020604090906050f010501050a020303130f0c0b040e010b0901021f 79
    0x4051660303001340c0c000d8840b034102007814a074003c40070104070b402c0c103175010090800741d04103186140240320241004220031003508408d0502d8507000d5180c0b401c040004c1003005002c290340109140742d40040e03c250002a18018400209400b902c180c420030400945110304104841d51060300948c0700d140416407250b4003c100260701c4c00720304411800382440200d0b01300340692080c410ce0b61104a90080c1d0413140c240412100750b00d605514040e1140b40d141d140c0044200a010155141c4050343c100744c01d607004145503581480030000080046558607035003080302800d100361107600c1c3c4c00140c82902d90764104010003151450640d00c00d0740c0807400140002e1805603124141401c80d030035030900f01c0d001e45d110820000a04120b44410b0300500b02800c04502e40204540c000303440c1c0c40018065200d0340d090140308002d1000c0940f10403413169001c81160411901c0e0000c8440641080c41170b0b150f40f0440100200d0741c0c4401da01922101c501c1a00100450307084501c00001181e094105145120741d141c0307 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 276547598 1250 276546348 276546379
    0x2120a030c020904240e0c15030f1005100206061c0f0b070509120a0b10060c140c040507020307050106060207060801030803070201094e0507111e030606150f09 70
    0x1030401742c0c2c0c0e40c00104001200700003091a14201401440750a00c1b6a80050701200309500500440b64407108d9696003240d281e0310003031000c1130801190800c40d0065207144540036100c0d00001c00300d001c0d503001c4800c4481c5a00d544965580d503d82c004008110b030f1986681000041c2c0c2203680700341c002a05041c0715041411000100700d40c4000700f40b10455941c03007000b060b400c0c0084c1d1100c550300400f601c08904003131410302401405150036204020200c18034448054031654046c0001101d01000030800d101c81e0508903002507994004101c15141c551030001c0014916000142a20859040b6192118180e05e1a11680d25507000140b4050540d500c54100a0020304500c0081c0342a46006ea40484040d501003000718039600c400c602004403004120396582e5824001602808030320991038100d94645140c034052010140fa044d0050700440c02804c0200b95401941c05407103040000d408640b0070b5601e450820a8003c40f52032042d01c0034008200300024902103200a050202016021041d01010303070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 276548848 1250 276547598 276547643
    0x15240f06140903060f0a050703050114100201020c0633030d0804050a140d02010b0a0b0d0903050f040f17060402130507091805070f1103040e06010e04051302120a030c020904 76
    0x121000d03030030a00217800b0040f024005200305a00107115107010002d6605148030040000350561100707205108610000303c03102d100750110380501c035400342079030031a080c80c05c52074880301c282240c04800e44400300c42030310307640c42c503030b11109041c0c0c2c00100186606c0005030f1041d40d1442011b00103035114001d42c100c440200c0c841c5900380c46403e1401c1e00800c0032102d11036009086443c1d28060a104248148003088000481425601c3d148074081c00014801e2035031500b659144100c0e405228928808200082c48481c84140b1400306c49002d40300700e02003d41820708c0e03500c5410858000b580417140786403041d03550704c2135441a6484140b5040a880d130540701caa0f00c1e800b8024030080b0303049064a41c41001181584081d9444035a9081d00b061180d80203c504003540301d01a40c0103140060407983d00003440c07a8861301c800c0c4c0307401d070f4050300c10080b1381011600e804104825800270303401104988a020b2080c10006811100c0c0c40d01a5a020300b018499401c22101c0e01c80a482691084004200c40d044681d44 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 276550098 1250 276548848 276548851
    0x15030609030e030706170a15181509180f030e1e03120406020307120306050604180b0603060f0105310f06210207050a15240f0614090306 60
    0x1c2d2940d0002c1d01c04842018a8855503402c09420062405c007103c000400c4207424a0300201c0c03012011450918514020900d074029504c42150102c030600d0704440003016522804214040c014614485900c03081c1d4181504c482c900840f1345080c0032496078020861405a81c004603103e4900500146824800620042c043c64003050380040b01e5000d400451404110f1142049074042c0d1070307400c0c541303407040113900d03800351200140001d11024805402c0074403d50045002d01802011181c546032a080c1001d03d40c042400341c044284e141000d014224508441601d1244d18000c0c02410600c0300c1400450341c0f50000a0034025500c462a07210101192480d4900f11000003902000022032a260118000074142c0e030105c02408943d00c8100808402c0c05900818549070b500d0260f0707100c000d454643e02d00b40d1700d107901510702142d13030742908140c8001c4d4000d41c5070f240703807030800c0320104600031b803682d43c041401e1044c40d175004080d0300100f20312406903d21040c5502c22801081c1040000000710382003160 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 276551348 1250 276550098 276550103
    0x2e0c02030a0e0f030c220e0d1e0c1203050f06091017012309060f090a030806010c050a03110c15070605100306020d020a080a09030c022416210207030615030609 70
    0x10b0035000c112446140d108180070b03e44070b87d00400034070844410190044440041c004d5449001442c01007030203000c0c3d00718502c0d040c1d00c81d1800108104200d001401821306480504905003002d02040e850b01c3e007030000a001d40c4c6400880300000c1c4c038040e16100010b000382c2d08240306548904880c01914590440d0a903144485500390051380f8040306a1030400e0710090144510404400a1141140002600c05c0c04682d2505103e4000d44400c40143d80c41c210100b0000c140d4803484001c44101039002100c2403020003d60120344d4078000d02c3e4200301204003a1016408005802d000c214003144598004a030003070090000b18030308544907118601640d11001498841c107030001000c015050340010130726404103981c0410820b44905030740003080708002c910080d00ca18144610082d0801e52004009078440f610320700c0c285e0720061603c415810b550450020f4402c072013003901d2440c900301d003950030b0250500305601a003086400d69864600400c10781c1c044510040c4552070200009840340303d1b44520030b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 276552598 1250 276551348 276551389
    0x91109150d0602120c1305040f061701090b100e150607080a02010b1903020d060e01150303031b020f19171210150507080306032e0c02030a0e0f030c 65
    0x4407034400409003104c007400c0e594540f8001c000c0810503c54620090781030300c100311804900000b130200e8084c060900368005400305022094015000d5105520205150348241545903042c1d54407000d01c20304089520030440c40b16681d01c00075440c4107168030b040395070350301c0200014107200c4680c940340120b42200002c000540e40d90341e1502c1882c03505a03d1801c20b032a43d2a191950b141c1141d02284601c84119401000240c0720081c00003144402c1d0400c0301c21880702c846e0000e18035580d04004000d400880503a004a48403040c1058001d4400304424030f2a59040001303222804045400e5010012042e178261000045050b0b25000440408000d024907250102d01101605080d41070011401d103d5010869407641c16140c0301813142c1003019a4485600800c00a882e6658480428103020400344071a803d209901c0e544a0344243c0e14440485511190750100b2000f0032665082c1d03500d10460841e07101088901d01c120b0385914101c0781c00c07035080001034295802842500f010032644c0f44000c0032858240b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 276553848 1250 276552598 276552607
    0x180516030312051e06030a021207050901050d080403030f0e0d0b160201090b0705130302040c0804050d2a060905060f071101022d0c0d0804020112091109150d0602 71
    0x1d035001c0c1042c1c0a50051078401c2000c2d003404018281690040f0005154440e4400006105a80c05003d0951036a802401445801481c01445900d4020500030b091140030150004509420308041c499000f60740140703c28a0700341551419528082241c844004124a024003101140c0321a910b8140700e610650300c154a0781065044c1300034681c0302c221113204580c90601a8800302e0303001100c0303a0b00f015039400c0c0640c0c3c4040d4000300c4540b0f00c07503a0308043d41040c1803400086400b9802400c8910440c000c50588200c200c4e518800c076a40341c0c0517200000320380303194041c10700032558906840c10400e1003190001450049603550605000701112086060f40c0d8a80c100401141c0206441800d80d03d0705000314902203584506c0484009161240c02c141e10442c1242e50030f420211007211090207452003200d681c51050900100240011035049000600e155940041158140030b42e00c94550b0003a00b54003e146040306111700610003c101030401102032100d11503545402041c80c010714052070313016959 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 276555098 1250 276553848 276553853
    0x20a09050f060c0a0b06060903031605011409150606090409050a0510020f03011e182408030a0c2f0312030105010504030f08070611120603070501020a0618051603 71
    0x485541da440d40500390070000201044008a03842d40c000740e0104001c20a40c41d010041442030140d6041c16404d0300c8005150841f94800d0b049000c200c622a000038005c1128842d0b4101c0030141c01c0c4d1312540740780d0080d64402014040f441005911a0000d8041400c0c900e04400180035110002c40590746a0030044100052000c1800009060300c2030020035440c01c0460140344510341710520811211103003c1e174100080200804450000b80140e128851040c25144554401840989206c4403091004640d81090705080780d10001201c44076401303542085a15001036650640d4490200d0f00a401a13101c42410b42da00d030100ca5100c1400000c407041c4119001c141480e10158446421585c2000e10040010381c0e030020494003580da00c0412034680b20a07901d010000c6010b82c48000781050b0420001c40002140c04001d02030715102a0581d00302c1d502ca10040c036440d0200c501541d40181c2103031202030702203076443d00a9440504000c003146480112502d0ba1810098401c220fa2000030313030315408206 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 276556348 1250 276555098 276555109
    0x702041119020c01020d03240815010503010c08040602160516030b0a06031112010f1b0e0f060a050705030403080f0703110d08010e0a150609050a0605070c031410020a0905 75
    0x14000114002403c81c040c0d800c00207903482440c04009400c0680b103015039100c0800200400d4a50030710112480301c020b0300c0312a955120841c00801c030040000c1e48000141514050040c1e00f54400300b0f8503264000d45550700c1d42400382d80f042a84000d800350204811300013400400c1003220b2403501c85441040c0d1821072419410210700902035918040c02c0c40828800300f21915034441d24500103c940c0801407103019a0a80034021000040b410140b0b00f00c124052014002030f0001010311940c0c400d03140c0000c1c2c40c20080d440303c1049082d1f4205038148a000d070140d0207400100002400b4408580c10b1a5076607917200720700d41c030070b0a000a1010020400d0780400d900181c2c900000d14010004d02180c2c41304c114020701d808014460303840c00034164004100081082d038000e0303040c003050801c2c0c40c860301d8881c3c13030182c03203004144185030107050b01c0c03000001d1301d6110300103490b004e562041740148c0c032038178549550313004104c041c02104403800340c92803d208071a0544001c0130308410750303102c008800b4900b404015 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 276557598 1250 276556348 276556387
    0x15130509160807050121090b010e060d0314090105070803100306110301060e1c0218010602071505040b2209090507060801030803190b0307030b040c150210020f07020411 74
    0x1116950120305020300d14001c00c004081c0c940c03c1ca07001001110140010451080403c404131842c7d281070903120510054107043c50684401d4130041e84582c5540f41808070100c04804054006100e03050410040c50000c0010b040440d41450280e00309506034640d1200e42d8011340701c1c0360854150f1801082000304500464490304800d03001c050640d0f14044002d00242c0c0402c855a105000444050b241c0e19500411044200d0b00a060b148130f44104035a2000020070078043c00d005446008000200d003070b070002c01444031031344513511f41d03084c28600b03c01050300303800030b195201c010103070112030b001599a1001c5080003090400d5000c149014103041140c1026030503041041081503400061001c01c283d40c01302d0313420071942800d0402810744940040010315102c40035607498001c4150001c240803850042c0c03070156009a4800001c103954a41c911b401d20105102c01d009a081300321401c507100300c0b5030b0107002c48a644401080c9011481e500044c01ca4081944400c0d0358076011510103442c000b20700006 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 276558848 1250 276557598 276557623
    0xa020114011413092108090c0f0a050f03010e0d0207030c06051207052802100b0405130807030908070338011202030f060a0c080906060d03050315130509 67
    0xc1582210000b00d060090080080209142c66841340801c110104480c102050303040010080486504e000c02030600e203080d00c016903584904030440c80d40745440740f94203e10301002061410414988001d004400d1001b00405a055507180486054448144440c002000140e8085d1001604510300f240e61b00b90550040b108001060000c4c0c086034040410468010110341001d035260154640030f04009180b031041900c0c001d60309003100c4051500040e40200c103013141c18080c002c0c0300d80802407000321a030407142208080d442c4150100490507041c02444424000d150800c1c2c02611103150b90701d09003440c1d104444080400700c41c2212008040c000c604078900c1c58540c14101c41c42c0f0b0440d800010b074180210075070034100c50118021135504110141c01c81c1c41080580f482c40c0341c940c60002c0185000004040469a031034002140c1c05004151103100e2400100300900242e41034400b207445030401406140c00b01c05140321031160761765411241107054076200c408074651400d140914140709501803032 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 276560098 1250 276558848 276558869
    0xe06011b080301050d0f1205030106200615010207080105090c0a15020c060a0215010906030b06030f060f0709080a200607050c061629061002030a030518030a02011401 73
    0x3840010341c41001c90b41102c00458084002c401e440c14192060014404010710111000d0201c51407030740c0080265040311202e4407207002080d00f00c2e850010b840e04e084824402600000c0004200b5000369902c40080392061040714003158507011140c0c01c50300c1c10b07150f10301c11354801240c500d090303c2c00301c4040c00581b800034140e00d15000440000f0317540d49107500026110b1540420030b400e045108212444604401011261070340d6941c4103528000c280ca03000a46104034114009025410b00240f56050349078040f0003032a040da41d42c40074200844018190b1010090030102c00100b440f001c00003d00c005e4000c1c220910f103103080b0b41c0422074400028001e14000c3c5c90a001e6280402c0c0b001c2000104801d05440e016516451a0300d450075601c0c0c00e020080403258a00c00241c0000c0100d4080342200030742c1140304909403a0705003000070310403941c1c401800580c401c00501440038070075004035411070207400d8001c115a6080903601d04540200f000040140e5584000b00c2c0c5228000d280f650041404206 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 276561348 1250 276560098 276560147
    0x4060621120e220204030c08070b03010e0a1104150206090705030c040203040602090d05100c0c0804030f060605092d0f011e05100f0305060a05061602040b06040e0601 73
    0x110245003051031000c0205020801650311503640741c3c0450b1183c00036402825940c2c400e2041609002900180030581c0c43c0307000503d0201e00340100054090a503900c6400403815686400310701000c41d0001004480c086807a04840d441c942284405480540082c0c07900e50211207240070000d00d010303002801082c05520a2404000e961804110104103d6055801682e640d0300c5041c800301034442e007034070203030071580500300c240500001007844007058641000a01c8081008101142d000e11342600280c2840420081000054502e01c22403a22501c0348802094140d56080040c0c090f09044030700c120f18000030405102d0003400403480001401003250908403504041c146902c07d40014050011903001e20300784c1240200f03030304400100400340100b58980c60144031034003c010302c02c0c002c8240f021900300808aa660b1818544030019a040540180d0410000340c071040c00e1303412030090903a00155580301ca40c556854403030050010346203200841e030039414118001800010700c2c030b40c50100d0035010781 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 276562598 1250 276561348 276561353
    0x1214120307030b1f0207052707031d01060609080d02070b072d06151401020a020f06130b070506010815010e070e030114010f09020a05092704060621 65
    0x9040d00d4104003145070020750000d211011031010840044c82078410003078103480016603a400141c102c16104141c40c01848605100000282416131035182051924614002a0014407a86c0185099448840001407819180000301c1c2190301c1c80d08000e0001d03050b11014419402c0030420001014003501c0140001490b100030f805481c00341550080030424008107843c5500010354400f50a0b1521000840c0d200044e4a800e6005044088404080410000700014511070100d41d6258010068000d0040341c0c419500300714640a0a0300300c0d40c1d0010080c005102d800c1c2045903250b02a1452178502aa11122810081e00d07000050740180002d50100190000c05807803048643d04403081d17030344c820005448821059a030084030448080c0c056190404451f603d0100b046070a0403112031101c1c3e1104107449070f0f50388080c1d10414200300d010403400c10455102c0d041c22285115420403081c040003480100e41081d09894130156019036030b1549980b82800f50002c5d20308580b198640c22940720011403080d6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 276563848 1250 276562598 276562633
    0xb03091606051e0904090b090a060b090919060f09030203070c0506161e0b090a110a080703030e0d060c08091b09040609020d080307170f011406130308041214 69
    0x4450250f1084004210700c40c45440302d030400308086130f102d90200c41a2520b0b01c00c2e41e94038092204182da0090411030300049600340780d0030b864010640790015107404003003151081b90020030b0300b6040340c1003940c484030840b85200c18454056014802d5014613a40d505508126000040079001107114070000c01c51000c0c8826023410401d41180c4c040c682c50b2088145c07500030030411443c2103015203c039403043e08026181d4004208151483d100e041101c161104c00700500903500700c1c0740a601001d610048045c000300e40a900d0350300c07480300020482d8510f0b002da40c1e104400d44002c000d290010940c0c0e90140240da60051204c402e07810324002d800140000c0c000001009500c001c0d101901d665502c003c042c06645502c02205038003900f0080c16a540d080c450390042004190000084c000015403001c240c120074512007660403151000300b40c044c1560780d030f810002e003688001e061003507040d600c403000000a0020000741c401070480312021011501d030f908181404100664510640c1d80291401c844bd04545 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 276565098 1250 276563848 276563887
    0xf06040207151a012601170309040603061d0f031b1c0309151514010203130e060307061107050f06040e010b040509070e100318050a06050105040c020604050a02190b0309160605 77
    0x50a1407001a103080300042381140720b00c0b1101600b0a00308a0007100f8001c464000001240b540b1211115590544281c56160340c104c0c1003008003500100006060034415442e86551a252501034030031701070a40c801240602d1440300b80f0001300303407141b00f41010300c03c80f07034600b072160380344094140554903407100d034074800040c5030150741e1f03081c0d000c41020003142e4030030001e541c2c40d00844098001042c4d242e0304650942103045402c0c3c3e10a109400012421a20139410089401c22241c01454103d0500041104000b0401d000d02e40141040c000002d0f04100c16a405009202c402c01c40c6070b43d0f50400d0300348065018014030000602003c5074150010740c03121480c0f020030144070b01e400117130000c10540d40d181111202030060418070561808006000710396000c2e60494004440070003c00d2040c5c00c0a98840008503006490358001c501100058102845a554003044507040d01e401d05840d40551a003d400940d0000307156440155408618000c40070100702400b00d0b4100982051080702c0442e60300ca00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 276566348 1250 276565098 276565109
    0x30c0303080c04090e16080d1d0102010b0d06050105030d0f0c0b0c090406030b0f0112051c020309180417130909051501030506070e090f06040207151a012601 69
    0x2440700040040382400d0544001d0b041d03548060084003c04000290307544c0c40840c0c0d0300c0141c454000005400034001802071580d800d191902ca50a803e002d00c01043c040b00780c211581035540b20040305080d96101c5283da00718a02c14100046c0d80d50504c424545000312200740e480c24016144221050503400020302d001ea26801503180b4500e0351030464034142170080302c6542d0b4000f801c081000c41084880350000d4800c0b90318220080f800d030307030b600303928403404824041c064115040304144014401020250141028143c01200d280c03003910400314000d45a08040e02d41c1041c1c0d081e042c00100f1030000030208036112650103070390601260081c840001038240c4115201180d40301413035400c20006020003150b45080c584503910b10342e0f40341413450700c5040403540c9a0008655106c04842480d05041c0c05000c0d0003121500e030b10681e140c3d8240b000075840b0040a44030084c4104142400315000d026483e0511004900d100c803003210800090002e012003c8445119451101840d40c800d2462880904548 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 276567598 1250 276566348 276566357
    0x100f030b0c0c070506032409220305070218041103010507270503010e0d080a0207080306060d020702030709020a030b010e0907050a09081c0f030b0a06350601031401030c0303 76
    0x2c01c1044040d18090050b071069421450200410440b8819284000424800f8008074003049172900100140d0361000c40390b8000c0c0d41c0b0403090510109441040c40390b22944241000d500c0d00f11285c0000b0302d401c002e203134145000759140d8200406c0000c007841c000c0d000203083d0b00070701c000e007402c170400b0700b014000c2c030b20900310070359405810181c601001171130100400001e4001c02030506459482038071040790710100b6011a5100000c998440800e00c202c4d4000b541005425040d600d07003108009c5103500281c00d4030b09041d000e201100143e0707000e200410040540240040e501d0354000000f030140c49030419994144580c035140480140ca50022085d408900c071b1170f003036950f125009000c0d41d000010782c000c100b4612858201c0941d0b84081d101c080303160f40541d140c1d0108044071141c00c5081c0ca0f00410983d401100a150821245000b90b00d041c6101c0d24000b981074101141c210710f005c030200385904200d050000c1405014413035030144100102800d8800d0200b9240d8159201c05480001071300c002070810 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 276568848 1250 276567598 276567607
    0x140d0e0304090b0f220f110307020c030a12030c05040504150302010e0a0b03040b09030f030a090c0f03030e040b042004180e03030708041e050a06050c180118050315100f030b0c 77
    0x8034456002d01c0d400503001e04d04019607e1a048502400e4208540407400351060b0341d103101084c6000102d2010302584600c58100303002c0c500e04200c000c0c01c81a08441700303100c402d11010070341e9903480c001c1e411044000e0084ac078606140d40001001500c02c1000180901c007086014040000e61008a03a88160846c010b03624503199142020f142d0311800b06c21440340c080c00b1050002420841d040020124020f4002c1d0500b652500004400414181b200801040740700d00d09100605107030f0400e00e0040c40081000450700800c0304a003102d0746190001003040da400040501c1070341280d002d40c410031002c25004015007a1030741c0d0555034a100c098880024004100b0008003080a0b580825629004c031140c84100c60f00e5514000d6a81c04200b18216401400d1a000400180400041e0b42c4604200c06141c6113808003c001503400001074ac0d850380c600d174904100490300d51410002da6403000c1660800050902d003102c0b00712603407a103d820203034011200c03120802c04140d903000060340044800700010303580c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 276570098 1250 276568848 276568909
    0x7020a0209041712160503060d0b091618060f080d05030c07120f1b03020705130204080d090302010f0f021506062a010c08040b0403140d0e0304090b0f 66
    0x600b070403ca4100c0525000801030115120020b09600a10310300140e60a5212103860039642400200c98154108065080c10b01c0403c0030340310203940145807030f0141c40d00316151010b191b5602003240c105040c0d0784915000144201d14510645d4001c04000d181c0300ca803035003400910f80d201c07800c0050034403c04c580031010a0100d0b0b0014103e4018542c40030110340c84010091026110011021551011519001141d10800510300441078201c1e8964098038001b41400c040080c0000c2041c039106800b9424000490200c00030002e9100c220900e8481780e1006155200040403595043e19000c200301004407d52400b58000488981010400ca10005030303a48110203c1d480b40200901d40241c17240d04a4071003541c0b110b02400e00a400d81060082c03080d581c0d07142081d9204003040d180140300c0d0a201000401191049030241c1000f86135071000d615020081e021801a200105820101a000050304002100ca2846001d18228056a2940340020504005962070722100000d080742048010307c41c0303c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 276571348 1250 276570098 276570113
    0x7050d18080d02010b1507050a1217090a02090907060504140d05100f0b06070b06040504050a0f0803060301060e010b07020f01121e11030415240b070b0601030507020a020904 76
    0x740c500d20084540800100710002e01034503001444a0051140c42d0b45103c0000015003214400741e00500100b40400195031401d100c0070802d000901004041101ca28031401d80041c90fa010707100c28402400060400e00402c0f604090190003070540d40c2c441d040412074650001e05480c02c840c800d04c0292016406980402c0081c666034000400600400c00d410321421059800702e0721440c5507240c1004030030102c00c1031080b98801c5001c0075180f1310807100003030114901900210f600030721403000e6408440556540c43d114640603442110b0602d008005c2100c01c0c1000d204030402080e0203008131715694074000444181d881007540190203000c0c48510b88000d45d005510300d5546491200081115207103d0b40034425422600c40c8580140d0304041404a00d8050007082e2800b403a0402d00b0b881101d241c1d44002e80050a0601c440c1240c41c07100040d014141d5202c04003d00242080038940303603110000d2070400e840007001015141494600f8041c0314a0130b80c00252082041e9045d0341100150300c0e40d0034000d5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 276572598 1250 276571348 276571397
    0x70c1101050d0609020a0e03010605062a0d090e0901060609030f21050417060403080711070e040b091608060601050f0f0a020706020f1929240607050d 66
    0x1401503040190024901009600906c1c0b00c81ca650b039030002d040d184a00709030a03150984103076a80240d084c031a41d050a410074120500c9054015200407c00c20340114642c203182c205038149000c01c0540204000300001c164030306500131001002080b149052103c007038a245003a00000c0c1004160524110411290300b5488001100d100042a060f080e0fa8400602643c414040d820198501c0c500009540d0720000d041c90099606885d2190030b40d5659208599100703011502d0100b40c4101040001c602c2d195100d2240903030300820b00c0b280c00b4a4210000c9107011110850346440c0e6003100c4040103080e81c0810300603080502445c1079503a517600000541100d009100310300d11030714000580703c145260006445021600550252252042d00440a030b4031600801401c10318003002202010001785024096140d101203600c07180a1400b00110129400000f02c0d10419100a0302a0078110707400783e00b100740403401d002c8440d1881c01450743d40315502c81307200001d641d09101d8002503582d4003d04044400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 276573848 1250 276572598 276572617
    0x90203070f18090e100f0501061101020319050403230307031a090601030209040e070807050a1d0a0c140d0b09010b1606021b12040f232809020d060e070c110105 70
    0x34004580e0317000801b0004d120a02c10000071490520b4071102c5003c0600030741e03224207500c1340000141e518541d01007000d000018011003c0010008034109015034150000e07102c4d01d603070502c0e903450b03142c050f038041c044420f030500400031800c00c0b02c0e200880d0780e0784c0b01d00254410000e1801580700c8400e240810041c4c08031030034151440c042d400780402c3c41c84000510a044a4003195120300ca681c0e2508510340340180d9000440030941d03844c002854401031a0004035403c2c4d184d14007014038549078458118990040300c0e0149005450f801c450380186401500031380540801100c00e45095000b4170000c000c60f1b00701400411040d008645082050342c840d801e400ca55902009035944400311420007403d40d400740c001c101944000071f4004c14030303c4400d0304503014140e90901c1c40b2564500f071000c000e0135850345148044000003416030282e4519240c01803c3c001c1011020158a41c1503081c0c110f400e852082c3c104141c0d0000020420103455400f000c2c0c1c01c2c046400c4040d02220030b03203000c0101c49038490301050b03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 276575098 1250 276573848 276573851
    0xc12101e15143a020702030607050901140c032206020a2301110a020f010c0504030f0c0503010e0a0519080f030703060902071202150103021e0a0f090203070f18090e10 73
    0x1080d40344050700c642560f02c015040c24a10f583c01080803108228021700d01d01030b4040d8440c4000422070350240f00200100001410403050300c5035840c00c140d810354032407088030400760030110302036101506168082100d200e815180c402400e00b00703100203543c0c0001130805001c1d40c002a0490740d050001174401a250840c0034024407800130008083c1c80039074041c201103801032098040b0408100e50600c184c4007800c07c107942d003515043c0b65441703c0d5242007140400751040000442c2c00202a5403d209118034504120098102085c40341040c03400d001009403c544e030840e50340c00e004005840e00044444a06421403d5526a02d030340104800520b0960015100ea5200061050900102c00f8182d202c03004150708480381c0008400800420700c8003031000a40101e403d59a02e16031603220328400c03d01f04400b91801e001c640e03a445e41c01298031810b9100b0705245500000b0300c01c2c20780d40050984c0300c440b02d901f05a980030240040280410255200f4124410307980c4042c0070074604c09000800c5129540d200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 276576348 1250 276575098 276575137
    0x3091406070e0a0f080c09060612011401091e030221070905060a08030c061503162309190f091a0105010206070f02150c12101e1514 58
    0x506602c0b003042415100340c00c036030000200b003151000c1031800d03506440e0162500905d02400d0141145021380b200394455000e000b11038040d249007820034000d11882c0e400784c150254080c005000c4004540202d0780c951006a000505141c003c01140d040700d0707065031011f1212070300d21002c21004094020700402800340020004203601d45802c4a03004000448030540100c1c1c0d03484d4842ea60b4841e04076900c846400550001d903070814010b4940000b02005000d440403400190038811007540035812228054a002c010745c0c1c0301800c500a036440d901c205a51b54803050402c101d4503199810219902c016154440010038001c4081750040380c1c4071580501034040007208120000301410090007000d0040c4079200c0000c1505108103696010200c0c6034016041075900445481000030004107240348419040041a003442070003140d0f6442075985900c84a00c45091024004c819251fa821900d40410300e060300344102c04800d441040700520604140c00e031080a002499010300698000109410203803d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 276577598 1250 276576348 276576361
    0x8060c070201031407080411030c03030406021b0d030210051005060d0c08090102091305040512030c040e100b0d020a090305240f250c0209010f080606030f0c0103091406 74
    0x103008154400d072001e02030740c000304040c2d400850044401100040841022a0205034100c40220a4030300c00f805075680c4231552008645560301540c040401a03001c210300315810705031f042ca0070001510840c3c0c010302070500342d200296106100e51811400ca591503022619450b100320640000304005008aa15000030030030120082140c6401140443c12000000d501144180300b10380d01d0352801851081c1c40410880000010302c00100119110301c62584044c9100d4141e10255124003001d0008665950510504d000c0f0200702038a610707881c9000600a2140701080d0302501c0d6400350b402001a02e0300080306045544c0142c1d030b407024200b070007948034144071110b03101546601c145091017040343c240c0b16a0450402c4a5003191108400903441c0c00c16021a08107001201ca40625403410750300d074004580004910b0300081c1d01c004641105c1000400c00b030306040c001d40e0342c03006007140a414800e0032802400e44401c084d141650406650305402001c002d00103050342d040300f502004417080c614004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 276578848 1250 276577598 276577621
    0x3070f05160b0702060f01061b0606180204180b0105070b04230303070201060f141c060e0307030e010c020112051801020c060a110a09060507060207120e01180e1303090806 75
    0x66603c20300600941c0700213501c15822807601c5048807003035558815422600d8154522048100c20225050384c0c5400000400c42d44043c107283e503c01900d8001a0380310300d4483c1c4601c850700e042d070741940024107180b900b44803603800c0821703110000d8001103030140c3c41c0d45d00c2c83c010341807041c0025185c0009068641614400c2c2e0000055840750089070000c0000c0b81e10744940003990340342d070310681912400380001c5448070b003090900300c03019641c1c140300e440001640c0e944a0055400c91040c540c46640701085c030f0000d1540c003c0c0242240768003030800c030707046208070703000200041e000c0c4d46040322131501c0e02e0204080300c0e400350000034071081100085456044d4911000e45484042d1901c1c3c3c079080c00c101c000d800c85045075084030b01c03628103034035882070300f41c40c00e01c0070b503002e40100b1000d0328007a07400e2003502c0101d078040c040c03011030154640e107803801041c6180000d000d00f580690150007001e01c120050010b051400000d40c2c015280c440d918120194500e01102c2050075600001c8160040e1001d111801c4940e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 276580098 1250 276578848 276578851
    0x507090f11160b010801150302060703030b06041211010801031a0702100c030504060b0a150f0903081c050106260411420901110a020604080705010e10020303070f05160b 74
    0x1603000f0003616640c4100c01403d0740c444207503108005201000800c01403034050014a49140b1030f04010030780951040014103541c0003680b0a40959448140c070b0340400441d41110b450b1a00242820140c650541c0c5451199103070406615058a6840d408940118020010142134100d070074402e11042d00c5e0002e00402404080c0d4080b9016424403ca041d59403a24900340c0003507407410208070303140690500d030448509030b00060740414041d56241c04030116a01c0d41c028558104c00440c000f46010a4040300b41c21580705920003001c102d07030705000e404c1c0c00034035201d80300104619403850f5099480320300b04000e400da403040d00e0544c060b0a4a02c2100c0c2c1d41001c081c0459016000341c0a443c0940c1ea4030007880d0304800ba5511074a5103101004424010760084000a06115400c1d04907550124540d002c109241c0c0180c2040019502400b030800070366a0000303d90705d01c0300e01a41d00209010034850065602c3c040038010070148680304040b1081e551050068810076042804142c1c610b502c1414900b054210 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 276581348 1250 276580098 276580103
    0x60a050d05010b0306010e010c0c0e0f22150b03010f020c0d201005151201150f03080a0e180a06031a06011409040e0f0c01020f0a0507090f1116 63
    0x700800011001c8001003540c1c440c25041e19140c1e0f08130403600044030840004901194a402c02c0ca10106a0700c580d010074500c01c80d0305914908040c1414000514503084074000b2013107040c10000407100241402ca01051040700d80703800490340400e038200090141c09102d406445083c8007080c05001180001120390001115484851138001c1c1d40b950503100070580038090301030740e01c500c504000280542d40410360041e807a40f0000ca00300000000610b4550664413031510980d120229a0b0131500c81d800d90340300900c0e048041110a5103585d9450545000d188400d5082c02500c18104c8400d03180c00c000240d40c4038007040c10301158a010b2452070700030003540c04243c4142c01c042d8030401e10000d08110381c502402050311b55010000010601035015484600c62603001521001d0078604407104004c0d4040d107240c1c44003c1e2412001c41c1e4002072512202c03100680e0740307a1241503001c0105002003480d07400d03202828008280384146e4101c0070082e1050089150070f0340790024200013284011224071042c0703031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 276582598 1250 276581348 276581351
    0x60f060f1e0d0e19080a03110706090b01050f031e01020f07150c030b130506040b030f0601080d091d0403021507030212010506032e090509030403171e0c010605060a050d 74
    0x2811590f0030755124183c0c1103c00040780700180c4580070403d640041c06120b0490710b00428003200c1c8805604094000742d4044441d035441d64550410840300744440343c0904802c1d5800001c89062100103540c8160032806101040c401c010742c1c20011401790119800005d80c5d8181035940c0da170510b003030040d80b00003414160340d4910300401500030502c28054074030150401481480c158092001c0a401050090f0040b41d00640c1c400107404191800d0103404682040b24019200e650302d030a15242c10201e180800408100c0d02220502ca01c0075104041c0c8010007220740e100c0303490754070b900e0164070f02051140c40608074100c82c81044042a0b00d07800070900200c000b00d40d0001c61741d868050180c1c40c0001e840101c0c1c201c136001c1545480b8400f603006440c5010240d40017010565984101c8802ca41003a6982c807a83c1e040010306100780010b100d003402c640108800711030302d0400d0011501e6410180c921024039100000101070711088003d4115001518005004a40c0c030707414035202a110354000114411081d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 276583848 1250 276582598 276582611
    0x312020706031808030703140109060f120305071410020d0218030a05060601050d18050f0f060103021e060c070f06110102071104050c070c0305030d050609060f060f1e0d 74
    0x314424010009440c40d4002e49640600084d40c55038000d8000401440400d66950145c03400000e6075201c0c64001c0c40b03251800240e0a040c42e501d1000300d40700390803e2841071403810b80e08001907440f800310381c94103800808440348407280c030030b0f49800c0c41d5100c00720045d160f0001c5001e24001005500500c5010320096a031720b00b40b010031701032540700c0d00030f0741c03020303010342c0000d0300280595001d03000900106460000010303900c5481d10b1070b40b4810b015488142c4da41d62007128620002601080034014041c00300c40106030b07543c59980010a004880140960107000f442040041341d02d88805441d1810714407015940c526071504041075002d0000d1045000003131010820122035a018821291015004015032901c144104284009060b01415002c110341041000304041041c03400b40001442c80366028565601090842a066400140082c0d00c2155800b0501c0040e0344d0701c0035a07001030202940c4042c0c84240240c00c21000d401080002101c10b241034039040007101411000303000203140c19078100041c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 276585098 1250 276583848 276583859
    0x20d021908060108010b0a1211030105030106060507050303060607031205132a120c05090109021806030108030a0c0501020d0c02160603060509070c05030d09030c0b06060c120309011503120207 84
    0x361019078040340884c81035001442411003010040403511901c1c2808140c4030021207c00c0101d94000700441c0303040c040440103104519003070160740b000b80002d00e0124103000c2e01e030300c80076207a22018102e58071601c40010a48100b600404803114895110f2001708018a07003200c8030709005050000480d445281c24000704401036075240401011024000c0e06520a82031000c040f0741440c80c40741c00d88a241e0104d400007420740e202d002441c060f0500c90000b6071500d50380d01e41c11100c0c01d07401203e0361141e5000c1c0010321000c072001058411003031003460041c040d40c0c101c2c03c06600a2140e0b0303400700c41e040e00f09010328034010303000604140100000405014030310f64558088003150b1150240c0d0780e00c582c0305008900c03914480c0c04030001944c01142aa842e0078108400007007100c0002100b00c02140381d00d2014414405480b5a856108400341c83d8035262801108a564545100130300101240101001290307880ba02580200001c0d40d04804000c0b01e80d48a040c81014409204490030047c8203100c1c000c03c5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 276586348 1250 276585098 276585107
    0x213020a080a0c1709070b0403080c01060605071a070903120e090901150e0a0f05010e151f050f0706020703021f0e060103020d03020f010507180915050f13020d0219 72
    0x88000c569a014180300c80f000070016050001d0281702c00c52040440105a0703046100c0140029441880255918240c8104c441e0175180554050b0042c09018001403012030b00d1800903080050b0300821040d0203036220341301542e01620a4001405a281c1460419042d50b0004003003031110030308035410030a1b9601c40002600b40d41280503030725911107442504004411100c0c041c40c0e00103805134004622112500c0b8200c0442e1026030042c001c0d12103000078001030b0b22009507001c203d90411b4800c011074400d01c1040c040258202810b403070800c03070000350700b42059042c01c040d5840954094025035881d416810004d50300c0d24881900c2201400610f8285038000c40391092495032000440604550380c0380d5001c00c6400b203d00c2400b601035000d164070b40b440e9a0401e11605201d200c0b01d0300c07045e00090041001510018464002c440c02606d0250384c1d4644502503100a02100c02c21140c030200422024085928450a220b54a190500100784480301701115006400d5055510708900c00e00c22501c0d100b06c1c4c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 276587598 1250 276586348 276586361
    0x1611030d0c1817100c14030405070f050402071208070e0303070b0117030712030506040e060412080c1c020d0e0d030203010e060603060105070b040507050a06020a0c06050f040e07020a0213020a080a 86
    0x5243c3e0b840802d42e6080031100c0e420400422201d41030120510030f104079844140e500803078045a01d504880c006000101540c01840090082540c2c11420418159500d078055803102051400780440ca00000b0b20300c91180e20100b00c0800c0240989031900c0c441e240011a0390700a00443c000e079044501c00c3c1c402800004182c481007600507076100210300c0d2486d0141e0050002402d05900507413680d01c2c100010504210180c080da10881c01413541903440180201080009007400c0d5031140d080081d100200c0399415201e40603008034400580e14158800000024404002081d01c503000b0b0203214075003e5003650182d8121a0600c512041c0b59954104018071407204480b8240460b40500c10f100108503413222140d84140b0500490310030940f19070000e001c0c0b03000c0e40d0040c80160f21401c02c003010441c0c0c0c2c1000d0401000641440c3d070030321503640440482400b8500584400d29041d6000507a036078420446132051940103484140301040400750320b000b0398003003080c04c40403e1009000c140f42c1c03000b511610707 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 276588848 1250 276587598 276587639
    0xf0106141e15030604020d18050d05090a0b0f04031208151f080a061a091c030503041403090a1523090d0303060312020309030708061611030d0c18 64
    0x5021040341c0b1128001580010b016543c1056086c060640300001620a22640001c4a441018080850300d031042ca0901100031000801600b0b000c2d54032580c486466110684003510444c50b21195a410019018015a0300c007610030b040c580d043c00300740f5822100490140c14610801c0d4012414401888070794170030250b011403104d4038202000b090910440055400c11070700c0704086017044d41e0385d07035880304240e10507140009598002818a4940703024201e41c91039030300c2103041540480607910050a54040100f010302000d04d9442e20780c1c1321030000d1084803041c1000424800c00706480341a0541c2d5040c012590101042c2c24100c0920030741c2c0f4100007880c41084000d0828540072041003800304401a400e012418540c40380400310001700007010380036241516a00030340c0c5441601c410149098104ea002c0001500413509101240040f90813100e4100081e04043c0e01681042e902c043c42e6114241d0600000d40c504461030203000e40c07040400300a002c030115070781d54054458050b007d800704403c04a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 276590098 1250 276588848 276588859
    0x4020117100509070c060606030b0f0d112209030e040509010e07170703082101050d20010e06030a1b0e0a030209280b0301050c030906060d050f0106141e 67
    0x4102d1490001002036011071039103043c44640005d0340c4ca400544880d80c11140100e61070b105001c6003400d00300184903600c00100d40118052440e07403506401100c001051a0260032400d80d1948180343e58103605102e906145400c007c0c112403400d000f0400020f07160041d00c00e904140110ba007405050003040007556210000d805810700d4400e16009003030016036400308034082c0000000c0030a00b0307203010b04038a00c40d01d54580000c003200c02900c8040401608114403501004881c140410001ca03c0400440c1d0201002400384e4650001030301c01e03103001c10600c3c1c1d1000c1b00004200765120075400a0003d8802c8150711440026400b406440224003c8172503078000c10184400c00240c60305018036a007001010b0800c410281481740d0501da000070556100311181c4d00d5580303845036804c0034410280d010401c1c5006d1411420304035000368680743c0c040e001512035440030403118103000041c4002d85860380008000c101c07155885070081d551443e4808041e11406804100060f0f42c0c0742d200c405000000b00501 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 276591348 1250 276590098 276590131
    0x40f0204150c060e1e0c0108070c080c070e0414010f051308180301020301060908120403081606060e07090501020705030d080118091e051014011206022104020117 71
    0x3007150481c0c1c039008142c0c2c40585a00c4030030080032040c050b40000c5085d104603400103440704003040e46064842c01690303040204410030082280d030700416041d00b440d4080715480d607800080001924013225500041d0110345288240b00800ca034400c241c0d05c3c005c180c1d030028001015030015990407a1806c66800b003d03030400700b03900000181c00d94001c01e9171000d02c00c094500034036103401003400c84e00260454804941041000e0000c034104000d4107011070300301d80c0c41601c2c0a0031640c9041c8903004801a95106d04000038100017001683e801c000042c00e141e282c002914a0041401001c910061090a01600a0b100007150904000c5500c21a4580d161910344107030b440c020354500e642c2d039158043c1511582d11444000011000740441410040d0100c403901540841c1c24150300f0410b210419299030346ca4440b03015007040c60460128111072034020300440080190400c10040d1142c1c07040503800044155800a0300a20080c149004c0c3d4001c1c0d856800d4113400d0901b000b80c80b8030039500005090035000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 276592598 1250 276591348 276591389
    0x906040c050d02010c050708030a1106090307020409110d031d03061e180d120c0f17150603101d090c150706051008240406050a0902060d0506040f0204 66
    0x4440b07041241c418035050b0b01884203a2111410300000c1c0d000f80203281c00015602804ae0380c49041006203d507000b01406107400d281c02c00540d241b144410003801a5100e0b60400e040c000e480e41e036110130344409445071604032410303d002003008007003c0c1d807240e91210f1146608802d0800044851040716038051403080c004e001010380f20300d800e000b00782c148811144d0100b60b006510034440031b164500d09460320428912a1710705101610668040182000054002d4403e811b50000e8041c40744c21071115024041d844a01700200343d82203a51500e038100300000140603c0b01700144280b000c071110661150300c000e14941e000f0034201816204a1b805a102000c0c4094503d4070500b00300f05200038081c03241c54010140c2c5d41c40243e80c41103d6403080d2440302041085280c100748107604404d200c081030017807482072010a007170714041b01030406043c1d41c3d6141c001543c50011680b040c004160010901919a1344400064000d84421140c1500803410100c140d0394000703850080e10261120441d9100c050030411 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 276593848 1250 276592598 276592609
    0x6080c0a0506090f0a0306090614091e160609050f0f01080406020d020d1803020607110d03110403140d1218021002010902132025030302070b0f0f0906040c05 69
    0x251220384e0720002861400070160350380c0f130084c030080d8410580480c4080c140e0502c0703400c403442c2801d800d4214400c2c10030040030070b40110b6140d1a071385030095034211400c1a001c0e101c3c6450715070303c444a512440000003003041c1d1f8000e04c090040303640480e0600500e80500060100007450200d2841c041182d15020400040c420340240c128606115401030900344c0c0b4024940030f03100080c3c921680b40306140401c20505605004180d404100b50424802d11000c0040c92559904214003a0b801c2640d514504100140f200003181e00a641068a400002c4480c99150362190444240d0b080030a103d03254070a4034901c45c0c0a508480703400001c018850140b13503000d110100d02074512210455603243d048070016690b0181490900c2d60080c40083e1010304102d258000000c42620805411410302040c8925000804035458031034901d19204680d0807185429006405141070042ca40504041040500d00501980c1480b621340d80512002c07a4440341d5490303484010544ac090090340361044140301c0703414003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 276595098 1250 276593848 276593857
    0x302100c05030706481b2f060703080408070b040501050106110606100309021503070807090501030209310e06060907020327040f0c080a06080c0a0506 66
    0x942003164103141255189400c551003080200c4400f0383d1520511003940b43c40e600040c0700c030f90080d0300c2000c805400050b18240d00440141d0b040a01400e00c004603018465291a041c0c07495000664410100910305031642540740c1c982940710004141801c0403284c6401503d52411901402952825110740c038101c4201800a00036a08003600b00311400018015008c0c66205038000c6000141c40d5040036001400f0a444900c4071000364400800e00c40241c0d142d110484801c0c00d1424001845030540c4041052565040081c0d01c00c00e4003c405c02003c150071502c0e05108203001d035030b980102901e41c40154102c0c02050101b07600504001d40001000d00f040c04400f0540c01100300303440e5000c1031901d4080035940c0c28181040300b42c100c4004c2c84001c0c05c00010f00c0d034210302140007442c1002c20f88a9205c168207200351040c402a4041d1001c041103840d1a80211403446c230151041c0300581d0136a802400c800f1080e0f0354450903600c1c000000a00d240089044610040000c0009800d0344c230301810408075400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 276596348 1250 276595098 276595129
    0xc04030204021e0c0f0105070f1d041b0c02010807050301120b0711031308070e040b0f15040501081f0e03090603060312070c0f090603031418040c11010e03040501090302 74
    0x1103c03c0d1140300100c403080640754121806000300000415084428203481000d01001c05218094a8803100c1c00d800410400100390042160f0f0710000040700041c003e0190242c03074020540c09001925042a8803480084d4114001c0c4c0303410b11541c583c1c8038202c4031b070b10003481191441d0b400240500300140a2a0380310781c00c01c50901e052011040950211811540801140803804203594020803000c401804500300a0103100e290305d00520340764554540021005140082039250740c00068242c0703040781c1440031000c01c09030041080d0342e10b4030075855072800c00c040900d6500f651032500e004d10303885500680c1c0c813003120600034600b404811001d0100381d406c058030007a49400b030544000c0140201c1c3c405007050070300a80544800900e010060004250f41e034000780646820040c091012a40081d0128525802d0464081e80c811002d20400b00084002c3c140f0340e03010741441608000254400d0410f44280000030080141c0070804001d15034920452181078085194a0020405450900d82d480d05045 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 276597598 1250 276596348 276596377
    0x307031e0212030108030a09050a06092d090902010210090519080918070f090302100e061e0d0f02120c0a110d0f0908010903090905180102121e0c0403020402 69
    0x603891010580364000741c0040101b5031000c141403903d95842144a802400240d80c80c584081c00c15200034100c64182c0100c000f001c10524500780503030b21454512072250070b001d15031158207071103406460240202c03c3c4203030300521031401005200d110a01c06c41401d1944640280080c036801244242000078444c802d030340d411800e01040049458107031741440118468555510a1300d41541c018007501c4401c0324100401028540610040e00e42c00c842501011241c02e08017a04a9900009045880341c10502d411007001d140054845600b040c000d1300081400841c207104002c001c00c050030880c000e2081001018003200b002c82d490900300b80040800007240c2c54a0f40000700d12088481c0380060f00301c11040010181c40440380b0f041d034030510304404bc0c407051000b07020303208043c1c400916250940c060407000680c0c910108040c050590501100c0055220003075441d4015150f040400500c2191515540002030220b60240a04400140d00c249003800a0500380345c25502400000e4000c40da5440010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 276598848 1250 276597598 276597613
    0x117040210030e010f0c1b0f1b0503010906050703060605121501020c063106020d030b1c0302070515090a1806050a03080a020106080601080d050f0409180c0501020307031e02 76
    0x70280607100b02105511742c0440d480f1030210006102480400a24082c00000090307040003400b200e070628a60389e040304481a51527810092448040866030142d07038190b103045240d104010040c0c10861068641d514104101c99480c0340554003813094a620740403030703045034000030301120044d009038030f0301c00c010b00c1107a000e004220045000c690000d03941c0c90903002c846001805058442e43c0d9141d0810148802c842c2080ca000400f035580c01b0b04200d803006058a440c8480000d480f43d80701f00c44600c1e05403950398014042070070081e495003902d00400b400340f0100a003d001e0010711000302d075480c810150002ca81c140c030b0100519102c15054100340c001540311440060296512401003000d1405065555550204460040d08440e1560b001c0a25070b0131450040000c1c034408a40880d103401070703060503541c9810864981e0f803180b246820050b045850501c1d40003410002020351212188035042448000d5210780069aa9005040e0014009184410f00c407071180c6070b00403c0e803020117849c0100d9070b20 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 276600098 1250 276598848 276598871
    0x415090e031e03241c030c0b071215030b0c03071e1e0e0306160309060e060103031b05030307050c03120c03190b0609040e07080102030907050f011704021003 69
    0x51108040c81001c6004044144002d1020301659614201407004c40d8032001d902e20382c082240c5192080344d40b40080b50a60003c400e050284140c901350980c0900744442c02d15142e00e015184035803100302d204600b460081750428101240341c00e0415a42c008154400d50b5507503074000c400d690f00040c404020422588108487c90489403032042600c5010b450740650b00e00d584c40c048070001e0341c03175000c00c0070424a400d82c00483d80b00490f090790458800220300804400c2d03048150080c103050304001745070b14a440800b44141c20b000c2022810780307100382e440701003140030400e803040d08001442019120760401c0010a20141c040c00052114550755419a41080700c490700c034a0085004a4400c04016000410840d040401213040700f1a2402018100100700105020441c1c07405a24070360344c05913075134a81d130001038502001002c0081c10058000d65407031400341c41154480740a031250500607555072260004560003000020b0400d60b00c000d504a06944036000c020101107220704000a06644500701c808 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 276601348 1250 276600098 276600127
    0x706110c0714090708100e0a110301090c02070e160e0406031407030201030b030706021c110a050c1f050d2004140a0503030a0210050615030a14060415090e03 69
    0x1020340502c0310030100c2c01001400701d0a08000d2110301048030b00301c10001c1c4021213041600c16501040480303252682c647c40e03654028840640080008003003c0000100d558003900070300b025580750303400d40e00c003207641c2c1440040f1b050081c4d039000c0842083e008601e98407481511850a00d0000401c0031070417982c0da0b1a544003011211320f891409400a60040c825540c150040b118613078002d80042c500e691a040009449080a4030080c00d6441d686050342c0019100d0601580b81d54452409d40d075402e5440c0c03074070a40c0c5042704511940640c0400001d00d214000b807000c1001030b2003054036402d2a10301200c3c042801484441000e50680745030030215860403003484048c001074503800707000c140c014420700208400041e00d41d010620a0b032007006007201d41940407070380891f6801c000d01d001c038540e21030800040e000f40c0e040280c00542e00d0044100425801646c001d81c160241180010400e80c5480c0d00780b009031000140529031402080320b080284071791540c0030000e41c80141e82542e0502110410519 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 276602598 1250 276601348 276601363
    0xb0a0c1103031605010b190803160f020303120403020105130b0115450819060f110d0f060e1311090103120f02010c1d0d050d050315030c060706110c 65
    0x341e0a86d9110226412810100500d80d600181d034000003400034900003200d5920310071100d030010700c0e480c1c41620004003c1043c5410b900a54003c083c0d80e110551440c20085440048405034015800c00010807400300079111804030907a000300720841561308010424103500004904602005100d100191110035401c0b0815a00b00030401074400000c005882020740349140c81901c00c0014480c002000002ca0000b1a0350180d082c80b060b00c0b908059a003041c03c010488500320845190510b4101100105c0000040541c8011103804104104818440707508035072081c0075001c4400ca1480c041407842c4031f8181c110388000d01c540e0ba07000d145030003840860140304080c0c0c8200c0304003025000590440d504000000d4420b4aa80b00800404240c503500900c0e900302c40e040d094840c240d0412a10564448030600c2c1d2000d81c102c4211004120500c0740140194000c441d1020f1140703846503981010300d0b022441103c800c200804007030401010380c0380d10b0010890003643d03803201d01040100e020644014440207 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 276603848 1250 276602598 276602603
    0x606011b1203060f0609150e06040f0603020d230a020c010b0d1101030e1603030c02010c0218040b070c020607120c0506040f060b06030603101a04020408060a060b0a0c11030316 77
    0x21403158a0401c00e13030059500b58102d50300b400546002031040701e50b02005650701c502149400500c00040e1004141c00d842950810001c12011503004122341350140c0080c0280c481803482040180148501054001d028440100030290b0b10300102c2e032910400d4014000c0e410b448000016174142ca10f00048450070b20301d8003240d00c03044a01d0440031660309485056569100c0001a284816900030f140c1c480202a002c014140542e1075085825039124001140e07000e580a002c6405680296107400c1c0d06c000c0443c0c084071412100e80005000754030900c0c00d00040b950140106007882e00d00d540d410103100780300034810100190038042038080703801003000034051805030803811b620741090b0410400352040380b1030a500a000c10800e0040c10384001904800c910601e000001c1c0d8108401c11000207a80e040b81d02c1030b4482d0000c500420003050100d080ca014895003a41042400c5e03460b00250310300e00409c03d000001c10318204d04030700820f440150400000c1c0b00103056a00d000c047c4044080317150a80d0300306 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 276605098 1250 276603848 276603851
    0x801090b06100302030702070e07091a0315030304060f08060402070f1a0115080703090311011a130507052505190201020105060a050a090b031c030b100903050606011b1203 75
    0x41c8040e034285615180000c01591405614601d0b240c07101964904003480f6a886138400c1c80700140328280700d5040040500000c040250305a00d02003c07000720b541068038406103503d1100c03080c01052800004071030813a10a03844501c0c800d05c0341e00059038114001170040742c20940030002c02c00021954604500c01c907100c1c144050003000380c029803071803410050300440301500241c2078034034156802c0051a584040740c1e2030040388041003454100e443c041030015481c01507080c050159903064011304901082401a100040d03629803030010641501c0b400e071005400b04008220070040741c51249075a05502c51080002b464405c020790341c15240000000c4860a21103034240d201c411982d0a0103020380040341210740d00c406500309000200d1401d035900c60703e604039550b4902101683c9003404100d501960f81000300142403008507000d80640005900e243c442e03171043c130050203c18015005513080d65000001880d80e035407001b00540e080f41c0500d290a0380701842040c2040020420840300c4450001980c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 276606348 1250 276605098 276605101
    0x1b1203010303090b07031e02010e0f0d1710031205300a0506010807030f11070c03110607080708250609030905040b01080a1a030706021f0207110409020105040801090b 73
    0x20700a03c1444140c201901c104420081440401d0b4082040c0140c1c401c1c3c402e0300765046c100084113034014801070b00c0082c018001c541000345003550120390711040001a880f00c0b07410030b07010314080e0030140e0112003480000b05500014000b1808410700d41e00c1107840e6003410b52a20b0802c4035a00c1301804081084078840200d100b50342c4c44c002020300d2494000100030018040c0741040000a41000001001d40042580c1c840444405c1c2e0242e4129843c1900c9170600f042da2043c0c90705182c545000940001c4d24030030805103d02c2c20303e003801e2044409541e00240d2081c20903600d603481c10200c1d0301041c0c8258283c00c0c030708aa8408801e801c2d00900040e4466400090700c00309901c1c01a040c820075520140c030591500c7c1c09680c0342d0342c0203004168041030804d0000784684542003000380c401c1e5900305007071309807158480124000e900010140d0301a6110341044c1c00403103102504005a02c03030000000e118003e4899074229a08140e04034107900c61050402c28200b94852164501312944882c050b00d150a5840 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 276607598 1250 276606348 276606353
    0x807080d060503010f060303081f1805041a09060f0907170c0405070311071104020412030923061803010b062106091b0a050c03070c050f0109060e061b12030103 70
    0x1244502c0c6000717050080c04018034545000c0d0085100502d401441003801002d1030758401c040030a036003e400c59041d107000c000c4081c210303c401004101e5084910303030040d80030220421011403c02c0d100d0040740008050f10380e51040b0310004aa00a80b00e4602031003010004140700c0c04a41c1041c91a0110300300406410f03604000300403c0e1a00a020141403526200a6102104c05c0f0780440b5034458121080c4013010b00c544010034024811036004120011840b2074136802c140e4850741d07860840d03243c0504202c8642460040c04010340719003070078952128040010070704010f0143c0f030007240b000009000046402142c400318150703070310481e01c88860300c0200d044452284102407e240d00040183c03a66922803806034450000036040d5550000008000f24203c00c8e164410b204440341c1a110700156500d806842c501a40102c003580101c40c45620300070070a24117548503051040485840b5900c40c5000c038a1203040c000c40343e004041c0c26005404400101204d90f0003008a00c000902182c03c1c00d40d0f070f44c07460 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 276608848 1250 276607598 276607601
    0x3030c031b15051e16020705031e0f190609140607091e0302030c010503041e0c0501031404110103051902130509060109080606012006091b0f0901120807080d06050301 73
    0x4d282059510790b1201100c101c0c910f44030143e0303000c90071900204985403840d005a142ca04154040342c1d06114076441d6030010312640841c104c400345c1050880389a242c48030303a0741e511100c08a10003000c0e2800b440300d410100d080c0e5041091803900803003043c0c2c211403001a603182060403c80d41c80300800d280d6402004440401003e03210645c1006101f01c42240c02d503030000e03071500c4080400c81e0400c0301c0400442d090011512685035054203121300c24194201a140c01042c0d0750081c840d8601083c503081584920b151146a02c038400ca50003082010ac240d8460b005400070000600095200c1141090728a008000c41c802000800500c2080c000264a04030030000d80c100010510760420442d04d8042002d104005049a0400002d0803d000000340d1502400240110821b6580c8140308507014807442c81800700e4261103100f04a00803503a1100400144141c081c005d0702c1c1ca035040004174004212801c90300200101e960700c2114142e10704952500c61941903000b8481348c51047d41c0e20b0004200d9031509 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 276610098 1250 276608848 276608851
    0xe070f08191e0f050d02121c060f06110607030c1e03061a03010e010812030c09011211070b0c030c0d0b0609100206090f0a24090501020a0302040f08070b0403030c031b1505 75
    0xc030700c01081c2c41100248402851f000c2d0223260a405c460710580c803280300005400460140450480791038440f070799031400608081c15240d0854042c01207102141405129018039002c8072030035210700182d010240710041885404d02e950104160781d440d000b09405250b4691310740802c180909142d10313541800c20f90781100b04180d00c100403542c408840051518000d0040d6988110380c1348000752034440c9100140c0b031654017038649408480c60075070100481e0a01c4c0e005004814007562420304241d1b16403030001064401941c800c0c281c400c0c140f1a02c802c80d4074642002018010181040c0d090005035404640c055149100c0c0303c01680042e0304000d80d0b44010081170580c003561800074440c08105440f000c507080d01c401040c01150810a448c202d042c1d9040e0410003070698840002c55680403d001c008000390006e0040540082d0007000000b068500001c182041d507041e01102464649980e9081c1c440001c41c2c0c0c821014002003000b48403920002001180406001e441089000f02a6140280450300e0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 276611348 1250 276610098 276610123
    0xf06051803010603050c09150603010906230a2108040807081b0a0501030b012609010617030328050a020901032307120e030d0e070f08191e0f05 63
    0x1403c2d00130001300700d00040600c09100242d03440072058480485441c0c205110040302d580100000000040d0305143e81d200c0340448041500680c5401d81240341d030f168040f402c0304000d60000c41600d05000c80c40d13591008040e0440c02e000a4180b941442d541c203c09034209900001d02da401404040100300f60602410103000002c68640810b0107068002a41003c158010281050b550302c1600e05c1a9000f016010041050641c024200f41c00e060095022031004442c40c10b09542000300028482c4462520000070111800195007107a0345c840c411032600b01040540d0b9403151603281c1d0001b0544552044038001c210040d009643d40d540c0500240640b0100c5c00d0140e500ca18031080d500c00c42c041d04100381c2d08900c440c41c04144a5144d20318a001600362041c1c0100c05020018072082c04094590211b0f1116643c58103444c1c400b42d4890b4171581025041c4205407054100d28550300d218440a01c1c01c20b182441050f0000310004162294102100c0000089480c00a000c41c0ba6007409401c0003035003003440 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 276612598 1250 276611348 276611351
    0xe09010e04080304140f0604050c1002030f03090102090a0306090204060605030606180105090307080105040218071b06140405030706110f070209060409020423090613020111070f0605180301 83
    0x145440a94a940c08000303101500011021004c10204400c00c142d21807162013050496002c18034013001d0688400003610100c0301071048400301c9800d414107001503c0f295900d900658148280c0c0071821440f948018100c0200d550308228101c0d182c2d44606015016501500c80010402c00c3c0340b05000072103072140c00c400142f00040c802c0026641e0743c0b00c11200c00d2f290042d100c1c00d00000000041e222070140100300c6901d80680030b0b000c98040c505600c542e114070700849803018000036035610884441025150040020401c081078100b481d50b0758020208284210800681c0c001a01c40800e20b42c40199011a034603000010140140a214002c281c2c000c2c10110309076181c400c05c0703000541d0034402c2c0d6000a0082c2c144c64002a00c0c2e550f03540c020140a9005030050026208030007041428810382981c11400c090a940071400241c4005403082c0f0410144015074046500380e001511440360040c1000c0d4070b4860070030040b071408008083e1200608880c1c0720b054445058407844501c04000c030304c5485c0281e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 276613848 1250 276612598 276612601
    0x1020703020a090c0c211b030203041a04030501050f0702010b0a2702040b0304060c080702010e070b0702120d08010911070f060b0d0501050c0310090b090703022a030a0e09 75
    0x40c1ea80041c18001c0390f04146001401c4015074100355a821203040300a4190000144901e100c188a01e2a019074010f10360b580441449140400c00c600c2d420002c40500142c0c0280300521200b0481040f0b44603889a820746e00f42060fa5941e2010b09660040f074200c0302d002000d105102d030844e0240544401000e040700c1c403802c220b0610489145050010101d07090a4000c00c103050f80042d15503049402419180043c036070f0b41d160034281440500030081a078400030342d040b80080d420798418461030b88200381840c040c01d513440c94109403a9040d0041c610599100d02050040d850840e420852440c001002c1c2c1c907850b00c150303d00b030820000c99804403007a6030703075031001c01407100000c00c1c020803004803603400070000601d03004001c0030824154603a000246150700c2d080c1802640d5105201540c4074103421540303d00b409031036800d0241901c840c0d001c4a45c1080421000c20f0605010360050506941c000d2001c108243d607521841d440000d01e448030900503007000a041c20110b92182101c040200d00b0303189034045 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 276615098 1250 276613848 276613853
    0x340318080d0c080a0903020d0b010e1308090906041806150503030f0f160f03020619060b03160e0d08030f07090503100e1005010b03060306070306120209060a0f0602030c0c01020703 79
    0x307104441800800f10103002030f014662a002c0c090003000341d40c0103041c01c0e19403043c92a1030b000c407800038000c001070190485c00040341c01c1ca0000030485103030752100502303061082c40c00601014450281409a103d9100c4025100e08814980601da215000d030402080d950200e142c4180140d0050b00218000d030400c00000e4282c960103022507160340c2d268600d0b1a552080d0700d00e4600c1c0170284040003041508800111000c0c1680005e205018800511380585c16072541e400400444a05124a014060080c00050801203400c1c40083e020040c500301071086100850008100041c1c2000444180764040140100d00122400d41c960105c240e00301a4200750900300000d591381a802040701d0420f45845580d0908001400b11060000450340140095615586100c1241e0000c4840324040d20a8000040c40d903442030203400304940490316400e007520340c99000c1c003c030300364010a85034200513024000508400c0068650001b06000c5d800b860300c4180300b0250504040c0e21440c200e0440d071102d40288003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 276616348 1250 276615098 276615107
    0x40203340503010e0705010c11041e0b061c0b011806030f050612060402090a09080318010b010903020f12011509090506090d020d03020315100e0109080102030c340318080d 75
    0x41d03a1b801d08012034840240c0c0317464058620400b2455410900f002030700159940c101100c5104000403c200f80504d041c41d80500180303001d113041c80c041c16098441c4c1c3d54155061a4000d036001c400602d00100416051746002c20401070300d81c000ca0009584d0040d501c4050400c2c0b0946400c030004a441c3d000c0c01c0e045003010340c0d40b20f00180c0f000e44a04028000b290940c4829405085261b5205d0011501e84ca80f25031440310708410b402400c1c0b000d5003040c030380c104158030032042da40a603607006164501c0c006242090003522501e0384641d0314107650f0303814500c402c028010507510042110110225522846250030381c00e01d000901200156030083e2455000e035600441e91000c16038481c40c00584a5a60f1001084209003420b24941c001d1036612510b001c060788281d40c0b210550081c3c80300c1c8000c95480444a080344802c503540703035610000380300380804280c1101001c0105002100c03120b480c0344000b0001c2c0b02d0b02800d44000c402142c2c0100d90a50b9a0b0b18803401e03640180035a40c060100340600250244c03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 276617598 1250 276616348 276616363
    0x1503060f0311010c200109050d03120b0f0618010e0d05060f0a062c07020d05030a0902030106030803010b12010f051e01110f010906060e01031208040203340503010e 72
    0x10042c144021000032241d20440c1407040c81500906424070151111003100d07001ca0f00c0420480c0054101000485c65062440034450a60740c541c0d95074483c855401100f8008244000249900803100081070b0b0745030390f407074001d010309440b41490319100403d20b5001411066942c100640a80e901c040384001207000810607951244105079000b14507981c0b0310a480041c499504402a000400c401c074049510140c0e4101190007180720403030000c4d84442074141d81e1104a0741c0340d6400210b040000500466032038100f200441e01c0a800410074640f20396a41c1180d800c00d800c6501200000b142c0c00d0b44042d10001c000d80140084517880c0810303130810020a2114580c1001c1400c0e01c039810070700d0107890344200400c1100c40c00800503121a1105029414080c0c451401c0607602d0f581003110100710010250035450480354400d181c0c0e030218a004c2d40980f5a004000c0c070aa03454010349044000902481c08280c800415880400101c0c0e12008460081606580c01060081e07240107621543e6000015455 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 276618705 1107 276617598 276617603
    0x70f1a0a0c081003110a0807080604062306010518041803121103190e06010b090909010b0a12020a05030d09050901120b07050d15030c1503060f03 64
    0x12240b214054404001062039504100300244c460a00c030510b8680c003815000c841a501c4201a08110b0183e01031045900718604110402c00d0f1407050a0024080ba000e40e1041400e1180d8400701d141c0080006043c004000740310007410030020039003121703130a0051081c00110318164070403e484240090480104120038642e120500080c0140780d05060b00028441c1540d40342c40c4144007541d400000c5100c4d0b640c1ea4016000081d0082c8840c1d4003030300c1c0314821241e494800000b030000200c40203080111a900d8000385403d140c0d10400d0301ea086415621000603401660300008000c5040b03540010b03450320519100606158202d900001103a00031142c4402d01d030390b10150110000c0480380d0003040d5004260000e07540d903000340301428003174140c0304000401c40c0c0103541200302580306820941e40102104010801c0d035410b040010040f005d10724040c840c4505d058912810300d640760100 = true := by decide +kernel

theorem cover : BRFrame.Cov 276438848 276618705 := by
  have h0 := BRFrame.cov_init 276438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 276438848 ≤ n) (h2 : n < 276618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
