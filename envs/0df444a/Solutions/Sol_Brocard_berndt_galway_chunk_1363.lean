-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1363
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:35:08.475984+00:00
-- url     : https://prove2.me/submissions/07c48a59-d4e4-4d13-93b6-123c4c8ae1d7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 244964028 ≤ n < 245143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 244965278 1250 244964028 244964063
    0xc11030a0215040513020c1c02011b1815090915210201030b04020f0a1107050a0f180b060f2214090a0516080403051e0703030e0a0503090409 62
    0x94000b1400904010079210350030001080980614451800e1941b17106002050300b0b05000204030803850500d80c5401590926172104034058400880005c01100c8014100010030ba4030100c0c00360781c0c001460101481540310051460741c078902d00129000505100d40600c0415070f150f10105a0341d60701d583d1004655950010105c0e242000e0b0b01d81d5408040760055072055503018090005c040c1011a82189800040b8880300307501c8c06044884010450482c1040e03841030700030800000980401010008555511aa4801c280a5502407413054499003942030034038030032500070a5200c800c000c0400d42084411036070baa9040c0c102e8111031940c4062480c05a800c2004520a880600b003541720890078803112304240f00301c020003d4154901c8030b281604010300c1c511121040500241c107490300700210b40721420700300d429010f40140c222100c50003148031100010340744010300100344242c600348084103900d202c850315102002c5029105070401c0201c100d42d46440d5201713000c600c0c81040810901e581e941c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 244966528 1250 244965278 244965289
    0x6050306010f170705040e0702160b0d0f02121e0103050304031e14010501060207061706010c1407060e120115090f0f0e0604170403050d050304061415090c0a0c11030a02 74
    0x1695404e000c90030028040c0520302915500c1030780500b86000030003101500801e104601500c903c100d10ba0b40c4000b151a0b1060714003a08a4420b805003003000355152152100c1610402000340d45100d514444641c4564880e540701001904880d001070103107040c40d280d80c43c0c0f12080c98074182401e078071100f40d10061000400c00001506270f00c25041c0002410b42c1061000780c45c091540d0408414083c8a4008030242c020022046522120a1030900b40040c02c40c9010142c0d040c0151402c1624080e09c2c60210f0220f50110500340360800c225840c43c50a8a0190041d0807907100c2910398a0074103291505100c01c45454004a0402900100c00110444000c1000c01203a03000005034640f5000714060100340200307945c100040c3c3e5000400149407500d955641e0381d64040c80c000300e109000b030103c00030302031001e0f82c0d03c00e00080b076017040302200c54035003c024800d00c40c1070303078219901c5500e51102007009014003205540c0065441d0f15401d051000e10b031aa03820030386030681c201d079061103000840700058841 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 244967778 1250 244966528 244966531
    0x90409051c0e0a080307110604120813140d111201060602070f080d0f030507030209120303180304150809070807080601061106040b060909120a0c03021606050306010f17 74
    0x920300074400740e01a44030080008041c9804207105210900061007440d002000b21110350380c4c40b02e4000e5034000f1840200d002401168001c80690000c40e6040c018081c203c40204045a00c0b4a0041130366a01c90071303a020840c900c5024160403640150b00280001d250101304011380c2c10040c0703540a0140094802c2d4203580b610340102006070480c2400300000100d25009501130000c090251035420341c070f004000e04c4841c03907038010420503440354045105d8a001c0d904440300c90802a092189100c0600940c6550b40d00684030748640d54071020700880f0492003c01601c040d5140000900404041f0701401c803030354800504a03503058014003200081100c02000b4820040c010070f000b40c07034550b242030809410f100101000c208940c02213000c100001e114621030551002e41114600050303240c0d800050300e011142c00c8501000302d030004080408a400121100f03009109074203c0ba020030408107103070400341803445150041281031010074003941c021005407200d200c407450108241e0605011010a1200 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 244969028 1250 244967778 244967803
    0x20303031005040510030206030408031803210f060f060a1e02070e01061103091e03060a0203190e0606010e1903150c110d0e061201180b010c0f0809040905 68
    0x75950000c0103181824043e89912900c032905c50b510701455500412817034400180001d042410000004110f14182e00b610000c01800c002100c1d1504c03003070401034440c2c000741d0494000c0294040d001900c88201c9460081c07080001401c8140c03090b4061084c0000fa80002810354288900c150424501c190410801c49450741182e0040400303e15107820316a86003c181c110500f00000303004942c1403103400004940558009445d499403500d0002c80d1740341085560190264980180020300881e0041034010314019182082840c280007203d0104408a032411070030108150407002c00240c0c1036010310700c04040030002501010000800307411100700550140c0040710646001400300340450f01038403078807811784a642420340d0141d54010245565005070b410200401c07000c044031501989400084d81c040c1a681c0150241950310348a8000c405080104c0009155103401e007812065881100a8a8020341041c40852041040d07100e45030640d0100c0343d02900a070311140890b0010703100704403107880040c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 244970278 1250 244969028 244969051
    0x10050f04110117010e131a010602160302011b03050f030a0504060b010806011e02010608010e010b0301140c07080c0a0804080a02040b0102010c021203360c010306031113060302030303 80
    0x40c061074026401c20722402202e04101c10a4001e000941c01c840240f4159412a0300c240c00342c1d0b0b926159403076000140e40c40100b280d030b5404040804200c0e6209810f050343c4007502075030846241800a4a030000083c40080e000510300c682c615410840d14000311507850003403400034a42030034440510000e50003501c28442c2c0700d90b20710811040c4401d62140c58485002464445d2650030f10740d00090410301105544240011114651004607000754080c5d0001c0903094020301c002d41c25818854002d054402c0d0050095082c960195030407680d68007124496410082103a090203001e8448403441c1c0c04c4610050304510a82c103c0401090304400540000c28011000f000c5087c0c0c82d1052006440802044906684c1040c5103050203680110700b40428020050015840307a03100c00d904144d04901540601c114034402001c2c840450f0101403c604500361242283c0c1c041e4002001113088503164480076144424503013268500380f4202c0e020343c0341c00400c0d020200300180c494000030b0031075006540008122 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 244971528 1250 244970278 244970281
    0x9011707090614190f02060a140a0506010201140a060501090509091207031106040b0604230601050705010f06080f1b012c211513030c051507020304031403030403021e10050f 76
    0x1590304000e05a4000807094081c400e02d000000c00a601d41d10140ac1103075140d444400040d03141e40300754442009064200381c144414100940c6006c0102440d001d200e00003200c00f4404109818802c0002e8010003c800050500c4044034003900895000107400301c0400c02c12040340c0c0a032140070840319001e076025603d0500a411b06504001c2121180070032014454545c00e0070786041c52201c1c0c4190760040c400c0c241165902802e00e4994014807010150b031145d0f514200c0040340000d0300240d00b0034ac100c0114121490750007041304000c0134181c46015a80040d41d0000c801e0707030714861031455904502107000d40b0141c0d4009503001400a03030014021243d000035001199000d00d408000b00304140ca2011001c00d80c80c01d0045a4064012002202034180980c1c194000304000c000c000e2580c0245040604604034141a003000352a0750107440191140c60340d450360342000440c04402c8070b000e15031680041a50324082d0404500c0010341c0034008006002d6210401107001030340c0100d5106a840c2440c11529 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 244972778 1250 244971528 244971557
    0x11107090c1b02010e010f1b0f0b0f0f04030c0309090e06041203090c14030304051302070605060a05060a1d1002011506180314010615050901170709061419 68
    0x11100c5039980c010704a4020340460144c0d07042030003e40514404e103040c1d514560107503001d0303900042160350000c009281c405040140204681c0700c00003244204500d5013036454462119005141c281d0b0340420010707100c800315000a004031031010404c0e22170f0130041509540d076442c0c1400c480c001c41170314605800402c104001c1001a40e03201003180d01c1c90904000d42a0075868808103400203010348582180c00d458100035a41e410400d881c0208402840200003420f825001c2010703402040044480350f00380400f0980e603280540703101c022340c2c8000c0c1c580c904209020004440400c200c0e558168010900d1403501e80c0b0f0f854159601c00c0f2401e180c0c001140c1d42000900440300d8072415440751080200141140c045042000103120480350081c0c405200407844940b8a4010465a0300c45460054000000b1020f2340d0400043c21900c4000d0300c1d1040c01c01c0c106d00c1c41003a03040b411103a8400040e06070409016250040d06100d5017504981446070401c400c030502000355aa041c080600030602d450107020b038 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 244974028 1250 244972778 244972787
    0x1608010c140310230402040803130906060f120608010e070609090b01050306150d060f03020f0103050c03060d060902060d0204080f0a0201020d1101181103150606030114011107090c 79
    0x501110404610b807851800c450000070301e0400780203000d921403901120740454444000d1030410404018011542d4940d40c6c10700940d254024400094500420340300010303084101c0c852482100c041381c0324901101c0c103a24048a000011700082d0300d00680d42d11001c10285001d201d15264622008003e06000e410660003074105244c80d80f00602c411308200d89014642d0707019082d2500038500303503102004241001055400c9001d00030594004600d020b8000a8100c0c0b0b0788010801c50f40255101d00380420000d0045007980c0080700d144c1040746041010030014101541000007540c000c4400103000f44c00c2d40d00182456000321144803105801240511480405024413a040c2c901400105800003103680040c0d01d444000c0b280c9028481440b5140310140c100390810b102205032481c007007c00900320305e44401101000ca4015019200d03011130326a080c01050340c103502601000f8840b50550380317030504094a40c828500228104201030041c1d030451141040010082e00325000c01242e14100020010b1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 244975278 1250 244974028 244974047
    0xa030c06150602010f0b1c0b18061312110706050306030f030d09030806030a15110912010e0c0d0b010b07020f0904080c010b0901120311010204051e091810020c1608010c 74
    0x74031411010000340c1c1c00403c1c400c016003000e40d00a00d81c08c13076656862042289400161032040a074040d160801030308841e035840d01d0311420700c201701e640032650491b002164820240c20010420b503100341410b11507240031b44003655005000030104c40c19101200c0b1528219040b01d8000f4603810303112101d074003c01d41c100c1c81096100105038002c200c284401d403203c4400141c0040d15a1800350ba90116512000c01e62048460352000648081c41210000c100703e070082180080b0100745000304090031640c1d1404c51500d10b41c41d6008031100e110b0380d08018204159500c00b06089078842020710902409031600507800744940c0c09441c03010b03101c10440c0c510600f03484600d850a0301c120007100060026000d09082c041e8015054a46401d00c803072405903e03030083c8150703080320b42e00040c1442c079020f64112403d50390755000b20646000c01c4986910030303105181d42c40d18001400c150001880491641c81075400341100304c240038100c41c82c7e2000302040d42c0f40f0f5503054110301841d23510381d84100021900f000551 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 244976528 1250 244975278 244975301
    0xf06080a0f0207020604090207030c060608100608030903070b0c0106031b030c1401080a02090d050709021e0427060f170f0606010e0d0804090509070810020702030a030c06150602010f 80
    0xc1d4030f00354903580012650f1180d030007a80404d48d404500642410b01c14600c3c00401c5920160800005840c0c0e074a00341e4410b84090541a030701d05141e0301243c219408800e07280c0d1288058028440c4e90304200b41200c0310340007100d09444a642c0c502000012681c0140c03080894520078103400d20050541c00c09207003040807a0040c1c94810300c14a0081d00c80d0341e0008140394068550b4000680b20008180003500c0c0389004140581a072164540100d4280001c3d07008050804114000079100c12a0040940607402203124100c1c116210070401080500400c5410010103a8541e00041c8507807519040c050a00071600124910718180c04010900e2a042001d80a01c81030840180481d1401e400001d1000c518100490b00a440d850b80701e60800a00c8025240906080c00c4240004e18001600a5660105103e203001611807084403030800303075240c4204c8001d02d80240c0582188000e81d00d090700c040c51130300d0084403016614000a540b5550305040c0b0009020b50b0350011428402103110b01003503c901c1c1100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 244977778 1250 244976528 244976531
    0xc0903150e07090203060f0d080c100e0a08030c0d050106180501050909011a0d0911010f0f0221040503010c0804060c050405030318030c10030b0315010b0913060f06080a0f 75
    0x2500440c1070000d41001202c04196026a80359206004514000030410f17082d034200b18400c010800b0441840301400311010408200c440c40d13080b80e5803034002e40c1d000640001c0a600018445d00115145200640d03100140c590351a01d4507a200919004a0313209910840001d1090b01d004225200620360300d01c01031500f440c1a0341070421f000001400f0307130b6061040d104604074140400c48454400d0701603480c060350740c1c40c0400444d951824402d55682c1c032020014001080c0c0c0c11490035290280100500004190780185050b28a0300c4200c0f20402c400208689802c9080c00300081070768003400395018181c05591a05402e0a0524002040e6a12109030b074062020a000c28007082d10004103031524801c17002c00c40c0d0603501001e4040b0b42081c4000c041181c1044012812140c040d401d40c000b400700800075401c440444c00071503155180b44500380100a0000c1c010030054500745402002070711248544000007990a07500c201c0c3e4901504603078410004500d0400401c10301a40038800c0800040300c0750750 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 244979028 1250 244977778 244977791
    0x1e060415020c1015090606030f0605040501060807030c141b0105090d050a120f02070804170319030506120f0c09060a0509060904030c0213240311010e030a05010c090315 74
    0x4090f841d5040950154669661403c0142d4a196a10389080c02050040302c10401c6540b2002c0003009003245a11002800d130810900191030705040c42080e040b207080d0340e1103011076111000120064030444550804100250b8002e01c2048140c10080c108903022400901305182e5000505094980c002c1080015400002c1c0c642ca11581150860384281d80c58540a07124102706203209004008006552600350301c08a40d5104100b012401001580c12807400b1119203102404d00c0c079540d10501d4915481c40c441410780c1d000d814002d0700300d0f6400c000e00924100d01c0e400d107030122514054445540d00700d158410b032010748860409005880c2c01c980103a401601c00350500010451071072018224a018166080014043c14844c48070361168950080c540319460b0000099070001d01b02091051140b03201b40040c1c3c0b5000008040460100c0c1d034015010104585020015248a403c0046407038260182c1c0b0010741c00900c080c82042030241c290b4072102d40c0c1c1425414016008240f000800c212a4900300 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 244980278 1250 244979028 244979047
    0x30115180f1205100203090307030908010207030e060a120509010c030b090c030c0307020a060204120201120b03280f0507030c0b0a091802121006030f090804090e1e06041502 76
    0x40075500b42d4000c000984114040c80c5421031401441d074969899191001c4140940408048000c0650600964802c000b003078540340c01608074410300e1001000f05204550110041c1000406094149124108041070280080351041072ba0002c546826159545c1c081c0912402e07050f1140140544050711000700624007031000e411188000b030680b40b820350300400011200d40c400c211015400e83e000105540b141c1e55110050741e981c03e00c00d012070200d003211211082d0b0300098424515003041c01001001000c50341c419403000404811000b800c608580855400070402c05182c076000640300700001c2000a18506080c01220b540b5005810752003020091450b40750390080380700c404d42d011020324812050005410900030320038001d40310741c4045410100944941030281083c11a01030392400e214000714400500c088800c82100140680014003051254843c5648404103004501d0101d402c007031444841064002c11300700103c4260752140d42003008124085150b02c20b08444070400f5400d040050 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 244981528 1250 244980278 244980299
    0x90215091503040611070c091b3608071d0f150a030b0705090907050c0312060d05071502100b010f050a03110c0a050c0603060a0b0f04090203011518 65
    0x20740d000d04000c04044003240c18403586a100070400b80000020640e104918a803072682c42a01e841074a85140c40c0140030308401c4504c5030011414501d9944082c0b410303e00d124021466036603103000d0340c3d10818010078148883d90114511025089240c0286980c0c2d14085455800f0072029040c0b2074120803030424803451540742000d00d0340015851490f0352030887c500780402c801001640c0041c00c1440c004091001c540e4200008000340d0a042e50110850396480300b00303564031301c40c40000c80340c6584104403000c0441d503943c02042d000320009000d11414000d40d00c0f801d14100c1c0e19085644010701d03080781800000c0e0100840c040302600800305000c40c40c04031001030f190800003002c0c001070040020b900451179110341c1c091000300d80325a40750b07512181109a00395503441c1d070309401ca41c03c0c4911070340300c01c840c90808103070382c46003c00814013020a4100049522260040c3c11181100a01440301207480e000c0e41c00074501803d0a02007903600c108094031f00800360144800800f030341903503d04040c0300c042d038034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 244982778 1250 244981528 244981549
    0x905011a070b0a0207060507090306050709030507140a050a06020309091807031401180b1b190f0203040b03160e06030403020a080c030408060c040303090602061003020d060b0904030309021509 84
    0x2c00c00c0c540c81d0380e54840004010784100d1074010700c0c081ca40010044a1b5401003600302c2683c4c000c140c03c104c6c3c0d60300c6c85004c0d6466549800094000c0d232154108000301c00301942001c0034a00003600a030001603468011800c0c42c08140c000314090381021403981070340d041c0810301c01d034008a86500c00300e46d400304080c01034a0b44150f010207003000c005401601e2200a0940128140440420100c010032809041031003090009450110740e4070580080c0c0210b2118603001d8640d076020003440c40d5072001d0107031b40644594221204602c00d6020034400019892100e501851107124a824130400000c0030050041004940341d0b12541b08000600601000c13aa00007400c40740d80d54414810341d03598002920b41c6107180100d50040040f445840101f06402c12448040c00459200c0e13162820f400781c50721000e82c2c862508445010911015a00c10000340c54450384022403513018000000360002000041030740504103c1d1b094001c03e490f91184411401d2981c04030601d140054089410049090005a545200d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 244984028 1250 244982778 244982783
    0xc040b0a050706090f151a0603160903080307080910060617060f131b020c030d0c08071a04031206151d0306190507181806050402130905011a07 63
    0x1054401c100400f9a01098406400210710740c200381c0145040701012500c0c101e98000b550034a00450809119128000400d040c000c240b103056a440c01c0d0070600204d036890141081080440001000c5502170f001140501142c3da1501d4251034220450f62410b500080c8010542d450711038200000d541c0024a000e004590444900707503500d41500050181d00c840d4003440d44000040c3c22288880c640381d0110b82109410000210f08801c51003050f03071030309084030b0030340c0d015004541d014404c0b51080c05414010f510440c030300e60030008162240f9100e00d200c0054850040006014401410703008200e203040481070718014031030141040040030b6010081003007a028090b10760f0546008481d121100c01c110728029044820918040341c002524600c0041c55010051074000031440381c900c54289a0500c000106240d01e010349071421a200d07100c60708000e00e42d0f6642da100c0100780e691313071800281056800c1044070740d4070383d040030b00740d038100da6042c1e01004813040c503403010b03500015403070081d00c82840c1c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 244985278 1250 244984028 244984037
    0x6010e010f03151d010b0906090f0103080309031908010509060d170705070302040908120f060901060c02240417030c0706140403050303010f18050f0a0c0c080f0c060c040b0a 76
    0x902d5400200058202a04c4284980036210f8001c200306505601c01100c01c0400c1300c280b12107031255000d2008622054551403001510403005102150300f1200a41d0411140000c0300e181c8150210351807204002903007503070000b60801004101d40c0c50580719594022100b20743c0c031100c503401996450341a403008400791a41d0301c0081039560602a05014010040d90046c0051058107043d2403c9503103540310305031041c0c04401290114400e80e450642da20320a60001c1c14203982a404e01c00151000e280d001c400f241c2c00344090401d806800310070f914510b42410030701d0146131514213144c1c40303161041412008001950090018100380e01e000034640c022141c040c280540ca08400010a182501c40d90700054102e00c000400050070f241e10085070310031240b1084103641c0c103880504042003a07560607241c1e55003009030100801c60500143d846000a0155070520180a059554821450303400590101c0c54990010400b40c50940301030109a0703110901c0390b401490a42441002c07400c0d0b0044800300400c01 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 244986528 1250 244985278 244985303
    0x2010e060702030105010803280903110d050a030206190b0d0803070908060712060506190815120a11030d02060403030c0924020c04050c07150f090b040506010e010f03 73
    0x1a200c0e5400c840805030050000d000a40c0c59035039603a542da02440b207940c044001f0b40d00c180b040740000400d040491302141c0c1e90002d840d1030f42c0c4500011010110b0803a0344a01021100300002d80f040059441c4140b084e00074240030b00d403d40c40d020000202c0c40c04a070903a400d001404040d6542d0200300400315074803140c519129103d01404580951094204a10502c04c0a052124240d004883e0043c019a0365a00340100c40c1c503502403102c03501034a80340c0300e0036200e4400105242d60203202e40a41c8035031400400b41d141040c010015100a40c6584484403940101800d00240522032182100800055005101c09020280000d640f114002d00140170150784400c1a2007070b40c450340540c030041c040da1411000c0b00b01800030300c070198040305044a01520410b80715001d141020300450740300700e482c2803016003080c525445462100710320404101180c4c0e44c0d5030b464003150f0703092b1040840141c02031108181520307207031514918080c0181c00c550b0305030000b01c0041200c41c01d841084070640f640300071030301035a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 244987778 1250 244986528 244986557
    0x609060304080705071d0a11090418080a030f14060a030209070e2709010507270503030f09100908030a030f1b02060a0c0c080d090f08040e06090a050f040201 69
    0x303030040600040150041c4100055440700050550540f110f286126286c40e48070304415400316001e5103884100c0c1d036020312205010b03140590000c1c80e00c2480c0284203883c0d41c403030780e1000740a034800d43d9a43c020a90b01c4010805c100038521030341441490020403400355041040c001108080d00d80b2009100300c01c040b00260000344250907021004001800400f01014681400301c11b85282aa6034080000710034000740c9072070030501503240a041140c58417144208652522a035142c1c12000c282c50119150310b000407540c4041000304010308800081c03503150949803081003a4964441c246804014420006111084020040703030100720503414005182c040c3c04200c1400340c80035001160700d0181d40510b85100a4000c140ea0740720f4480d114040002c001c4465042c3c0b900503440802404241e0700b0b00101200000ca0b510030302c030380c0c2d016407904840d0190310b84c0c65010b40d074059004240030131642c07010b00509040410010b5000312000c4020700c001d20742208a614424001000a410060b019004d080d1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 244989028 1250 244987778 244987793
    0x3020d0f081e070218040c0303050313080c01020307110d050301050427050c01020105011505040302040c090509070302040801181104090c0b070c030c050a0506031810090303090209150609060304 85
    0x14044808030840e03944000c0404aa40e0343c020f14400d0380a04840c2c410760407188807407044c2c81c2c4501e60082480b40d10905585048403241c00091800108a00700130780325020410702006004441078100001d07a681c58241c00040000b030700d08a03841c0491340111403100b5107036045030940e41504c0d010354000600c0003d1085041c10301c00c0035172074902034000d2000e110043c00004a01902209401c2e00280b2450f41e0301d00410a41000b102c004030700041f01844144018a00340c0c0000e11510254503200349004d40b2140052202c0d802914208080381d40000c0400c03001000b0b00914200504d010150300700d403d91034540050221501c00d000380300e565900980010404074072080d8000d4400035000940f14850381c0f60444c6200007500040e0380e4505400c3c07001505180c45034224055074800b502280c00c50700e41d048030010350305483e0a40c01660144003030303609155515100f4820034500903078010600c50a140184241d81401400c14203240009850079680741c0c58110817159005016640c1540e41e079164281440c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 244990278 1250 244989028 244989037
    0x903050d030506130216030e120d0e030f0d11011104120201030f0e060709290a050c0c03100f0507081017010207140721110906030c042c01020403020d0f08 68
    0x100078404986080c59186c2a0280440a0712a03255501d40603500e0040041851042182c065217070b01410b81a02c407075101d244401c0482c0c60140894442c200c0d04292903082c400d0890500b0009801c0006041c103001003405600c40301c400e880c0d5007900c1d141c10001a442c2074400100060305060f2143c9000500e028542d00c40484c9040c8541a50040c0c02c001e000107000b8072052290741081102e60015801ca4a0034200d01d00801c426019141d01d4040251400e45003600b024680c1c00960003900900300d8070307490601040c0c40261212500040c0800519144802ca6001034203c104001d495010040002c0e000030ba00e00654000f64880f0030700e010700c1c12085002e841805002402a269500c911000004c00200c50082d100508044c4844a1101a00708104a0301e0000a010252a520700210600b8110600358000d00050266410f01c2071310030101d801d98010050b55150080c4c82907000d520310390010200595084048000d5113414a50f07000148152200e0001034040042e010300c47c800c000d280001c41c5c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 244991528 1250 244990278 244990309
    0xa0311030f06010f0602210409111903020712080f0601111204080c0301051b0306060a140a0c11010f020a0b0a062601150305190501020f0c0705100903050d030506 71
    0x3282c0035a16400d100d66012560b04c502800741c441c0801e040041ca00505400c1c251099000b0803c2c00c251401c4644809400b403044452007076082080b0f4440301d071202c01d038940c40019407a100903944065602d00000c804200d607a1840403c040d1000380606000e030144402e420440074a00040e01940d298075050500e4240010700c080c0340f0000400281041000c9001480080c084000f041241e44000180c0424444503442408040003000028200d00c2c00c4006881000780d1440c01e80000345074400011100d82c402102c1c030380840d050300c40f1841003010f50044099680402c0c078000440c111001c10107552526001e00040040300c07010300080d04c40b401c0d680890010b15180301803c101445031540b46142c52442c0e850065503500b00b5801030442d42d288100380089950000092920300036503c414002c1002940e030464403035400308005404900381030058091402e05401a110040c40d05042001c40078a040c192018801524030804c0071030008214211108428100800c0940d5018005002501840c029 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 244992778 1250 244991528 244991533
    0xd0203030a0309150c180b1c0c17041511180103180b040b01031b0501091514040f0f052b050c0a060e030105070306030b07140f0a0302071509020a0311030f 68
    0x80803030050740008205054107405000030140c07070301c0d00e802d000d03d23200322050030040f0085246460350301030007940b210310701441d54a80007a41c0700c40100b140d044042d003560182c0b42801024a880e0706080f051191911800030800000c1c0340c40c00c5080b186400b070015155050506654102090f00c044010458454a03984200999814601f80c60042603218081c0000e548000309d01144040d1100d9000428044e504141c550035120b40c903051790700d8203901c20b680740303141000001116070300000580030162014010301071080c40038504101c51035080020b55884140301d440701602501d0380140010403d030766146c85d185006074022203820000c2c070341000030001c2a002a01030000151031644034140f44160741d0100c00038441178a0340d000882c01d80d4014000034005408801c089980d10380115103102030480c80c42e903403034108500c40b13040310415081071902c0004a600054544104400640f1180c0744404507402000301182c10340210740c0e070450307500000b0985980318002c142a580c041101800e2110350408 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 244994028 1250 244992778 244992791
    0x2011514040e01020d1407090e07020303130602130305010c0e150403020418080c0105040605061008010e060d080c03091c050a080304060b041a0109080321040206070b0a06030209060d0203030a030915 87
    0xd105a06c0502103031184d000940c1c0007070101304007004021242c001c0d0300541c011811521011540c445104a0701e600700c42d2540d080104c00b151883d0024118002d502801c000a003002210901034403400b082c502941c42440454060210f6503140410740d03095030b8045e03400251000c003d00c0c3c42d4807549080700d005845074402041c0703040321070707030542020b482180700341d1042c03007244c9440c000e01141010104c0c00601103640103006000ac1000c040090340d219100920b0b180b9480300c0780c0c59800f1075600c0300c900341d203a50704002941201030504454483d004c0000940c5030804d01507680b030310341d1140c920440051110348004003107010f100c610740001e145607800600030000c540510b41c01d107251000420216001c01c55240000414050100544a00055000c008019058440b01954403044004d004036030141043c800400803d1500108521564050500003036a03400c50040005007400245014811407811308048010f8801100b500ca05503042d003004142000540f0700302c2c49030003000421514207071803ca0b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 244995278 1250 244994028 244994051
    0x8100e0115090b0406051017100f03060603051b0604060f051209011b110a11060412031205130f02010507030e0301020a02011a03030a1e052802011514040e01020d 71
    0x501040f4040c41c01c840400840f95500184a141c0100704c21007400308010000e48034000811440041c0e220200d09050a00e0a80304c02da80c0401c6112030b0000d075181c1d07603100b005204020f010071040b0a0780445110203814031030120002003182c441c0d40201001c0280c18034074221910f0051050300c08c0840803a04000c054582443c0440c02001d0384039000d6102500b209140c3c00d00c42c0994086004407428402a024201d090f0315911a007a844160701074110304200301c00151511000d034819103151003a9911040c1c0004007103030346c0503204e011380f6981e4082c3ca000c00d40070010b1528882050785a42c2803c10540b80c109a00b0244d03030101440000d0303605940006110a00a68190f11a0002038a0f0701100d105046000c1d05040e41e0f8014100301c1c03030200741040400f111a031007910300c40070b0b070406902d000c1d0300c1d0010008403901446541e2440d01c510041d01010506100d030280120041c41c00704c941c510000503c0d15451101580000742064003079541c03000d00c041402c07401c1d01180c1c10f100340c600040c8903070f06456 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 244996528 1250 244995278 244995281
    0x301060c020103051605180d0f260406090e09030d0906020306030d053a0c08060f040516030b03010b0406150e0a0b090108060622030210050408100e011509 68
    0x5030100e00203441c100000318012420004100e80310007a5031a5800c11088145100c20301d00010710f42540500c2c200c03001d40000d440c1030032802015208040c56000401c0d0f4100403810320f404a01a80d000910a02041c000145e21041c0c50048480070448c0b144140c03030b500c031501c0c110f00c290181220300c1400c0280090600c50030b030700194042c0405400702e80244401d000c04595030b010f44a00700f205105031940b1080705945800311848800c014890100c00480f5802c20b0f40101c850220a0002145e0a10100062841e00541400f4007000070b50b424041403030b201c61404000c03860b5075070b00010b15030f5602092880e81c40943c002c2c401440040c104100b06911900340081c00f007100c10618001842007015030702282002c0c40d1074411100d2000f81c450400c40000d0066a4021005111b543c200384140080c24000041404d0b051039070b030280301c40001441c1180140036002540c40704041c2401010441080000400100000702c3da005180c002204441c0e440903130301506804400d802481c02e540f1010580746a81e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 244997778 1250 244996528 244996547
    0x6050d0906061220041a3c010f08090d0c051908130603020703022806020406030f050c0c1905010609050f0114030c060406030203180f150603010e060103030c080f030106 74
    0x90740042c20540f001034100015600d90071b248503c0403c121000301143d041c441d54028030758050386040d8a52803800c6070406019000300c8806003038070013114050065175800586c41d1101035131a2030004c2c514640080a01d0b51184019080320400590f40741800c1800404c5c410800d4610100c0320000c2080240d0070901626040f2118903454050601d00000d1454041d1084403646503142e00a062040c5a9500350402401c000a15115924400010a000072120300c0200003500c016100000c0d0417408940b25800c99a001741400444041040489248540010100403002e21501e0744080280039150241c05001554040450142010b0500005107800309166050b118800315110040b18031004140e40d51030403010300307504154100814440316111b60001d42e8081d52011020b0081290b00303040c0f601e0000d282c078400221717800071000300b4605144a814103400c11800c400078010300150007101a1039000610004080c0485c420b120070400c2000419036050103c805805a12507a454401420380402d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 244999028 1250 244997778 244997813
    0x1a040f020915041410031b0315020c10060302091b27240906030a0b0307030b01090609050103080d020901022a04050f070e102f0706080106050d09060612 67
    0x10070240c203666041c0e01c200c8a121701d10040c00030002914544a217580e03015204a101c0c01001c8205004c4041031840d02e42c0c64125103e0000142e85a05940342181015402c00e09801d02c0350400750200096500c091810f504040880040d401c0542044c100305402d00c240b803002402e0803030140342896610051200b852041005035043c0d03403064240204204001c20007036400c1031465052012030f02e107003025400b81d80c0c80712030a54005800d65038000028a800d0a80d4400c66000c5a04030043c0b14248040c02144018007141105108650450362100c4250040d04000d81c1c5160b030204008145030710030049038080b40d03c90140200c8070880d04c8416035490112082c9a40502d01301f034007040d2900c03e2000114030544540d0340703003016034040c0d0040021884480c9001e004104010300c55440084250b10b15110174040400c082900c420f18075425410000030341d0091042c050554010440c0b5038020048892440542c1000034800c80e10b881c07c0030041c511a007054015009400c00601005007e500241d081407 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 245000278 1250 244999028 244999031
    0xb10030c06050c061605070b0f0a0b01050a120c05040315020702101b0f020103060b13051219080708070c15120c050703030522030207031205071a040f02091504 70
    0x584507141a0b07020310401402c40d20a502c150005035405504281c0d4542e19150b42c9052442c0015a440d28a03015801b40c8000c0d5010241c48180401114144644080480e00b800d00340e082c00003410020303044000c00300c4602220313030704c5d5898040201d10490455028507400b80303292042036032044e02c1340005c0d08030314003ca002e84110442d0549942c000e0344800004003513290103800d45012540c4011401300629400c9042c10b44a000200b07000c181c0d4005440c405c501540340046081c43d2004001881710a590855020782010300000106101c5024001046421404082e41e60700329140c410007511179084040e0031101d0384075010515402445c20085c913a0401d1382c1c0d42802a0391000716004882d1000000004140104000340029020f504000d03840b20f82d1842020a104140015010301c1090120840050b0802c100034010001c2c02c2d2413010380c030351151030000c0c203024043d40c411814468452250350411344040025007007081090fa0000d1007903001c2d091044c141060541b21b620001c40469039071196 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 245001528 1250 245000278 245000303
    0x5070b103c050906040b0d0b07020f15010602150405070b040605030708090106051c030306030c0311090f010501120905031918090207021c020102120a0807090b070f0b06010c0b1003 79
    0x2124224154182c6200511a90309a15481c0800c030090400d0b2002c1d607000b400200030390000c1480541494891440d0703801401c004070200755030034200442444c500e802554400010321207158002282c41c6144420601c6c3d1304a41c40740d050841ca40030040d80f200d43d102000203008160350341c0c0400998003480031501d41041c203841d11030368182030307030014042c458012a48007280c04d49105020302c072480d864001e082c00110280c80740c4812070032403801c2c0c2094504040619407a1124141140d6050f0b100c0454078403c00c19504000000300390485c040e10203404c1c90b0301d400303a000c03e0041c180110350300842032540d4011000c003c258050300d6141115030500601445941c0054401c915008461b200e0b0350080c00c504030720030014402d0416408090b41a81184109801c0e9840352000b00d004000b4840d041c2c9804807240340940d401015040290400011064103105110008001600071a40c065103c00c1c411510ba586000480e01c046c0c501102401007003041003071003410400c100c83c0d4010f0300e01545042615 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 245002778 1250 245001528 245001629
    0x6090e0a0f060519060b09011713080d1103090703061b0207030611070b01060e0f040c0c0201030c030b040207080706051f030f1a090c010f09050105070b10 68
    0x4503110800c020303140e54240480903001654542c061907010010300081414418101d003804100d410640040c03c1c101e6002a840a00d503802c0368804000000b203c030103219602d0f0080b203408075030240d9a00240800c0d0302080c00e4841c7c1d1a150040043e00d058201134a8903481d00303403041c5948503010b210681c1c85925080c00d4400b0800140c041000380b08444e002800f5030362550303440c50700030b04116141d8542c80c0000d010442c0081c40940503903000380030542c0c90503111500351042141e07550104046511861400b44100708442e04140031a0a203502402d0011302a01001c40075000b400c0d04c4d1003010362140c4006020410490b001000e0442c25001c0c0004100c035690b550b000c8000d0b01501d44502c45003826001003080020b541c0300b8080622172046251001e180c00039100f03400d81240c140d64808444d00b004620007034030b580c403200b14141070f1498684015500e00d05030003e8030920610a028140d41d007a2800141842c14000c0070a0040c00521410300d8000700c40c3c880310407004042000240b0302150f1400c0c5011 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 245004028 1250 245002778 245002783
    0x1140c0408210d061203080105041e020304020a2105121608070c0e150906010903150b010e0d051e0a030f0f0e0a03150b032a030f0706020106090e 64
    0x7960304a20090565079654408260082550790468000d41400c02944007281c83c107006501c02003d40030300d112079015071460050807c040c160005800345151810340003400146c01c00d1000c1c4c1e110315400040e5661207600200d4151099038020001e0320101540400d036a940851035006064000c0702907991086020180100324454440a41c8182c4000741e81c50010861a10003032071031600c25420300313109039030360070402c40880d400303c0f045504205402c4004841f4107090f806c00e61302902c24a85141e60320308503921000086c490002c003200b000d41c1c64a410030340f80d000d141d184042d000c000700800c0d581c0580d8901302e680d030400500a4641010591200c1443c1c20340004c00034a210b03403617211080c8601b200e801c03c6840740c2500308220100720903040c3c1000d0f0340e01d880700d084010754001c0b0a074070304010011041c041070b14201c0381f455001c1e03800f081031510741e08981d52400120007840000209c50400000010f440d00040020901890080030350008413544c0550060b001c480070040c0c18011010040e000d181c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 245005278 1250 245004028 245004037
    0x5060912030105213d0903081909021c0201170106120c0e1002070504050c040302010e040209060903030309061510080a0b060f04060503010e1521010b1201140c 70
    0x80d000007951400344403002800681d1362004003000100c55001542c070004e140b00c04002624040b1654441c4400815118070702c1c98031804c041407550030312040d030440ea801880c5000080544528404402c2869114282e58000d00015500204055001881d10300351485110300f09034128003090541c0b00740100000142c0945040740c4058a6000008800c00e8200e0041c1100320064010051070340c041e1003151383d5444240d001e850103580100070041c240018003080b64400341c40300f40440400c1c80b0806c0144c1c0c0c400b20016940f03000791030260300c5c0c3c0e0710340000c103a490040340080c80e0b03d4000030080105502e80041e020340300e96a103000013502d01b0340ba0002c1c0b0010445240f42c030b10000d6070a40006408034000e400ca846003070009001c0c03a02e401c594140e0900d4039009500010b00184001004000010031581d085d50840703100000e107030070b00d100c9400040000030b030240d00c103040040010021840e06401e50040488039800746c5030110104c02c61000c4c0d03008080d6220740081d0a4440008180c0344118507003900c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 245006528 1250 245005278 245005289
    0x605090414072c1005130929030a0b070c060f0606080402010c020a05060309010608010e240a020d1517280f0203030c010203190c0516020418050609120301 68
    0x5180e003802c41008000c580d404042641e8044054482044041c0c80e6000540d8884c1503e5440c070b515440110740c0900d1007400e652044035007508010320001c5012040024841c01701d07080500d244140400030101e42011440314010f40580000130802c60300c0ea401c1a0a50501031080c03030b04001c0003804040c3c0600702e410b6401000000b0f00b54400080055016110501c0110300003003101c10340b550343e200014080d038000c071100340007a5110007042000c400f0034091081d140a100b0068040581200540780520200150500b41c02d075684002c81d10481075541210b901c528040418004040e400746000404080c5101c1d4592000c3d80310300091110501107801010011510011440c5030010180760212044010301505c80c9420b49072a00010b0b9010002483c420074048009a01c1e07203049611010382c50100039141e06040c2c181b610745075007654044120b84818141203420391b8412024004540200210340c050040b880002071100c1c24400000f60062150070210102c984201040200c500140001c2c41070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 245007778 1250 245006528 245006537
    0x1806030c0f0c0f110f090a0e0c030f0d081e040f172703030906070605070f051303170f0d050105040b010c0206090609180703090507050a030302060f0a0213060509041407 74
    0x1140019924810303450004c4c000401103580058100001550000142c1c1c0c4a14403554a141d88201c8050910140740c207031100704d000d010320301501e500040d21010519910310400c0109400940001c84c038454441c0303500c1000e990702c403007846c040c0390281107406032000980b43e504560801084003140041252440b00305070310740c1c1c2d03182c2e03905103060038000b000b003000990306010901c17000f0b0154a5400203010003e0141c10045203d017000640a00303500b80742c010301e1042002c100300c0c4843d2030380c1c1e142d81c0400b225030044804a46091080c1d4a206a000e4990008050f200000d25458010407d8020b24180c03902190300704034501c01300e00107640c04061410025080b40051150101626184000e8041080d0141c4000815103c896810705250000c072881004280c1e295a070805000b82046040d01401098803c01d0015040d911702075900c000003070423101c4800c15100050f0411744240c040c3c8e40d48400d071002441c0600d480d500054195000100710341d024510b000075a41c89a5420300980e4000c2e90117854 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 245009028 1250 245007778 245007803
    0x324010c0210140a0905090a0c02030304080313020a0612060f05030c0d060f110c15060a051c0c06121506080705130e1303110a051207031806030c0f0c 66
    0x20710903038a0452042d4814010208800401c4402c0030000700b4000e0f80075540ea843c07250901081102c0f40501800d041681490040000022030700001125005504200550b0f240d68840c1300c22a10581103c03802900a000160005680fa400c2490808682181d00040c8100b60715010359500ea05090f21074980d045e0f0012000c03500e10305242c410f001c29140144000314040000d06108005d1b01d400b10080c0606c200d0004240c080c0840611507801c0b0603640d1300711444d850825200080b507040d1107000e032501c1403003003c042034050078462007000c00007640f081a40ca0b0703240c0d4900e40905544030182000c40183d0604110b6590035285d10085030503603030507848101c1540c41c5d03601c00315040d400c0300c1309900e0204c104520209641e80201142d602c90900321880310341c0031000380340043c0708002c5141c0d090760543c00160481e00054000c6030904c50130350081041921000304c0e00b02200c001d1b41c221024481c0c0503091501083c1c5c1c0f64980c20562411b81e6036260f03900c80b07480040007280c451000d810f014005c4009400c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 245010278 1250 245009028 245009033
    0xf010e011e05090904030e01080a0207081206060714010510050d210c050a0b240a0302130b0402030a0506030606010507050304090c03090614011404060305060114120706050324010c 79
    0x5601d11a4616245052410401e10101043c80c5003c103640a501081c0115a00c8059617402510203031700501c01c0d10154100319440d6101307141c0740100740c0f0403000101420000f6103261076139001c0c1ca02d000d8001c41e04c103100c1c060b81d0000782d000300070654600c0030307400c8044c8021907107080c09120308450a42c03081548076180709501d036114569111151220401203c48284000302e841006405407840c01941020390324101405290024480504014200310241441402c5603962141c0308048940503140c0c0a070500360042e0b42d00051262003485940030384080103009419040c2e62050307101d618140d04450294171044d0056440f4000c161000345554800c2100b8031089889400c40c04030860749050100d041c09480d07580c441540e91000c2c42e901d81e8000000100320401c2012440c003503d21068408219543c2980c44050301c0d002c05001d45c480088041c050010a5104e240011006c0c0500200307842c3e50700c0d200c0500030400d41c007c5c0d075003410b280414401d4071812412640b10309000e4005854118031450300350b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 245011528 1250 245010278 245010317
    0x50f031003020f060c061807030b071817032d0705030403020a05010203090a03120e0604091e02160602160b070207090f0507080f19110d060801090c05060d0e03070602090f010e01 78
    0x87d100e0310300d80c020010000001a801841c5901802068541c0090040799103010340148120742d02115101a440c1c3c180c4c8901c01d00841142d540140700b541040e4071035852441482e000ca103482d1940f02d050b0000651105010011019100340c0b44202c9101000580c4c3d4401280d0320b002c0c0900c0554044260101040001d000310852203101c491030400c21031002e510f5001980a0304142e105400c410381300c030581c40c0c00c40141d030184e04074004e81c40421420000c68420408080d60400c10040c160350740014200c415441021407000d00c41c1d030204000380305151440380251247c4045c0b062000a0307080071480d00c42051280580d034441c00d440c0d41c0350f6495980c2c6008824600740c0161802e40c9825020504140c200454010100504581c620f1030756149442500c2c482140c3d0741d41d02441d2a40d1618112400085001440e001102c908440450300d480d41c0312030781d1004105110031708606110010700002009415000740903048411070300038030490b540d0001568000c0d0410116070015100803840c1c103010400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 245012778 1250 245011528 245011561
    0x30c03070908150901180c17070b040312090603140f130b040501051b031504051009090c050f0f01020d120e07030b2d07050703050f031003020f060c06 66
    0x103850142407840c0e032284400d08050421400c4400c000700310080001210090242c02c1000c3e01d440c40b9440089400d803182c10401001d4000c2c00300300010380d0855540d0360f0b801c02625000e00f8407040c9842c0e44a9581c46c2401140c440da21807400440c220560001d0310b81d000f03114410070042c01040211250703a40d00296008480300628001d83d55010422440200d0b40d00340c002440782e0301c5800005124201a0010f028503901068451801e030701c03c01c2048209441d0114020070007106030b6011520751103219401e800d1031420380000c81d40d9494140c1e1001402680e4002c402203034410349080d54010108401d0011520948006034050303030140c5503600000d84201110301c02c0151400d00040c0e031180c1c0240302c0e17080182a52054a10b50034201c00d00001c644002128451103134858542045898000ba48001016000705800180310b0003103010320606004500700c80b0348152407500741c3c0c0d03a483d001019803d14485400140d00618980c1d01420f1203041440031143c03444110401007409a88040407440c0c8002c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 245014028 1250 245012778 245012791
    0x2120a050a0836010506030307030909110c03030a0501060e0612060907030615120c0503040c150c0c080d0e040b0a050607060209060c03030f06040c08062403011e08070b030c03 77
    0x1003400c40c0b0002031015451551031441aa82c410741d6074101500f01400d664002d0b240b5031013070b0010481c400009030460282c1044070b03079042012490130b08421081b0320f107008084a00d4410b000000421110004940c06036050705c18076203c10242c08286001d0102d0b50269011414001701e5100c08602c451401071450303a808080c900d40820650b0301e80a0380d00d01c21a1031030001010a648142840a882440c083d4622520961400c60b0a51400e911900c8402d0114800d200304441c000c4455101148988810040d180e040141520441d07501c0000590b90340d00100e4000008112110303118a0f80791502403008100c10081444000b01d0030b1200700078a035440001c04803082a0308003e80580741c1c4541c806400019100300285031640342c100c40c60b0710001d500402480c400c51070030518a10190b0007805550700141c050314181401c4054220f407500ca02045803124180c5000840001a80030310f40c440d01041c0390a0a1001c0d8509035a4521181e03104140d008911465109000003120303900d204001d15440345 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 245015278 1250 245014028 245014051
    0x50403030f0c03210902120109020103061403071a0702030d08090607020105010b090111010f14010e0906010305030d09030c0b2707150e06041805010e0f07020c010e0a0e0a06030302120a050a08 84
    0x103c41e80011111f41039881d15004a075100c00e62001135680601c2224000e00615043c40210404c5c0c1c40080e4035040180680d40003043c0e0103004100c0b462811040d2040070b40e0142c101d804100003103202070300d2200122140c40b42489800c0004000ea403060081e58120b505603118142428540401950300c111105140c03c5590740e10103804000c45050b0080c2500c800c01d0cc1102c0589504007003001e4080100100f10580d44d9100400400000790000308a508030355020100184a42161404449400722160041c0c40002110240011659648510118071588480c000d02d4224481000c0e511402144030300201d08050410240c01c80d4024140c000e02890000d00340d600c1d080c1c403202c581c098005691070050f0700594410041c0407005c6034080d500e8000c1d4010142c034040c1d1400d0140256545102c01207a810420404403000060b103c5a4400e0050009072401200518000014800808180c8010b40042c07185040c104203c0d5414400c0f59520034541d643d49240c0b46400704c0982c0c032600054841031015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 245016528 1250 245015278 245015291
    0x209011d180a02090307080d1d0604050d0b061018140303070804090203011a04031e1506090b0a0603060e280c03020a090f06050904110403020d03050403030f0c0321 72
    0x842007004154801c0000300401a00ea0510000341881e020b955040402d031940542c107001001908800c0110010074a5503946481445003004540e2a025542c04a9040104a69040100298811014407c980c19100036110f0200080200c03050303010804050302c00c402803c414010781d540c1c0c041e0801c280201034101e81ca01002c940e100f644903401684140c000d01e50205c010302c6083e1034071115407103880c0c442404030300701825604c4030f20792540e1030343c0840c0d10b040e070540c1140c0c104108040c00c100074000b9024200082130b6a42070b090058100e42c3c243d503100745402c200104001d4041e1243e07205a496522698255a46884c00d00b0b0b9441201b40da54040c400041c80c15003042c4100f406200810301da81e0b036003d41c403a00c911501411041c140c0e00b1174405640c48100510010382c0c441c003910070082c0201d401240101075800d0b041064481c90b0000383d000564035050320140364224001b40200d9100380c0c2d9024030006100d8044640c1c44800400031300041d40b0307807280c0008056502104040b8002c1960010b8403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 245017778 1250 245016528 245016559
    0xd020105070f050d1d01021c0e03100e160b0307020c0d06020c0109030903021806090c07110301091103100509060a0504111918020f0a0c0f06061d0105040209011d 71
    0x244800c0040300c0001a96524242c0424145d0380da603c100740e03070280010200303a80240003400c130001d072104420702001811440c1c61007941d41041f5100071200210420400c1d0181c8480141c1c0f106592060101d620210791030005a015051044a2180070307164042d000051380c580030014100d0340c406041d00c11700d4080c0700c1e1030080e0900b842025411f81c4642c0303c2004103450b600c18400c208030401e0059102098085c10803070a07407a080d100c25030084946a851b40d81f5500c600d4041030740e003c1036640c250190b01e440890f400f0000c440000f00c2c00041c0c03c42c111034410910010160903035900320784403000c40d042040440d13141120764000507003186c07051818200b0300400b180441c440c03070b529410740007911401440410400d18403204e226907004818000b585001c0701030548000c14801c4001e100b0402c9910710710070701441280d00d00002503541c04441809503965680d00d00c840d8121910003000e0a07440c9100001e0323289018800c44c1c00410060712800c50384040d850308076081c0c606041040d60032090004070a4907 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 245019028 1250 245017778 245017783
    0x10030507091d0a0f0b031507030e01020c010606030b03060405120f0706020307080a0e07060e0904050f0d02030c060c0405130507050d0207140606030d020709051b0c0109200d020105070f05 82
    0x2c4440301121003440038541101c203101510965484403d00a10700b03030342003030307140c0700850700d40c61010501078036000d241c44062088004090b0010301041c994808109040c1c1d002c01034012400319215550b05003c601c1404040507141c80c030950b0700034015801242d001c0c030802c0000c8040c006880d090800c16081010640781e0a003640d000f10390b24000144000f003040300a50892103220b000b040014000d0407118185080604001c80004141d0b10500d86c02e40041c082110421451080c8103859065901e40f42d1030640c080e5481d00041c6140c0d615014210026980c28410b0087d24203c030402409100e41c0c1c4c4100030350000601c0040e042c181008810031420500c0003881c0000c102051046410f184035106200b401c504000002d040030384290043c202812016500040180c2540c0d2942c40000b255200c400000f544400d918008004120020403034110200c07065010a0f050741c010a001041c00c4040700000140034074030b120741070384860169012400365210f54058082d40e071094bc007071600c00300d254136a0303407 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 245020278 1250 245019028 245019059
    0x61b08030703020a20030f0c0709140f0123010c020a0510051c050c03061e03070603291c020d0b091c0206060307030b1306050907091a1003050709 64
    0x1030110f0740000e4207041c4640d02101044110100802207041508941c65043c0c4911410360a2281d690005c1107c8480c402c080c08140700501c005801044401e611a20412038130400b252000d44c080045e070000210b0072145c1200c40012103801c40f1000340346803c1401954525134a01e41a0707044118a81d020805465504020405c4207864a0b400d45902c42e003900d8858900500303c0403c00d05060905024200a0100c180ca802c0141203070b01b44214040d0200b101c4100b003c0c400031a9251281c6000002c4190b0168072001c8801c0340c0741003072000d1501c204064180c01c088224695002500a101c0c041c864000d15480c045540c0b000f045141d402d070217522118034001c0b040d60f6014070b1382c1000101c3d030064400c0c0c5103102c1d1003c4190003c0c1c6101e14103603001070344503800d0748409040981c040c00010907452900381c0c2e01d504a98031044c00c00860505031689960358599010340240503180c6040c1504c007010000c401e00c007182c0014103034503491140e02c0c400c5001c2c000107003044040c407480036004a240703543c00b01d0f0030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 245021528 1250 245020278 245020291
    0x31101230108010c03020c0c01050702150a050a0e0306040314030a02090303070c090b0d0f08091503070f030501140a090b010507080c0a020108130f140c040f09050606040c020601061b0803 82
    0x3500c0ca5040c5035003142182d030a0318582040c5481001100e000f0318020604840202090034810740340c400500104401c049115142ca0020070001820040943c202000d03017100c5000381e5864400c2d1001d00241659142c065501802140c184000703844100d0000b402194840e1201202500f00828100800c5c60341d0021a0200ca407010002424010129144a030459104007150000500281078550013900c0c4d1031600b000d44034990002d03590400c0c0d20b8050900410171529030915650f8508108014100310401d070544001070f080c40000107426000c0d0214522010700103014500b458540110403004010400d41d00d4103111040c4a4880481d0094001e4066014218080c2400017134910005060002c000d0080d10031400540001d80410240d21304810380c10b5201c14200502a04a00d4107441c0032805903e00ba4000c0c00d1640800340d26456401074800e00744580115109174031490100010f40d04411b0071100141c0c440401040603034414600c001600709220601141c58200b074544d4030a50380229480c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 245022778 1250 245021528 245021591
    0x3070e0406140601210207120e03060708010b1206040902060c0703060c03050705180a030206040815150117040f06020f030106180f06030906020d0204080c030d03020313031101 77
    0x1000280415402504040c50b854586070000d40342140c00070b003e10300351802c0c0b40c2e0300c44c207101c42203030050310164112100f0640108441100c0c11580100030a001c00445029003e4000c5102107003c143c024811181605d443c04285030801240040d1a40e0510009083c150301507150300b01e40000d45c0750f1500518141d6507800103401e4890650504901b5034604941c0c032020103281c04200030030582d1040541d01902404501c41041e40700380c000041d5000005e8001030b6105d04006000207282c5000a810460203e041ea2001496a204281d29a0b196031041e001d030b0100d10000000c1c4408841c950081da8032034451940140840d232242c89040c2260811225000b080b40000014001141c01001100d0a400c0300e00390640c0356414000191a40c017442d1251109060f25619240e00300100c0e60180d40c1605c200700d9045440b1a1b070390380341943d00c0c0c14201120703001340250502001101e100c7c0c000c69100d0900300a480b8100c4129544c200c6400600f094400115562501c1d64460a6003185c028811100780000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 245024028 1250 245022778 245022781
    0x408030603060709030302030a05030c1201180605010315030b090a060e0105060916091e050301090f06060501050315010f030902030d0e0a06032c01061a070b060d05030706050402040b03070e 83
    0x501d850042c02401010620200c0c071403c00009a00008840c14001c0c0c62412948a4981403044400c501484132030080780c48520001084180d04400741001102c0720407000c4c41410394400065040700e0800c404680b205071089401e1000c240c240144d103070051100380496240c1507064451030300b06c0749840307103002850351504280a180c0c60008151070704500c20301c000882c40c0c0d41000c006000c480303103031051030f00142016520780509491101c3c85001040060000c1c84a040b4501c1d001c1031440344410200c40c010b140c01404030b5154071810940c0c4c8140744220a896a29400740c0040d20408143c80b101c2d400c040d1200403640040e10140501b500c02d215548804405025030000c01004202030f81048040500d0050002c0e88410310811080940c0241c150f0207404400071040140503021070381203883d5180c1c0b102601c202d07052000d0010542c06018441204054450380100000030f400036074040c04c2548180043c0c1d021400a600140d002840140009601081c0201003418032030294084203070202e0090 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 245025278 1250 245024028 245024041
    0x30c05070f08010606050f160501060b040303030f1d07031b03020a14031c020712021305100602060112170d0e06070f030b04020306100c031416140d0f0521040803 71
    0x60304000e89406e003401400c0c010100e100030142c3c01103610032a80e02c01c6014480040c002c0a45c0300740c6c040d204000c1070a5171070341c59060240190044c0e0528411070f03031520b002100c0c50344000c1e41d03004595010328064a10b01d480e5480b1440c0c02d44854980645441001d40d0000c0160341e6503803800010801000f04070b040c680b4583c02c00d41440038424400040381140000050748990104041040d550020001d44801c0501e00104c0e1080c0d601c000c014520614003401c2c06082c4040741b0900f800c4803002e508039120780ea21a0f944692000703013800300812048000c206000e002801070058400700084120004010058011702c6140050640d555004102c010340d8a54207a1380c540600074504200341c405601e10b0400c078001c10a2a1600400c2004100c01010305030308042c8a101241c2458410300e0f640c0d44c452a481861100c07050403803c040390b07100d15402000401090210364000328000a07121101842d0200700143c0d003030760014114081c1c0441c5a0642d40c410401c10142d2402540a03280090705d038500403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 245026528 1250 245025278 245025281
    0xc01390b0609012702040302090a020408252112080603100e0d08040212061006170403090b0c0c0306010e0403140f04150c020907080901061409060d030c05070f0801 72
    0x2400c0da5004450b03002c010b003d80c1c1901c1102d00070740d020100d4005601801d403c0d03000c0090140da00002d5000c08010140050009680c000c0c2003954903090984402010840450003801210354911145a0711482c080122940080b249080d141c1c0b01220840101c0280d540c0081245c549036910011560002c103102c40703410204020540c04180704000c2000552a21055030740d0210808020204942e4000241c03c545888444d0543c20074804102c0320141840b00030000360000354010640000d0846c000342014100c2c81c0b492034011609900c03802512401d00e050381810398800d22490142d071240c0c500c010100d8804000090007005401002d45540c00d161500030314002c81550003140b015824000d00300151650021a802c0710703044442d4921a68210310140c1d540d43d0402e1021354450b0f03000c0100502d180e00800386a02c10540300340208001525005002c4141c01080e01c003a0300200154001429030411480b4846100d01900f00030f0b2074038a1695a0f00d180c400c1075041185041d000d00740c01c1060388001d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 245027778 1250 245026528 245026531
    0x30f08091204090203090a17030108060c0712081b0a050405041803170a150e160224040602070b240603010e0a0203041a01090c080f01080c01390b 64
    0x410303014011000a610104225010350300603c1c072010b90000c04180000303020480034101c00e40c420210040306004071a054500c3d0024415600d03a8000c3d03000240c844802c4a0403540b24952040500312000600c041c102e4880000411054008140c400e420040d1040b20019080030000e65441c590707954105000d20060707480b00d80c01265244140c07484d117800260481041440a071138212600b00d07643c3c6580424024002003030040344500e0540c036021030303507142c0f03c0034051145070001020840340c0d000710703000c90380c400c4903801d140c0c0c4004030301c0c11000a282d0902c0d8003903001130245c0c4026042103142d82301d5846c6020241d401c01982440c00d00b42100308802142d03100c030140c0741102c4480c01c540c50700c1503c44034803500030702c0018001d600100180800994070002c0c25000c10219404a046da1212090b40052404501d85000709840c08006103e154500c03d40a06036400203011f000140401c00c01502e25100c101d00e80400401d81e452018035911a98503410744035139000c0d804c20f000058604103040100030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 245029028 1250 245027778 245027791
    0x2031009050901060504240b130b0c0a0f08040905070905030304170a02100f110f060604020906130b0d060e06030a0209190903020c1516030e040f0207080d05090304031509030318030f08 81
    0x1400d200c094031403800e40c80b6076000c0b50003640d032b606d0b91100d072100480d0070315001803002000c00e00700c03600f66000c0c440f41c4009002950105401000f0549901d002942c40d003000d8460241d041d401007000b8080000c0010200101c803600a08403103010b05183e0006224010003031342280050f04802200309226840a6000c401d0211000503146111103411000d8654070010410b03401030b41c00080344e00350ba446200840b101f030000b03c40007201b540d0700e2318500301e5140d000d400c10040c00c6060850124100d400c5400c690b0190300014001c050308503061f402d10010f01801081ca030901168004503030a046864018222400c0c0710764050071640c5000d1040144514030211580c02d07034007040c88241406841c4011940000750103051003c0079071030b0140020060b050309860084e401c7c0c00421a02c042001440240102c945130309814003803a611046026034034015448007a00120410001410106841d4030441401d8004c0c5804103022540c540d81024410500c00c1c120002028078003103120856015149640005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 245030278 1250 245029028 245029049
    0x60405040e150c07121d180f070e0f09040305070b0a0204061b1a041b0b0403050c04020a14090a0e091f1505060f0d0e0d09090203100905090106050424 66
    0x1880e520780c00c51040d07119203008280445944d0740714200d005010301b001c1c07140000302404464552102d04564200c02598501c120a17913400103c3c6003e8000c032500c00041030080d01306000140d0000070812010809441642402010045180400d00c980e40b103500c64002c403072016a80f03d1920f000100317100c000110502c007041d82100000001a0066050703c000341031298a1841d5440b1f13820f1584440d80500010303054060204000607500d900e10016004690007903041d10f080160f405c00340000d03407050005000008903180e2080d820755010501411454201910340d100981d101c228010300f0724002c0d100035242da402400e80500d01c8002d103401030342460081c07070140280003500c0403c600d908607074001d85101d100c000c11030308006c54040081c1c2d210285003440074450508510211501c814103000071400003801d0100c0890082d407580200e03800303035040485400308146031040500c0141070250281c00503540300c50b40003885955502801c07440010802014640240c1141600c0d44500c040d44070103000c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 245031528 1250 245030278 245030287
    0x70504021201030f150c03060305060a0203101208070606230d030e010c06140c030601080a0e03070311150a0e1b030c04020a1704030201090b010605190509060405040e150c 75
    0x5241280e12181129488a199031840f9198a00700035174003010305d1400c00741494000501c03515030340354119504881c021410b564482e01c0340b91200060f84000c82c0c00d02c056004124040101140c0a524407030710b20702520300581810b025583da001900d1155100070a0782d540300e1084040403e40d03400c0301410100c11102c030a04590300d603401401408200340b855042c04615500c60b024040c0720741144000004194aa81c00c1e0314141c041c00c000e0b500180c1d00c440c0042d01c10000100c88000c54403822603a035800e04011402c0c142d9a0380d0454886030005284882801101440407800000b0902030780200130151010031080d04c1a12440e00e4500400c0064a038610010385819403030711b000c1070610040301e003070f07502582da00c0c01c901c81500c0703804d5170040481700706502d501000281a17043d408013490a100f103a50440c940da03a82c10840b02405030648103156040004200740c2c040c3c5c054801020135560280082d2f046c40c0c0d4410024003190a0ba0a41086030f4020703000030142c072013001c3c80c0280d0005500001e1800d1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 245032778 1250 245031528 245031547
    0x1050a021902010c020607080606040801090501090302010b0612010515040e0a090201020f01020a1b06020714060906071d01200a0807050d0f09090b03010b0d0f051b0d0809042003010807050402 84
    0x6c4803c00f4040c1400c1c0014840811136545801c02285c02401d031082c000c0c06001c04604e4118001c101c0317104144c00651a09140d402240707001011144030407a4254209106d900780001c1103072881034080721500ea503000708800106040b000701094810000d1600010b09000c4d24000a07080070000e210242c0c050340704104010002d600000b603401501c03515440910458141e24240000703201e1020040e01115125421034100d80d80020881e110b8203081043e580540c6031524280c5002880750703112a1024a6441458515445811450399403410f50821940d1030b001490131a081281c014002d4600c8500040d882d01880420004049089000d140605030380e51a182d0007018203543e400707100101510f03100c401c682507409401000248070014040c80c0e8100c81494001070150788443d084445010344588654014803103410003240c240c0261034200e00d15842d907283c15190703100f6181103134001c0d582c01c05450510210702041440c0000c0144c101d41d46c1d410b0400e4140790900c0395001510480c010002c0c07405 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 245034028 1250 245032778 245032783
    0x302090d060b03121e030619260c0a030b04020307050406060c02120706020703260d020304050d090308300403390803090a061407110313060c1401050a021902010c02 72
    0xb0321045c5014160703140d840b45800640840f0003095440300c01d13080183c0c0801d0940c1034a407103000c4002d00c8811690346e84e1820841c03030740702d020404c80d9551041ca048001c10110356802c921542c00740c401401e5480444d29400028121442c45d0483e00020f440b43c50480114244001000300016140d4002c060386407400d1402507607112a804002d0817415010a450f24490000800850b03810507525032940340c00580d10040025001120192194890f040d0084540c3c0d0003146440152034000d007085150041d20700501000c001d40d02c00864990480c00c0080140d030006603006030180784a0756038207140714a0680001c80091040500d200f11946407480000940169100804c07156440481c0a490f5030341c4550301424a40d402d071000c0d1815041c000080e40c100014042544101450b844190014465000c030580d240174009507000540c026000910445020344060304c0810f10400d1400c2090102c0c011080c250303a41034400c1d480c900e80124210110b04099030b61550940514402040070b4070403070780e0007503 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 245035278 1250 245034028 245034067
    0x1902060f0423030a0206060a09020a090308180312030f06031504031409040510050405150d021207030807050616050a050a080a06090c090f061407120302090d060b0312 73
    0xa04142040b29032000300810014000d0050400d4030640b525804810406500e40078200e50341032048001c03110100d8a00e640780b0035640404641d03603070041032030305640d18101654001c0c9200c43e043c0000320981c840603601088114a0310981020468130b81c10700b0b5081c40c1800c0009002184640c020034541800341900e81c1403564019054a80740c00c41c0441850011032f18414441b11a42040c100310811410107203840c1078400302c401c00d5904000a030f5400420720348040382007122941c03001940f00200090329000b0215140444204140c0e58916a2a5103541790b42c0e000d8242128160003480c1003007101d20030000366002c00305150403d00d141c0701c00140020258403807024107005000300100030034214000c03503000c43c020380b041e001d003000480b0a02c400545800603d114010072040c2004001c95540c2c403030380000c81c0d5400c03140d14003800c203007056607098000301c000c3c0032030030806034203024440b40f65855042e10704c0305c01d001f8030001840300c009200741800c22107011b18200c00c1080410410010b16100000c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 245036528 1250 245035278 245035283
    0x307080303070c080d0e0f0d08060a140609061210060207030206120702070803040b180f031203150a14010206060103050606190203040806041407090c05040504091b0603021902060f04 80
    0x2108840c203580b43c0700f0b49500030806a070117010f151241400303c2c81c40004404514203407941c01c80e460440c4440e4100c2d10500100c4503680c200e200e0345001c0100c400d030b1089500291400a01140c01c2041440102c0d049402400741490b006c020201403000098010703e40c0782c05468144064440302d411a00420020b01c94101042e20140a00c000506440d01c28002e81c03001d4881d040030f030390b6540c1c3d840c882c0c200c00d0b40220410303007400075000c1e014494501d44000700c00d4101001401420034000444100e5140c1e80006010750a020f4a18644040c0e03651139248540181020380715503158501008002880d200d401400e050615141c0030600c1031903075500c801c0c7c0f0742000301d01c1e801c0144003400035030407421401140c0c0010024410b03c01404100610a5154840c42c41c6403c11114100c1d030b40c40c0ea00c810349a6038508034000c01c100300030030f20003800c0c1a04041d00d8103002e01000350001c502c10100001c90295907110300c0001e1360120340d02e40c45005d2401c0c0440340480030700c014052400d00e402520320300390014100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 245037778 1250 245036528 245036537
    0x7030f0204020921160e01090509120d0c080a15170708010203040503030901320604020f0a0f030606051e07050c0303070b04020a0504020403050316030504080a0c0311030708030307 79
    0x54004556480d01203e481d19000f070a0708514198090a03c001d0003480d4024004501030019440a10013040c3c5005044a010108050a607481c00c20030780028640034148140a000b500000d003850004003008004100e02c8080001d465000802c0080903003001a107001922410081c140d0181c2142c00c0c60306003951003107060a4824550003c04600d040665800b0400e9540040100014444040095031060030181c00030700089902c2060543c0d40c0381700000040404e140100382e605d09000c1f000031b45521600103000185444a00001e001c802d810003c0100006840075038000c2d120f41d8140500310042c0701305d01f003032410054008a0081c9615180101e000b40f1000440c1d440c043c0401005a410305200180607a9650359947c2804152214101e409034040d20812900040608247c402c54007183e4200e2302460810510440c1451604009031003501044014000826900d50034484003000c20322030881441301a103140f42c0406c06080500803180b1a0704058802c01c0b107040040100d0341d00c207009240 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 245039028 1250 245037778 245037803
    0x1050d06112205100c021008040f02090c07030306081c0c0213150e0942091011040503030a081e1003110a051f0309050115031b080703 59
    0x181c0008074014140011075902c982002d02c4002c0052804000903140240c605080000d4189025a41c22560513802500641000c0c000c014081c4540580c90300180314941c50144c12109400064400c2800d03907080688000c002032040800d0741600c1050f0080c1040c034003030541003501c0744450000c03059102e12101070250316840f4900f1075403144001c071400b00c40c140c41046200148800040805060b020f061900b40503800815a03815000031495200400c0810f400c41c2c20b108030701c8440245101d050301c40d00a00c0381d428506525440c10f04094071903015000100b144a0b03402d032002e07055585c030459030380c800c00e0100310a0010b03880110490b4415207946c24074040b0307507d45d074240d010040003241c0d515a200001c80e0620200f0401010051b0403240600d01c000a10b4101c1e00400403c003905100340c9911440c0d514030216048110b550080d200115803c00181c01c85280e201c2c44e0a4a04410107017001d0324004a0910400c0007000300c04c8504403e002c48003880a0800b0319540d9117088134080908012039420 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 245040278 1250 245039028 245039051
    0x20907030c0e130209010906140711031e061024082203030f05060f0f01030f090c030f05060106050a05031306090f05210a1b020f0a1503050106050301050d06 69
    0x2d8880c00c4002c0180090340743c0514440450002d400c880c4040b4005941d0540020740c891168030202c44c55455190b02c14039100d4141d5811800c011000c0c94035406000d841c0f000024001100700408540f10078201404c114900b2204c1e091070301c074064104110a5000040300c1400040d100c101d01401c901b10305000081e81ca030481405504a03219a98a40501860610300c0415034580c009004243c82c81d5824041511000d0030007850303040700c8900c640c21811a20760040298030030f8200201d00c40d120400028801c456031980c0900711010340041e140c56420850700010040100704650040c0414a0702a003401d00c0c511000301144000b800d495549141c01001d10b00f407101c6d6a1011400d59801500c0092000f00f511340355481d5141212034002e4003c0c204150300d02012440700300c072203e408969500c3d1051489180203002d1000c010001e070f8020023010005091500c80101c000c0c0034000c88858100c1000c0c043c0c00040546005800c41e804200c0309100410860710780c0c4420b03030f1403258040b5010074024051b6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 245041528 1250 245040278 245040287
    0xa08150a150f1d01020a02010e06160c050a09090302070306050c0d0c030f2405210717010b0303090d081b06010b071b08031b0f070e160c020907030c 65
    0x60300701c205114420a0058450358200034404080542900c0c0d000440d0081c43c00d6614900507103a900380580c01250700200198440c103100f042da0b1070014440d6080c0040c4410f1880c0451401c2e408954000c540c60080c0b185240050f0568000d0150510600550602e680c009480b8046480f0003403e0b903442d9004a40d2800c20803003a61050b0160900421003105014401000703000c1c00c1405d40c9506140c01071141d038610003044159038040f01414442c41c810b24180a004106000001c0080382c03580f20321180403442400c1c8401001000042c1d40c0103070001e000c04406085451301c01e0310501c25401040900c1c3e681d2105006010a83d0300120b070b1a072245500a102c203541c01d0710400ca4101070148400214200904002034041c2602402240e40f82444400403e4140031690141e4071481d8014002c440c112204240c06003280304115041e180c180c1c120040091400c80503030402d03180e0f1012141008234480c5078240c4461010003510300406003c205801144808101030a242c04050301c41e204000e03158080d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 245042778 1250 245041528 245041549
    0x31209060f0c07090f0204050906090106270b0c060f0f150105030612010501032d080405040c0c0c03060501050414071211070506040506011a040b0d0f0f020304111002030a0815 77
    0x1341c00b410300c031070304501d000140294071901900b0303c40c1035050301113462801c044400505940702910707080292079200e0801c000c01400d4000d1680c01600e403000204040b541140a010340b045001c0080c062420a074040314946240140b41044c40410441005201a040c01d0910690902030810664a031110408148801c00c000004107080d030a000000040000c0040d00440b0003201b4110504030000420800c40c040561620140900034180800d0004d4a0954010014664107080002c4428015900e60110000590095a040ea691001008103040c18018a27035040c10881c0460150300c0c0c031020240003011801c80000c90039640f400b070441141080070850394600e4002085030340070b25144c0307003440e0340d14800d000744044980c0e011a0b10312010034a0b81a203058460414055041010138003418008101c03c1504900311354440c41440440e803c148000d50003940581c4c00a1030106500040c0016001e10f00300703003c1150300400c201c9407490741c0410060307042004440500c0003802c280b0001903a8955 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 245044028 1250 245042778 245042789
    0x220306090c0602060109090203031e0915031014090a09030e060d0204140a030c0e04020d0803070302070c0f120f0f0209010803070303050f1605030414030a0c02031209060f0c07 77
    0x9000d03028024001210401d00c1122aa80c0c22100181c4e00c0d0314140c03050340ca02000094042e0700c2070241c4651507184452522007020101c03010350802e28000009804000a003213402c85084001040c8045031284044010252a0081e441084c1b07056160102d2141c00c0010b21140206948007001c0c81094800c11641e03005100081c141606d44200043c4180298054410512003000c404501440d905107014600204c0c1e40140844007a2807400800d0200a0401402280d04c240d191402c180007402030800745014940a550046e1100071601d0104034912640c0c001c03000c01100304800b0800030b41131104007510303640d000e054980889403514196400c021002c01c001d42c05980c000020406a00000c0038100040c002d0f034080c440380d113400b180d40d0707a0a10107030b80d030b52034409054040d481828002c100564105c0c1c40380c2c001801504100c28000e0458002d00409000100d901e001801545010000b171205404140c896030f1402e400c642c002540f9200c1c0500c140c1c9112400f142d00f500c080c209202580007080c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 245045278 1250 245044028 245044031
    0x506190314011b090f051509211006050f030a1211030904050403031e0204060c0b0c09030f060601090902040f141206010e0a06080a0201080606090d080706020403050f030c03220306 79
    0x141aa180076109404c1c901404400e1512030350002150310348030f00481900d03e9280c0041e450f255000c0c040c050f0022802e0141880803440501700248903204000168184003811000110307a030074007042100c66810f044c1003e2007640f22094080220b001364802d8205010141041140451074444550442c0180b4010380d5000340f0f040e00f008240354140d04000c0852141006180700c01341d601b80c00708100c0c0170f2030141400060403402c1e0036000840601aa0750800384800b40365040c0090500083e1030325901e05086501a0441e03c00d100c41c950300708180c4009815828815401d19081600c0148100490720600552001e02c00e07040f4102c1e1201d10f03513541080018010b485696840d9a00f030b4280d280180c0b06402001c0c541107001990788030115001c40360311741c1607590403034a4407040c1c03c00c94079400c0b0440a503800700400c0b4000e00003425200080c24a03501c10302c0d0142e140e5140d030504508081c40031301c0c055456001005640c0d5480004411151101d0840740c00001000d40310a06544c1c1c004190002007805 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 245046528 1250 245045278 245045321
    0x20607060b030c10050901140403082d040305120904110a0807020c011b14010e07031a0921071104060303020a11010207120f021206070909050619031401 67
    0x102034001c010551425000c56001019602c1881400b040e040034682c00180309008890f41c540c45405c0058054106214150070300f034403a2510750315940301942641c840e28543c02c3c40b4010084044402c17942904802c155800c061030340e120592110341c04a1040031180c00000d00c15031a030f8895000c02c0c03100c1041514a80c4600301e000c0090701c4001c06540700380240c891803c41540540c8a8001c100801c0d00c00003403201075821079612000340292101c0011706a540301d214a05481004000c214000d6029403184400c0d502c090300c5480040102802052231900118010003a43c0d0014014180041140c1300060341d440b00740c00d110711269224280c1c540d0040c1449000000c3c1a0700003030703404425025100c80075104441c2401a0781d01d81d00e911604203080c03151901e1a0124141c0900000302c1ca00240079200000d0021818508040080325003201040e48000c0c103201001841c4612607200c0415518503002e001103010710709a4080c02c2c84010011340303e00115071840031080d0010305004030200c0f15545071 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 245047778 1250 245046528 245046533
    0x613030f11030303071e030e010c0e090f0601080420040504111306050102061303030e151b0c1c0215042109030f02090403050f0c0109120e030d1803020607 68
    0x10501861020345105403400700712580ea140100c1200d0090100303840f11519020b419100342032030301040304841c00341070ba11081040c1d03180d000e008003016041c0c00d41c0d40605030902d81d03041101c4c140001d0811130000406030204031071079811401d42c64000303402c584100d01052503207144c00c4500c8104d800443c0c120b41840280010840d0401800c02042021540a05800916039207041101e06c81c0c07280c44e00592189010880702e504c24507440e000c2c07500900d40030995034007084105140452180744d00310f5200f1018104110040745001541ea403241c1c40c0d07207140c40c000a00c04030950b1443d5400030807141d441c100c16a00b50b614000c001128041c51070350b22401d210715103801c0000e069443c41d0b070010380d16000c280a19551794440c2061609480d40900e9071060350707140b6000d205404c04010000c03000c0c0001007041502d01c25407072000d41a0340c0102800401c0281c001d2400c9440d4450001111083c841c10302142d150503a80801c04d00d98289541c50300c502580d500882c00e04a00c1200d90001e9040307880007548805 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 245049028 1250 245047778 245047793
    0x1106041a0904050901090f08030c2505010b010f0c062309010504030806030f100e03090a12020406050409020603041506120c0504060602030c0318030a1e020a060315050f061303 77
    0x5401d04a5040156550700328200b42a43c02080004249900303020f4035500017128000515000b6840031401403e109017036018001503038900c142038852107071040d016010480240224075558200b031a02ca461240c804401902c045010040140700541b0350802e1030030700004580554201103a101a0b070050309110205500800056600344d000441140c001105800d000940320064904513004110440c1201d00502c020142c06444074014001080014010754480320544090a028407035060320403134902c10003003200e1585d4405030081b0304010440d009696401d064a5010341c026018045c43c0380d0b1f038400900100200d801c00d400708000000c0d0030081c0700130080d4041c291401520100505510707458240c0c1e6a002e5241c1c582c0c1550b00c10002c94403070f61004032141e00b005201904031800b04981d81c0d241811016600038061090324407091038400d40c6030118143c0020f100f541002c00c0900020401c544294a15000750307409501191140541070705c94804030381c9111401d41c8540c114940b645000030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 245050278 1250 245049028 245049037
    0x20708071b0821091c0507060206071d060711090a020d1103040f021e0607080c0114010503100c0e15070203100b0a03020d02010224010807080106030c031106041a 71
    0x1400c1c1540000441e80d0b100008480100100d2908401402c400710243e40c0b800ea80300c13064081e0842c90314045041c8a5800c1c000c2107515900c01c8010f030070101e0412000034038101e4002c0c240410042d0200d06001c0c0080300054000510b042a580c0036a00c00c03943c1004070060080c01e0100390004081d4003080b810604a501901d808000c0303c90911041a40001c1c1c460140401d0b50050920b003252a06003006150101c0035101440390800e54401d844403000000b0025004600d066903210400554004002400c0c0315506e03c1610447e150102941440086942d5601404501312155030b038082806045002c1c0380ea4500c050303001811129514940e0056405540017803104074001d101c0e04d9010201401e15004c0c0c0300b8807070b501800c3d0401142c5103070204641800c110742c0031b90643c000e422039060225480c4100d0542d04440345a215000e5140007200e91600e850340c0d10818441e4540482440001c00450f440c0741241e8000c1440a0014a4800059214400c1b03501103214003c1d0781c038009070100049005403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 245051528 1250 245050278 245050313
    0x509012c1815041109040f080301060e0109170d080702011401030c050a080607050f030c040e090601060e0307050603010b180a0e01060e0a0305150901110706060e01060203040e070507030302070807 86
    0x1c0b22010580d4030300e0500350006440c028082d07003420384c1c6032800d070400300a2140d002e40505400074801d0380d02d4403a03a0180d4400e0b045100002d80e42215921130396007044024008084c85004105005130040c50a0385a0202849a208100303901c004620741134800d4200c1d0648040c07581a10a03c1d5942c1d281100071009107115680c0501d107910000100c41c0c00c0450aa840b407000368840754503211003040181401d601c003c0c0004c640000900000c075102c044c80101c1841909104010803165041080240242216900151084c0d119a505000c2a100c00007a64111103609920300d0311440d10212070007008020007200e9070130494220340056000803210100b03048071940c0e107030010700c0c00406040c4801c03448680400381059002d01e00200c15174403070b0880d450b8400300d50400007070301c3c10440300d01d01d24070761001030280e40741a107501c82400007a160303400142c01003d06000075494146019400c40c800913004091005001c2d0205408040c10300a8044900c519400f2200565030605c1c0c0ca0541038100880410 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 245052778 1250 245051528 245051533
    0x30106080706230f031b0706050c071a01120204020c250f080c0f010e01230c10090201020c1009081005220206031609050a09051f0509012c18 62
    0x602c944040604100d5500d03405084c001d61459840e1851120f04006c021031011042d5010802c480118a90340700d204c2c021604001c0260b81d503201070030a01c440202c9490b070040701d003845200400400d4001c140c2c500d010340d8140d40c0940c950a42d640070300e042c4000d085c400500c42242d4045825140f110b4000e044c20747c2c403001103100000751143c5140341d4540107141c90642201c0710704400c49441d8010b156040140c2014500008000c1290350524030052000200303425600000c60802048807060080c0c00e6940309040c42003200030540c2c2c00003955800c4610b42a806807040a28060141c0c0c45008100701825008046540e01c070003c110150041c48102c515080a030346080c066540001c51a510240454004080c542542c40c0c491481c401d1880006480703090294440002410b5250811001c009008008001406d40750524604203403584660b00507803801d140d000d060059a446203034242c1541d10001b14a00e0b002d0001e130150050b0031160440c0622a420b4400b000304a2034541441c41c46507040d0410b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 245054028 1250 245052778 245052827
    0xa0e03101802010f0c0c0501030e100c12140c1e0c030c0601031a190b0307081b0103270b1e090d1e080a05090a140c0109140906040b030106080706 64
    0x8080701c000245c2e6000801800c3e4000c020811580309400222001203140e06868950003500003420440e104c000102010980592040a43c4445c5210310700000200340c03408882407402c118441094072407900c141d042e8503550b49040c85035007004016544100c2d24070040b255903c1c840100503596960900c0115039800080c01d4080c64040662801c900035960040c0f0780340e4400400c0c8600000d1b00c2c5000303002d80c01d8811018002a410340400034000440c7e1001c603491070200c0401c0006060700c200460820b451041580750240811064014610003034201e003822185c0c0d03c40d000500400180c08105401500c412420301001d100e001c00c2c901a4099503448034038501800c0c1c80c51801c1d009461160038080390003940080e000d0351164010580c0300c9420310a40b0007080190782c03202101d0700d101e9105186640000c00c1102d442d41c0000780b001c040c19404083c0750f000c400410000384200402400ca9000c0c7d80c81b5a424078203074078250050005814003500303481e01c841d1501c2d00206881c00c444440c840810501c0c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 245055278 1250 245054028 245054057
    0x819051207050c0c100e0303040603021206060a02070902031b040b18040b030c0915040e06010602010c1d0409060b06040b0d0b0d0f02400c080603030a0e0310180201 72
    0x30200c803e540042400b409024a03564100511002410300d064107101d421080451076940034001480500040c0e2401600d5400707070810000100b40007403001d03000d400c0400c28a0b14032600022a8000c0391220600503949641703d1101c0080410700001c0080b02d0301012a0204420501c2e00181c0464201500651102c40504003084243c1e4016010f56030142c1000420140340d05080503150b0780b10603a902c1c8110400e0044000c01d04a1381d0f0f42c0303600c1805800100051144541c203000b40d071910307a02864031508900b00355201c5c82c1221004282144a03e40e1903c0750420400385400807170074104020721840c5c40e140e44203e17108541c2d21045141a00c41d00d000c4200f0942c0c0b906112000b42117800c03030382e2100103040c1365003404086229a15041a0101c82c070012220502c40785007400c0d007950185094400909040304480c0681d054602414140003200c020044140c07800410387e01c40f08594a0500c44080342000424142608a0f04040000c0d0402d122407031000144c6c010700342c44c24401e80e200b0f1211a10030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 245056528 1250 245055278 245055287
    0xc060f0705030a0914030c0102070203070b030c04270c0801051008040c121a1f05120c13090b0f0403110a03080a05071b03081b0405010c08070819051207 67
    0x4495010101c0c1003400490001d055a40c080c0701c960740314a0441c0d5000107140481c61554000b501c0d080b00581d0009206411030400344142c10042c1000e1103c0350071418441090031081c041e1380180000d01ca80d2249651044607100e1102100710221042000305800f0000000c08080090140794000e18040d11340c0d16155204550042c416a085201040c03054100a00e03c200b080304031000340c4914019841085580c41d551580c1c501400d005100e407910100c0010002039a8083ca50102e807054049001c2d03c500326802080014007103400716801d12420303213084034404c024241d03c14080c1603114041c1c10010840f1400c0d0b4142c1c09140a038480c40f40480384c0c00e00c1265110f0391100d00600180d1f4650204000213840d411168220505081c660300f1001c0d4881d0110b07010803c0c81e4260001118081440704140207c01030803220424048034170310f402d08100000c2d000918002d03006001540000381035050000000503201401080f1140d0300310340c8000c081c02440382c1c00a00741c0c4807000f00322078041600c3d40d00a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 245057778 1250 245056528 245056531
    0x10120605060a0c0f020409140307021512040201082e0503071a0d18120f0f0206150f030a121806020601060e19090507030f060e060102070e1f0603020c060f 68
    0xb40d54418240304040c1d0340c1d40310b0f01c15408030704a81094456402d01c00143c84880400100c150035001940c80303542c2c034010070454062007030b51355140d40002c12000202d40144160030794080d40a0070102c5180d02d07000070b00d0b200607590807000550011103a1400702c441030308000c08422107404504480803d038903404c540743c02c00d0300396a90b040c8600b02003010806404080e0020159045140407041500040741c5a8410385a81010360070009810306004803030903034200389040c0c400c0b50140700420b12898260f104080c164420524244680044414a98243e0b010080c4d081031591000e50000720b001d001f600503010f407510b420400301600e050140400e01520006019040301c5496485807043c10070141405010f02d0302c40d0001c03555005d040008500c800d164010310b801800780780c2c0c3c00038018202c5011130048a031581c0201c41089903203414003030aaa030010304070f01500c80d00404101d56441c0c1c0d06402d0800c9003c04501442030446000001d401034040d400b81100080c01c000f510000d5450200c1c10106000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 245059028 1250 245057778 245057797
    0x6120711160f0f080d080a020c0d05030f10080601060c020d020612090f1b04050a0f06260102211e070c0c08030a1d0109091a1219020105090f1012060506 67
    0x480d17103c94040601c518140c40d00142018401803070f02070320100080c24101d0b030000000201d0400010300515200103e001e0794407000303010307040d00e4140c00c00352000e44448040c07080300e041109104414003075607512142c1c06c020036801041190f0b12801e0803001006070400300c0d842d0001d401103a22640d074000e40490440c41c40b005e4044c46180280c4400100001804050204480d05680b0020190b41d50a00e204607005007110034245100c0141304020000d007000c41001126027a4018014100e041c02101c028032a50a22070201d0007a658808184140d501340c0d00b500c8a03403159030101849456500a80d03190652030003401c8844080d521159603d41e03a105285541000402d100da0301c0c0311564200140c4600b10f101450103115055444441d80161001009009000300c40079011551500d80200c082403480a460080e00d0a4599000b4807101000d000c60b001e410700000085403901ca81c0ca202c0d00d0500380c0303c003e000e0781e2517083c1002d00610340e810302440c404440b458604003140ca8a488003d9032030905 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 245060278 1250 245059028 245059033
    0x40c0f020a170c0a0b06040e03070809060702010c17040504050604091112101d0c010201060303091811040806060f0f0f060c10022101060e06120711160f0f08 69
    0x2161940c590040d041240c09020304000c1c14490f0390080e990034052448407a006034854600c5060420802040711101d10b19961154410400140002c1202081e80c61104e01220399a856a0450005031512000071400409610341001a100300d065060050420349805032000c01c03043d9112400d10044401402014003403c0b08040e01007400c1ca4070441d0304010a4152058541e4145000c80c42010340e030313513841a0380101090070302c000b4450390200101c0c400e2500074802070149c90302d5500c0150104005010341266203945518000781e000191300080201c01d00c00440943d65035503000e4054807500241c035058419000200405454941454400c2d080240142600c012210f00c0080044a501028402e011405030280c2e4000128007440a800c6207401c17410044180a12401e0f01c80c0b502405801c840d0034007070002c02c0302d20191180025105020001d00100351a51130300c00080c0c0e0032840310ad4010295104180015015008060310441240c00401a9028241d180e1070501b8412699001d01a0560f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 245061528 1250 245060278 245060293
    0xd0609020f0d0f1b0f020c06130501180815060405090c030303013503210f011205010213180b030f0d0e12031201140d050c01180b0309060105040c0f02 66
    0xc046942c0f01c48259000d0210001e20000c0c3d41040104042007504000f000c908542102d81c039894042c044003540c4d0504071041898880f4810808030788000300d000c1c080c1017201c0b28185d28002c41401c000341000d807011500300c8881d40c00ca04141d0344c066030115615030180d420040400d101d400b000980c1d11038600c00a0107141168204800d90161210721075480403d913112254246850203854114540c0143c20009107582d800d89600d070510030444229071980150814081120607080030807000c0c1510140309907150700140340d0070b10b5400b80c0507a1144004841d025100010f545c401107054500c480104c81c03050041d280104109a254903400344210626000851035107051031040030705c00d804100c010154180103950080d81842c40c0c01208100380e420380c422006004c45070828504142d003010445a60001a480e6a111034444c12f5100c0141e041c0003105024a0308004c401024902500e2100d141e50340340e15260080c0da0341c1d07031402e11a1301d0103180742c14030b80c04296214075a004040600c580091109 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 245062778 1250 245061528 245061547
    0x3040c210f08030601090b030a02090f0909060402060304020d060c0909060605070f020d02031212040507050a14090727050f04022104150e0a060506030606030d030f020f0408030d0609020f 82
    0x160740f000704041e041007090b000c0810905d08000146005036494500140c49150100c284170114100c840e0584c82a42020b04004085070000354840d0320983c1540c0172a2031303071520700c04941d401c058004000d01031800c1404408841e0b0f0b0007020f8070129481103606001e060b0760fa41050781c0790321600601610001d400d0502d8400b41c01d107082c50403041c6101600b258910800008401d00d188c219100b4881402c0c81031082c08140101008010013414048074610a9285480e0020354415140300700c0f540a004010700107030f580c5000e24003d44903404400c040b800104201c0f44900710210f940e000b04c030320503500458144480e041c1482a40c0031980034401d49124800200309036000c0050040086031002d218400c00c0d58003110b02d0284d1400b0107000703801004c0a074018508841944e40040445010342d2001c02048081d03a4002500344510042d8100050107010410381c3c58060b104808a43d04105400500081c2a110000080c1000d60290108215054840c8019000d921407a40c154014a4041c0444101c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 245064028 1250 245062778 245062793
    0xc0f11070b03060a05040203040506010306051608010e060d0605010b2d0304150b04020406050702120a03080a0b030f16030b0703020702030705040f1508030a09080a080301031e0803040c210f 83
    0x2040f08000b02024001a80c640000d010380e84125001c03030741900302e4001041089030500400340c02c00c0d0690456400d602e84010010600441441048000c4820001107003080e1201e40074000c0041e00030006101540e12101ea00500354000350120703108000d0525004050550380e4806000411a0780c541c6195880d80c0d1100040421001401011036517244442c82c400d41e101e100a00c02040306488407074072180b0600400030300c030600490912840e0010481c41002980c031428242e44207403182d40c00a918119540441c0c5008100f0040080034802c40503250311a00d00d00311328008172445102003007140d40d94280c1c214140e0003481d000030b4150388406003e00403460a82c0101042c40150140050040c4000802d400074004135801040a038100143d10081a50300c030340004094210303400100301c1c41400d555010203074803051001600c0207058070301721416400304403102341840e500880403d03143e040500304000d611060b4458440e003c00d00450300c81c03a203500442400e03c0142c00050721642403020751030707d80 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 245065278 1250 245064028 245064031
    0xc04270b15040605030c0f031626010209031e0106050a0e1f1d04080d180302061e01090c0504050904060b0405010f2d08030720041404080a030207020409060c0f11070b03 74
    0x29414040e0000c80502c09502d09407000080000c1400c030142c202c50305044105084ac40510035401d81d0041001071000d890015022203035030700ca002c0f9014030030200340c0c00314014140e45d084a940203000c0400090000c61501000c2e0040e5004048038030105c02903002580c1c030802c10704c0394455410070100301884110b225410070768000d00459407d4a419841140d44040f11143c05401d40700460f0400e40509150341085a25800450100302e424580c4034500c50007402081445104207144c0c43c0d00c02c0c1200d0300e108070140d40003000083e280001604140c601035003e0010700c401c1902aa15110001401c0c840ca034100c101152642c00d13114044064511801660707141a040c0ca81d01b060180b00009130f140410030007041c4041c0115120041c106c401620010401030100419200e6402c0002200300b02d245c0351009900141c0c02030600e6500c4000b07500507000b81c001c501000e90322178a03060309003040c0315840c0c003c8031500c510b50340c811000a00510050790314043c20082414982d0000d1810f1000542010055 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 245066528 1250 245065278 245065309
    0x5030606070b01030503121602120708130b030a05061f030b0d05060106120f050c0405060a0e060415030c022b0c0206040f08070f05030c04270b15040605030c 69
    0xc61400c0182c1d1030320360001d03401303074411a9a80e20001d92900e4002180144581000c0c0300143c0d07580001030108029074a81d00803941d581c0750080000ca950400200c50121043d503015807402681c81c554501d1510140d0300100d41901030344e8103010014445180081110004054240611084207001a41180184007610300c040d00005051020000b00d2010031203140208415a03940d8001014090082c06499440c042e4038012400d080c2840424401d540071394060b10b1080c0c5580e5180d41441c03d00b11030003104401c1050f00810300090106046a88806100260304180c0742030012114111040313940790b4400f490302c1c0040304484941c04d030300b002c0039866a020f00001d00d070a010500302e540008409174013550015080700b4907a04204900401402050018500341c11840b60162909011130781b5000400c8074644207641d11081441d204d03140f1401e50342c0280702000c50382c81149052424524008058890340c510401700022080e81c4d241a0040a00762a005809810800030410910070143c500d0140b1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 245067778 1250 245066528 245066539
    0x7050d0207051219091212020304090c0306030b0606070314090630010b0301121203091b1a040f03060507020f0a060c1205090309011107090f0b0a1410050306 69
    0x2004003191041020f5001e103900a040160303240300340c41e40511614031101000c000e00500d1030303040142200e1001381029954016035501c0100d002800e04030b09500c0f5a0304070000a07840d003e52264420f40c1070b4402004c0d60700c26102203d407038480000304200e0b4040e040d802000035043c980c20082c148a801e018100100010702401d09060003140640d40006a203032020001d10008064811000101000240140740d046091407542d41003401c0e480b1810f100070000352060350804202000305104c0d0340301c2c1510a80043c264004484074840007601041948a03010b51030101c450301c075502501060803a0304452003180650216480c5a58103000340c1070040403c1d0550080c980c0a20900e00c0510a0700105841007900181c003402000300a40008a400d05140700e00b40782c0020003814010000c115000004242031090350542060101450101319400401c15142030101c6860b00780f08036001203840310011a007802e803ca88075210354007044030040030954020040d41c1d1000485010b81e0003950000b502415 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 245069028 1250 245067778 245067787
    0xe13030905060f0c190f08130b03010b030f07050f07110d081201030606090903090501031d0d0e031e030a080a0b06040303051b010e0d0f11060a3207050d02 68
    0xda0039400803c009840c049000a200c00aaa000e00002000342c2d840907105607512203d0b1507901c103070202c03500001d00d100d07000100d01203040b4041c00e01f1002840f070790030059900c0d80c407221a1043c0d90815a0780444201600d008214094003540030b403094500780d1943c050504200d41c90350080b040700c6103c150f41112200144a01084060000300740b450045107605a10b0b5140d49004011160745d6804100114a1706240d08006035004051038100c1c0d500746000308040c0c001c680110404400c4600c18070342485812403030092607070400380003101444105c007070310200c400103401c1010112024401c0c0d03d59070420006030a03110300480003150002221040092202040c402207241607020380c00035004075038080f6400e00404000c40c00c4542c0250314078028880d5291480c43e156460840041e1002404210060001994483c48088079112820000c80782c150a0680c543e0008010351000c502d8003450741c40301114400031640c00303584010300e61450030000d50744800c4111440d410507080700078155020030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 245070278 1250 245069028 245069039
    0x609150d11040903020a020306070207050d020609040e0d0806011106040b010b0f0c010f090606051906050d020c0319020d050c0615040f0e010f150806010b070317010f050315010e130309 81
    0x300f100f100038820340081503034450f580109482c118008200d4021075014410030303c02500d44400c0281d034603906480150715400148006006404180414485803046800c542e0502c4d43c0004143d0142c070007a2280e00d0040c1c8aa003a441d100d40d0221000b800b8803210b030004004c030002c0c0700010b110a6040580942c10300942100c41d500707548005442c40c0042d5262040e4009101c2c1a10407900100380031905400d25080d031590703a000030b819901c20300341809804140d030901002030350100d400c000061401d9940c2c90605c0d540000083d1a440c401714014410f60680f103018900620495410307020000080040d40e8a212007403018100f05251a03401540f9100aa8110081d6016803280f410b00e450010030720b011301024500403107a03601680d40b5a1095214104449200418802d0644a5420f00b055603605542002d81e0800ca21078401c241d07a10b100070000071710a403100104c000b644c004400f0b440080000e8486400070040a00801e2407108039038011038014121410480d50a600c80d042800c1e00a9683c07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 245071528 1250 245070278 245070281
    0x17220b060a0803030106020a050c06030402030d080624070501060603020306130504021503010303080f090c0123091807020f0601301407090e0f031e19030903080609150d1104 76
    0x31b86c80300d00564003000403401004003d08c15000d100c4000d445140c1145001d800280d9582d45151240040c4585403000c140c0c581c4401140005400d0030034100320a900041c040340d1441d5004a100340c0380d41d40381940c040f03925403081c0212801084001e043c00b800e030042c194080020714000d0812030380951101901ca56820071900914001e502907101c001a40c0380c00100089040070040100185400c000c40401580c1e030071000542503d401501d081c4004400004015018400d007000240c3c00030000c1a034035500301d85254414450402035080d25404003d00b1019941c0c1d1000780610060300051208960100380070030340052145001d81c1d500300c047c04842d02c0e00c140504d00034245440c00d4002440c1440300c0307202806a05078080f603200c0101041c048044000303480340074452041059559020411040f010b0031000e607134161101107000c6001c5100c000300640140940d1030100d0108042c000012400d00e4914080341c8a90440080015407030307550700400c00500c540401c2100c1c05404614007075601c3d240c9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 245072778 1250 245071528 245071531
    0x2060307050405090403050a020d0906050d020a0c0203070e040c092903030d090b070f14030601051b1f05090307020d020423090313270209060409090317220b060a080303 74
    0x82d484459440d094001c8c004d0500c4140c41000b810f1000c025820001d00307900004a0b86400115100140c55000f0b002d4100e40c450f48032040607501d44202c5902141c0e90169254460245206004a006540c1d403000c816040d1480d00210701c80c6400c0000341c4007001c0908070002040000001d041d81c1c5003800c48005901151042c42054071201c10a01c10841411780280c0d078607004d44041c1c00c01e0b02690a00351408901484010055410450302040345407070500511010302d068a01002a6102e10808400b900e40d031429003120506e1076800c020201d01800d03404030803144855005030461280741015000d20024142100c004030b440d224591130440c3d0140c05500941c0a050418043c5a50b810862090b491548a50b04507007620700126404180c5941413866001091a80200c05a1142c42c21000200c82c0d000303560003100c1036400c0c0740c0f4800c201030344881c00c0350796200b03605410b0021f40c6410500c00b8000d031082040140081180d650080450080f2603040d601000040c080d080d0356031070b904a9800c5810 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 245074028 1250 245072778 245072783
    0xd05010504020906040e0601050409021c1202010501062d05040b0c0c032401030b0709150503190507090302130608031c271b0f14040e0304030c03020603070504050904 73
    0x15114107000440c5440b880194120704100c40a000d4108800241912540107100d540d02c616a1450b0035006c544030030040c40d1a0ba5001418400032502c203040400030703241d8111228005518020010070100e00588226041e208100265000000b54440700d08500b2040b8440c05d050200901c000a0b07620704010041c119038601d60054507440c602c0c107060601d010485245014002c0302601c0416a15082c1d01002e411250442011000c0b07417503440c400e40e90b8460310703000b040c103001044490298a9404c000118000d806125541420b018003103101411218262180400240c03070030003c20141c13401d059903005146c841500060500e5480300c1040c07840c0d103c1d40a5a407002c1210140306060100e5200d079100c446042110320038020071030300491400d10150b0300300401101c3c40140003414102c045490401501d003040d04210700c40e071262031502101000c464402c1c881ca040080c403840002020082d0780c100d070b81c41541c140541d0309680c00c10265410041091040202c1400006187d548010240b4000e90 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 245075278 1250 245074028 245074031
    0x3050306030f0d050c060604050c0a0f05070803042010090b0f09090f2208070303091511091e0d020f010c0c0f240e1003060b0f041523030c04050d0501 66
    0x5000305d40c240f81d00204414840c3c0d01c1c1504009581c2e01d41e0003128080c078254a040d04249009d05000d4500703000300500075001210100c00c00003002903044210420f02c10541c0c0c0340b1516240b5104001c80e000440144a000900c604d50400854080001600a82e42a20b4601e82484400c0020841010003240d1607054200c0c6201440440211440e10203200d5042600f012a490940d4441112510415600908050780c03080c9200902c023403c40309a0a60000e14801d100400b042046201e060700446c50051060009080d2000081c84682d05948078400140c1030007410b0005800b002450920001130a041c00307584c6541d400050700050301100542014070040c1052820116904013120300303a0703540f50741d5401444080c010150041c0d61400e45000854070029203059201d411800f41025900c030035450035012401105142104001e001030b9001c0381002280500801c0f070485005500c10000d80c40751010701c40a11881f81100011588650484151484c2c00d59403c04284903005525017a200359 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 245076528 1250 245075278 245075287
    0x1403041b0515090d02040609020a0e031902031203101703130b030103030c06090606080708010f0f060e07050a0201061802070308100f0e060d0b0702030a0e03060c040303050306030f0d05 81
    0x4452000005400140d40700ca0542c007860100e61041d1040015080c03003092208141e40441d40e642d000480a030408074401d42d2102251000900034090210b00d161280c01215a40c1120101c5001da000c0f0b90781c0c00a00402c5030300b40740326008801e03510140030f161804880c11000314005140c80741006000300301c000155501e41000c0c20030450004c02d40c10441d4600c404000401c00f02e644a000071045030b40005000849134458a0003030000e0030954090007190040403070002d41c020065210030ba400c20111024003100d20aa2682d60403540607005140501d0511008100c4480c840c10141603400c4860000107501d50304c410601510f2142001140c0005400280030000c1550044046402c0300307142d40380024140c1021820040e0795090f0280c1100b0305080c00000d00903564054807501850340002c207031400703401c210728001d4581d80f1800718400419198000506e1034200000c0e014400c064980e085803d00f42036607011503d41d840a4280b552511401309070201461092101c001000d000d80c65032541c5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 245077778 1250 245076528 245076563
    0x30305180303072604060e1c060f2a0804200418031818020c03120c04170c010203070b0405010905070e190b0a05040b011205010b04051c0f12140304 65
    0x42139507048198941c5052204020050f0040116181071208486042c611181510030890b082c40c0c4040c06000c43c1e040041c00902600c09a01612030764210300c00f2640b030401c0e8640380001544814800c21b00164400c0001000303d0305c103800e8419805458511395040407140d8000505841d018405c03054407201c150f003201c081503080402d4078440c5070b2128000a9642ca400d4980b108010400507106001e5000105902c00000c00e00440d10281100100e118035400c04448500042d0030034014100300611240c608152000c00042940010005038001c5252614607680c210b410140904203c483d5926035003642c0c0003c8d0306004810261001902d216807070315000c0700c042c4141c5110036000e80b2041c0b4003640c0c3c2c03082e5100c80c0f028030242e44040e200800d84c450300c080101c507280414005604090b181c038001045400307039500148103c0d02c0856041c6800501c00138040c01c15175569000906406881018200140340304000348100300e142d082034070109401e440341030340c0742c1d2007150700312541040381040500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 245079028 1250 245077778 245077823
    0x31e051c0504050c09092107050c0306010f0603020f07050d0810060c1e110a120632060301020d1107020901060f121107020406080a020108150a03030518030307 70
    0x103901a00c0c01003841541043e40300c4949460708840000d02414602000038030307000003080769140303060b00744c2081610080f0220880425401411084941d07000d54a001086440c00003032aa050300c1c040f05200720058a420320640003075000e200441070b681000d201050102d102480307005086800b988521031180341210740c0040011541d0080e0703050155034400d000110b1010805466044e02c03100f0010888401401c1c040c1006055001c030070b51060000c4008a610344100702d8002c1100e12802c420320003d04c8007400c10455180c6203810102c0d0005a20b02400c204003621f0803c0d4100340b01400040c03900d50748041e010156001c1c21948414102e000440404505101401c1801001c82e03113840f65100e0a12100203154814a40c40f58018640300c130301d601144100c00c0c0c100d405180d03009004120b015910604141c031805010800da011a80800000c0c1c400c844081d100000c0c000e00a1400c01d0181c03c40d681611190400004403020505c43c0813080c226803000c03c02007403c24010804c2c0d0a4140700702c005002c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 245080278 1250 245079028 245079067
    0x2010c0305090f070528031a0702070b031501090f0920090906010507030e0306010e04140106060e0103020f09091f09090f060b03100c030e100204050a050d031e05 71
    0x1c80b507522a02038980001804641041507500c2200d030f0000c0c95007001080e45051503a4800e90030304a0b200c5000000704040c4000c0605000000e81d0004041c2c0d44001080c1c0c0c4445040c401d122030001c0810001d00d4a01c403000d400c03c1042c030f0505111486a880b11590141c0100355040003d0083d07a400411402003040d000c106010b072025840140f4100d21a00401c02413200507120341c0c144880482c2e40030416025102d5400348600180c1140c0440d82e42d502c0750b04070181d0540d8140d803072120094003450102418020345064801544900e40c0c401e4050700110001c1d80a45008010751209202000c0e045da1080314050040340e4503134084484449000d0b258480c10465484001a40e01e00692030000800c0c0e59185059942c1090300010b05a0504006c079081074000301c840040645020b00d01d0500940641c800d21448401c40102c0d1059920500300d04202e00c914007a0aa01012b403a0003008249051180080c643d44a4500310311000241c41a641d189884521002c0108902188060b80c4805449104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 245081528 1250 245080278 245080291
    0x608070f052b0b06090a0302041805190317072316050f01050c03010303121a0607060c0801050105070525030f0b04150b0d0b090c06040305011e090519060605040c02010c0305 76
    0x44e403524810340000340003c01644030090003070381c0341c00b0600001109a0380d2880c1240d0000103035124921b2242485501d03a080b0481140840c2ca01d103821126801c4d400305103031155102d034850480000d051901e035604941448040c4a0b13240c000c02020090380d21b554100101c5030311035001082803402d240f01076401e45100402c024040a070a200410109074802070000d88032419440000b01c49000d488940000103003004c90036084040080c1c81420441721f80e10455050b00c0c0c81da03031f8540d566200c1004445070710407480080c129a22107074078117007070803040d2050442a0341c12640010740150b4a544484802d8400d1000785c80307050f00601007106001d40300c04510000c60700344e1401c00c007003140e81000901e890041d10000c2c000c20380c1180058194201004203074078407034005019075151a1340f450814041c103038220148403090301d0b964800c11021600c1c0191703032110341d00c80c01403c00c500c0c100c00c5140040030a8941039594680314030001409844070301c40c09803c1007590340049801081444040d007034540185c81d4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 245082778 1250 245081528 245081539
    0x1c14120c0d1b0f050102091809010b09190515120304060f050406140a030605060d06050a080a0309150e040603150e121e0f0c03030915010608070f052b0b 67
    0x80c2041c094451401d82c055003d244500145043d0400c14024050a14241e40200309226105074503014680001e00c15800c200090111640342014001c00107810f90700d45088400b034501c440124422504120340c04290501d04840d41c030030320f000003403078003406000c0840e081d0000201400580e41c8981e244c02485800d09119242c0361901e84024500200362400c030000d14004606440810f109401100083c0001010584c40d5440b1081110003002c8511501d4032803480305600090049000c2110303581c594250700c0c0c040c0c580d494401c0996500005064541c100b1444803072641440c1e0b2148210000303113008499a01d42401c01c200c201040316849101001d43d40c0c01001460030307139a0b503081280c400c80400400104c075440b1805c5100d00703602582c3d00303c4c141c2420105252a544d18008061807294000380126041a500e1658010341c0c1d030402c0c016070000031401c50005030b070f8070300030083e50203030b0011850200c2c07030600050710200c08080c0b030300f151224215000698280c50300d0580200f40e00350804454 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 245084028 1250 245082778 245082797
    0x2130909120503042a0603060603060b0f03040f1707120203030f1906050301060902090a050d152007031110140a090212030c0304050a0b04051c14120c0d 67
    0x16240012180e0007807034010008000002001c0001402c030088100c2d052109055204801c0f44041102000c0790040c440001d10300a800190b0a1007809004101c23140c0e001e641307250144000000c61313268401442541c0340d5008030301c0ea03000107030720400382c24518510109440d211001440c01e4520100c000c0c0c1c85070210750003030017032149040004126913045041c852104490704009807041015007203d80c881a0315510b8108001110843d64000b045c41060450307950903481d840d80708200207038034010005440c0c0c66164078080b680422540c021881c007001c070041620918170041c100710b0300e07a021101c1100040e0080d5080850340c030040240c2420540700c04401d20900802c50346544180500818032258143c680344240150b44440e500d0001505003c0c0699659808280d41d45076258042d20075a4050b5501c441c001a00c10984400e40302528002000c034a82282c0d0803030580e03524041c0c00702c10b0304c210081c1030342007200010070000c1000e1105001c10a503101d0a07107100c114140115803000f0002d2103843d60 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 245085278 1250 245084028 245084033
    0x140a0227030c0120030f220b0f07021903060c020606030d2a020d2a051804110a06020a030201050a090308072006070e030d0f0e04020f130902130909 65
    0xe0600c4402c03100786400071601a101c4151100785003a05100c90a90000044015041051320001c1c211140340011041e43d008000d80c0c15012181c9510401c0b11b480d00a00c04129a44135000c020070501d8002007403200f810f0ba40e40c0c00080d05c40310b681d0048401035600c07801034024540500c000b42d40207004a000c1d02140c441c1e449c2c041d00007919503920038000301c440326840e20050f805a017401011900644400d03042c205a01d03180c04550090010301d901c4040d956182040d10001043d000c1c165034000d00310310760011200c003502803030f400054000c46141c885c1d403540c26543c0d222403c0354001071099500403c418401c5050280c03c45001905000b00c050800909001084d00120900c0e000800c0d403804109581e404200c0701c25101e000021b0744868001c04051064042e4000901c0d0400e400032800e60b02e000b02844020764100d890340c04104042a01010081e40d686403d5000d08075402c020200d5a1900784240322484035943d1603044160b001d903012070354016044400c0024800342c41c480c841009105a00c1c1c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 245086528 1250 245085278 245085283
    0xb0a05010516031e030e06010b130e070c051f11030103020d020108091501060e010f050a090b0901030b090a051015090506090a0306150501030e0309130e01140a022703 73
    0x582542004070802c465400b01841804d20020f41c10001246500f10b00303003024004c018010364100709100348103841c00400d46846403821120710001600500304010300d0030006608941c00101031006001c4061105000305100703000001c41c0030100e441c0c805058144455560883d01406514166040140700500040e10ce1014540005409080001e0780765100d000003031814032084003804428009070b000040c0c068005010f641811303400d803203800c40000c15071070488460103a0051500060380d1501300700b107180c0a0f00002c0c0925031040c94041103e004501c0420002a015102c110300e81da5100200054402c40f0802031014040c000501d040042c0d28040c0180800720718002d0503c1034100148101c0d1070b540f004680f03c011a44400d00340002b16050605100c100074074032480f0b0100f820604080700c4e07030f000401150b1159a00034000e240c0c003221101454020700041c0c0210100e596101c0592085c00480c480484c410040f070040540d442c203040400100e0b40b030340414050b00f02c141c2c95072480c0659401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 245087778 1250 245086528 245086537
    0xf0f0b04090902240706061512240602060603070602010902010914042d0f0e0a0f1a0c0301061409090105090a0902060307020f0f062511011e0b0a050105 67
    0x41c02040c002d5250001801c0c0d0304814a0050b045a2820350361005090140040d04400740154010030030f0325956040320340700a03008408040003401040c902c50008581d68040c002d00c24511103281d00e1a100221401000d4906801c05005a80302c603080003614a400c008110251a03144002e0040b60711903800600020294013582d8440d0380309506032601915564012406e124880480c00204001013089026400e410340902c11a14200700d420f02c000e13a034074012080047c407800300501c010170050b01c40030f9961120300b00481d00124090f004c1e040408050800600506004600710f9880d45412805071080002d005c000b8036072003040c013816416640d00c094050459409a44020302640e54005160050131340040c002e60101c40803060210840e40003d2900031488003100b10f65250320622855a0303100030803150145824010101c002901c51540078903104a0824208400c6411030703a4601425a80f80c01d500403403002140f900046440c1c100d00414100c00e45c15541e15402d281001c000900a204 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 245089028 1250 245087778 245087789
    0x40c09080316173a0212010602060717150102030f13170a03080c0313020d1101030e0303130f0c08060412031103070c1106070605040b0a1b02063606010f0f0b04 70
    0x10080004104c404a0381081ca03612070142c0d003150794040a42c0c40004c0002e0031700a200061042d01c000403040750107005160a500411401e9000d190307610f1000d4006171004045e407504501080c0140310000051b20003414042403649000521141841150105001c10314031103030141c1e05c51000040440e0b085035080e9000b01480071090364960740e5582078803c0b40c16400c0002d411901170103403a400e110360401e40035043c1c442640c0600c00000c2c0c0c1d840880c2c1d00c0c041901c004c04100c2080304c000e40010140c04000300d8252150340e8030380c101c5a80307000f040d04108049501f0f0b10038000f5152004e01050707152040d1122080507000013420b50a08900040c51070b9141080100082c5600400f45540c0d82e070340d02039070412a8040b10501551929180c043c8060f042594410300c103500f05101982d1090200000c62440c030b081d80c1c01003829607219543c407a042d4140304011245c130440d07800c0001e4007103208220404040780b07000c000c200c50351401c1e002000407400b070352000d41c04100704542031041c035480108a401712072 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 245090278 1250 245089028 245089087
    0x11a0f07020f010c050f100c09081b01030e1917030106021903120e030c0d11030a2307030509130605030a0f0614160206010b03060a0302040c0908031617 67
    0xb803090300162500584004080c00904c2200e80c000551070000030000c07500280758605110810007c40142c90b41a03450080322800e41101d07400d107651009001d0001c0d24074005242c00b00d4206480b903510f03410040104101a070107949200b0000500c540d14130700c1c54005003140c000350f00d550314081c8000c0d20744445881c41000c1c2c0c2a25200c28040c10701c0f8894283c4400c4140e14200980b0044903001a40c0b5030226001895134041d10141822050080030020316000307040010b503282c000110402c403200b82e20301c00c9890b07504507203891020740c1455410140803003905c00c2d00c80e41e80d01d0a0030010019843d2480c50246070841c182542030050361800b0805001443e4420b5000040b21103d26004020b03103104c1d41c420541a4031001080a481440344220004070741907001e484081c0d0700d810206c1d040d4032088030390a0b08188071400410050900ba44011031181e80ca10740801215102e0110314250341c05512042041c2d121880103c0a0104a024144c0f001d50507161180c6442141d12517060350b00754002c01c80c800174 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 245091528 1250 245090278 245090299
    0x10504020d1b0306050306010504060602120c07080703150b04060308090f0d0515070908060907120f0b040602030615030f04020d0212060a0606030c0305072a0204060e011a0f0702 78
    0x341d5004001d80d580766a8407500c0941d00d89000034010042445103512a10441d00002183d081901c01d12060b80c42c2503000d001030800c040040c500384e902c14401d03103015105041002407800014404040a18858290300415004800c0020180c80000b08050321aa00c1d0160400c001099407007180da0b01d00080d1a0701013030219000004e40c000d0103084c4003904a0180c0c4c601c65440000240450b841055180c403010503243e241c021407071b83d50310210f0304104260300280c011700c203600b40c1010080040e481540001400702031541ca0101c44402070300d0465034140c010050026a04c2c003c1c0e1458000d0640c01c0e80741c2c1c210702d05071035110b080c400c024201078021203a040c0c86c0002c0d5294042a85a0010150212001400d08a072464020b011a1003080d0010703140022041e00c06e4840d008842c0561225551140701c2072541e0b0780d0b2984000c03035614141070740d8481401c0c100162558001c02c0d000b07101005400080750314100c41007058600c0f0740d84410007900200640b6400e043c01e00141c0300001e40544008489 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 245092778 1250 245091528 245091547
    0xb180c040905270303130f081b0f010e0f07090e01150b0c0705042a03150306090510061818060905030a030c2102180d0f060c090b0301050402 62
    0x3485941c11100041d41000c0c20400181c1c008111030762a0a50006102012025200183e13180d01003074640b0107003c140c016040340885c0307038510112082030054910601c1d02042c2c2e19096202c402445d11000d654006c071011150491080c0b01c0c0140408405018006d881d0780c044495450300801d0013201e48659031610702440c3c80c14258414501d05100611301918552500c016070280c0e008610001075078440c1140c00f2070f80d414280500c140c00d2914840900144960925091503080060309400805a403904208040b5100d07a04903c0150700a03000003c54440e282012814a40c402102400c1c0c5801c00340200101e2103106014040303030119107000604e0104070440745d0070343c0d9001d180c0604803505048181c005d204020009026611181d2410803a421559400703407005a809204090003c182c0700300c0d6616007889800524045034051f0558040301c90810000d4083c940c142c0b400d640b83d103525280c0108101d801c0c03080070850403413428880507252404810004500c014001e090007513401003101d068 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 245094028 1250 245092778 245092801
    0x105030a0209090106090311040606050304021002160f09050c041208130302090a05012405030a0b010c0b0702010c020714031024031202100509190507030f110a0503010b18 75
    0xc07030b080010071001c407035691400024094401d500041d00c1400d500c80c01c0b15410f00e4544950780c21103001d51070315420f40d0b4a84d0200600300700c1060b841310544c0500c0c507818a080c6d40f07040c85480a0b20551141701d0480e420407103000c080303440050800001200c100410f000304d211016100180075444104141d40d212000c05000d0040525800250048402010300090310410342146e0305883c5100145491988032007a900a4035501c2d400781004a1170400c041841e012068222050042c01030416a0f01c0f43c82c0c0e55200d040c0f09400303c0705140140d548603185482c8a0381800020000c0a0b0100312000540000c00040c0e20f0780c0c00100c095003000d03903480802c0c121410101c040c00c030781041c04020350480c69682c205940c4200b0400c0d9800014080d48106ca00703016958823925005a04001c000c03d442010080e030310241d01401102640c080c070400c040000010340364210340d103216104641450042c0190018031414a0391500b2070343c031990400324020141c2c5c45034000e00c007401040c0e140248298079069003958 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 245095278 1250 245094028 245094037
    0x1701031416060e120d0e010311071e02090702060f0f100509070201090c1a07020405100b0d0e0d08040305070b0709050409030216060c0c030b0402060909090105060a0806010b090105030a02 82
    0x400024400c0020015080040041c0030f40065a108820f004028103107521561001c040402061340d04040b04201e500c60b620003880300d0b140741940b600d403002070f840728040c80d00c2e9240d01801141d10b1038044011810001e50650b00f01501d0300007003845041c007441150640310000c040100c0c0b04c030842e001545c1c0002c03403101e11000300006455107249040101d4024040c0400490075104110700c0c100000d0340c1118188540d411030710310000981020030550802011781800750003111400c1850201050400c0e40c4001868501008080020352040b00e81c00b050820b001005014140300a21080101007034001c0c081344d41e820f50007640920169030f804000c0c0d400d8000e907000142c020707281050100802d0340010350a4010310243e0440e08000b47c5ea000d007191345041010008009074000d10041000402030000307142c01600c01820a81003000400c0403c0800800302c0e101622607440d101801000d007005410040a00001030140c005503050092488075489910b0003e4100300c800000903000162690654 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 245096528 1250 245095278 245095303
    0x40e04020d0b04050c0a0b0f0a05092b0c0b28090b03090d020106120c0302060a020307080f04180b0a23030d03050709090c0e0d02120105040302010c020d17010314 71
    0x802c6641480c1c10b14a80d2100310840c528041e491291010501e0a101d1003902c00134206c5650b520702c2c002180800f10b485400804099030408500480c0030b01e254405081c2056907944412003088850142c21308050500640e80b124203000010448090416425030904600c0c6001070b1102071941040034048501320010381c04890710080c0030050200881c0041aa0908000e15600034040c140d120b000700300c0d901c007021800400070343c2181800c100500345600606540c1a40340140c3e41803d5054842c0350341c40d07108071013010311400001011b000703c022900104030ba896040c88208a0040301501090b4861038900403081507813124112000c9104a05c3c841e0780000c3c1001e000c2d03550f80c40c41144044c0141ca4156242da0100d020141d0225680d95107100d00c40540e850340e07450000b0048020103100180108442c03da0f0010b00b650488640303c40c090150601441c445c2d40000f404945a11000b4180a800b072030300b004000300340543c10324180411841a06603500600002140b0b0744201700a4030700700b403d4100c03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 245097778 1250 245096528 245096543
    0xa030f0f0b0106110c09010509012c010f0312030513110f03010f1a1f050a0909021c0c030e0303010e180a030906090e0123040b06070609110906010203040e04020d 71
    0x8200300b5481030900913002620390455031038034000001c00c81d13070344024000c85811030038640c01000358a420311030070300039000101c120540042902c650003809600076080100d20400c1030504104018030103006c50000822494100046e0521030b261409c25404690b000c3c24941c081c400449981c0e58a480b02c0700c001000034003c1040c1004d600e501c1c405003455030200365406052114554007410424000c80c1c0c0c2162400d80b00c03c0e0070002c903409403040c0d0018002d5604022400c040400c85045a10081c03e0080c50000350740800508120101e06480d003c000e280c4c1050300700070400c004d01c00700109483c1901e141b902c0c22007d03a50381c180300c0c9980c030b0603518202d019440b4145035201415000490b12054400c0c1713594043c4043d49a00141281040c04c0c0300b1004804014a416a941e1100410241c58800010800300e04144048005a01900002000d4a00b66a5182c52004000410344c1092490034141d9100200e407500c040040e4483c000c41c4a10b074000201d02d00010110354455004070107070381d80200d0303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 245099028 1250 245097778 245097781
    0x309060a0c1e0c12020712060905150108010e0106060e0303070b0c0f1201030302070603050408220302040e0f0120030115090b0d05093009040e010501080105071d0a030f0f0b 76
    0x8000f85005415182030390b510021411020415101107900c600303440c1c0292200c54102100d50300c200040641d6002940e1900401c1069000c4403110760b405802040c40c03c0020a160b00c59941143c00c56400b9808007080c42801030105049444c00b00a1315641e0383c000c00c80c00c6a50769828494002803040c042010000380b0000345040c02140c0c2c218049060340d0196003180d450903103c2400380d013221420348003c3c105480a02c180c50211500e514000d01c9031110b910441800340d0380358049410340c0c150030303c00b550b02e0300940054044000c0900c100e00044000c00d20140015885480041491106006040720550002403031031000d40100401c030020110280060780d94480400c04000a28003a2881100d500654040c0c003c0700d035048020060104184044c55103d0082c3d00803251607602c40901c15411940f51082c000322500288030709402801024000724840c540000020444c80490349a8408a16182131807421a01c4409101c02543c3e404419250070254901300400082c0c40c12800500102c00d450 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 245100278 1250 245099028 245099087
    0x1a03010c0903120f080109050c0c0f010507030c05030c1213080d09021302090f040203180715020f07060807030911030a12120204031e06021b0309030d050309060a0c 72
    0x300300714200c90003400d00008162142c2400c90300704401010420025522200512007aa02c56000b250001c003800d021601c3d10a50f00100c60400b050640e0501c20782c0d56490800c40e5880e00341c01955840541072400c41d2840c0b500381c0106901e409404650500e06280c800081c05019140f5403440215400200c03aa0b1511f07404800a005004101022801031210000c0904d92418030b00a0b913480600040102c150380e0052000d10000750002040e0402c0200c21401c189540c88040c001c44014024034411030b6000c110800d4040d16108803221000300e150720140003042443e50040c10a500a155407501144500c46030501e80e06103031f901c40c6905d0381400341250203000c101c411440010003006130f4443c2030842d01a121450103d008500c005000c000848901c3c0c03d00c40c480d01c001c003140911a0100506282c0d05080380400409120780300160780d0b00010700305190f894204001055115945440e91844c40c00c0e5881d5074480d5405807440c0c0419803580820210315008080c842e0000c13034100c031802d00b95032941 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 245101528 1250 245100278 245100287
    0x40602070c090b01021005191104030c0506190809030d050915010f080307060b04200a08060301091110021f09060f0203060a03030c0f021005030906060d02090a1a03010c 74
    0x103002141d074400c60410005080b507160007019100c0c1416000f800340405035000031806081b0003001c503040c4c1e50b91000b4020b65a0094481d032008940316051b00c6845a0551030b140c012121690002c91091405002407500740006898101c00e0000f40d14021400c0d84a91400a1650081c103610244403400c0004100c84103000081e614006c281604a0005507680c85407402400c00c013074090580e540d0420000000030507842e810004c40864050400034120403400e0403c1c1100d00e444991070300d5200300050b001c030720725070104000b03070000c05c118000c001c201d0719560348075014410500c0d014041d0358607007180d8401d18003d0144448008240e031000f102600004101d00062001540403660185046001c0c001b05c8418407e4071320403040a440c048640d41961410344115050320800c580c1201c3c400d62100040c0c4840b0b0b035440301d01c035064803940c2e00c0e800c01009680c02c09030003c00050088040300034520240c0d6800c44801d40004902c10002144c00401410348440a41000b1540d0558200b045080c1b541d40e01c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 245102778 1250 245101528 245101537
    0xd05090c0a120f1e290c3405240402040b27070906050c0c010806031002040605041809050706050f0d05011212080c03040830100f050d0b070201060e040602 68
    0x40c0f40c0300c2a000ea0302d0445949078807490802007175403400c0d1400621098444401021140c4041d9541984916800554075822259031000c4d0f214441c607104681c10094204121a81d10040000e100e13840242d4200350f45049000900103882140c0355250481c8a4070b40c8024480101d46290500109415024003c00403400607940c1c50002004c0c80c00c0060320611070030545404c0000306028140010b0b00703200440c1d500802a01d0b46600d4000d03181201c01d160800d2004000a0400c2d803038203601e03107103422400c01d217116035020481c840a0510540100040000c41d80800703a8445043c442d403211540c1c2107801171030203011800d201540c9000b00209110441c000c03079003000c500c199801126455040c0041703c0500c07007501c0980204a043c000b050010f14100090590580e0401c51100e0003014034011906140131480b00042a901e080180151001c500355140c019244032500780034074138a003d006c90304450750498060f215159010203c2c110364400c0d040a4001d00001d490030685042909001009500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 245104028 1250 245102778 245102783
    0xc0206030a0903120e2d070f0509010b0901051204030915020a021f1416080315100207060f0c08090a080d030e06070f0f1809020d05090c0a120f1e 64
    0x289407880100e213000a01070350f0b070101200c0000c1c04071400202e01d51900c0c21192682c0c00241d400001c185128804100300b050b0040c0b284106aa903064600380602c15520030603000181002c00c2006003245e80d90300003048503d103003806244181c044d03a99003021140418950008045440310100701a405903000412420040c000c0303500401401c00c801c0301e2a800c0d0f50300303d5880d0201b01c0620041c0000a4048050580407000e080c800d0741d0f140c0c09a0303a240c660b600c2140c8080c0e403002e2a44444030700d42012201c01c1141c0c015400200400c604040000d4814421005450100a4810204001c02880c0d4003500c101c18030103000d52001c95100e40b00c66840d2607500004900092400744240551800058182d0181019032140c1c00f1401c0542d404070f404c01c40008201d07003489020380b20508002d0400c115640140206600140c440c07401003400d40c20f80d000600702c2112903001003410b0300ca60362020807510440f40000e5801140110500c0c1074030a29040100c0501143c3c0e4204079516017200c02c1030f40050052 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 245105278 1250 245104028 245104037
    0xa0f0813020d020108090109320109150b06040801020a0305011806030209071209120807020f0c032d010501030c030605010803030f07030209121c0e03030f190c0206030a0903 76
    0x2590140d0440404a090030007070350144441c02c0203005540104c14051b00400c9030b038008a190034183e112680409610141800c16815100348281c084c06901d80c0407001c20120300086c054a135642e11030340454103081205090150b030f100110b51003581c0c0c40b02224007d20101001f03640702e148c0741c0700c081c000301001d2040c18071507007034402c035882c2d00c0003940701d444182d0760f0060690410703841d850003c84101781d0158410b115180c1d90200100460041c200c014941c031f40f039a855005600d40311000a0800d00042c03828001684116007001181e5000310303141c00b81d920055803011400070700c3d60698103da151103114134080e5103400008401c3c440e20401c01015640101018000c99030307500826607880c8412140303024064a81008200310301d03c26001485803000082c01e4120510030840140e0410380a2851000f003a0080d05100d04440d40201500310400070440c007031814551400c3d04a1107a100b0000c03412056030f01010508251030180d20400201600540722548a140ca0401c0c007004180928040c3c0114 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 245106528 1250 245105278 245105281
    0x22109010e180f04020109050d0b0414030a020c0607050304170a120804050d080c09132f030705220312090807060e040b0406030506090303041b05090f15060a0f08 71
    0x82c14104045840056442000310702c07507580442d0800000c401070004c0703040220003140052203a69203a442400c00c2e02900c0780c64054101460720f041c0d050002000b181840d0014041040810b401048028404405980e00b581d80c6125260250540c4150f0b040800881c00c5408202c07555800042d040b20703440c2c8640d41d0350003c40d081d82016185101c080764010a55800405802d010398401c3c4a0142c10060503500282000091b40001303901500f4030441121060f9210316008002c1c50f0f084a0000c0b070420b0300102242103600d00202c03516403000810078814090002450489054861000c0c640c40c5c2481d1404d81c00c407500d82c505100b0004108142c44000740342c4c86400f041c0e015011903070900700d540e180c0360821001045020b100207424062407003944242e80710f1001010030700c28402c1c175100d56543c2020b1130340c80c5801c0c64010410210560581070038001400c06210ba510340313061950300a00c1c00600903440d580c400d40010180550744940940200d00802d100758103e4105d03041542041d5543c032207001e00d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 245107778 1250 245106528 245106557
    0x703051002040b09011b060c05070b0a02040e0103020d03050405100e09070f05180f030601030c030b01150f08041e0303020a0905010206100303050c120705060106090617060f0102210901 81
    0x1a0301030750080883c007110800840d003066000d0000d015a44840742450500b60001c0d888000442d02080c1c82400880e100003085420403410316111a40210840030460411741400c2c0821901d84050000901943c81d9824410a00d4019030a4400426000341a040c941e0380c0400010414107184401d64040c8400701c002c0350b000740c01110b92144020304ea9a40d1030901541c00680c0302604d0291807005d0f0807814200b2004550b1302d0500030680a140260f0703810031218a549000859140140e01020300540c20004000c0b20980c42075040703103002c00354541a641600d86048c210503c013460010700300d9075a10b1104030303000c154054002d42038003002511640a01581c6000580c5c984004907070400e5007040c0032a0500000340642c000d0042090312104403641c100c4030062200060784504070070340e0380e90f020700010030a01d540005400050005481d0504013150401e600d40748044020306807034070a4192002c50180c3e07910030003c1c0001e40342c4101c2c051443c10145841710040368004a1400d0003e10300510040d60b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 245109028 1250 245107778 245107781
    0xb131a070804021908030d02030105030d08010317092205060306182a03030403050a1b140d060e032115090703020d02040b0705010c08011e0b0d020705060907030510 72
    0x115030040c1e2500300980e900e03603081000741d8554481c85000c41001c54404180b4140400180800c001000750060782c80d414070041611745a01c000040081059150041c000070b10914601c004000200740b440d6210120540007405882d080c0041c40c4900c041242c2c4a043c143d21900118013401d0183c05607115601d448140d038540c0d503038011300c0c00300a03440030f03000610450350080c1c031780d42031410140040c8030030120400003803c50340558000c1e03550350310440c459810301000d4142e561440b00440502440c4900d0602081e900240e0001701c18826001a011035080c000150050001d0002c0070003980c0c1c0d03409840c1d400820341d1791088030004070032800c100000d0002c51034021070445100c004041c429603a80b9071104402075481003405080683d000e2200041c10b103004400380c82d140384904004200c40008840051550388141d001445030b6012018441074000f01c41a80800d41d04504000d40e0341d82c20398a100806481080c0c4014402c0c0308010801c524908080f031008144d900c90410760703110b42c849030300380030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 245110278 1250 245109028 245109031
    0x1101030e190f1109010e0a0e0601180b010210020a0c1406071403101203031d1606030e01090c080601180c09090e0a0f06050910060305030a080709030b131a 68
    0x5540c1c04021100038003060b511007402d01c855100b00e4000500c0d001520204075010000c1e400340c940f5007401d4080c02040b552502400c07214500300c01c01081c5a41c074103403034034010a0a596100b10840d6944521040e01e0344284400d00c10b2402c0c00c1d00544da1681d0f44080100721104907541641c2c1011581e0713405075402000308409001d400b2640d1409611030b28400c203485260f0018010325aa04051400000c0e0459401e070948070080c08ad031000601c0c07200c422801d84641500c42d603011501d0f00109160440004203001400565001d8500002c603181440380e500d0041c4403840014211018050001640d10303000241241a0380b400d0540e87e0041106000c114142c55a40901001080b1101d00c14008d10059074440003420605c601101c00701c1d0029114050900907250b41a02d000e0703110803c0180301a01041007100b02c0c0c444a100704015490341d20f58030789901500f0142c1081001c1500071400c05442081700001854119030041c0300c1c4d0604c903c10314950175460208407000030140c0241500402c1004206 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 245111528 1250 245110278 245110303
    0x1090b040509150307091407080106020c0d060f020d021902010b010c0b04060b0d020910150e06070b0a090212060402031b10080901110a09050307050d03020d0c02011b1101030e 77
    0x882c41e40c58206400d0500d5400c010802d4045c42440000181c1c8130f142e0141039a0340c11031900031002410072810003004980d050700102c06561181c03d143c100707900d0740540340002e1900904002412090500541e000e1b02c14005020300c070b140041402c6001c4810f401c40113148190603002045603886480041d5041f40e2071410117441d1054400015021586e6074025440c400b0008014a140040560018501071802c0d40c08001041c038001c020f01c00700e00d001251091400c102e003007141651309100c0c0052001d02c80c0f40700007008d4a0340080032070410041e40d000407113407aa00404a00c0400c0d205a01c203030392032400301c4c2c050f4824401d04855803c10b80030f00840c0f09103c200034007501014640f89070152281407001d0007501c040c0d982c1d909006d60804501019081000140da585540d1500e00010945440250303000301d407040056148010009400194240d47c2c0c800d10300702855990b07a01d00040e07070410701e80303660843c403445000c18000070020b13400844106071100344c0301084031426084540350b4807241d290a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 245112778 1250 245111528 245111539
    0x703031814090109090303150306091205160807051c020f06011e050607051002040801020705010605120303010302210703031e0e100c080408010e060414030a08060d02010c170901090b0405 82
    0x40c04105043e40000c40000c6c0682004a04004428050a5044502d82c0161010395070307404840c04002c82c54610015060307aa00d051410288190a00d00c02d9012090004007031110008407101000814414505203000440c1c1045204803c9480030b034444100e1500c0d40042d0040b040080780c2d0a0016054000c0782200c50380140700141000c0601c0007603444080c090b00d4500c00e20f11210100f80c01c90000300050030510b000543c07100081c7c40c0003420b45003c2e4010078840c8444410f908021200007042d2411039030100c400303a818410004081d004049140744001c482d0240b2007000c428960804030500282d030b00600c04000b515080e41d011607040301d14201a0341d118545001404000b44124040305c44140514410740c41c5c00da480728a207085810b107078082481504403000300004d20110704e0181d0300144018019518214040100500d070000003022944143c1a413112a81564441d01103951400c5d8810840504103180302840d01c1c0da0340090382460300003003c0c03102c0482d003020000166000c5481c050003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 245114028 1250 245112778 245112781
    0x90b0703050a030212250815040915020706060e01080303070c20041d070f0e0601031d01090c030203060a020705030f031e0106090e1003021f050c070303181409 70
    0x50072200d41d8800c400c000c04154080c800d80340307411551a03802d406450300301c10501d0218207603010720446440080f9580300b03105180302003145611480e0364403030f4000011280004d540f0a140781034001422401c03000101c9034408101c1c4410040c459204800f902c10003801421140e9072100700c5562403201301c94841c0003601003110000010030044590780201816103414807001000e101180c121012101181c2030041300e000e0310b019450b030510002c8081d180701c10642c0851410452038441744440582218100741d41d5104c032031440b80245048440c60a580d00092002c10783c28200049000380b80d01040e4800d000c0c0801080c803071801d134800ca40429a000014504040c410b804c1c0e007456800040c1246110501e6002c9201c81e600d500b00d456019221179100e00231a58104046041c0c0c5207001819224450328000c1d0500169841c2c1520115580720a1740100d104100301008031868080c9000099191041800210415030403504030340100c0713407040100c8005560f99164811550401d030703d554002a4180 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 245115278 1250 245114028 245114033
    0x6050303090f030c150d0b01050406020d0c0206362b0507031403180402120c0901030b06040602010209011d01080f0907030803180d030c0203030105011b0f08070b07090b07 75
    0x1ca800d2002c500102610704203d0910042041440d2402c41c041a006000a07009004003052045030400c490a1800c24282810314802039a1880031444100a11003c0168403086555a500312541169180300d00c0c40c61860080f2840300340d0403503a401c007883e01e0401003c01400d081240c01d003003085400101c5040c024040103803594413124605070070b80300350060744c40100110341e0841404000081c4c0380001d558409501181441c680c070703c0401c0c903101d04d0040280041442441d9031568124a04100081da04c2c0f400d40010307001407241c040c200341c010f1408240010b4041d010340c064031442c2c030300303803556020512408c0311020030494031040d5901054054020a86202c1c00ca045030794030802010803900440d480c1d8440d100300385c00845007041c205032102c56000c220304080c00300c0d001c2078415040501204c0030a0201a41300e0005010b442c3c100842c1120413000d03070500c02800008141c005110020410650508280b194005a005e4402008030004164842d100342920000c0380e1800440c1740c1021480e5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 245116528 1250 245115278 245115289
    0x408190b0a1121270a061a0a030503040503070b09060304060b0d1a10080105100e0a090807260f220504050708190b0a05060a02120f0408100605030309 66
    0x20002044602e800307108000c050103664800c404484a014141c00c1d4a142500b6440034141e2511241c542c043d0040702c13824005080000c02c4034205a0240700866080c3d000110300d5032070400354480303a41c42440228000203003c0d0100c0180169482502a90320751a266040c0150300e107e447d05140d0440002c00001d0081241940141000380009129101044d00e036103400306070185044a14056810500611444008500703643d4003d10070003000340070514007560042c08511a41c421011a04c80c0040028030b01c15056014100d80c95100030202d48440883c10030b691018500107244400b00122005d050049414400351980400d12240daa0304d0202c8050003801f004071b220076a04800f0b40f0301d03200400c4555a0b4020240b0411165a420300c06283c00146000d0b101018921740522502d07002204119480c0c0764120400d0303581c00d0314000e60702d40040350100d26105080d0003629407078002140c0c981c5050351000c014011282007030104c400c0102040c06440031a8500e00c5455030561082103041c8603070500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 245117778 1250 245116528 245116541
    0x70804030b06010c1a0703140c0a030b0f0301060305030903121222060c030b040f05010609030b040f080a021b060f04030b0916060f0825050c07090906020408190b0a 72
    0x185401020680580d4513040000e0b0703205c2540700716002420822012681c540320b080c880040ca00080400c9040113040c4443c1482561034940c10507494040d241803036180d144007002e076514050002c102c15a0380e400c1c400d84a0700100b0312188640039075130705450204003142c19900c0d0092011007408003070300c424543c030000f204030310040303c075541e02c4003080ca0104400740302c0c1100f01c078440c0d00e0200340c061030f6908200884021901d8684414030f05001480002c2d8081d0312070080d02c0e80400000903544803800d0403030038030380c0c0d03814003d201e1500003d003c107501c0c3e40030442602c44108034990000d40c1a4060801109025101c03140c0c0074280180700c03c02c081103d140c2c0d45500420524203440d4606058485d1041c0c200164018102103100015059442544200c065501500d051003109990404101160a100c0f01e003401307004002c4003148440c207506090296500802030140e040007401510b00e04071003c5e400510402c5231500480c408540c0903003865900c80766203580580d6120041e40c40b0400301c0c004100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 245119028 1250 245117778 245117791
    0xb0306010f150e0402040e1e01140d0f15060608010b030c030a1109150414120a0b0408041d042306010b0a0e1e0a0501020f1b12060703060e090102070804030b 69
    0x2007192440c0d200b071304d0f0b40c4010b2000e0262800c05180e180340510f0743c0003aa529103140d1b81481c8440c080100000d5100418209404d0f00858002c84160104d0030702d124041ca068002400f207203004144000182610303404002245c9203520b4004442e0381e509005940b900007121200102d00e410400240d0081184d031004501c0900c040f805418090840042402c1171000e00c4010340c1d00000207001c0c40300d10400a411f80b144103040780c0094560003652009130310b8600b107001c020318611349003020804102581c1c0980b4044c0c000c40741ca904e0403103104240c54002d0a42941c058541000d445020080d0000751824200c0c0303104842c006004c02d07440c00c0b0325a03600341d000d515520200400840e1400b015518100c1400e1058544200448015030800c108000010700e580a507065502c224a091005400410106680c081001840040880701000705d180e16a12045121440c05850104040705402da40b280741035610000d44041700380d480030007943c202d00c544900608000302c180401c000103400395290a0b0b0018 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 245120278 1250 245119028 245119037
    0x3071e1209021804060515100c0204110c0d090e0f0103120806060f131a04061b02060d11030711060106050403022119050d03200702120d0507020102010b0306010f15 72
    0x20701442d01102c0d840140c031308440882d200c1043c021030030100061142e160801301c034009044040b0101c064031415440500a0249450b51030b80749520b81d002d0281c031007600140703060707400050440e03000820101442c085e50764222064400305403030107241c205060603241c2c81a1540c1c10348450759070a07205850014004ea43c840b01c10001d444807410110060100034940007480d1504a061102404003000c0c10541805e175a0b8090004015060f80402040c50380318400c24990f8500d40c503800400e02c0ca10411400202071801d103000e5400c61103901008511400159030303903640301800026800c0d02c4031000c0c40b0b4000042c0341800188050700d406c250032400343c2c481c2c2100181c1d61002c9101c0c84d0030b20a841b80641c0460511110030401c1c00b1003031021480d850102d240030000941003409408810306441c031010031040c00401c0043c2107449191a50016111080488110740d0540b10010f0903035015110490040d402c0980000d07070f6060009140d0b0503104503d81e8400f50f1800e00c07195580040c0490312410400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 245121528 1250 245120278 245120299
    0x24030b0901091b03031707090b03041103061005010e1906110f0106080706080702031309020a030216080301091404020f0103021e220e040c030821010b03071e120902 72
    0x203a1210f45001c1d000b5981480c03481d9940c03560501401c03a521609540d1000343c0c00b02c0400007207a501c010b502c015110b40380302d03482d12920382e82003041508050a40b280d8051281100744680021550482d400705c80b8240d803032028245a0b02d0512160311002c65001500c4010b0702c1c801e007c01c0d405021144d0411418008450f810784010302403500752101ca1b404a002c81d0040b107000d004440e4052100343d8002050700045107054070180811500e06c13198450490340c990301182e5901528032a404882c1014481a00072250900c41c1c10044001c1d40203104241d016071404450b42800444c01d03e055100700c0e002060002081c82500054019504c4064546407a040010b0b500404002100240c403100240081581800100039140159015035400ca002041443c4040000045203c0d107241d041d0b031740c40061203071110103180006004042400e09644082814800440c2410508000d540309240d203545a81d03202820b928003504250300012414002005203603501d2007c0055084040c14920240409402 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 245122778 1250 245121528 245121533
    0x20702060d050103030f11120304080d02031602011d060c13050a1410030501080307021212040b0c06150a03120c06021204020907050f1b120705030c0124030b090109 72
    0x46500000105034115682c50050092560280b4001300c03c800030300b0426810644c03c102d140e41ea14005120290190001001804108079141903900d5120001000c5d522818107100c085c445000400c0c0c11b60066203080d031078078000f0003180080d201e4242d80720040e005503140c5840000c136030303444841c149010142076035000507151142007080005001c00e0041e1401c10008004000c14a48100b81e41010181004d0040c0505000802140d245030ba0444040031074101600c88141000000041c0c504925004180040c148d400c1000030143d901000054a00d10307a15101c401400d1180d070404290400c40c0000c0c184005212440c0e00c420408150600c14a00003140d42c5040aa13401181900450342c1594140411420560708454024046007003103424031040707400e50b404c00d01031101245404800490940d4051009102226503220200700709541c40d40a030900650700c5d07002d004046020b40ca00072841c81c1e800803001820741c64021612008000900c0d6440300d41c09880044c0500d00c25540c0c3c0da055200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 245124028 1250 245122778 245122789
    0xa0503070303020d081e0609100e0c0a1806020706050c0703151a01030902061c090807030207030c090b0616020f0405040507060318020a050904150606050315040905060415020702 78
    0x80d0720a43c0181905401c1101c000d10a203005040e58410a200050804c1807101c0080c031243c0c0280b095a0100d041d5a440b800d40c900000c850b406114078030251401e020855a01a0081110041c20344514400c1401d448131a05220050b00c1403030b005820000c030a006141c03240b002050164000811107010740c1d102c1c2c45d1128510342c500d01c030070700040d624010125000c2e0002015070100a0034203040164107001d8020441c103100d8003013400201c02e292880c800401000360700080550b5001074045440c1c800fa480d003e507070740c2418013064480380c03180307000060407844901a05001d1400981000d040103519018400c0d1701a861008a070700145140d0703294019205c0c1d215640c415401003005000842c030b000030140031185c44680380d80581101034411805622020083c8040380c0082e51451815903c40c2441208801d41002d00f00c899800d102000412951100107103001c1d09807400c1d200c654070b83e000100000c507045000b00420300d820801c00500440c000c5c403034410170340824080240c60000399500142 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 245125278 1250 245124028 245124043
    0x50d020d140303091f0209090a02030a060f0e0402030c1c0b040c1203030b0406061d090402010207081009050d0c1505070203090310050907050a03080412151b020d081509060a0503 78
    0x31200d07440f45c2c0c00d44060140e01194442d003086800c10440c604100c800204000c0d55004110a81058002020810325285540000f0041480d070032080009500c660b80c2e8050001c00740e070241d1107440703075013820015490b0055450f0440e042c41507070011850203566a20b25051401801030743d080020280000304c0342c02c10450360b45c2c124071a030340010f00c84c0b41c03007000c01c001c0390b245802c41001c000c25802d01052000d00c0c1040c207107101d00110340c08561540c4510040380340031542c1c1c100d05c000b4010075407100c1e20403c10745c000d86042403088042c0c0b10404100340c021120500f8541d0083c1200e10b440d460728040c42082e50000b5000140740c4147c910701800c503000302e0719060481d04802d010690302c008208504d8002d0045e80041c20045074102c055510310380f601403035401280100c0d90b0103802c19186400b0401d034100405114540c1d1401480351811540406400341118101603015000e0001c2c0001150b1007a81389610841c05000c20400000c6207800b031002080c8010082c5400c0f495490010840307035402c20959 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 245126528 1250 245125278 245125291
    0xf0203160b12070e010c02041806020a0503100e0720070803130f050301020c1e0c04060e0a0f0c02030301061d06040e072c040b04090b090d0f0207050d020d140303 71
    0x46982d09003031050011010300c020503d40401c0a01d1444103616a4804615101a601120003080421429215101c81c4401c13082c02088248002510024150082d01940c07040440001c08003c89a60341d4113150345400880341e18000415140303155400c00c414082e44014082d40c1d03001c407a0480e49680c000e61440c0d0100310043e100c1000500c04000120211841402070070040e0300035403e000f10344040e80d5813410200040740b400390101d26402c4100c4010405070603d420010028041d0517034549026040380305c15608203400a06004521007054038a00905c03212030300035402076103560300e00242120b1030000e45000d004072038020704103414660744030006040a844200300d8407000b410030000160101120708842c220304c240b804084042c000414081407069070082e10003062440d07d07074000400402c240940113108401800a0201901000800380001d580a8840300c000f492540801c1c1d0356000288600340d40103c40500c41401400e02500d200203961003454030186c4451075202c064115002102c14 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 245127778 1250 245126528 245126549
    0x90b0d021b0303060f03120f0f0c010f0f0b030d1202030a020912030307091215020904020706020a020106030b070905130b040b03030403030215010608090d03240602100509030c0a0f020316 82
    0x82c4030aa05d01802c03040300508044000308150107000202648500601009139001c0001242000000503054211030284802c0e800070001e01014580050003000714040711034001e0301d440d0364480d0a080001380400300100c0c540781c030200e20144a213901c0203580000e04500700a9000d00c0011f000b9140d03075000500d8843c0e92000b40d0349918203040010620019540083c8214002400d00310204070f025100c0680a0183c030070241e9600682c2c2c1c0810003a1240c40307001000c10b0320008101480350f0341907220005803480394440d0806900c4540044032a101540a01c6500906040344541c00001640c002188401701400c08100582064002421a000343d80103901582001c1c03c3e000c0808101c8900e076001d000c0a0801110a0804220180c0e41c6c001055006007419a81d54441a400c1000c044900866a8645591002e2626440002e4880030224000e0401c54107002c08161014004001d07920042da01000416a04440b034480082c0314513004816038160089003284800d002c201c440310406410280c45 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 245129028 1250 245127778 245127781
    0xb0a050306030f0604021305070c02060a1805030303010518090a0c030b0f0702160311013e1209150906040902030601020d1d0f04020c010c020f150601090b0d021b0303 73
    0x5050400c03003011100f08003500903800708001030b03454210145a0140d11480020150346400c802c0d00c000e00c044001944c05540801d2660001d54800c120016242c466a040c00030b080d0303034000f8150b80e40003c0c0105644513400861110f101c04a440d07440c0e0748040200c0482c0c045001c180c4440c400d1009580040d15081045010001e000002c0d009403600042988001c00807540c0720407241c40c004070f0741d000c004c045c540b090001c02c0c4940e10820341901403460398880c0007441403c07a00d502d103041c14102c4001da00c0c508641451641200d000c0f4801046141001c1900d28101c508010001c00c6c5048220406454800380110307041e87e00c0e824090b20280214a500507660305000700068544400c000249040220308000f407030700c01b1006c41d000e8410210503224208661030250020713000c0d018400d0424427644c07030894420240c640c0040c9084010701102c0550306412041240440516021038103580801d41280e010804c41080c0402070041c0d0003000d02c0103080640740c80070746002010307440b0000c0040d030002c070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 245130278 1250 245129028 245129041
    0x1501050a1404080102090319030e210d080a0b0102060103080d0216080a020c041103041a0c0d1415150906180301050a060302040f0c08040204020a03061e03030207061103031303090b0a0503 82
    0x483c00c2c0c202e601d200300701d807015a920b80c0c00070a501c1c40810b269000f0bc5000d603109010000818142084009041c00c0d110300c4540140010074941d4100c64100c0500e09180c0520310650001c103542d4146d0341c200c03000c40e00e0316804c802900044e5001d4148100d90200b2000c0708000b14101e45d000d4a403801041d0b024001605150007003106541400c401030110150400610001400b01c03003000080c20401c1610390520760340c50341a4032090098000300e0050500307141040050703040003401540315045074010800000402d078144243c04540c070180c0203424000300240c04140c030b0703d81d01404644040982584038040c81902183c250b030020750ba0041042d4548800b4003c515050190000110813140100b08181c03060100411045025101034091a4001404450760307100341c10080c0034018800d441100210111040c80100ca600e100903401400ba9040c04258203108001021407040040025821178a4089000302c182584240c2103090201c102c0b00058100042c83c00750211080744e45801340c1341d03d00360 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 245131528 1250 245130278 245130283
    0x118080a06060b27060405060c07051c080a0305060307090c030c080601110304270504030203041406090f060d06031b08210a050c0109020918010c03051501050a14040801020903 77
    0x703403c0345072901c40078054200d45040c114862010b2141c04912040c0e0580502c020800710720440c0c00260300b05400207140e508901000030321400700e0384103840010396810719034100620107407940002040c0303080c1002104a100d201e81c0006400c0b42004055400c0c2a940325050300031039030b4070702d814808a9100c9000a0b00305420136401584210207003004000503030307440ca8907500c0e4452800754a50720310180301c1c1c0014502104080e01c00420290100300440e0415080281d5030750031a208902c0c0481d0610001d10b02818000251501d408024090342c804921110820081d504000c244060003690340c02d0010110311883c244800021840c000025030a00b40700da50340c200340c13150007410401c0700103299034086294818202c52030004245400740e2078502e500c3c0b2440c05844a548060f5000c40d42a00784103020410000e035201c0680b07444000c00c941101d00a0640513204111a803205040011a00110b00d50040700104001e480c83c6c03500300c0246440b02101d410542150b0002403842e0b601041c9880242800c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 245132778 1250 245131528 245131541
    0x1b0d140f0d1e1404020102100f18030504051009050901030b1f0303030c020c04051b0c1f0522050a1b0f0312141810030f1802030d090518060118080a06 66
    0x101e0f4403040d92854a500080e546901e66403900380e800f40e6403401241c168440340c0c4034070f00601c1e207801c0d05211490710741801400d6411038024288101d100703403288520103020b074410000b100c2c0301800b48010b0340c2ca5511042c1c00060020050712582040b0943d20f402c00e00c484070f441010714402d8500203900001c0d0b0300001c3c0fa007014018943c5c007580c42c0c90180640b8040c102400106030805a0120790b031512617000d15400c140c07101040c0b0f64014070651070b4449600003900803d21494041140b0030022000381c09412030600c40c240e0250150700418443d2001c14100046101000d40954201091917590b412070b4008004903801552072100c50300000b92015400808025102c040c000681e0424503040c2440a440c040c149003a442500b81c0b005c1c841080b4000d41100740000c036090010403894004c01d203c0048551000b408a201e8003400c41840c80a40c040c030001300c1a5040030740000000e402800d0105d00000000e0000741c1405500c0c0319442c14000d1360190980a0040381c0060540d1303541501c0c001c1c0c2a140e1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 245134028 1250 245132778 245132801
    0x140103110d060f0603020f04051005120106020601051302040b2217060f07090e010e0703060b120402040b030102041409100503010203040f06050109050105010509040c12050c1b0d140f0d1e 82
    0x41104050010740b1805403400c0e100e04542e1404400b00b0300c40c06607028424114038254121214cc000140c07a60003180c3d96040b40d100707858190540100404040803845280204601d843e41031000118000400c03030200c501d00500d15817280d9031a128240200205107050480300c45620002c10040d03900401d51685410100310308018107030b14281458004c540e0340501030783d102c48000c2400152054442d40051000340a901c0c0340c181d45030050500c00c0b07031501c01103400b0390056040144c80502c9007014401c8404130b51000c40e400c2021102e40e0b04026445201030725203074812b080710030081456a401c2c4011030103203103d40c018517411400341ca048025120140d00c1840c40d20f262030010042039810104030341e070005c0212400105d2041800e0292400341040340c140155510f02400c010381e1f03079031a038024603000584511100c5280382d20346c07107203a8880740c64944a0024148111040d4042005c4000c2c10aa04007101d01030300b480158031400007280c013901400303041d8150104810035041c04500c180c511141 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 245135278 1250 245134028 245134031
    0xb071208070306170c2e0c11040203181603080301090905030d02120103031205040c0e1e0103150e0708030f09030a0813051c030f111204030b01030317040c140103110d060f0603 77
    0x6800804420306e400c3d19003014140505141584100441403042200c0000e005000b151070b4140b1008003400802103079a0031020384680c400070403c050101d0380d1101102e81c024441450350f03080038120380107029181c6085a903032109114441a10845001804030340c0700580c0140c01035807640c100204a9100c40584900840c0ba20060002103410081030200391020424540d0f00c0791680c102c500c00000c0007849680b861002c040010080209081c221111159032520610100c030035404419103460141c032940d42140e004000344e142078140c800241550180040c2500c00c0b807120760300d90740682d500c40c4c4540782600400c407c092105103021020104000640702200c80c00d1126998040e080382c10308800b480900c071440742095140e07038080028110020044820035190b5650b07140840d400359003800304a011405441c9091042110807866034455500302c040255101e141850390b18080c04049009410180c03103040980d070010304c0000501d1021120240003600074a41030306a000d1b21402c1c0c00040406 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 245136528 1250 245135278 245135329
    0xf030506010b0715020a030c02060a0b0a141f02030406090e0c0d05040c05130b120d0210020d02131d010501021f0b03030c06040b040c0b071208070306170c 68
    0x114001080c9054034040409550b40c1c1e0914101451240b94881020380494000a5101c0000f0741c0340e08840c160300b03020740840c0c81075107075400c0c11815501ca403d24160031107560703181017001462103010b0408558000d03020404104040c592406003801e1016100c0141c3d00005042080c40d034010074050040ca0746105160031400e10540c138828034494203403159250342d02c8030081800d00c00c0c0c1340c02890061100901c41c102900c1c0d8000080042d22103040c2d03451260f10f1204840080d14008510140c540d00c590380030f400b815404003d03000003904103500818100741c0c01c1c40f80844040003030f04100302501c40c400482d000c2e2011000480118031050308070034115040304107500b1250310f54281081c02c0b440c0189011508540c0c21011030301d035000e034204403080c2c0d1003114140414040d14144160155000340e8010413842c0c2c460400c2e4406102c2e15400070102a1800003401c0c1d40c1e8811021030341c0001c0703e071a020130819943c400c0b01000e9600681c0118003074118091682341c620301340c5c00984c04200d9070304808006 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 245137778 1250 245136528 245136533
    0x1104060f26070c03090b0310030c121211071a0316030e0d0507021c06150b0a0c080304140703030504090e0703020a05062208100b01030911120a060204090b01090f03 72
    0xc820000e040380c010310030601d4050f0201401035505601911800c9011030300c7e440c103030301900c00009051206440003644410b001c201070950444822825170020b054120351541404115541902c285100b000c0303029015003c6001100079000e64021500d07206816141d0805038035003d071051441c1c09000a161400300c42d150440404900c40d20307500400d003002600d411050001c100720911020002404050300900e50042000503803040300c08031020116551807580311203c01c1c0080c4030b03006070080414000280540004d54003c02941e205d4030070b00c441803e2034184204545864669002140440e00202d01442586501e21506288840580c02401a9459500481c90100141c050140648000160700d4a5000102940d075a00c4c0030916989858564906010740c588140795002c03900c0321b05102d180c2c802d66109025072141c0303540102809049101810801c8280092003560206074007030b01904001080309440500028907800b03001090044001000502e94100303a000081c0c1080d21040a101 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 245139028 1250 245137778 245137847
    0xa09050103050a0b0a0621020d09031404060c201011060a06030b01030b0702010209030d090602070501090308030a0e071701050405010506030d020615030a020a080a230a060b041104060f 81
    0x300d81c0c141c100800303007803494548107400d4413291f401c0082c9140005854403100c1d0036944480500b03800f9907900d81c0d01440c041c038410304038070492203003200180085090701e0120b40e50302c02e084811150080e240707900702c060001103804003600c00003031030104004658840c804102482081d5100924080030000340d401c695550044007410b02000d40840c0307421000502d018000d40c103c0b00c00341001002c0345e104145d05c1000600c0540b00b8058000180544180060a540148c80ca0401d0703a610504441c10740d0381c0e9070008802442a6500340c00c82d441181800555105800d1241032080340c0b00303002045528041c1049030035644060403003802540a1500c4220710ba6005c070b02590020170a41c1100c0780e0800503400240703032901d20381c0080d41c45086030380005028600003c480150301c1c41090080861a40124071440c450100c1c3c0c100c0d4096003000805100050303c0b41e00440e00c4410007480000c0074501e501121586400c40d0700110089500c0307207034040115802c0901c104001c100c01c4c4280400310442c010f0900b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 245140278 1250 245139028 245139049
    0x8010204081b040e060408071202191104091704031a010602030a120902031203041104090c05060a17010b0a120203270c090412120e0613080409020a09050103050a0b 72
    0x921195151002c10030382c2e582d03034000c030b480907101408843c40e90509051081d11035004900c126100f0011100c090182400480d01011841c40019040c104040c1912a06280c41070440c1065100d640c0b0004040003e10007414007143c4c16200020035159801c628001130710384c480040e820349009a03070004000643c1e0001c100c41c07441549250280c02c40c48542081009852000320080d45401104d101074098581e040c0038600c180c0c09a65100641901c070307018003040b2100848041c2510107000c8003031286040803030040000c40201d24042c860521000c1104070061004e03001031006c07540005143c888254480e03545820f900c0c504004501c2d41c1821040200c042d65401d052030142003000c1c40348280580c0c00c6c010340104007800341021086103402d18003001c28580010b04280414009481d0b90b601414034802c40345c090901000804594460005131075580c080c10f9011103e050301041b0204068030240080e01844003251220300d0200d003440c0002d015140b0040c9100041c0b4684075220b90556110340010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 245141528 1250 245140278 245140303
    0x10603060b0c0318060c031207120e060f0702070e1504061e050d140d0806010305100302030a110a0807030b09010605010e030606100522080d03020c0706050c07120b040c0801020408 79
    0x5031842660940805c41d02d0007406400e4040340000305180341103c8101101c107102d56034666807581501710300e048040440d40c1900415a003980701c0c80014000ca40303510075841c0c00800ca030048a105079036920038100b610104580c0b1445000450b03616250f2420580143c1340681101c054000c00c01811003a1380030381240318807480d441501e9800142c400d0040b112604241c8042003c16216208081d01000d002500d068580c580024074040001b10200525003400090380d600034082c1603040255101ca8404010814103d81c0c07000001c1c0c000240080c08004901c011841402d074100c00e0715168081d00d084a1070369004034140000c51410707000980d800b14407117601c10811103d0403804001020204c40354040e00c0e00030314041c4054801c1d80e01c2040303807030170a00450b45d00c40201d94005440c2001203080c1c1c0140d10300c000c680ea01000781405001e00031310160000c0074101088601c90341c1c3c0c0c0c0b0f008040c800b1800030152010604d42d400c0c04184501c401408010340400780c020f628084c502007440e5038406061240 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 245142778 1250 245141528 245141557
    0x110411030f0408071a180f0105010b070809040b0a0810060f060e0603090c0901090e2103061c0c0906080105061009151214090d08040201020c0f0409120206010603060b0c03 75
    0x5000c00c00c417505000c0c03090805458212060307494840343c0444012074403483c1c00c0e024445c16410a508080c14050b20703050343d070380c80401c0703003092a195943c0351660030400e40070340d01c03540f501508111911400c4036000100104001001c00443c010384035800c5641070b801c200c0184036444000c4c8003880c0c000780900003900e02070310855969981d213005541442085028660710000e040000500122281c02041d40008103200b541c200307441d003100700c00c80070090760b0182041d0070f03044c00000d00502d0803003462030a084034240d9200d24035a8680c1c40044111b169000150481d0f03035060306010101c400d100301a403051056840c0044403801d00f40141c4409114410480f03c0301404c9540720b011031140c6107540070b85141d94000e0040c2108014003184117001280d031150303548544821000c1407403207103000500ac0d40c0c06801071700d19a49000306216641180c0394210303030040e85454030724000903490740c0422109c5596501078902c9504141c002416a01e00364010305d4600000e00081041a9000c006c440400c0b00c3c2540 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 245143884 1106 245142778 245142787
    0xa0f062c13021903050a06020403060c11071401030b180a11030f07030c0e131d070305030405060c0703020a06020a0b06100206040609110d110411030f0408 68
    0x10401181c0c04000502005401c0c50000c802e03102c1401521101620b88a8850910341341d00a407003115501d034005000c2062042074405c507103001c1d140e0f00e8424010700e000b00e075043d80e9515174014a401e282c000c00d42c01d03265030300a50041c01d03d2080074121015203142c05100c1c2d000420f04440095481307003041000c0c070200c150f040889201c2c810304403101d4604d0300d41d540d086004000d07541c1c20f4002d101003185001700c1da60312514600240819000042000e4054100000e01c0f043e0400d500040d83c3d114200500004074003000307031825161f041d00c070036884012040d81c4524009859001a4101c04042c0005c42c0095010600c02100350050444070581e45595080c0502180030800140040c0c00403c0070800140040c2c00403000c05001c2d81d6501c5401010718000741d181c400704201152202000c0382c94a80c1400d03d4012134150008885c146030071481c058001c41a0b401d40100024080340d00004e = true := by decide +kernel

theorem cover : BRFrame.Cov 244964028 245143884 := by
  have h0 := BRFrame.cov_init 244964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 244964028 ≤ n) (h2 : n < 245143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
