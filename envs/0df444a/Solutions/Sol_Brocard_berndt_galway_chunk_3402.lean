-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3402
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:33:47.370028+00:00
-- url     : https://prove2.me/submissions/5c962604-5693-459d-bda5-f263147bbea6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 611690647 ≤ n < 611870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 611691897 1250 611690647 611690657
    0x60c030a0b0d021c0209161b03020c090106051c0e032706040306020c060108070602120d0204120506060f091512070302090709090b010f0e0d021203041404230403 71
    0x7650555a0000c96909694014007060b602c00c44820400d402039031380b420709900861424005c0740314001c3c80500011003c42640c0d403262441021101e00d0f054180311502901140b01c0d400c0325140300e0b903078201c40034024006034813100d03591140071100b41564080350f6000c040481c505040c04c000560080f08a48074146c0800c0c5c80c1d2042c13545091501e12810f60b2141d240d40161001c5408000c018941c1d0040c81e54142d00011200b141e1380c0ea500403583c40300c840c019000182c0200003d41d03601c0092201030321030b44281c0c66003d810185c036030024003052000791f00250380d25840601030040b542441d803182c004440054585400c0c500d841d8100400c0840072041160080488400143c0c903c4018040e40c0b01440d80104402400d04215138000c10717041960141d01d40e1039207013902c01c80740d540c000c07000c1e000c0410060f210080c20000000070440c0605007500700741e0300042082841d420189041c00107001400c0001c003c001c0318144481440700300c49000b410100503403104245032101c0e51024010a500540c1450f207 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 611693147 1250 611691897 611691911
    0x3030c1a0f0712140a2003180106050d050706050a0509152820070302030303071e02031314131d010606081003110105120a050103120206040c05010311160b01031103060c030a 76
    0x4243c071b00c1c51010f00507031040039020042c4903010740c1c0c000d0350b800c1d00800b040c024000036031076108003c138800354102c0040265000c2c40e07081100f94042c00182000821906005003011010000701d40603100c01516902c0740030f0f0008520030f03610000440d211a00c64000b031444160740801402414261401c0b04000c1e42c0c0c079400e4034281d44860200000360240d81c2c0038081d01d4687c140400d0161030920b40000c1e2441501060354a2201180300005036070039403c2c0862003500b001d28080a05c42800700c80c46003550446c140b800180b51a65507030082c0c81c0052400b00e0407071188818101854210390007074214204100508090014050109000381c017900d170802081030b640640040182e9240c881d42200384071440c00360b001c2140c0704001c0c1d40114101d03401045141c450b4a1030030070482e2140003c0320014003245500c4400d00a65220341e000e0b036646084910307110320b01003c8a16a40928001d40301c02c49000008000510401c041c0031000d1090702c1e0150300070411403e10141030111340c00f0003441d00d8849a91914 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 611694397 1250 611693147 611693171
    0x1020c040b040f091a0106050307050708070303060302120d090f030f060b0a12060506030c010804052d011401050a050604030b0a0b060f0f0909090309010903030c1a0f0712140a 77
    0x40f0402d9028aa90707020810711200e85060741d905840001110000035241740002140360292003240d125154541c0d8851400000341d81d961010b0b004400260201a80c0f83c1f00480161524184c0036079003c0300d8001403036000b010020040c15114a44c101c043c0d1410000d000b040001c00804207003001541c006070109140c2d5150000c1041910141d100c070110101d4241d071101072011a5020301d0151a0aa007652500c0c0600001903d04040c15039009080ea80700f45d031091103190290030318484c0302e040d0000900c424054689210300b5550b100d4100c0b100c1e50311020040007246401060000141000e0307903060b092a14503180c940b20340800030704a03104641c840701406140e55a450498103441031010840741c0300c40400b0710540c4942c021a69041c02031740b003900402c55002000064a0750120160b40c3c1e034010a08690301120350003095207080360101700c003407000e8502d208404940c034454101a00080010f1400520091100707074604000321146103402c1c44507030000b00e11f88a190348420f03000e02c00304420034591 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 611695647 1250 611694397 611694401
    0x40e150f1c02090a140709030303050f070806090a0b03100b040e07061709030403021008010303120b03210708071406070c110f120a0605100e0f0708180d0206040c1401020c040b04 78
    0x852446507145c40c0810042425040036000040d0b03030190303030300300f055640b08601060b494406450440c04118958009482c42c5051100141e00c04140c40001c034010b206c100100e031404070301c003001c848041d807101c0414001e030074203108031070702c41c9500001000c0312441c10802600541903080e9070b50203007008a001440c001020400ca60080d0b42c050803110b80c50f0341e240401800b0840038042100029903244203461024098000c191030307028024040c102c1001c003d02c02a080454040c04c0c1c1483c030800380f2505011170b101c003015118040c0580480420805640c07207031410508010084800c4c000f055100802051610000d01074024082c1c40030458102088009540e403007281030198514880c08411804005482c0c001900403980924a5160a0307251601454600b00c00c81c1d0100101d483c0d10b001400c55840b034060107400a100c80c008080b0541030321401b600344200c810005000d41d000c40c080c0010007910061600041c5541042c0c07850600020000035103540840000324429500c5814650003690380c5d03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 611696897 1250 611695647 611695661
    0xb040b061c020a09171501051905120703020d0b01030309060c0b060d1703090d02010e010e03160614040b0f0a0e1c02010213170106050402071205030903040e150f1c02090a 75
    0x81d0701d00c0d120741170340780388010b544070b0386459006c0301c2409440c00002c0300e080004850007600b00840c03250421030300b40424882007200700c140346a1984141d01000015841d1800c0d0603107030704d009121290b0650305500340a44900c1c5641d108070304110b030043e04c1c4d001142d07070150b1443e0001800c079016052460982441c4644d8000c0c41464848800000300344098a08000303801910304000c1e80007071254000c05080d190880300c0c0002c1425042d0420000001848503800803016458800c02001034085a003003000c2c80c003060211740450311b43d0040303c00d11002c4582c891071141d04c2281c64038140400038400d000141c54450036002c1109080d009036808400034000c0d015500000b110298402566542d800e80d841c03803034902030100919501c1c050000c03078181854001c44414941107040e50001d42160b000481d65036200a000140c2808107010200e0040d46442c003681c0620b14594901d40700041410401100001c0450001d12546403160750b502074411654880d071410380c048508424540d100b82d007600141540c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 611698147 1250 611696897 611696909
    0x50d06020a020a12020f1606090915080d050a03050c16120215090a021327080c03130504140f0a0f0923060705030c1605010906050a0b040b061c020a09 66
    0x1002d21005070158006130340c6d5115028842190414001c04031501c4210400303000b03880c009101d40320b09200e8080d458000814007001c01c1c40010b0440d42c1c850f0b0141c2410710b02d02d01e1f000001c400180038244241d1501a80d41c00c1a0039034501440c10200140314600c2d86540e080040619907804002034000d40207114503041ea002d1401e030b00026140c00b607503031511160100e034100d00c215403510080c4140c0c08640300d80d450850755600c800ca9002503440f20740003000c1104808440700c6208010f001d400d41414405810b40da025040341c9074400b030801e0104401e81d08651a10800c1174072003003c01500c4850f8028030f90300076901040001c0c40039408503050001c0d09000c40081c05004441c0e00450001031580044d8580101440543e0f50765200c994084a552006031200c140104d814032008030840f003419103802109200b0300c00040c2c055115a1200c0c19120201c0b030f01c2e0502a920b00c1d0701041d5007400e00030780ca0368480c22500c5521b0320b02c230381c0484031074508420307980e030308583d8089041214640204080d8000e000303 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 611699397 1250 611698147 611698163
    0x4050114040b0a1410090b1306180f1803080604020c16080607050a0c020f0d0b091c110307060203221506090e0312070306090c050c0d09050d06020a020a 67
    0x1400d070a0041002c0800c2e03400c0001c580c078000c1580e80104d012180c10740511600120303070b003000e494040e118019060b007650300c41d4005500c145061040606114400080c0b42441685095440b80c0021204850700602803400c0e590170284a0540080c903402388810b000d43c10709011283d034940801280090040030034050651240c040c0640c04002c01056103021208100c1c111003030755503080700841d02802100540e070041070901a6140051074050f0b017a00e1000d80180040e03c846420384c440009050701920180d085400507403c440700c10030096144240c108144c10030300c0d040001000010f64920801002800d081e5011001c96650400034814400d24846040c107200b5140c04c50400d284070484013142d50518078034061001540b010680101c070344034854040958201214002c13290300041c0300920800802d0755038a0041103030405441030f0000101c131960366907110030351540482d1030402510f000070300348806801c08104d03030340d20b02800c01c040e10390203640540c440c400c08100361b240c20200d11380100984 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 611700647 1250 611699397 611699401
    0x90510201005151c06020706020706020a031509020408030912190c170a080301030201050a020106030b101707290c0d0e040c080405060703021e030703020703020d090609060804050114 80
    0x4100e80103180100c40c201154502d0280c1c21041202c4c202c00309007082207403a6140340b2071010030b4540c1d020f000050701841c0b0162a2007110f583e4401242d00200070314001c82c1c2d58081e149075403401c0f4201000640b0044804501d842c1c00c0210a5980b40181c0d400103110341c6942c41d0407040010148000040d0706851005000781010340c1c940b04006a07a00c0c040e8014041944441c602e0300700c800592031303c0c12034100704c0350f628590031600110703110350090703019805564882000000041441446034450403003c00315100c85401d00304100d60307610318840f120714154081034061041141d4140506010348030310704210081130b8106042e406034010050400781500407001c1c1d2441030358101416640d82c42080707608001400b08010700703231014203060b240500030ba4000390000740d00c2d03402036004042c2c0c2140e9440c3d40344c140c000a2902030302d6600c2100e8810000343c000c12200c08040e01008080884c3d18941480000c85007001401440c50243d441081b007040500000714003070010a51007244068160340e9840d0080c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 611701897 1250 611700647 611700673
    0x17030705121210060512040f02191419060e03120f0901121a010e0f06040b070b100e06150c0313030c0501020714120f1509060709051020 60
    0x2500b20059032142150070a00041000c000625004162880368a805040c48565002d80070040790017041141d1100c0c2c80c51100000d40e035165450480301107619040300c8420b08045440030800e1203414650700811010905100405183e518041541d6180c40c00140300038403a0002032a00b4151400080340c02ca00045c000002c09044008002007282038a5070300719281c00e04800b800300c504000c0e0710b405070000040101d40c00d611031265465200c200401c080c03141c5e920f000000e0b2040d809030b8840d44030702000040800c00c020740010000d0b032111903845a000d40710b140c0380a01500703003c0103103494401c1d05112055180300000109884541c40c407801101e4640180720041c40c0c080d06540404c0d90900c0c000d15001402c0e41c400940a000d84551100d80d0250145803024401480900916042e040c0070301d1503001d003810030800080c0c05001c140f500e030f1426400e02c0b00100e4104a8040c0c088020420105c47c28041c030b0300d9080e21040031080601d05000c000021030b8007540302c05500705030b1901038090951100c0c52 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 611703147 1250 611701897 611701933
    0xd050402030c010f0f0f03020c120409180308011503180312111e090d0f08070c0f0e0c070f1e14030a0c08070c03020415170a0c17030705 60
    0x1059109500b12644584050300541c0d0746103130205030800041c8404580381c3c2c10b0b0700c140400100c4908606025080c403095818860074140c040c09480c0100f000440e04016640e418043d0a44c45a24044500700c030040382e0b1002495440c050003110302c8281c2880c00b4a01c0b443c420703845100c0c0c49910301448800d401451800605000c404105122464185103515103a60601011070780c110780e0f2071480c0240c0d52105081384115801c1030900540c031038036454203d00403a0380044613102043c0b24044180c0c2d282010b10b001030600e607254000c030100010582003807002c41c20528003145c210302040c909035101c4801d441d00700403032000000003c1520302218461510720002c030300c6407501d59225641c1d0850044548003010381d00d0044401000c00203102002001c007080c00d14008203851800ac000d06000a501c0b40c000c9015917558041d281c2c0b401c210013004101c440b10b44100c070313013240c544035000e0a400001c0da112480480294000c03000b986020640342c1001080800c22241c4040c2e008050360681150740718880f030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 611704397 1250 611703147 611703151
    0xc0403020d030504152d0c051002040612021602060c01020c0d1206120809041d0111040e0601020c0d060513020904080409050108030f04030b13050a06050103051b1e0609060d05 77
    0x840303541c1c500d582040240c05030510300000000c600300b4458002d008480405000031b000f110b00144040107141d000860014851a8144e2081c0345015907034505d8040c00402c018180c0d500d54143c9032041c4103400115101d003c051001540465505480e840c42000481c02481a0b00c1d0b40301580c400d010f030010009802c00d180d401c035589000c40810038250ba40d240901004600040240594020465000c0e2031a0684c06041342c00c001244040c03517100017482c0d40c0d085450420030300034500c102040400061a11011007070313000300300b0b01c043c00b0040402c0300420f02142042d9001003140b40c9400000e0030780c00e400b07000750f441300f0f400418004142c2024141880d040d40180103a21a02e8101000860008000000c40d841c90300501d98042c5818595101d0081031071024001c149201498913140e40840d00030054101640d016402c0080c0c1c9500d1442c0c660f10740700000c1034540b070507100200c06400d140d6a02c3da10f15450b1034001050076140c3c101100040252140001e11070f03001b100804c0d2a001c95031503a102c4c40c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 611705647 1250 611704397 611704409
    0x4120305062b0309080d021002210c030124080712020c100506030115080d0c0204140412030c111e0a0212031c0207020a03060903180825030b06090c0403020d030504 72
    0x81041038685c603d01d85c54050141072103000d44c0c007900a00c11a03014550007004482031846281c800d40303d58515003840c12206a90601c01818040014010012004c19088072078801030405180410240009019024014918000d02002c02c0301d41d1340c20b6100342c04031403140c440d8500b5260038042c059180d0008040589030030f03019601e0a48040f5141040e440f02000380e869241c0104030741910340d0301c100c401c00c550343c0003241c1003620740d00944040f003120000f05008920a08060000680700301006045917419000e4400300a40041e60081c11030020408082108a007158800e007006da04100610740910640000d42207080c5801803441c60300080080c001484040c1c1c00e022501c6110000d0001b03a00580c20080d43c03016441c4401c0000a115900c46004c80d03201c0c1c10141d010100001120301035003019880418680c10210500700040c81c007031510802d800b10f03111030046d5242162034010f0303000801080c0a001d07294030300c007080764084900140ca000303641c01803141003807120782d20300107026810a200d15 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 611706897 1250 611705647 611705657
    0x9080c0d020f0d14031509131103070501271e030227010b0a020f06090606030111030c04140a090606020313050603040f171c09120804120305062b03 65
    0x2040485a0100e0720a145080a603118004c9000304611a04c81d54009000403da41c1d0b54211251010346a0320242441000094803090f906021030031301c0000c500c40700c00340d24440d400044003840180c0c2c000d9009407988a2214040c07002c0c1781d8454001c00c90313044c01d0304041c240e8001c1507030301e907900300c840c0f240642564400d50706242804052070002040d41d5004070000703083c482d00c40061203500c42ca00d018041c00d9000341304440249003402126400c00b00d0940d0902c07070a401100030403200303080900482d8802e00100c10751500d1031074840c01040e000d0280b8040c8900130304440b061000190703a04426100603040c01002081021394070b5001030740c1c0358013190440b828404181070018403407400d070301500e2045030464031840d4160481d54480b02c2e02e610758000d158480f501403204900000c00c581405400300c1d82d01c0300004082c022400d0442054440c64400c608011004040000089940c5c00142a40301c140c2800701d070603204c1400250381c0460042d62056008000c010710480c4003000d0072031515880c0280c0358 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 611708147 1250 611706897 611706913
    0xf1104060f0503071b061b0e090106090308160302150f04030906030c0e220f020c0c09090a0b15040c02010515060f180409020402071a09010b1005070609080c0d02 71
    0x3075503107001c04c44000380480c4407100460300000035900e00782d24142c41180001503c1d40c10083c0c2c074003921030049800e070004d6110707032002c01c050034000300c903501600c51400d10f000e4036440d550f903689241c41842c0e010103885006262010400d4002c104140c1d0030450f400c00100c4901d400d0b03001c860710010803141600080c92301c0d0300004006000740300c4d20a0262040e1307201400101c200302440820380c041500580d0380945a113401c0c40c2036407603100b01d80c003810004a001d0790710b101030104145085494480e82d03105030940003c0c000d000e0400158500445d0340590240025a0f032014001151944400c04d56001030400e074107001c409906500081c4102c810b000e46458002009082c402707a4011443c3c64083c0310070404c40030703542e1210703180000c80c40c4500038404030340e5000b150701083c180e801c40c000c1101c0115041c00d0f64651a44141780075a030100b20341000700210444640001c840000c030600c0d10050202c009010410301041c0d030022a825034004402c2caa9844a048005a5805010750284014060948 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 611709397 1250 611708147 611708177
    0x71b15021b010507330608010f0204051f0201090515040308100305031804021303060504121706040f0f0614180405030306011b0c06020a0b0c0702220f110406 69
    0x44011070040c0c2d0780b82d0400030680ea030001480f002409140c055041940e100f0400b12240e584003040050300e0b803000c2602441c14088500b96a00b280c8641d64060040c00244100e0302d80c681c03d012414024046404032400b0202c0903801012400405840c83c007490180e554101d038034040b101d01952180d40c81c0c0300c880e035851208120a6031940002030040c0c0040000d041001c0c1c440414081c8070034002c000610385100180da6400b24803240e803045490b41d80300c07020003041c090031002a140302000ca00380858096200c80d00c1550b030040003440303140308030340d181042258100554420030081c480e2240400c141d54940c201c1d6075154102081c3e1601c56000e100d04440401c1c5614086070140c1c1d4080e0007035055459003001900c0103e100c17440c03401c1c0c0000407411a0b002c5041a9000c030300400c000c0d0040e041c00a41c9050515100b00000c200304d28001007046000016211240049118600c15a140000409602e120806880344c0743d9003400305402d01e071002908007910f00c000c20880d01c4030307241c031864840d10344 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 611710647 1250 611709397 611709433
    0x90b130b0102060f060f1f031404050304050103090305040902070b09010c140412080906040303030f06050609030d0305190623040603210216060503090c0301150902071b1502 76
    0x10a680180c20000128010142628400390021001443c6c48042020031000c40d00491000b00515003c041c1d07080e085154540520030710032540d0f440c1e0410003241c03429072250781d9203102c0c03481407030b04065032103141c9010f252048042d203015003180c82e001d43d40c1d50220b0a041e40c1120040d903058400354a883c02045401d401040e81280c00306200c0b09650030a443c26541421810600c40103a0702e4510070003e002181d65494002c00c05540301e520b0019662004500c02401c44003d9000f02d4051a0308010310555070b42d00041c0d20344600c0c150f16000c07415035103c036400b8451710422416840818204840800e01401c0d0701001c08980580d00a611032040c41c041c20402501e4045c07102402c80f0410306803480034103c0b014020b485960890044609940100c40f680580101e41ea0002d400240c000c028403915080600c106922103030102e00a1010b00811002d0b040800700c40d01c0f80303451181d400200d4400300180104070003920034000340c0500c0016545c0440382c0d800a1840002d00060203200700f0b13240381c8a02c0b5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 611711897 1250 611710647 611710661
    0x90a0b01030f150302061605060705071101080f0f0a0609180314070b240306010e041a09031801020a05071d09010606020a02010e06120910061a070609080403050601090b13 75
    0x140c00f0f000021855a000e0101551113501e200c001c140f51000d6030000b00b8420040b280c0108400c1c1c0d42d2907603c009c0e40c1083d20b282060040054108402c0c0340510044004001e003890704080000f1120f51a0340328a48940003c020a07407010710300d1804c12460404072206a0b02c400041307800303902c0d4100c00c036800d00d4040030700303105e1a00010251031103c030205200007030091900c04203025805402c00141e890303400003032410001f68401101045107400704010806880129403d40031b10180800e42410701841c1207850b4002e00c107040c203d85990540310b0405a00c2000011080341d04241541d81c40f540b240c1031243d205058070300c03d40d0710081100110361182e074148503c60455806030b001d0305a050540d8011200107454001e1103910074024441c2004d4400260742d041e0150b5444070080031310310300480b003007000e40d01958042051544095203109541c2c130300c1c404036039076590301c0000041c0fa15140e16140c0e0103401545c01c0548148100b40002c5400012030703100c0000810f0031646111641d00014400d410baa1003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 611713147 1250 611711897 611711921
    0xd0306030f030c020112140105040e030703120b060d06090e071509030204050604091b080d030902220e0304080708120415081b0703120e0105070206180705090a0b01030f 74
    0x1809200004244506030403d0824414501081c60f049115100c000b41d5410760103c480150758140100010300d420700c560500c048245016604101843e28007401034818002c0041d440c3d5103d00005070b142ea50f19080b0f651000081404101140d04c0311040d82c01000341c03110402c0d0034402c07820041080760205104d518160b28a41d0b50030000fa003113a0a100243c90b020300466085500c4091000024100e421f2101800250481c83d07080d007464160380ca842d22003901e00c00d8040c585041c003000301684444a407000261180c000c9010044004031404005003410140e244580c0004940480c4034a004640502201e16250417034039042e1070015000c190340319030310030300e800100c2c0d040c3d000c00414050b010031640407032420001c003000302001d5142880c40d400031030304500140f600c1132010300c1403010740705c0c400140c02210000c003e18501341da0040d42d190300c05810032000c010075200aa50000b402c118a0002e407070041c000b000f031402c000e00c4c51006007600310142ea010a0800d12100c101c3d00b581e01c552618810 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 611714397 1250 611713147 611713163
    0x6120e071206020d230a0c050d020c0d08153703050d0e09071b060b15070b10080703140709152c070c02031c0503220218060f0a030c080d030603 63
    0x807504070046c01400c481d0284018800244280c0c01c0711a80b501c040d00244100c00042d01d036890030900000c01da40b80080286104458244081915803101c0785800d01c02d43c02d14120311101c03000b035000110f040749908026203203081c9582002c001c020b40800e03110030042464848690075404c1c401003010000007100c0c00b00c0042e0a000c0d144420088290125418134018040043d507000c5241c0810041c421840c038000d4207440c0000c8010400c801042076590040c2050f20003c8a1400c041c199900e5040a10028043c03184c40b0400301040101480303000028100c4a404110401820119040300c0549100e4000120720110f051810845010301300c210b04030350081080c01e0381d45c4400c82901c441e1032603e000ea8244c4030303105501521001034200c1c0b1392840c2964840c0b0380c4900e406c45507600d414641e0204034401c2c06802800f2001a00c3d004400c1402c2910001c529000d50345603c04910040c002c1d640d40ca80c00303c0c0080d400420710030382c0030408090b038401d0426101c544800c00c0003603080c5c0f039540c031000740088 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 611715647 1250 611714397 611714401
    0x602010c0e0919050106020d020c03150f060a0f0906090b060a17090a05010e0f010b0a060e01050f0702090f040c080a0f200312041d0106120e071206020d23 68
    0x102c0d0200140c0d52044a56615550b400a42d0f0307040c3c01158030982242016078441c1a40540c80ea4041040d100780400440c020704030354414094881c019800a0080c054042200b00812215518007280501400e0300703450780c00780f15640300c16207809041988980020686041b800403041e080c003030120740c12030320f554690129181300c50300400e44079000181051446d001b002c50650000b5001c0c090610703103124400c02405100407072000e0070308685c20180c00034810382960301c04100c11500401416141031090074001d40f0352440f456000c40c42c0c802c01c035000b9442000300c2c08210402c00702401c1507008a001d221808034158132914a141ea5071030602001d0318208250128a001a51400c03925050403500c590a4003003844a40220786008459451100d950341c000c1005c0c458500d10a1882200e0103c581424140e54074160014010b0060920440c541c5a01e400d04d4035109001086490004c2a02640700d128084c42030400390f0013504180103d401c01d03800c0040e0074088000c5000e02058407560500e4401c856 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 611716897 1250 611715647 611715649
    0x60909130206091002060f0c041d0411040e06070e0a050609040908120c040305010c090e01090c020a082a0705030c010507031e081501230f0409110406090602010c0e 72
    0x318180000880c0c1c4868104480e090a40744c00c0d00300c14507001c460700104194108542e03601c401314002440304a10355400c2c4802c000400c01030204c0d04201c400510307203101c55100c50903d000a10900c3c40300704d0304241010044460044005041c5100d6141541c4803034150740e2140411600c2c90a40c85070680c0000c040c0062030381c62804c0e5000365441d80c1700e500094034004403201208443c49044540803d91030010030100240582801070040e651164905500f4003800d08688040000060060401c150341d03c0e1300d0003480034000c01c0b40c2410b081c0c10035060744e04c3e46103c0d9184030aa00c015903d41001a6200d400c820004c440003640c5800d540c0010302801d548200340c0700440d1540c1014205404201c402101844a100280d11400004d56503680300d1203039103410a0000c0380d040041c081503040013107184044a1464404c000c090240c40442d0075581d403034201c134042c8022400755410414949142c512120203c244010050040b10a00d8560040e000d98a41d826822540740100c40c1000c10701c00600c204c0d507 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 611718147 1250 611716897 611716921
    0x1e04080d022e060504140708070203090901030f050f12180901151b1a06040e1f0c2a050f0d1d0a09091104180507170118051605060909 59
    0x4004504003000803a0b55036800010207986e400c1c2c04d0500c085542030b0600061076842828030354000428002180741150443c041161610140310250140c010900c0b4041000024003844015400f4134003156810032a000c4014040d501048007200d00407000001a1442d051400310f45049840400c2d503030000307102c00c840548030104014501d461030811081020005594080310032584a03a0940359840c51030300d001407000303c1b00001c48280b51503008651a02100b9002e0600041450310000c000c1450b0908002c06d0760f85440024504840344180344140d2001319041d00e03050319131401101214034401d9000a05502c9000041c80400051220f1841101500c040d00c0c080c51221006042c44c0354003a607a80c5410102c0b0040c5504031000003400456010764945401070845807c072082002405001076601c080e1b480b4042d108035079040184070510090f0070029404800c2c082e03c07561440912141c030b0700e007560b1aa101819115a8030b540c1d400040707462300b40352007542d081380d0004d08071100d140c07200c0c00c51300383c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 611719397 1250 611718147 611718223
    0xd0c12030201021303060b09010b0f07030e0a05031e010f200a0509040203011e0506040837030908011a0f1306051210051b0415051e04080d02 62
    0x20356400f00081c851444c003000c815801540180e4001404405130300401c072800e4070603485a1a41e00c0180034000300e0191610450304152f6050408400c00d10030f050100344114040d60089074503020324000404550303d03107080e003000780b07903400d008000d5100070701a008100e0b000342031032480d541c16010585150034034400051940391200c2c20044e040103440070006069074000d0300311000072012042c04404d86d60f200303650040035040c12100306007403d060580447d03880c0403504010a4091a01c50b000303030001422110190400c0c0078005900245549041c013510340103452007075455540c039180c5030402544078000250030038070000b0900c0410a400c5810004607440c0d01d140b41c411242d840c400000c5035500c903400700300121208800b511185052444500840c0e4004121050f0803003003115040200c1e094000f00d80942d01c2117400c44c0da4640b40e03802c00300c4160144c02d0784902141e0030740801a07605490b5074058022501802c3c2210b4942e200840b0403a102d0f0740b107091b800d0070240c41141c01c3e0342549061341501 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 611720647 1250 611719397 611719403
    0x9050105031f09020418110a03090f0512090102060a05090d11030c06040c090f050c071b0e04030306140102030913020a0c080409021305150913140403020105060f0d0c12 74
    0xb1007140900d5036900203111482e400030418907030004d8100041109540208103008105908000500b003108803803c061182400c0a801c041d81e440c0400100709041d0700300e403040703600301e0104e910300410b02107908150b030701800c25071740588281000544c14200c2d074012a88210038240180000c500c8103c07080d900b8003405200e502d85804284440c001c0b203042080140e00c1140500c40c5120f0a5180c8a4400b0071140d0030050340c1401c40c280303002c200340e641980040b0b410342c6170300140c42008800c50b5614010b0901c0741350800441403515000b4042410340c150069800c0d80c642215104c11441c4081c010f90350f9110b9940500d0704152070400e15500c100d00c0b030340034141650740da09040c4803071429681d48401d41e600c207820221aa5501040103010381c110381b0088405032005640380b003260348000c00104200d00170103540d1031081d0400e2280d80c01e101c0c2150041440f90080103820500741c14186006406443e0484032180a05510868049603207007035100403040903003000e2088840c50501500e84400400c2940513 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 611721897 1250 611720647 611720671
    0xf090705100507120c2616020604150c051e060402010309061805030d0c0e06040b030408040e0a0518121806091807030c02010605010e0f13050910050f01060905010503 73
    0x5000f04134144503003060301525549480003020136141c80003001d400d5064540444941020f40340509200c10110707203482c09445040c004400e041e02c000703186480317950400c1500c140011090243c290b04102d1124103d40b143e4103468186079030701c5c109100021011052682c036403001010401650099002d100158040c0c1c10100344d042000462180d43e220f49801226960300001c1c00d41c402c1280b0307101c3e04072114010314241034080308880000710303070340118095030a01c0381000011404102a20b0121070003002d021428030301e50701d0504600c90040400701c841100000a84000221424000c640c4100c19a400f03070815091180302e40c4200d00000c8425106a003190003041540202c4d07030380b215900300101c1c06030b260880501e0220002015103031400188410b681c108101488240e030018a090070414098840c0300390f2007894070000e082100842d405054091400050040a10000c1a1604038080d101c1c03017401262101d5215080c0c10038240726000020712104070034405507200d4002541c00480f90025 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 611723147 1250 611721897 611721907
    0x501030b0a03050f0c040f0606050712090e01031208070206060603151c060c09082e090f03030501080d0c0b18030c0d021c0c1104050a02040b0f0d050f0907051005 71
    0x3645184c00e80b81124076501350300034904032001340703044e008a00950b00c10075002c0c0202407a00b44050858003580c2030040402224040c07030034403e1f200d01c42000007800022210000c550f56400d080c01c040d841448840b002410001c0010042c0c0d000081590080501070301c41841c55450310442c0d40074101503864654000c525050340c00400300c000f054101d109014a10009181e42481300282c034585e01580b01c03180341d030000c2d171025510001e003089070900300a076640400300b0304c032603c150b4100034181020f00403c1d181c01d543d04c58040c1940765010605940140003103503000d207070139030041d6400c26034020000c084010030341c0015200b03800200c4048010390300008481c2886028101d080c2042204540355005a000c08624802c00700c04800c6010a4641400d00740d0700c43d101a100c40241d20028100c1600881d2260007003610701301d041d0704440c018040f600b402c80c0c544850f40c1005200fa802074000300031880c1400c000c5030104200460550150700b40b8401403940714500002d00105104d0041c241d01801003e100f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 611724397 1250 611723147 611723153
    0x50c27101206091d0c1c0f02180a050a1503080f0f090a03060c08010b0309061b19120c02010c1b0f06020a0206091c142a0319020a0305040501030b0a03 66
    0x103a003580800c01c00c5509100303a0425003140703848254006644901400700307401c906c05211302149185644c129051004016880c004100e899400c20400a0740121400400030346602a038080380c0241c1e1000710500c01c082c20030103100ba6060307403030002a0407403808220f880b21242c03984005000740340060303070020b05006403030b00050b140c2c8109500a440064881851448003940007880c0c034058003046210506500704141219030726140141225481d00c4e1603052290200c1d00300c0251440c7c400c55040c803403081040b143c0c0081030080244444540d0360308001c200d802c4540103000f0482c82e004255580c007000384d12008a10404c80501d44180e03058070444500340080303150360004102c045482e8008244504110025920300a00754050340c0d412400c0d241c1c81000990300492611021400340e81c0542c23a404543c01034940f911114035044402c4021100c412680d0f400440901044083c1c024505d05a001900b402ea84403421301400600141d02000184100c0d8001e0740504c0c032130440948501550380d00c0b56 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 611725647 1250 611724397 611724401
    0x120304110307180b0402032502010605060a090f0b09010f080a0902190303020615090c0705030d0f0b01020d02030f040b07060207140c0406080111040e061201050c2710120609 76
    0x90001400c0e074000392283c405882c00c5020324102c201d800e45013103165183c01c2074240740030246110b203104929054200b94400c103200350840405040000c050540d01e600881c0c4c00b81c154501480380355070b034618027200003a0250340c05d001d1358451041a110310b40102e044180413070303081c4002011880c0d41c41da40c2c840240580c030b860b000b40b2642c5040c130a0844010341581030103490b0410060000c00247c050780d0f10b4100c151910b00250f900207000100c880d84031031580c41c1060450003040300301c0039100d10b400e40c01410000e4a403c4045242802e0302943c02008d0340312000c9032240700d00c4048003000c260401040258000100050050a000d1000141805503640d0707100007800707024030a1040c0b6400300c1911010381c5414407409008200a5008002d149500306214095004501c50455030600f800300241c40350300e40355907802e03500030204003c000a152082107180f1a4020103003405840c2e0b41c4d032960148803560052078106421000300f80c413680c0144600204c0780c074540c850b44410700300e454030350000e43c104e128 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 611726897 1250 611725647 611725649
    0x803070c06110d020d0e04110304060902041125020114030f0709060309020109050d03030e031902011a09150a2612030106080106030e031e030702010605090108120304110307 76
    0x12904600001e203014001001198900349240b06900407034007190b810768000880c0e1160010301d06000030340c6060440081c0c01403030314152524009500004100c200b059990280381054421201001070000107480210103015204040e80c2c10422604985800e641c11000d03008641d1051400600ca003070030060b0f200c0c1580041c2d983d605c0c104620000d01004a0b0000080406040e0500c0c003003240300210340000340f0115191142d13502440e080d100040a1500c02e80001b410f00e66048200c0340c0d26402c0202c407041181034904001c00652816180044e00844410507400407800104500455181c050381050b000f0000c03444039600201003100000c204400c4404402246000b48488012101400301d0605243c039801e50034240c40401c00041c010660480d101034155111450002484541c0752078503491441640100c3c58082f510b0b2070a01c040c494288011481155594001d100f0650f54200340900c2460038010303070009810480178409521404400385901c640101d02c13802c0040d2200c80803d0030400030b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 611728147 1250 611726897 611726903
    0x60108160e2208070309170a06020c03090303040b0322020a090c110d09051206010b0a14090a0906090b0d031b021c080306090f2404091b090b010509090a0b0a080307 72
    0x1013152014550002d03c02802049410f0300c40445400340c0300c030300b030711100c811388024031459002c00c111003c003404100703071451030401404aa9a66440d4040280503030000c9401c884540038010303040300100c020385800310040e5405409084680e040813040000f500f10302003410704100f11040d284042020821440e1110030007900c0d295840d80c100710a0203000c1080d00e400d103915502c40001004251640011105e28101c103107000c500700302c081c55a00505201d46441d1030b9200d40b10030008201100d49a0041044440020007013001c0c0b8103041c06d1142c400390303000b00600801c140035903a07107000c521000c10111310f80c80103040e04e43d204071a02c41422194071003002640c0c60310000c01000901e0900603450794018101401c5081c10b40b40030510b0f0000c0600581c8025088001d1103420740707043d26150080e4210941c04607a074401d40060b010f20288142caa8481c0741134141c00c10050403807550083d0708071703032080c8405800d844170b603030f135400180c0b0140c400f259035550044040040096006000c1c00038200e00c0d0b00c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 611729397 1250 611728147 611728163
    0x140909160306050301020903100507140f131d0408090a03141b0105040807060f0c12031b031a0d0809121617031b1c0e03060108160e22 59
    0x5840c0c0040c00c03a4240c0e0040ba01a81c41000382050950b00002c0c900310f85049020041102d55030b0240071500111204115490208045200c0b0442441880a03005404040c210409440d03500c60088a001e14600400d20b5030014000204002c11a25401070018080c09403030503204594980c0d0b14020303892602c038803032029017041d0a90550b004800601c001100c0b024680ba50805040105890300d8a40c54804c404c244666941c3c1e515000380510b50b0080c00d150070100140f0080d0400501401405082d07849a040c2a05801180c0a081c0039104106040c0b940314400d50f1022811814014544486c80c0283d42031002400309030f400d60389580712100c0c4c0d4401c5401a00e4000d41480c0500f40c05411178101d003110480580d4110303094540001512644030180311401c12059000898500702082c0c24240503c80386a048a2060a500082800000181901100c005a80c1c40501030349030071000098000314081d41301d08000c04416003401d184c01241d02c2100d21040030100b44070740d2410180c400c0480d4501 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 611730647 1250 611729397 611729431
    0x1f030c050a0617070e0102123c160215210604110d05180f0f100501050a06111612060e1513111206010f150f140909 51
    0x41420040789004041034105140050800a040450180000c040c041000103105844040fa0702c2080100a4940c9040441e070b61141d428081a840b00401d51213800c0d410240d95480001c41c0300e08030103030307000340b84241e6841c101011a01c00b008241135100c2c1c01d03a480400c80100060345009180181f0020800c54096000784a040510700340c03102000b0807030340c42145400f45c10984450201c003202c2c0010542030340029075684490fa050800d0352036503441003480c803442c0e0149241150000c0c060500300d0b050012100c0125a240030300301900d20901407250451510700003007100ca0302841d004a50110b198054540c1c2d6000c44482d140d1400c841e40c05014613f24954142d01888003038810040c02890b01c06c090030f09500340c2491b018444802400d6800c0000b1036804441c01e01c0942400141e4140000702171000488440c0030b49591650280103038041010100000180d003c0480c0c070030b108a03111313526011602d642e070070741c19100740d01c11421018965108218040f40c5035140582c40e445945008061401c403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 611731897 1250 611730647 611730649
    0x1510111e06010e07020a0b0c03060d050607030b01031404020d020d05120d151e051c0c09050f010f0321030608010c0909050907121e02100206010311010906050703081f030c05 76
    0x100c64050701300c8055400c1040c85c000428942c0384801d50005502c400c1039601d8a400e004500350001e804800b40003400b45800b48119581e15810030001038009903002d010f03030744508110141b200415070b0001d501c2181e50031210f0060800703e02c1c0042550151003039410301c0020707070700c4900f40340d0002d484000354540da00f4014101400c3e503d4554040d101503503076605a209400584920711206000d1648202405001e41800e01940205003845503031020005140d00c3d51090120050001070302c0310349400340c081002103200c0072164070100c00c60f500100558004586a048c2a2201c0070780d0304144100b54640c00b020400e034809000e01c50b0140482d13519080036501c0e219440c41124000303441c800c0369801500041150f4821000490710458119001c1219400c50304602d40c1203c0207040025005040070552500d600e40110341281200c0c0a00a042603170481da40c011101561580a4034021030402e00c52180428410135820b41c0c000c0c40800180c583c466a46908006a0306903030040351644401c00d414401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 611733147 1250 611731897 611731919
    0x3090210180b0f12040606090e0303040c140117100e0415141603020c01090516031401020720040b0306090f10020412021c0204091203051510111e0601 66
    0x14403201c112035040c6224155829024451a4012024052400c1c007042c02d06c9401c2e0300c4800201802d0358104440c4444481242d2281c000700c40a1340d101507150800104100e5030300a48808100580d1a13825110030500b1244410b40040c0180e840d04240d4440171070000448001540224022003241c17022403002804442640c20b6039507a070310210220424031110002546102078071604c02d0a0250329244020b13803203801061010b501801603c1250303e0101500210360098040e20300801e0303260550703940c1101c054280e03c15440f00074050110b11090781780500407140a0035103960002c0010641c501d00c0c1e00003e181200030b0701c840003550440c43c400881050200710001a40e21007803015410035280c10510b6140c13003c10351020740980c0001d07440351494043e180c003600d15035500074030030054035182d400c1100003034180e900d884001c030f40742c500401e480c1504002c1800c00c141c001864001007a1200c182100d0920344011107103441d2241c0400640100b894010602da8001c4180007803200f50701d0400c43c110 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 611734397 1250 611733147 611733149
    0x1120f1a04021c02030706050c12031303091505040306240603051501170417040e1f0e06090c1b01020c0606150403030f350a0b1c02040504030309021018 67
    0x30043c501c041c2c0c514010385012031304800319038580c1030464075003242988950805100b0f000544801100004114249204003c00701c0c40700e000381d4911216a455440c0780d80c008500c0e203a032201180d022f00040000031610741111500238070605001c109244c040402044409040d0080307400b080d2140100040c50308091503d04c1c1070300091804145055030b00401a4514030302800103003040c910300d014500420300080c1110700801c520b61200b0450b15042400d010341c0081414100351001202c1000540d8040c420304030b5009182c010100d0f0002d88800200c90350ba030380184030841c3c980d0014148803010360300a1020384584038801d03002d0a40362401d50201701c401c0780c8801200b40c144805005c1440440d61144282084090328140500c040130907003000c06c01f010000402d001c48404054503a080154910390310360248110704424444008139108100501503410843e05102454010f00005840c0c0f6401441d0094020b040015402c6801d401145070070313010152500210321190003804000c4039000c1540 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 611735647 1250 611734397 611734429
    0x91005100e04060504020102070e01030b01060305011719061b03020301030c0501111e15070314060616170708030117070b090906091008100e0f1501120f1a0402 70
    0x4445800c16640c95010324020b4400b41045503240000340440e402000428080e10440c0503142203176940746031004030403400340100c0e00000d0600c000065108032079105c0380c0a01d000e01014003004081075812160b0001619400d803641c0c0d481d19491920315000d0002c40b5001c614541e0056565030440c00c1030000d10525512071410400051245822031001043c41c0a100100e50b5506803501c912a0240740380c002e8a482000a8246803000d1050540d0554043e001c400b4600c2010045503449000300f0042b0b0151320140180000751082c145c4c0062000805440c0d003900200c0010700700000c41c0c0300d02c1c1598000740c0102030100310350050411000c0c010401d0000400356280e00030302d40854100440c2e800c1c80c010f00420301a88540700411101c0032807105440180c2510800c5035511042800b68001400d0140d222036618080c0e02e030240000c0f040841d51060840c6442032108180c9d01c1c10b41c004070071181c1c40000740c55000100101c1400940c1040302c21241460b0601c1120341c4e82880d00402803c0e80d803100d100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 611736897 1250 611735647 611735671
    0x70501060f050906130e07090203060f030606010905040e0f06040309051305150d061e0c0f020609031803030c1614010806030c0405070c050f010c170c030109050604020702030303091005 81
    0x401090f60703040c14240c1c3c020811744503004103c403801d02c0305001d817a00500c801054040e411010800741a80da010390f102e000121081c906d214041800c1c50b446800907640707a0700140581c0800d1001d82419000030301c081409104607003904d03250015113800c04405407001c50000da121041006145007003000b0b1494a80280d504000c1801e180d0b6480b0140410058417030300070844181564207001d107991011641015030610723646051001002c1e10000c008004407080404d0b040214429001d1001600d82d110b580038400a40c80c02d100e0283c030a542503000c7e4616681032000300070b111110700d01808080c0500c0240c0c4240b910840c240541c2140521030b00c1b6200341080042010021075582c0084c0d5914800390668000800340c0754048120b48000440c88050700a1180f50003962801205500281e2600126500e0301414a58440500030180c02510400c41242085c0700600c04011668030060300101300500c01072a152041e404242160400c0f20102440c0c2c0100191480d0050f06000d990341c0102c81a941c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 611738147 1250 611736897 611736899
    0x3050f06090c0f0a030609061d01020a0c141f05010306060b0703021507050409020f090901090b0d06110d06270b130f0212190e030405090f060a030c0b070501060f 71
    0x48542e99600d0040341c40c0c815452002d4038450b0b900e0f070881380800f035030b0403500601c001b0b216030400b1800341001d007446108411001180040552041c825544062004ea484141d60381098840707141c808108240381c2d6507401001418404841e0f64030b42c110f0b400d41207000c046a65803550405500f02c48655000382c2c00220208070100c002a808541c0400c1410100c90002c0c29446410f011075060049411200c5c92610004030320501490241c082c0141c800c007200c840d503142ea2500183c1050b40c0c441c048598001b07821140050000307c090308212129030048074592f06020b031000000054134004d45c0070b03980104024407071014503507400c94501a901c0a140050181011100110300c0036203a20076108a02c030364840c94465040e40701d40403500382c0e0900e003180010342c2c2000da070580070040390b0700013904445241403100050b82c2008002d071000c82d900281800608d81e0340c0079450020200c010311040d0311030386a01d00400000c5c880101d040107001d0404086450352203614101c3d003120382c00d0b00301031021502014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 611739397 1250 611738147 611738161
    0x190909050c070308070e03060a0b04240b25060c0305070e0604090b060409090b0f1b0702012703050106081204240c05060403080609060402070218090a06110403050f06 73
    0x8102d07092958946030012569950718421600e480140d411a0b81c035001720418005000f501e030f0070410240d6401c50b400c0151004544110502072101c00806488848514003080640040f5000c2c00714800f091114070f10301e03840558080540a0b215004035052a5121800303494954584a031503813003003072030404d500c4d410303090342c000341807802244038440d80151200d15001c419110707201901c005000d140c605004540003441c00440d502000c641c0c039503480c50181c0c0010300a0307007688a01c405c4050300c3e84180c1d15255030758004680510750303100617405140c8041010b01150160f1011000118040c070000645541440c0b085802e040744c400c41d0791a081c205002c14040b0094820205e00c10511a6032850140e00c039042d019266001e02c10000381260051104010505822201280c0b00303070303011190103640341d94017000c000403400743d4000030350000d0244500c0d20381e64007051510740d000818070f81201c1e20f03110540c0e1f41800b6201c02540705050751902083c20030810808100c4d00c44400b030440003814076890540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 611740647 1250 611739397 611739421
    0x5280b0904140106030c030b04030807050a0507320703031d01020312090f120306011e08040b0a060f0311040e0c1507031e03020304050c030f0309131119090905 70
    0x7500107021000200c00c20040800254442e6005590000c0b080d103c1603900e040c8210000c40840341540894880000200341c1c40c402c80460303040e000d41e51503650a02205031a0240000490310070000c46901e000d6956071031919400811a0f403400754402070004904618005100c015083d88054818403010643c00c5142e0b00130040d510740b0100ca1601e00955603c120035180b07000103007a0008880e00900c0c008501a10b076480056100340002e817210081600c5c0c403221603d259520500030f8000540c0c41c03021400081d0105101c640044581b01c020030801d84400407180794032003d90003152071907910001c0c01c2c01c5051900030215140e00c9500506202068440884c0000810550680810900041e2401058041d4030305641035806aa1b01c011030456542e400f400070350040d03e040c1d4091003500306080036440c0016044805d0b4078400c001d503040c00b5014040c8000014047ca46004103603e4204029000c03000002500b8003400c1003881d1140c070300814a02400c1d00d08a5040001581e00303240070400c02c50030788 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 611741897 1250 611740647 611740651
    0x70516261c0902040209150c070f060906110a060e012012060d080f070c050102211e04030b0901060303080108011104030206090319051f06140402070507080105280b09 73
    0x480102c1c41c0a02880000e0080c428001c0c00c50f40b042003c02150070300c5136104c02400340303900c510382118821511b503444034410140b144110400a24114820b01005209841a0070400c41131003c07039518642d296502c405403081c2c5400344407580e45d210340524546008401d03141a45a007201a80e103050994040d01000c49070040004d8011450380d9030134002c0080e58001c1355885040340410316280e040c9840c000914103050312400380144914481c41c7c0c241e80f134049007621a60041ca1b04c4a180046035800c542c140340042d0b0300e030380c2011401e101c00400f0405220f40b0b00d101c3d800c0307040009561340c00e51401800410f4107810031141680341245195000002d003040720140c03a0100c1d402a10b030402d450000707160100200c10300b403841c03006030031490407c88006000210014142000b40910410f01c001c074040b00d04a12030701100c3d01c40725100901c01c0c1019401401424020001e440c24aa1105003103800e40d00140c03454410b650b00b4a0aa911828000150030f461071503003101070000030001c1d4005030780d403140 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 611743147 1250 611741897 611741947
    0x2313050a0f0618031407060e0f0a0e092d0d090b03130f020607060f0f14061c081314060a0f0e040e0a080705010b01022407051626 57
    0xf454141d900d01e01c2c0d8001410010366000c04446400a80a0700d440d444030302d5482240081840803801c2d4540d490081211854960081e04c80c8000901d07140001503180c402a114000a0040100e40314006000e5100e0074641047c040069400c1c0b00e451018516100c0e0144401041001c0d1407030500441580c00b003265001084007412020f41040d90070400c500f070039103140081d480b1000107200010800d064104140d909819481001081c400724951020b0341c207450070b48a0700a2220000814524049210744000113108580046d400b02c10703581d00080f940040a00ca0030413a5035907081007414ac0b403100c9046000e4098a2060610300b040740007074000d010354440c42c4140120715480808584582d404141d0f000c0c6040304548440f4035038201181658003001d4251000e500701100c61400b5400021000c00c41e0760a03028421014040030f08800500c03401800300b4042210400450342c9030095610310303034120390040641510070001000348020200c1a1030507903410031402d100300c892803442d400b502d00c04004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 611744397 1250 611743147 611743157
    0x2060408090a12150c030e031c15060c2603060d2103020a030f05041e05101506020d0815040b0a0b0d060f0902282313050a0f06 56
    0x3004500042c038000442d0000b0000c0200b500f0103009101040d02d042181c840b018104000300030b003140f0b0450a5840ea40031503201580104208019110f2214860743d0800b5003140008110960b148000c15649141c0e00650028103a220749005218040000300c9014415544e441c41a803880000c03034409003c020600c80c4100961010311052000320305c014485a42020001081c081c0c031500098000e4000e44100700000745000c5203422003103110312a85000d0340c0c12248200b224029840d2008040000030021501d500441e000403180103403e014520300172004050446411781002c1c40245807040006882c1c04200c070b01c9042c041c4c85010a150708404181c00c0d50045801164007000c03400b02c0304983e202c41c1203030000140c0c014514400b1350114044c0d6111070310250010317942d080f41c03000b42d00500802500c09424020703000844522000524250320503810a010f50b0000c4805d07080003b660001212801c54000441007040d000700b0681c4c0700035000c01c546443d4a10308001e0400c510803490f0040c0002c4c80 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 611745647 1250 611744397 611744407
    0x60f090d0f110a050f01060906140f0111070b030414010207030e0f0d0b0108060403031104080601140d2a05030a11060d140403030209030d08070c0224162102060408 72
    0x75101d1250400d0554440044404001c03462808550b28074440c0c4140456503c0c0c128045200c040d5030183c0b40480d0380300714a17a4041ea00880070400b110049000281c140034403200340d05880003041c002c1c000200f1b001d131003c40e140e02d414105200a0540204041520b034410000c900c0080d80100d010580e03200103840d0040844500808242c80801004020b03111514407030000030000c0c0e0000302da0344035a06c26641804102801c1036003030b8160043e4002d081c8a6041100184810014030300220401c450003054180c4c41c903c1034a0f03030707940c8180c40101005041e000404e4510008900b601010040c0030075401060002403036101c2d000d44808030060035200303400002c1c4900c179004041d0040907401016001040990a0603d0050000c0d801040d010740a0b00807540c8205115014000462042075240c40c0c180302200240d00308034200d0710100c03900030000a45a6500301000c1020050705421000c2e56441c1c8050f0f4990901000780380d00801600000a9150f030f4100318140d0214005421070351104040d0340301c2c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 611746897 1250 611745647 611745677
    0x51c030506062b02121e041208040305070b0712060f050d020f0f1903060f060e01061b051b1f1e1b03051c06060905060706060b04030b0108060f090d 65
    0xc0c08140350900e168500100f2964060505d88849500445110014000d0381b0305165454034240000c450240024a002405000c410b0146810300d51182c807914045140626660710300200c0507040d01c040d00020001c9200d0105501c01c4c0c030424000d0500651034042c0d0310300d400005002d008031084000c0c0101030020030701031291180380a0100e9010020329040d10a03d0504007040180b0340d038802a201c4c035042c4074120006014500c9002c0546e8810042021581e0074000280d40c42c090b81504000100c20340c982c014040782c41032013000c4501006c40099075484420b202000840e0b21a56046840401c00302540c14074a80c020700d0410410041c683e0708100040b02c120260350010b00004245000650415490201540310000344251103c1ca42500e114031241140c0200302d805500810010480a0f0030900031441c0501c003900c9807500c030f9400440c046444000e0f0034100e0b0455801210391503224001402140300a000c03181c3d210740d4151118140b45441000301d55218110000c0105119040c507844100c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 611748147 1250 611746897 611746957
    0xa08030d110c01230a09170f0c1606090e09071202190603052d0c0d1107051b030303040305270612161b1b0f03051c03050606 55
    0x207041c5084000c0140c01e4083e000c0d483c000c403075101c40c186607014260000b1707002440d130301c20317106100d0b00502d22401c240042d840d520500e0f40100f00c07040303c0344400d000141d0400c008101e1400c0800400d07880450541c034240025020036041d8225042d074041c0c0354108224800b000403042c0843c0c409048480104202c0e0002c5040c0c107801840103088032030301e041d01082d800e0b01500f1142c0101c52000d0514100030085080d00424003074142e0354806c21858030041480c402c030725005800041607d24000811b13544041d038040c519405604201c52541104000c0c0341181e4001000600b0140180c0c0031f145940f0303246d5030042c03261140c903d0000141714566100e40640321107088040440034007400d050399900c005084410400800c45428a001683c002112015403140d120303c00b180300c00203010130b0310340e205a035a010643c1d003210101180c550030120015001421200e000300440c040c002400098a00008459007100012000428142800240329040d100c000440b468100c080b0b0340c00c11480c9486000f01c0c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 611749397 1250 611748147 611748157
    0x50c0402280201051e13060f020d0905060109060f0b0a030906090f1104111e220b1206010203071505060d021207080c1503060111030d020403030e0f0a08030d11 70
    0x6603484449074107160040d01548058083c0c1500e41c540340500c8601e213158240c3d403500721102e0001480344600078000424940001e698442c0460b809828803480b21010303011185400420b64295002d400104040a5144100300141c030360900c1c01d408980c144800d540da24401d511803907081654900f00740b0107101c00c5134400c5a110f030388034024460320013041c1012168001d41c200894441d80c030381b1480310f1591103008100d41011500050f07428044a2000601d90143c012500034102c0c03841e035008190381110300100300070241c416a034400e511000c6408401d00414402466035041d940100406400710780c001d155610f441c0090f0b20301084c196100c0010400d5415084d60007500180908030000c2c54840200c0c4140c15158860116009549403e0401c60500810410500e4080c420004102e4651064184012000841c4110b034034200c460042d04c0100d81c440c1e4426000542c55100c402164680031903c00c031010000c40d2240d200d6800c1a15841d26481500c243d10280340e9103003034041c0c0d00030b01801520 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 611750647 1250 611749397 611749447
    0xa1b15021801030b04060806010501030b0409050303070c05071202180c1b0c0112050f0c0a0504080f010c30050603012301051018030305090d15060806090109050c0402 73
    0xd0348880d850035048003041d501c1207440380400d081219600460030544940f104840300e14008196903407074180190020808050303140d4120340c640503500d0110320304200842c080c07201c07562040207103586810914107124142c1c11080700807110503108000b40c0d44040c078400340d840e00c1942030702098803080d101d83d0b898032a8603541e285514500d202814004000305400190240130388800c01c8040d000c0038808100c4100301d4840210340c4a020200d0700611011000c0e000312101410a01d25084c1c6803020180390074681042140160f45800d00602032613480103086540340141340550301c20301100b000310700400700c9041c1e40d4201c20f0741d01c0d4001212543c0c250490b034000c02034440d0340d8403595200c0c0b2610a000d0b5003401030074000c20200b6441c11505210f5403410211080b03c280c1d03001c0c0d04e410750ba002c5855503c0000080e500c00380410444010a21030351101c09102c521840024445151120b89410844020038100c100d91512880901080000c250f200c208002154010390340e01810302814108402c1c66021 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 611751897 1250 611750647 611750651
    0x90b1608030a061d04051e0a11040e03040e0109060509040b040209090c0a06021608060412050717040b070b010801020a1205060604030b01182009010f09080f03041a0a1b15 75
    0x240b40c12030302013494103000d10701480c183c602c0c0c88030301d49090440d04615642c0f41003035440303a0380180226003070f0b80d00c541c0003010082c00403540c600031030f014901d160051381103908100c1c8407500410000716540700324402060251030b008120300c0c0c00d483d41c1c8404040280040d02031b1259000203403040006003d86600c01c0d8008100d110700c0b549408009554105007544078180d10141da0021a11b0100010794503c565030290800401d0001064226003903000044100c030518200d941c02c0700011143c5000d840603124160300c80741c9429a41c101741c0305051041c0e00c83e4078540d00c10468103401c0c030303445400d010007688800380c04601c0d80c40c3c042c0407402d90b100720303880504020075100000c44c0c1095020b114548249a281041c0100c84d40b40000e50f400320165035a000e07807203170100140710305940075215804c040c01031801c1c410420b903500c0201d1828148250000f1468ad00001400d003c5405507580700480b00111503c100d0405035820405804500412684d240c4a282000408100f08403100d20200040c2241c0007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 611753147 1250 611751897 611751929
    0x21605090622020a0914030a02010f09080a0807020306150a05040b0d05010e0a02120c06030a110918161b0609150603060911062706220303090b1608030a06 68
    0x21410003501310100c1c600010f55004400100303046c502c0500c245850005000d0098a03210368019109111001c9900d420701c2640c02000810140521449010500400240e60355600309d204050030010014001d8012400486c4403140b2911401d001030b0544006030b50008583c50501c00041511920400062256080c5050040110404184030100e640309484c50303d065035142c01c040380c443e800d001c8095000341040c0b00046079000395401100780445003102d100d00c2c0c80e003510080303100380b404851030359201901d0200780580401ca6030300300c05100740310703183c4090354240d280396000d010015082d0250200d51200c8190041c4603034130844002d020100c56003049401d42c0e82c9844c1000d2701900e075042e80c031424201d052501c20304142084402111a030f2038140e03110398450000201c00781a440b105a044030050110f03080200d0000988181c8245440140802c589949001043c0b0521384d00219108a010310108100801109013154080d91040f400d80e100d5483c10200c10003021141c0c40b0f00a11066180 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 611754397 1250 611753147 611753209
    0x50a020a0206180307050a120605062704030e010302070530190201050604051603050426090a090225020f0d080c0c0f1e15040e160216050906 62
    0x1283c1c90840d03c2c16802d0302e030190390380c00c101b140c0f500d100d10895090702c02c04d040b5030000541681c407607580841c00134816001003441402d203156100c58031140d4101d01940d001070000340342c1c0020000894180900e02503150000326641c89031241d2052203600c000b03882402c061030141500080c03c0b42210300e0848456110080001500706e00e07401d6081c084090f500c1e11021451a040500039184503015000112514070704801c4200c00600c8002c0007503c5500c0302010384482c50742101c1c50324201141601c000d903103890b0000100210070b0059444182e1080c0f04000c43c0030400e02c1407aa4505089220b101c0013002d64082c0003040004040004035948030301c008a000e01000004d601600a0406007000c58881c5003800c02409040301d08000c000c2d601c034014401d030701070038140c84510101c10f03e0061b11000416107111034107070050f08607411440031950308070104070700c0801120380c0d508841d41a20040260441c000701d10030450001d400703068040e801c1000000d8071900c4240c1d64620007540129141c1c20700d05201 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 611755647 1250 611754397 611754427
    0x10b040605181228031e0909050a060303020606120a080307020304270f050103230a0605010807051512070f230d0b030303040506010b030414070602060a0c050c070501050a020a0206 79
    0x10b80c00340542c10800c0c4104040507041110b910101c1c0e8035403a290300346c16002c00551252003e450f240001c02c03800344408500d200c15406402c0c01303040600d002189003400d514000c1c0c00d02c40001c0510f8001c44400c40c0e02c8515100c0010030a481ea07400c1850b203680d0313480e130010490540c415600f0a40300305492080e111480d100b00b182c24030051101020420074400d850b02001c05440c0c080c84050b10441c294040c80002e20070400c00c1000e070741c074948100c2c4d00c1145d082d6640011b52f8001d07403181c240380c0c000e888204401d041928105104001d80403400b41390050084421100100c003429840804c0080c1506409480c00f40307003010566105903290948070300009a002015034403140c860110343e0b0420070040154140081520300071544200500682e03801c114482503240c000420a9130800e0703131158040014042030020001070481d99001c2c080d18a0090184010b890440b4400c41c1049420403100c910b18401090302003c2d590700b407074442d41e110f091030f401f03e141044110b4065481000000c245440c0b00f038407 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 611756897 1250 611755647 611755663
    0x20c130b01090308070c38031914040b0f070c1209080a050d0207080a02090a0f110d0911091611120c0a1202030c07090e0703120f1205010b0406051812 66
    0x6d501e41144864030f06140e10780c602c3d0521034010700c0111100c0701f1001000180265920006078a190f0003001805000391080d0780c849143c03181c422074141d041c081804401003040d60300842c0b58084104904041000814508814074080e201401e4109400301c6203115400d51401400341104403401c140803800d105480304145800c1c031025101d04640007134050b00104c2d540c090503400802c1c4040340e50b10b2410440c05044c61541c0124115034444040c10061010009000300c15800792000440001c0c03032421500d440d602a05441c0f0505c0030380c0821140b030001c01e100402280062401000960501c0503062a000d003511809400200100390103c3d10a80042d650340c02030300402d494030480c0c2540c801030340c50f4898a214184280c2007400c05001d00c04550b000b0307103669401402211140d0751b4984a41c09074032140801240040c44213030b604400b96501180e42d035001d0342c0c0305d441000103524001d00440345104030310400e4207100300412031001218500d1a407011191001d45212031030701a050b507650700c0f1156 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 611758147 1250 611756897 611756909
    0x6110f03090f07050a0815180a0311010b0d0f020402070615120c0909031b0507050a060306061d010e130608060403080603101e09060b040c051306020c130b01090308070c 74
    0x7407050f0010319031030440917010880e000000a0311ba41200c1c460144a9003400402c42001a020f2000d01882100200f05132402540a561048060040506040d094801c0310460314815441c002c031940c04100500714071001e00798126001640c4000c2494524080c058400100e8007010705950300040380004010b03043c00b402d20801400e00b289441c2c46204080310410100540001d004040c0d41030f50003400095025002e0064084901940c1ea50b400154013080c0c642120700001e0715a002041281d030040c00082400e085001c5040d003540e80c50f03000074200c03078141d0700c0303644640b040c5900d564403518a07510042c090040130069500515140c06c010304030354415640785000e88a00140c11460202c103108051111082900508180160111001c041c041c009000d81d500c1e0b56801240506075558840c3d40d48000003910b5081d1120483c3c41c000c00649542d511507020754102d119060a140d03120031446820522021000900d0340e01c4a004907258000c41c4c000403c204800038503102840551001001103c0c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 611759397 1250 611758147 611758153
    0x110102010c11030306090907090519060b070f03050f040905010e010608060a1a03040c0b0307081005060403021c060e0a03050306100906020a030f020c030a0602070b0a02130306110f03090f 82
    0x30141111502c115200403034807034000340301103038240c9031004845401c00c2040307007201c21040c0c59002d8a800c03103406681d0241c501c500e655250b91010480d015410050408003400390504c090303512404501c1e88001402810003a00042040713070012544d064502803c801078007005191385078100c902c804142806244041200c00000a0444c03801c50700c011305035034411201c662541c0810300b180342103800c090402c0f5500380c81c20302e001c15216007200c003951290029030303249011030070000e410400302d0300c50b80c000324060141003200703001689441c5004e1011070322102c01e0a14984490902070001c2180307402002c01d601800b4000000e040d84100918000c200413100107210891000c800c0d0341000c201c2c401ea00158100031115808a0300803d0f1850800c001d07030040e070381100b01039070000e81400542a030480750350394045090418462456480b070f502c4a00402d04601d043c102030104220004d40d44030050401e6269189540ba041e601001e41d0000469000340c2a180d040c2036540c6500c030100c4000c80ca1040c8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 611760647 1250 611759397 611759411
    0x30b01052505011a0d06020723010b120609070509060604090507180b0412032006090706080f010608010b0708070f080c0c041a060705071706010305160317090f040911010201 76
    0xe1028000c0d410020001030074807441840700e07500e0034041c8d088030300c080d143c5038081180716880d0101c41c01b01c94120344134100001001d58036401004801090703c0d060040e00c0c0e0001003001400c100c00142c5006440045601500d69500e10001800c5481581c2084010074140424000c1c4140c010031042c1c2c0d8014408946401a81c0368001c1c8900c038041c1d0310810005400c0c1102e000b0100f030140c1d04000c501017511101e034078008a40d6145615000054840960780e900000d000c00c82c499000b1200da422440c0e186610150b549400d00003084542c06001c0e032085500e00080160811910404a580c0c0c1a4402a0000414018246a007440c1c0011801d10024000da40840200345007a00c00c0306c40803090f0700f0a003590170403000b0520600d41c01220b0102c420780308801021508040d984c0c651070410119400a000e550b0462415030b00b030840100303500506070400d400600000301d658801c1c140300820080410348070401d00b0300042c0d81e80b607480703e1240c01602d404185418820b500e8a8502d40140c00e8009015030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 611761897 1250 611760647 611760671
    0x21140309130c0e0f060903070f06021014011502101401170c10050d20130501080c4008070b0f070f0f08181005070b07030b0105250501 59
    0x342d0b8124220000088142c02030f0b0156180021010405480c0a0b200350708100413007010919000054001948207940184208203065042004546a0184d0341e018001c460212800c0108208180030f002e40610600d0210b202d0607200708030152511076624820302c0084d420410505002d00b003800b84d050103070401d41220031130310b1002139145904c1502418250a08441000c2142c01e904010501e21006803229000403060928103034201541007081a100d6551981c071412190040c8140d01403418800e1020030032080240308001d842039a41c44040040c00d15280011803002041e84008004001c1030f402ca000c2282c100c2c00301000c0998200d84200c0b41450303100c1c502200030f406903000d844e0742e040041040400140c500c002c031601107442a0405c0c069101344e83d1b24848240c000280d84101ca0002c103110140510b08691049480011030600074503002c0c440d1030341c0c480868000d200a042c151180508038099228004850000001c1c2001d10402c0c01c02542402e98000004001d940f00e60810f03200d110030b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 611763147 1250 611761897 611761901
    0xc0706030b090f27030c070f170703021503060d061103040b0714090114070812161409061e0c01021c02190c060f020f0a020105070e030303012114030913 67
    0x6044401c4122804c031070328050350380c070754590411100610301040c0140c14904504100c0e40000c3d202c940145000103040904074086035207a00f03489126944250810000368480b00c81e100d551482a5401c00d40e00d0b517800c0c000c56029400c24800401da11b28000f2000000c1031210051030007039100e2602210207403250207048512007229003c0c500c000c882000000f5036136004110b802e802c001041106414401c480d00c40b41c0458000300660f605405458040002c4078804080d201100c844d207040021104007a82c088901c603014010009006000000f12072042c1c881440c0c144402042c0c0c58041036841146003443c2d8003030b4108000d000300e07a81800301e8005c49250300d0300944040202d100003d006c03031500c1810403100103c584000342d035400d548400d844ac1800580c0000c0c800824080e11199a030380c000c010007400c4800060010701005200198500d0941e00803080b00d0440d14120b03440b580928004860024080d00204010204041044d0941181d1340c0070000d03054a28003216000c003010005218102 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 611764397 1250 611763147 611763151
    0x30703020702190e01140d0804090b01020d031118040207020904060b100206041115162306100504020a05040518100510020d1d0607140c04061d04080c0706030b090f 72
    0x13800c01000380140b15050030f00c83e44090f06880107000c2014076001e6180c1c0011984550800e00640d0b448050710055541c04200b8914040341c01d280401050340c2da400f00c02d0450017040c1c0307801c00c41c0b400c0c4080844296035540545170b42c160000d185d42e0640c202441d007407005203065441c0a0080c0108803141100790f0000c50840c0c891904040301103043c050501c10407809640c4001d2146c1c0040341440b01d8200c00c400030080e01022441292100d02031440b01401206003110a10181d11550040040122b015041780342d0008403002038a0143c3ca41c80102002d83d01402150030154010311250001c4040200a1801f0b0340110502c3c40014200394942003406901c0a1180c0c0100150f4070800c4030701c5da002c2c401d200385044814041e004000c141c1705113002079925400384c40d01381c4105842c080392544001e42441880d88107001120200500d910300381c0e40c040b075000100761480c1d202e100c400c0000c05114510f022940d00109170310543d11510348500d00a00107156003070b02c0c180910b190000086427901400d030494 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 611765647 1250 611764397 611764409
    0x110703050318010915020d17130f0c120b0105040c0806092a0f0c01050711120309010605061612021501090b0316150e0f0109030201080c0f03070302070219 68
    0x625025a080c5403020b007900801d034032070411000790400030b902c1489042c116082c1c0300507406400c009140c040001c111a501801103080c04800b80b080c0800001428404419103a11014003982000141025680890540c0c410117050008280e010200603013003101034140c403c2110b0801030040c929004a4507171000701c40e844e82160707205002c241c2000307407122066000c900c104030300c644811000c040d000300e0ba0083d0949041240c40454202c1442400380921f6034009100d10301280314540002c0429a100344515030440142000400b00c0d071412420b403c21006004051301c941c0c1d6440c1450001c40501902103000d450a50402e20000c0364944080f94a005d41109075a14a119908100840009080d00041e20346d0501c1203c9415400990842c0f0380e030000c2940b4400100d9103444214050251045004210301c260001c5216190b260b07048045030054030f030203203400704003541d91a40103002d500c550301030120100d0002c07040142803035140e0000c03c1110300c203481e20a1b50b1203c85103000d2b03004446000340 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 611766897 1250 611765647 611765653
    0x3c0321070206030c070c12030215090d0c11040e071a13051c0b09030c010b150301030809060c0a051f05041502090105070807050105060f01110601060315032111070305 73
    0xd016180070009550811200802d10b498417001d03588000c03010340079a01408141d5450341598080c10780622880132120310003002d880b102c0c074020f80c14a0f1900007507000c0c1000d210140303806405119614092052692020780200a43d4510412680da1345c0158030070040440011800901910440f009442040200c5100e40e001c0500f000308005405004000b00c6001c646414040000303d5000509180168440409540d481c48101e01050030349070381586a0b400342000e424080000303130724601140d044a4200080c80e464154810000b00c5901ca800003044241c802c1d550010f007444804101454006001121030010555641664059030000c842c0500303204240340140303a80302c6158000f0058034905150140c544012070761500003035081514140d034180e55800800600d4186080c071100c50000034200655103070000380900395248014000d501c01c060701c030040000313500f00e004080e0020356408084a01040720700102a01012582c1076220001081072100c02c0443c48003060303800c145c80d00400a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 611768147 1250 611766897 611766907
    0xf03020103110c151506040302060d0c0201060e04151a030d030b040618060807140603070f050d020703050a0305010b0a02033c12090d0c023c0321 64
    0x560082c8070916031281c0d50341003085610000c030800d004500c002c0c2c1d600d150401aa042c0a0040903454510f00800b500550342044180b0160783d1713050540b0540200d07854042440320909008901508803a40401c0f505802c3d0800d12003000480d6008500b11000c02404104c00c110032003c07407100300d1842c183c1e180c2503040788103080c80c0c3e0317403080e04015103007807028002050040d40c420000a1203520031400711840c56890303400384100003003404118001c0026048001c91602e5400005040b44406850b00003846000302e00803420038090800d0391030040414000b15112007040c20080d007258014042c0d440080e240100118040c0300c12000e4810b0900b6a60055040120307110400c07096100c5000800482080c40c441ca5000320700410f00800c0c1d8948016440351030303903261101d078014288040d0440c00e8541001c441e26108940c030086003660a50100d0b0310a4210b0380148400d6a1400c0c011100305483d2184041c01e00200c604d00c0c103003401c0150541c200c2d540301315032340700340404080c80c0c0e03444500d66001042 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 611769397 1250 611768147 611768149
    0x150105091303021204090f05011415070f020301140604150f0b0a0309050307081e28050702120618031c0c02030409060f0f0509040b0406110c061f0f0f0302 68
    0x4200e2031241e12a0045a40c801c072501003444154100d58400b86c034041e12004440c4c5601428060140140511045903003806442e20004048200301540b0122401c0049910320510450000c10740c001038024000300940b5400007031440030680105c40381d81c000ca04011420021000f44400c080c2100c41085180840380e051841054040d400a401002010380350410400072410600c001c141c01032095079050781c1e0305e8229012400c90354901803012401e120500070302d0300142515041c0b65107074035040e4140080218140058442e8010543c019402421707189130203c01040001c0c03d10300803070305460003010030320700c1401281c0e9038401d5035100c000e502141c615220812400381c001d20741c81c6500c2e00607a41401d0319a640348040325000d07444078036000180002048065030b038110300005008180c1c1e214880b032038251030b40d05441c0d00c090001021955a0f1074074042c4640a0000e07103070301c0c0342d2a80075110345042400c0300c1d0480c0b0345806580352951309400070025070140c941c0c101c682200c81982c0c4064200d85590 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 611770647 1250 611769397 611769421
    0xc010305070221040f050a060507080d060b0c0f2e090309030b07050301090c030e30040305010b12010e1b04140a020310080d09032a08030c15010509 65
    0xd4440415407203403640f90241c820068440c0ca4080c1c2004044079103882c50101c0c1e00c842d0117080d902c1316020300035442060007510b0380001140c400f241c01c80300641d610300c0001117402c0280110303031000304c500d600842c00b0b2503801c102107203440d161358808d400c45900582d040043c400c030031480394600b08000c840ca00006407903041c1e0380000c0368272402030034042d0f0581c1e0359403140e846240080360001c0c0010b8000006021412040c41303160a05401403a08108803202240759658407450307a040d145410804000c880380540c9100703144020009154013598a40e5501c0c605540684100e402d424495814a044001040e03070501c0703080109012140200741d00f540d40c4244284200485003802e40203070311043c0451300381c00fa4860f0b40d4041d2401c0c0c20b0059907803034090350801c41c103107094100c505a07420156183c003001d80e20a4500090701e80264045170101c00200c00404410f40c080306e03c06510302640d03400110f030340011000c3c4c00c280142c9002d4980c0c0c0794840091083c009001d000d02680b00c11f100011038602050a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 611771897 1250 611770647 611770651
    0x902160609050a05030a021606020c1e0f06160303050604051501110102220305060a05100611010603050601030f0c1202060406080a0212190f02040f03030c02150f070c050306090c010305 81
    0x2c10643c0c0c1420342c592507035030456101034040e00145e800a6083c0d400030842850309001440f2510180c4a03500c24440004c1042134104552469010701541b0380c070240c0c1c0d81c1c10010745805401001150303148081c51011040c13000d101815004130380740900041560425006962181840c9034491180700141401901d100944e503118450947d403d008815106c0307000080030300760340d2025000c4100d403886c624001e0319002008120b034003010300f00fa092052040e680b45840060398040e0400c040c55081500e01c650051171503600161003072260000000510061300100c0300c15a002c0c00d0411981511801c0790080d1490b1504001d4008c0d90030841041024031901c00706400c10b00c002405490401a2008840401c00588111342900103504845103480614403480846050070071040d42003614006080000702c0b403c0c071014003480115200841190780b45d4100140340c282c00c0001686034441f458001c00e16802036001100c42c0c048009020515140c006070040c400c011803c0100f104800d00300044002d0a80 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 611773147 1250 611771897 611771903
    0x3e0613030807051c0f05010915090b180109060503071a0306100e0d0302100b04140411010917030a020c0906030c041d0f15010504050c19020c060c010b0a0902160609 72
    0x81402a581d0300030300442d2140c0040313080c0c1da01041c6072042401c0b240c02c03104180d0010601928003041c2c1030000c1200300000c0221007031a40d00049000c0c5c41008551620f00c001555110b00850000100b407001181c0d1180094850546c1142c0701c0644a00429503450880302c2c090004803c00d0000412074900700750511456462071400700440049180030421500b42c0382011405a04456204d40c00c1c10303058403c00b007925004079401d00070780300b0f400321143e0072000c098005001c0317546a07140440c140c0d0140c01c048008000c0c152000c01d014659800e01d54494002d13020020060048120300c0100d0701d001015640034100003000751801d14019009c0200600c08a40d1007050b16000c2e18540d0701050301403010401d0160039401500c04c9290707207000a031000c3c4058201038031441c504018000c031503d052083e140d480b21501190b0840d00c0942105074582400045d0071540000002041c182066042d000f13801500c0042c0c0308400c4503522041e001d001d900030a00d8031145600d0340c000c2c100c046078040d0000400140 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 611774397 1250 611773147 611773157
    0x102030a0c1b1a07030314010f050d081603020601030b0a11040b1e0d0606032307140909041406100503060703020f070c090b0312070b04060b013e0613030807 69
    0x543d40c2990b0903445100c600d512000200030498105060301070042200580d0403d12040310f44d0304100c25149240000c0c018140110010b00d41d200400400d174088a94540142542c00d0a0000b180340013592201d0134041242c0f1000b4000100e003000386540a6542c0c0b0100e162940c17810141001108c0caa660801c076088202c02556049c601c08184801d002420b0844c0c5200000c2030082c104038014041d12201c12202a8035080f00705200d81520082d10400c0e080303c01d5280245403000b500303403a81e41e903010314640d65a1064110381808100007400c0303810303400341007648103841d1a95101220a8640c00f0244103460305900130b40000348450344a580102440000c84865604005107034440014043e81504034400e80750b40d1300e05120481c9401c0008405900031017040324a031034010740d19043d070064081c0c402403640e41c45030301400c0281e00400c008100a44c200010321401c0e5030300c0c41c1071181000d0400d04c040d146010003042010b456408200c50340300f82e0200e0500c02c41100180d42c100c800760320040000003046 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 611775647 1250 611774397 611774399
    0x506061309050a0e0c09061020030a08070305090a1212050f06030c062b020904090f150c021509030f0d060905150d1b08010c0306090b0102030a0c1b 65
    0x810249051014107941c0100098070b18022a0020484840201c400085c1c0c1c07000ca030f00744042d81c0306100541d004a0545d150101884001004d481614103411001c0f0820070f4080c1c030701401e540c004007820b070b01003035035446919984941400344c003218402e03102c6c802550071410a00780810010042c1c411040034070b01d4140225090080480704444041d00d2000128883c5002d204a9103005c014041c407054040350b48034038000c0d4855100d209401f40004100c007400e490f00780c019660110b54143c80d880711000c0c2050007004030900d0000c074000d00c4070000702c480b030f00072001e0320003c0c805e00c1c0706264402c211a002421400494031103444140c5008120b030055120421503004050705850191134070001d4041d0100d0f0306400c4c41e5008094500081c10400c00d00409445501c0503510303401c60455840d000030b0b40040b08001c0d500320f108455101c1e040103420b50b08044107504000c4e4181e00079012603040700001c20060400000481e01e80c4101c010348800501004410400704004142c0d000c5c2d03030154540780c20703c81 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 611776897 1250 611775647 611775667
    0x2031204080c09180114060901060f0f080402010504050a0618090501050a050f03010204091103012909011b020306130209090303091c0c050601121a0709090f0b060304050a150b1003050606 82
    0x1542039162030040900c0d86c4400d0060324144a08503902500080c2801c46c130720042e0010041580d01e190414504121700b8401081c1964002e0301102e000d010003408036075065031a00c030701518100009480742250004000c0c0001c81815a1003400c0c1030300c8005110160007031030003003003250351441d0801c182c1c1e065608000c0000d036074031244174215213542c02411042e2290300d40008140080c150201035481400d541d00203442c240660320446500c5403007400d00b4400c0846109681c0c0441c042050000d4051043e9010301c101c1444551442d095640f00302d4003425140c2d00c0740e0385640c46e8041582e402d86240e02c424107140801d02409200e54001101c0c1c40c044840e160b0326202e20745003110a9000a41e0211071600d00e00a00c4070381c201030204105480c034100042e0401c80001040740c3c405104001d695681c1d41d2000300300c020706800c00c2031120402402c4607244d0038542440c41c3c80d581b00c00030460312443d007018840b01c0e0038031600030100d002100030103130143c80052103402e034080c0100500310f6038000c02c00c200304489 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 611778147 1250 611776897 611776901
    0x111060f0117030304050a080307120c0504090606170601030504020d150902091f06051e040b0d06120c05061308010e0a030f020a08030c0f1603020a02031204080c091801 74
    0xc00c040101100c403840d40741401004a400c0700101c502442d410800810002c1400002c85084840e0f2009241e80e9070790300d8400031946079100b02ca88042c01030904040010040c0e10901500a0703880d580700400c8504d58a00060b43e80d004151030b20081080030400081c03241d03021780c2c002d070390044c00540881082c40b026941c003055000aa952400400d50b01d030301520950034001c18031541b024044502d0080c00307000c206500103c580500c00c000406c480001e10180402480c002c0c240e241c14094002c0342c44030303103401e007928003500000c00b0382980b01d140c06000207030808002c080d504032070703046030030403a01c1824607082c00071907071181c0009882c00e01e40610000d074407034091080500d0556010050141c4a0326840c000f0070b0700d8000200c4804642c0701004080100752204100e03508a0031a014040d912200c2c481c159000d4001c0d56460901d000200010741c040c16000304094903414801c4080e942040d040e0350140c40103006038000c015090b80840008241c900b480140705401a18042c40450481c50b0f2a0282c1d003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 611779397 1250 611778147 611778151
    0xb040807030806151902071e090e011806020a0e181803090f040b0d0b0412030e120a05031306050a0c14030606070308041e030e010813080d0209011106 66
    0x908910009000050551004201d5004041111207145410340c104240120f400340120301346400f0341c02076010f072040b402046002c0003403a158a1180001c081c0e030203c42c050081520400740003a0820050b180f6080c1c06100b44441d9801140107859600c0c100d454030700094011700c08550500910003031000780345d0345017414545c4944414003c003602d0f01e0310303851544600c0040d203d00c4ac015402071180029694410921500003981918005541060640003c0e650b090719403021784038090400521050142502c01c8240c580d8480e07c080c004401c10301a090380d01c10235140030002110040c840020b0b610b116000541e00100542c000c0c050401c100d445440c01c590055550399101a902c486a05200f44c10403000075556040c0324006055103400408954240b00c1e40c0c5000313040140000014080008903031341e00d11422a0300c030b0a5001824585000307000507400c00413030340c0812440000121130501c1d00518050082c0d10101560038820440000b1029402c180a4941440045654a081c2030b174100030301d078 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 611780647 1250 611779397 611779403
    0x30c0e0a02041d0a0e0c1e040212040317011703040302041109090a0e0c010801120605040f06020705010c030501120314032d06010305060901082805101a030114220b04 73
    0x20941c20b084c100c1c5021980501031205680d00801d01c079a1055544c4020360303115018029190310401c01d038500081c024402d60f1408030b0301c403402000784814184e001c01c0056038050440e075011a180d0300c8000c4d442001c102e04000241541c41000240300504241d0009541551078841c407a003031040200004400700c104a03500740e03440756510404100a8002c02240c1a07000342801c24020550400300925020915580042d08158580d4040b500300189100e983d190103800141c11074a034103003482c100c3e01a00c80c610320070001904040020401d004a210b00c1c9184690640b00c1c0b00d15104402c122010a4200514514921099408048414000d42182104584140c1c1d10924071302c2d00c40009803c88030090807090040ea03080005102d8002c00003040c0441c1d10040000d030015212051841c0b0b1070341482000203200d80680030b00168150184c2e000782120018443d0045114810310f1705040c00c9594a12044c1d4590141c80d0200701c485140c000111907610917050600c404400d40c2d203803001c0c61003050750f0403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 611781897 1250 611780647 611780699
    0x20607050d02100f0c0e310515040c02030a110c060408160b130909081312020103050633040504020703080901060b19030203060f03060a0e0c0a030c0e0a0204 69
    0x10200c011100c3c0700342c0c1d0f0000c544500400c0107009660004040040c45080c003401480744070320700e600c0d51010340c9603444003071542514185000c5048024501410089d55030307070102c60740681c40c00c1c2185030900079445d0842d419802103050101c1000100c1d03e41c15003243d100b00601550040c0b10298840000610160441400070140d408a40c0340301d248076034107a4800300074424103105c02d00000d030f00d510142d802c030b0342c0f5440040b4480905080c003019a201e803c0d4a0b100d071b00842503002861108100f406607225000344c07802c1000e03603650410b2000082d13031101e4002001e582200181c90340207005180d0070052484141c000e0400b41c03550003103402c9038488181a03001c2040d040821030300f078000740141c00c00b070140d2850131420b0001da01140d002a1094a20541c20301d5004800a012529040e03180c3c4100f83c030080486c1d2250400d009510018400e034401074401d40218401700385c0030f040018800342143c0d400b0300c1c0441141c2c0703001500440e9000103095258856000c11001a00c10030030318995841c25160602 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 611783147 1250 611781897 611781913
    0x4050c090a171f1401060c0209161b050307060f021207110627011b0f0810050904170703021f09050d03020901030603080301030c050108091612020607050d02 69
    0x100400200e180e03011030107001d440d442c50034010001148000c0050084142c030301e00010000c80d0740003c0c003210034056115041c58000000c50b26400015003205d070b8000d03903103c1200e446483c0359126026a8a101a02141003460024028400c04512007042c1d1b001d002030300d0500703120382d5418055440410101d00c100e500450b10800c0c1c050030704e41a6812030654200f035102c0300e00d80456140c540384020a09408009a200c00d6140482003520142d111400b810003080014495000340b41c4002d0003010400000c0d200100700000e030350160b000d413400385035042401001d0519007001c10a105400070300488036171500c07985009001404001511619100381c024000d0343d03254541041180c05000f5001e00124100020b403000b0a9011552501340c00f081d01d00540d50b00088401680941210341c8001c2c0412000000003041c800420110429520242d0701c0c915142c5600950760380e51684072136401048010214200440f001c00300d405100944060191400c3c41c490b43c58543c2089001171060000da00070b851 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 611784397 1250 611783147 611783149
    0x180307030c080606060307021f14071106180307110102121801121107120905060711041107050706080a0b151c1b050706090605090307060c03180b060a0504050c09 71
    0x401140c3c41380099541c54150700d4680381c0290f41d19014000445011500355180b4072140c416004052202450300075041581403080c401020070500c2e000201c00ca0060324041426510b01803001040000140b00075810001e0580f50030360758405100b80c1c281584103401905028044034006414541d400d541070003d40c480500015201006010800c540d2514105088102100c00d81c196010315411160074414040c0003141a540c070340c1070b50060b030b50142c03000c101d50040200945401c0f0040000365014041250002001c0c0c1c440d00544000800d280c0010b90213020041c07144122950114020b000480d08840c0c6801040c084840c2c045c1103c441c2c0c40004c0c200c08006d5850034100c0f170f048418003041100f000ca83c10b440702a60615501d2030104540040e441e82030141c5504040002d540201c810402c40c14170034a4245e07282d00c080300481d5500d01b00030415100320300a10031903010104070904440c00340501e80e900400040300802031a4400200480402e50381c40d54071070644030710101e403031003540d4004801c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 611785647 1250 611784397 611784403
    0x1061e0f080102030106050f030601091e03060e0d0507031d040207063306030207030e040203101a340c03060b01110307080a0509030f0d020a0b0a020a090b180307030c08 74
    0x2400507101a030041004202e4030b54000c00b2210b0040d01030820a81b00d0b21850012280d641c10790b0b01c40703101016070b00d608a5558031111000011684034030400c210414a5424240c1c039010205104004140d0900917000800d0145860346001103043e4145042e8940709000075007243c01060701940c1c85c5d65924201505804050014a10001c2c3d44e0412030090a10b03100d00507820b030441c0100c0c4201600403810800b01405000702100e08400100155282c1c0b4084c0444603013901309105803a409580507903000c0c003440e201c500b11900492070200308040680340b030b101030000840c0341803650001e01000d4480e00200300c103d00c0f004040c610401c40499030001900004280c19502e85019103540c108004400015403020201c2d55104114240291285550703c0001e0401c61611303200d03a600e0098103034040007141d01003441d54019101d42801201c9440d00b141c44030407406104005d03c040385c0f458506200c00510340d009030074161b4000041501e0401e00c00c01181c00d202d90340e80212a1b262192505000502e428 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 611786897 1250 611785647 611785649
    0x190f0b090606030c040b060702120d030b18070804030e06030f10051c020f0103090203060a020301051806010804030c05070b1315020309090a15170606010306060305062101061e0f 78
    0x30000800e09070900800107a16050500d58580c4a540c1d0b820400e0131b144c0310001600c3e040d0b60000c06040880d1883d68402c3d0715a01201242000a4a8075051610340c0c503108101c070f94000103964101d1035a0307130751940942c0c030300901800030350034450b2072081d05005540b644011031064526140c5008642403c503441c0d40c0b00c0c0b0640c0c00c07182c0300e110340c074414440c0211008000d007072541e012110044111349500043c0d00808042401a41501940c0100f2580801580045040b16401c1d81c244038455441007448000000940d4624000b03000c040100c0d001c00c4c410380d110048a4060000d86885903554180300b45503600071900b03614031800c0d202007081841d0000f9026603001e10715001031031600514100260b0b490740700400c0741c12060740c2d80c8044451900c500503d20050101004c04013490501800c1312540c44008480042c0024141140420300c03510178041c550240d440641401350403100028a0056640c8404030340402e0741d80c4040015040c0189110f400c80d41d0700c0003001036085800c2201601141840d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 611788147 1250 611786897 611786911
    0xc03020a080709080d032f0307120902100c170a02010b09060d0c1503090803010e0f06040b01081306090f08070c06080709060522171501030f080a02190f0b 68
    0x4650100b1500c40c0104c5e01804154141c82c0c002148520b40086245041d425400150000d00307045d218010754610744000c5020f03003503e48809000d48428143c0300c043d02c034034850003500503040e0105400d00714010100c15400c1031003080c03c0c0c002d90744000c41c1c1d010582c024105590040c0c0d10f0351041421400e069003202c0e0030503000e95280d00000107980354114001010701c21000c00600000601c00c14a11a502000805a0040801d9507a50792800004140c501c01e075040c0925030780304808034075507241501c1802c00c1002c040c2c5500c002540d456116100086003143e06485c002d0303c5010010009100c0b5080c1d43e2414400d5119507140e01396403c0c0a0290082034120300140480c02040c0041d45410000c1c04040300d030b040ca80107940f81c3d0301c900086400e541c0c12030980411402d040000c10f110079680d1300c400c28041000120307007000030011100400400c00303200190000840360a41404640010000c101c0d10070140120b5a0000d84110514080040c02c1810340d501e02c81c0709000c07401c00003120b50382900130704 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 611789397 1250 611788147 611788157
    0x100e0606010e0f06070201141204030f0f11070b0d0b06030901060603241a07080d09060c0302130504050c0c0a0b150a1d09010e07091e0204030f08070203010f0c03020a0807 75
    0xc18001c14510700c00c2880c040d050200f100380c004a1200504211089d43c00280d446040c24103051a02420280e07203230003101e001ca0304024a1444c0c0503c6401e46032908400c45005140c01494481c0c03210b40c0750f01c0440e402015549400343e90702035490f0300d0000c5002c1d01a40d0000500b440c5085002401c503080300004850f80003550400b00b07400580b00c040710054070314441c1842e40014640742080c3c898443c1020007403504001040c2c8035442c2c81e465000c400d0842c042c01b424006040300b04822800c0780f042480002703a2204907141844a400c1c00c2c1c0c403171070340b00307604900c420b24040e48081c41d107107494400c038000c8403001814070400c80340c0e40120300984100e1038103072a038040590420291080d043c04443c044810000048005428405c013500f01119403803c00054a1030b040e2100c1900300075040318103a003030300f00e0059401030400e0902c0b03201301c03001c903a0468610f280022165499030410741c4410000d036810340d200c001c058005059486202010081c82e100180d6589c80751a003c0c1c01c0040007001281442 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 611790647 1250 611789397 611789419
    0x190b010806103218042310090f050f0313052215090e03040801061505070f030201091a060f030705010806010e180106050a12050103020a120302100e0606010e 69
    0x21002c1c1610807000001004481090920440c004002103180b0301d0301d40c4081d1050440c12215145a25240a00e0050f25200b00303244d02801196019071b036074004070344690b100680d0303a0040da50365840384500d01d02c55441c09820310240d407202890308850350010107160700005880d480494500c88400c3c000c1000341d62049515007503843e2019103a0105500c2040181c8506503451010050b4158801401c50300c90108141081450070030b40c0c076009030041c000e156103420404180768840705800d40e541070072541c445d46095800d03520720748841c46404d011015036403a43d00030030001c1c0a41c480b800400f51581c508403071345d01d0010104020000c000c4400c80c02074005d0744040c801c41c0d0380134034031582c019800c0c20100e4001000c0301c01702d0340300d2419583c100c124464000012078481e5100008041700b0500707950344298179203074030003000807200c00303120017984010384a80c2040400851001101400d00034016901307440c01c00c4107a501680c00d0400c022855800c042c0810601e03681180c111a003540081d54400c0c500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 611791897 1250 611790647 611790659
    0x105011116090507180303020c1c1716060f0209010e010c110118050d05250608011a0d020a1709070f03021e10020705100f080414190b01080610 63
    0x1c50080d0140403a030b1078542000582d45400303000050302c180208107249031a9035072814000d480e200e01c18411441107012281340803800019175004809190007141c500c0d80200c07450000f81207603020200c100300e4001c81050740d10203c0c07540e12491001c10800c07a009a40c030503811000400221106040700d06009090801401050791b218103000303c04420700341030850040180b800d01e18220f55600c0f19512080580204c01008401310f8000c4452544020415a1200803940d1014016040c001ca50006450a004004803540250f82e950003d000ea240145070003403202000b000e0364020002030011808041c1c80d802490440000282c0c0814940d01400059040500d0403e83c0c00b1180b01c040d2150710500c08051035000c2c00714000c400200f004280780e282102d80200030351100c0c03640c49554400c046620312000202d0050b02c410b0044241c5a503604019601e03a564206601c61043c80584548501d8446100d0304d09081002e100c514012080904d003036141440140c5032030030041244c058042c61312000c000c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 611793147 1250 611791897 611791933
    0x121b0f06190c0e0f04021b010f0609060e04120c1e020109081c0e2b060501082d07080601090204030c090603080f03090c06040f091407022a0901080601050111 69
    0x207101240c2803c0c0320300a040005d0003a000f4001d000042004070304582410006c15800280340b101c4404050000f180c4e516075000072944035225882200d2480301c00600001d011503040c400340c011908082c5120095912140c03030050782c0d4600060355660045040055682000c00c1c0c82c001d00c04080280004d00394a404000c4d103409070a2148180940b201003811540c2c1d881d4215034648046983e8180c12180861603d1070b03003a07c0c0181a2030030b0f8039040020445410114a00300d0a000c107d081030286000780818544500040041d41e800740124500419002828002c0a00030b140d418405a11141141041c003000f0700c0c181d10510907540751140810014254034180c90754106582c7d141c68072035944811503400e0549855407282d115600260115410400400c0e0b074050f981812810054a01403201d00e200604054071850003503480b0031100100b040a841d40705c0c847c40e404a03041b961135244036011a0540000b81c010310000d420107070060103a940d0103086400048045801040103640c00420809 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 611794397 1250 611793147 611793167
    0x809130c0f050c010603150b10080709050904060905071e050409020306041b0906060216080105040b0606030709050306100305010b0312031605071e0b010b0408121b0f06190c 76
    0x307102c00032440701002042944424001e680004880d00140300150140000700302c0d10b40e2540c0b00d001078403e40148a4030404c1740ea0310601c0c003519040c1509050108011030700308010070807180c054031040d020303001540501c00e040c018418201110000b00190521081c10404c0c0e8000341d014514085040d070169a002400980194000308010f5910b00c0ca070b010314443e4106600030900c024100000041d46580c0050120800c1c54112840c03403220340c03100d002d103098440643d0042e0054282c030380411994a00140115003010310f40c00c00311005941c95000c2801c080040301c0307070303084c48898500401c203002c001c0c000d03a04000c170308074003420385000001c0802080d400040d0140110000c1e13101c6041049004404840c40390b9008540103c07104884c0010081519900d441221190f60039000010460003041c140e40984800001170228600d0041640b00c2355041003c0c04200c2d03103284006158801e40a01400d0f1580070110098584c0b4a45880d01c1242541045044114a80f40000c1c141071540c3c0014240 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 611795647 1250 611794397 611794427
    0xd0c170d060302090c130e090c10080103020108010906050915010e1314090a0305030c09010207050901091a010912020111071d010e070c421d120f0d090f0809130c 71
    0x50054854408889c43c12401d1a02e0903007007070003480301048581d003080300742d41202d2003660380c0305c8a40c1e2115510381c05c2d0380d244e200d2203420040ca440840d03804407040c0441c8009840c180350031000c40b00000e00085002080400c14482c03990341d0000a540007aa120001e0fa05c442c556008006503602c9682c000d000d444018203229428101050030a02c685c42444100d004080c01000b40036556100c030b4080000f010411103908002c4080c0d441d89001e54042e48480702240c03903601030b000030400e00b6001560034042144071000c10f40181c00005c01c01e003000f0401c1c580941901c00e09907865606108500182d050007030301180c00d0100004010300040c4401c0700e00340c181035603034601803034034041044270415031021130200740483d2661311958208240c00750300400904412a950748281d1450b40a015114031501d030707110151000410280c0c00810004c1e0040441e600d00b0700f400924071813a9241c9921440ea03000048503c600300203411901803070940c04003461120495010080c122074200042c2c8101c0110f04d0032 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 611796897 1250 611795647 611795669
    0x9050303070518042a0f0519050417030901080f061e0321130f0b040308032e03060b060c0606090627010f0602030703020d0c170d060302090c13 63
    0x1168150f6038612090f1984007510501c0207201c1c0017091100085042c0811280703000c8111082139151080300b01381c03503600b160b0310b4451414000740141c1482030200e10008080c040100070000c0c0e01070030a40e000b2008440a80510f0703e410429000616001e400750504a0b041030400a205696540499003a1200c2100348446000c04480e008241000c440712060b004001e440004549010241c2000f004180560900d0500407074842c2d94034108080d150041c01101402400140001002040103503001592503c0d046212825540300d05900d10840010704000a0940f130100100b0919000d9089499002c03030b2140c0c240380d150440c0c150b5030800103042600c80c1c1c1c001300104145844445801d2800882101240040008040c0342a8210b40a104241c240300816200040851011003694a5954950b0241c00e50503800e101c122144942c2c8403090b5420102c80d01ca1040c26000000200700f82d49682d500403408510f540104161850000d0034400009402c104161100507415240c00680c0c09000070b0b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 611798147 1250 611796897 611796907
    0x30507150e01120f052a0c06040209060409140102190305010303020c0d291e0403021024030311120f0f130f0e040510020a0c030806120615040f090503030705 69
    0xb08000307013100441c5214540e103820240444040840c88800f10760348020070340c4180000e21140e4413054850401c400350240c001001150041ca40003e4041d0030002c0100b010980520b552569610104480303100401c503075002910407111a42515600500d00e1a82400c00c05507165841c0a500c0b4540c1ea03000b184507414040a00701000b48800f00040c0c4050f40440101a0400284640310800d01c10764420900c400c00e50350b41c5000040c007100091040d43e059018005441d4400c441c00041e2020703513a50024041c5001ca00002101a01e0404004502950307401d464180c006074182c0c2800116007101c2d0416204001d04000070480304111134449508000c4e25541d101003020314204c951654104180543e0074080000d0501e1142a02038080c6000380d050314040c07105d00180000303c4c4500c410b22404555801d460300c3c04607016880f941c2e803004021f4032034100c50000d003c0703041c10071408a50342c0c001040c40a84080d22408c25103d0111015081d02c0b04000c0194240c580c981c0c1d03404014401d10420500180b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 611799397 1250 611798147 611798177
    0x40b12040c09270c090c05250c0b180630061011120a1e0912020d0305090a03030807020d05040b1209160e060f1009060e0a031b030507150e01 62
    0x130983c0020040d2100400c074a028480e4010700c2580117820000450500150b100501c891a402240000340d00c810341541700c03464004604a560450907024004600c0000301107103a4591200a103800206601ca61f03c0ea20303803298107800585a4142e200c588940100200001c40d114440b00c490071a842e414082d601c1da0b501504540b800d81a05611000c1420105990f40c1c40d0341c1240b01100d005034418214484044607580884100945101d01c2d103001c002c05c507000001d130400222a004031070103864907a140400c288040342c0415010341c4114005901042041507540d0705121031034a4030018640b40c0d1401d0703d81180c0d800140500141240c2401400e804101083c104122205052101c070b8200340405036200d00d42c807441c3c0011214240035076100d00d17031a900e51900000c0b1159040c0c444d02c0e002c280c0c0303040520484402201c0c0b0403e5401000c02d2030f020000c21a12000310000c3c60140840306070b081d095103015402d00d10180c0c006440c1020810f2440d403c1c1d0b8014140561055080c42e00c0503158240170 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 611800647 1250 611799397 611799413
    0xb0721021b12120718030818060c06070905030c0303091903021002012009180414160314060108070e0a020714060610020c03071a040b12040c0927 64
    0x420610700e42d124050b4480b108002c0302000d4103c0d048000b00c401035944e500c1d0801d46220460355101704000e03010368800c0c40000c02880c050021079850010b0314440d2104180803840c2503011070000c0c0f001d544948204008a588900854064001500980251582200466501c1c003c1014140c8540c11840c81d07151101d2204480c800156001040300d0351400505d50082e0003040080640e036500c02c0b059038214018010141190700d12100a8180b05c0e892900568152030094040c00407220302001e00c5451048600c00c1084181c4802c001c040c00300326502d1031400c0c4244546442c00c0f00403130341044004000c40d8002080703002c02c032086c029821400b9501c0c0d40241000f40b04250000303010340e07000a5045007103800082c032140702c3c00082c1c0311106903070180c1906a0ba10100c1015080c0d041d0300680051254018100c0c225071190b840100c01806d180e00e886200055402115000840d05205010001840707000c424a10003481c880d07408011902a511000140c070300082504298168041c1100080200d26 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 611801897 1250 611800647 611800687
    0xf1706030102070614072d081003060c0905090a050c0304120e030a033203060f010210241d160e0a0b0405040c020105090c1002030408060f040b072102 66
    0x4860108000c1114101c04c250115094800000140e090308411f00c00d459426401e40344010001d86441e210448810120b41403c00100902200d600081f00080020450b0081c00c043e00c4064840e5249a400c103010b008244c1001400140024101410701c4818103085045a8010390060986559244c45950075540d409044c080c2503014810070480c901410380c0611072031120514121200d0400014150f20840491850704c1c40111000410100e54503181c1229191071483c0180166601c40305500003600459440c5508100041c01340185200030322018035091001e0009442c10120413a1048040f0784261001400c2403051002c40300415000c502990802c0c0201e00003c0046030681d480c1e40d1441401d07003003441145d000e681041003c2d100d0500600429100720440700060541100c03030400c12207080c043c95400d6041d40810000031880782c2d0284042e03840303070900da03c55450b9130425180200c00c419005100108000c414030b40e80c200c440c1d2600c0510800e1008400c05a00c8220b0b0590000c00c0180d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 611803147 1250 611801897 611801903
    0x180f02010f14030a021e090a06210509010621030c080703030b04020c0d0e061215011e05090a170a0b090c040f1a0f01020a1b0b040303110d0f170603010207 68
    0xc41040354004640d0010b088580d1541079041d90b010340e1400701b401d5405401251580645095003d000d1a07125081c40100c0c040007008c140b800761050000442221400d03035501c0d510365128402440742840010f220301d808425000081070b1644180c4008100090281000706641000280340c800d06110b500039001d4424001d100f10354558403106040d9480d412081c400c004074498101030090fa113006000e881041c07110101010950b42d030788080904441110140714103210303150802c420b91920014284901c404181c8030503554040c244104801c400565004200c1d07a18049030b4101c41540101d02c003855145c0c4031010040c1c54444903a22824403000040c0f403038010b454845003e0703543c0345942000652250300c1c590809401001001e1180b250401020540941e0007841f041e40003ca2804110392559034070381d0070b080d802e80c54601c0460700f94401e81c8103400203910410a085c00520034080b5040c12819814141112010141f02505840101075113a1124140e80b00040030703514203404a440c1294 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 611804397 1250 611803147 611803187
    0x80a1e021b060703060531091a09010504030f230a030903030f02030f04140a021801060f09050f100207051507050f0706050d0e150712180f02010f 64
    0x160001c0c240c070400161820400c11032003010003040007203010348906010f485004e01429014140800c4a11940702d89582203c0c941c1400c038544c038441810352180ea0740e4140705142c514448205014507050340c0401804240309640340005000c0000c0e0041d00342c8030440400d041030241c0100103040c0d6640300224501c8000401030019030303810060342c1a417181036a41d01c83d4804001e0074820303804c408100d00040301da1016000704240480c01141500c1c0703014110340b21031400c840f62446140d010801d000c441d048118000301d085001400200d4108041c2c40005d5070514101280501e0400083d100d080700700d800e6800b501140b40c1c03000c0038600c248105c001a11000e0004414550701c80250042940041015100350144a42d03c90241c1004920401203441a42d2101d0809084040040041205214401480c8128041c27100c0f4050300400305841003141c6d480e42030900e290001c901050724030815100f6910781c038881843c00001c0048426580c2c10340c0a1a00408036941600c05481c411010050068104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 611805647 1250 611804397 611804407
    0x3090d060213060905090f0606040807080a0312150506090402120907080c01110604080306060702040c030c0201051602150901140a0c0905041413021c06090c1203080a1e02 75
    0x414a41c00524150100080b01240c4590b2039408541c1c034441805074a6105e4010340104864548541c03900b504640c0003080140f070281d41e01072042c41e0035095800010243c211207070796011b243d000b85403405001900344c81406914030720b0480c4030f5081d0050160b94801c2c3c0c00460326a040381c41e90781c103591036040003030554070481c00d00583e41940d81c1614840e604681c031880032403a02c5e03540306180108014138441c0007000c030741e02d1f00da0f180a42504003d102e5a0090350910054002da960744c0511305124540e51000260700c0b080c2c0d0306c003e094880041041742d103180061229041d650f40091403206001e511401d19800340c0b190251140074008038a07020403405407110600c8a0405190300600103e50280c070f0f02010b59540d48140416070f01c521480c9480545c2e2440040d45606440d46100c5207244000d06012845107001030111039201140810b448440d0390350a03040800000030080e40103445508610504010f4507507009004200081c4003034007550704c801d0b100d0f202002c812400304102a862800b5510f40e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 611806897 1250 611805647 611805653
    0x310110c030a0825090905070201180609031409030a020409050c10081e01120f020f03060705070b0c03010e070c0c080a080a0f03090809120703150605010f0822020303090d 75
    0x4058404103450b8250710135481c001c228004c002d20182c605500c0704201d06142c20500c0e0000d1a00170110030070b5540303880ca542c4403409241ca000c1d00ca0303803107072000044584207810010407101c1c40c0000b02008100801c103d003c80d5900180540c2d01d690304540205002c1d141c1c1c50b01070305140042e051a0f80103a83d440e40b803000725030031009d030700d2040d491024038020403c5200e0f80b80302e820b68280714040c15200c0180309a804607e014050340f070400d00142c2862003560f01080840c0c90010b08903002c40006030082800ca0800031034145460f0440300c080788850443d4107103544c000c5280406001c0703101303101d00c804c003200401544500b050010804442640d03407020f20b90078030440f140d01c000381e01c1000584104000102c03034064454900000c0c0c014981c2400c00341000180a621248040540e440e482044000400940981110140c2c20306085002c0748951800c00050408602e0503821420300c82c002c002c000e200804004014250703103011002419070f140d140007190442c442e4602c01608507140310040028 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 611808147 1250 611806897 611806907
    0x270605042d0311010215011410031b05040501030b01080613091a0118050601021902120f0624030d0507020409080f07030c0b07020a1a100b07111306050310110c030a 72
    0x210f000a0302501c40482030320000c82d0784410309004082d03564400c12141c9841c0c0c1010791103405090301c2400d000031004812859800101c0814005000003400007405022550f490b01605410380c0c820308142e06a81051800260184001c1d00340310840f5560305942d03000c0c86940042004165030010450705256103a0600400201c40120490079284c10705c1c0102e03100f5440013031410584501d4206540440c01c40b58200180b0101d0104402c0003481444401c1d0180d580610007503000c0e00862044c542c2e00031104c011000c603605c0100d0180d210b030704000031121905401c8411505841d43c1218001005401890281210700410408415208002c034004013015004503954030703094083c21094640d9a1108000c9a842d140c04200400e110900624159400030f80c203031140d000440c218000700d94a81307400c0e07501042c5c1c2007944150380c5e141001c98818003605051007180c140b659100c000380110b07800c040200b640d80d41500d600d0703840705540e0480325108c1a070034010703650110310100c00c2d02e41d90b184260740202 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 611809397 1250 611808147 611808173
    0x150c170106080619061d0f120c03010e010c0206011a160602030f0f160c11060c160f06090b0c0a170d0e0c010801030f0c15270605042d03 60
    0x80030344d9403010b910300781d441c449840301d04541a5903114900c41d07080a100c0540708101c00b00054000224406401207941c500f48013442c000410801040601981c0d4100f40c25035440c03001c1d400560745041c0c00c1070f480b2640415070a05440809004640801c000d4240a81ca48165802c98002d041c0103049282085a5600298040d5240200c103218036211003400381c040c680295500f9032038003402d0600c5621240900300601016014101040030240703540b000c0f404c544e100c030b01388801540200e550b140219500800b0301d8041c1c9921000040c00078241070703010b801d0480e140220082000040394a00e05240c08120340e41a5980c000b0710101113000030f1002c80e44641010541c00405803c002c00f0540780fa1000622000d2140142c0d50701482d640395484480800b002c4030170540d0030100004000c6071510200c11404490f00351541e0f1003000a24449046141410000103100600c5046c0010071800340d0060079101035555a954803181050110510602100182c40398000c4444c1101e000040c0803c0e50340e0b01e2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 611810647 1250 611809397 611809399
    0x307050d21200c06031801020f03040b040201021e0c0d140a03030204060e06070218040c080114011502030306010207140d020307090b040b061207030506040e010213031202030403150c1701060806 85
    0x10010309604107086440d0b403908501c007904280c0600008001020740c007140c1b640d440c202c500051408241d9030075504150700464059614894900500085590401c8030310112001c000f20400b001c000162429210511101014401c01d03001c0822014420f02d0300c41045240010030882d50292140d1038098083d41281c400d81000c12690800c444060511408882031103900401c0154005403030207140c000f1074030251081d9840c040980003c50401824490f940e05002d03030b041c81170079030b615021012000301e04ca0050b0a086402c20b02c05e0252a9800144c440c0589900d410402d8101c50340d64046500e40b0401c40000e0b516215208002405d810150320019840000b62000e002c921b4412040c014107100701c1d02c0d41d0359510402c00000c1d4007140300f0b070b01482e0440c1c0014008a42400c0c000c060a0036030300444002d0700448002c0b40100100103407040f5a2403200214005103007484e103142c9600d840d80c41844410310500b500d0f450340010322881580e00401c8083d150400e506030f5612840c006040e20800c582e01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 611811897 1250 611810647 611810687
    0x6070815031009060e0613021005070b07081b160c050418030311090607060f050a0c051b0c090c0c0f0a0206190c081c15050307050d21 59
    0x41a45003920403100001424003400404580100c1e02c0b03080000c0401030026540b180ea1941c3c0d01c80481c40c24032910b8041d00448000401d0a01240100105008840c550f5800e00c03408200b5600050401d8003030740e9010010381086c03d840ea032b40ca110102840b0a51801500d00e1400040724903140b1034100c110a00c442c000c0c40032036500da4a542c1440100e4546850180e4100c4900f409030000901c43d81240010000e80001e05003003084410200d000c5800000c4201e030a07941f56000c0c40400c1c1c030035114003948103c9001090100b00c8003050007800c241720380f000415103038403412201000140308020040c0c4a1101414031001d1b45031101c0c00c0d0840b9005441812403500800f40c100200c00385c0000e440d401e039500249840d2400e10111001c801c0791500d4140c860500a400700040d0224288078040c00064108404a130317404051034a40904079220941e400314107181c20b032000e01140d140007071584260f54054600a880da0035605182070041003052100f4400c001c040242c001c020350100d1b030030707140c8800c800e28 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 611813147 1250 611811897 611811901
    0x20d0506090c0306090712050a0b0405090c010e120a1b0302010f09080d030b01020f01110307020c1c0303050c070b090127051f090204060b120f070926010c02060708 72
    0x1001003100c01550b02071074000041c808641e141c9007448405400c220705050032030124029000003020b90b00300f120034150340c6036541c1c0542194109802000d91110840c00500382c01c501401c0040d060325103c1030154040c0c0502260301115003020000302e14130513040070645401011180961400b41e8150000b24001180009503540d2036004080c1d1350181c030440d0015128442d5500400c81c02000da600f0510b046105007000d4034101c1f0740a10440d00002c4c1481c001c03594900d800391020386000480c510190040100d0702d00c00c01c031032000b42d4100400c20707418070703010442c0c0d02c1d03030082c3d0389203805464005010032440000303204403104154400c2038030f9171440e5003000b1064042d0310711683e13802003080f0147c82600003100c2d410700344400e10340c9103940c1c2c800c0c0003000516440d140c000c00c1c201c0303480b90002d00307080d580001d201110040600c0c00070b82c0045042207022a510301400e0041c102c00c0517104805410608103070300c2103c4080480124902c1c81c2042c02004160081c0c0b074002d50314102502c418020483c1400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 611814397 1250 611813147 611813149
    0xd2c032a012717040b220509040c06030c0f090b07030c0b0906040b0606030906060907091a0904051503070b0a0504090207120806030712110d050f060108070807050a05010c0c08030a03020d0506 84
    0x4e0b6012240c0c450141d90402c805509085403001c81c03145a00102d00120001080300e964040b13801e070044d401504004501414150301601711038000c48034005000329100d844001c0d5600034003007015075405071611519440c0e14135054602c0b40f1409402060701030384030704020005070b00103a418491801000c081d4419190401070000300d11098425203910303007203800000e005042030b10740d20760040700c0c40c60414a1180c2c0c5644072100403c1542c020f20a9034000211000070f0314260042c0c1e90400e05041c9540740f04011400080d0392020b040c400d0f80036051001c91072005003405442614010300c80700000f03540e50b082a262210f03618640310100c1c40843d80c0c44000c20194140001c0b0a0140c0e010444850103a001c607494010142c02811a2544d00440c0361240c54002030092011410000030b1500511103541000c03c2c19081c0000b40c1c21800b442e5005030401c05c0641d90321a08001141c0080c200061040000d05201001030341c644c11503001c6200000d8000d00c03540d8075600402c68901110001c00540d142c0340 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 611815647 1250 611814397 611814443
    0x3030c160603060b041710020d0212010f1d07051309060503010c031a011b20030706030e210c010911011202040308030a020f0d2c032a0127 61
    0x402413000500e01400306102401c0c0d82134109010110308021242d03400c0d40d102d5810b042e6840801c0c0f6191a540101c0d541d1100103046200c6809000201880d00b400c50070502c0740004940e40d00b0440410305000f1020924540c015001c540458070500e080e4014240c40b86c0c02940944402d11074035006c2d41ca0030051160140c03007031103501e2111514041c9040c02d003017410011504000c030b0500180d03030351484091820004031103c2e000d0701c60158240050b540c0c40740140c10181042c2141d40860241810020300036900380c0c0100340080e03800c1c00507014900004050001030300d14014040d861099600e0586440148584103103240c0124030700341c0e01c001800f03410340c0d01d080507801640310062041710103001003048145243c02411611521000840c04c00c840440c035001920003100c8124011084000c1c1052104070b02e00d11091080a8100110701c0c0280d0900b00c00c0982c4d645c810b65060700303200079141c1c403502042074000444140f01048044e43d1504001080c2504640b24a800c5814800107d00003c031440c0070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 611816897 1250 611815647 611815649
    0x7022704031215170316050a03090605070c050d0f0506040501050f0703140402040f020f0d14060d1a0603120c0c030c010e0a031e0c080a0b010618032003030c16060306 73
    0x1641030044020320300000c000e00d015884003030404c107000030b0100000100000c0c64500c040d070301500040542c40c3c03032030401601074842c541109003007090400205c1d01041d4002d1220049a10564071701e8140c1da11420811031310314032020014150b008407018001070001c1508a540600c48904040486469a00c015001c85111030030175418802c03c03100040c0580740542c0100b120000c22800940742c08000c198110003a40140003000e4050307a5512207440060100d481c07181d00020658a401d070008454a0b0001800d0008a0107001d880e140000595591810b0090342e03500c0c2451000d890326400240381c41c0f40c4528058400b9402889114001045507201d510085a8840c0150142c54a1030841e00d07040f008010103203c0c00541c0216400744400a400e40d490340005183c1c0d100036100640d501c1c540305100d03860681c0003908011168103002000c8034070070b04840c02c0307940c8048030403171007154003813032110482d01c00e000706615000216000388106004504d1030841c0d00480700042c842c0d078480c0340641c04ca4040d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 611818147 1250 611816897 611816921
    0x111b010b1519090810050903210108060f0f010b0a030f06080c010810151103090d0b040308060f10050c07050a060507140f0709020c0309032b0507050a08070227040312 73
    0x450900c0c0e0115060646c01070f030700200c0c074200782d80c5054040c2c181c1c203c000d90448140314202035140c0041100030001e1246a4000c860385502501c1414030201c581c5000006001da407180040c000380001c4601d00980c0500e208407140002441511ba030341038070544900002d200c183c042002d10001075080c000d402520001e99030240c0da40c040d2121514411241076010b40c0380c00a6502c02081081503903900c0082b07108a240c854041c6038041e00e040d02e00102505c0d00a0079082c003600c103414130b0100a0340c555094540c84003061610580700c0d840c2a6036286045659031140b9040405120007007841507110000788109400b46201003a141d100d400700d6036640c103c20342c0b140b076a50000380e800d201d01000380c0c00401841c0d0300c0000712402d00c81508002030421302a020000c4c80081c044c840c295002c1308642425641307511500b0a0350404100351212070f00e403800e2860042209000280d19002c5580f054404401098102d40550302c403003622480c20105201503505034082402c42c401400009054028600030f190 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 611819397 1250 611818147 611818153
    0x2805010f0e190c02030433031812090306020412050d08071e05040905070207080c060903030d0f060f0605030901150b0a11030f0d0207020a050103111b010b15190908 72
    0x2e6014a480b0080005505400860100700400908001100e9040c041d241d1086c1c1c0c0d201e0500c8044011280030803c1070500424141001441d50320440d4100d520030900e600032034026280c1240c450304403000d0029400080c0000d10201c2e000c60319403108104d880c0368a00c24011039a0801051406071020002192024000307442c1d04040d00c1815101c1e0003241e080381940c103090b0f041c151161007100030740340100e407810010780c0902000c000c1c0381410041c03d8000082510403510b0b148002010940340e104140490426544404d03a160303400405038000c0c0014848403007401c0036280c44000c001c1003507106450780c0b000fa41c00c2c41740808041a01c40c034480222900c81104500d0102c0c0120143d0712440d01c01da04140c540024010000224150002040e03071520803440141c1e6100b0314030400070b42426a130010b40c109454030444503010529a4101c8880030040d845203070309980401c4400340540965248203803c00360002d4070051419406010b40358640c40010341c64610090315100719800e14040c810b01c00d09078 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 611820647 1250 611819397 611819431
    0x1061707050a060c0b13060b04052d10050103091b080a11100801030f1a090a02040509030412201e1e1003020c010e0a03110d110a0206032805010f0e 65
    0x100341d10b410f1b8480c403030040840d0220380f243c00a002c560040307444140c208030325000007800d00c1d56003202240204441900f4451828a0304200c2a00041401001d05140c1d4a104d0203050051030ba43c10520290b2070a8001001915a00c1c0e0680310f00310381c030b801c854511403c103002d0300ca41b070301c01510a00360780c2542d01d01103503070719548441c02507140749502903c0001a11006072080400028440d2250000400800000c0903d1061100300c441c0109441c4070303038200348001e100c4034501c0040400e800341c1080074004404211041c05000010b03194411354405804200c01400c400e01d245a001501012030721854030303000548205000e807000c0000b45901103d420396038451380d800390b809400341c00040400000c41c2c01c80c1d00001c40c940030364a08181c0c08612182e038144000002081030030a01000c40c5480c1110880d0300142556483c02c1c510001c0c420b10340400054124036a00c124030300148420a41101c11444180c68000280000c0c05074400710355880c0c0340422007010f0904200d0041c0501d110141c1d0720 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 611821897 1250 611820647 611820661
    0x6020c04090f060e1c0512011511010f05010501030c02031c1a09011e1d0420130603140c01090b030c090312030708130201050a030b0301061707050a060c0b 68
    0x8040c6200202c0382100c039440924080780e0184500e81c60110020300074214019000e42d80c200d03000c2c00203c3e100800100300455803180429910007030454450701030940100038169025500010301c944900c1103503181c500c000c1d15114860f0007103412260b003a00c080142d07110214080f81c4030b214031841d9080440070409100800c01403030f40900c4080121551a5031341e4040d20b40019030b070710020783c01513043c0c140f0b12650149001c0080031120050502c24055440b00702060707000b102d180741c010130140010680e003855407000350024026880111004010041459100d0040070050541c4e0005a4040e03a00304040c2c15030060001d041c480c503210584030791846614011041c0d1a0b54401006030b03e040300700384094041a02d040003140201000005600c0e20b03490501b4000780b103998010a44122488540440c20260b42c100c0c0c112100c1d40c00c98a0081022202500031a014080550003500c070b05504400c12020f081d404200d07102600e004032070a0b0181c9a070f55108031113510101c01c4c06000003283d08041520 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 611823147 1250 611821897 611821901
    0x6010804020f0a080102030109110c1f092909010b06040506070204140112060c0c02060315210102042d0501050706090807080405102a050f010e0c011806020c04 70
    0x101901c000c00d0600c0c03040082002c0303010a0280c0d0302c5a0203a0390088014040e9200c903008003004858031b8500c9904085441e0324039940c0303a03504003007c440c1c4010617240901e0079506400083c1c1e42600940e8400034130404480f01d080b4820526480d4a1011030748020440720003040c010a0240c88004184504050a040402c03060364003006040740e01a60350f012a400650150074014004c2580740d028036480382e05410300c00c0c291449079052008028120310400c1c01a0340b03a1040d07a411440310041c02c005058410045190620406910040c44100c460741c100b01c40815001401a1859090300809400740307100c014400c0e09080484803030f00d0710307180018005948950040c180c428000c1c41c010400d2500c03611100000e510002c0b056416110001e0180884e04015019180805c05480c1403d00380d1b5880d4002101d101e054106610244a52550141070107020004140c4c1403182e440204248141001107540e125024840705d404103858000015503a4103c6a0300c0007241c19980240c400b004c045410400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 611824397 1250 611823147 611823151
    0x150f02061017030c06010e0103020a0e011503050c130801020a09050d0c270216020405280c0c02091306051012080d0f021b1612080f190306150c0803060108 68
    0x102d144400d01012100d5201000750500038464280b1103010f07035040d8010b00419a030307030340c01c91100356001c1001041102d2030580c0400003845140780015060301d58174189a040c0c869203c02c40030768500300102250146c03066000381b00340d1032107866903511107640d034041c4a01d8109290014041001580702042201c940c3c03451019240c0c4201007980c1c603190942ca011040760060030421801000031102c0408606280c4140740c2c0040c0c0103024900520680c0040100e001c0e080d0014000054a50400d030035428082d04d001c03415990300070507100251031700b50100030950074846000d441050a10000c14410a02010a0019240b03105902c81c0624956210f40400384e2003950381c1010355585403c2d000803680544081c3c070144501c0c0700ca2500e00010030540c3d601c0c0180d0100c10300120302080c0341c10001b000c1ca11030100c10080d40014a2034031404c1401d8065054058641c1000318581d110982c800380d2039050340000291441d004982c071602c0d0010394101d03101a84514010184202080400e00941c09104038903 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 611825647 1250 611824397 611824439
    0xf0e040c0210020304060204120b0703060b03060303031605040510031e050106080a090c120308041101031107060902150310090c0f0c03081305031803010b10080f0411030601150f020610 81
    0x241c5403680c1c410f0400c8a000c82703a00c01341c521075018010302240990502039640106104144203086040000000b526444060a60000c104180c00c950903120300907400e4400038480288014034000502130090064080340034204d0048805088028012419100d09810303516903a84421150388e0320140040103001c6490b060b149941d050500042140801c91101038481c86691070302203a050034a080200c0c00c002624103414542401c417031507603400c500703010f80c4d850540010000c13a0030740003130020540f01a0b4010044103040e000208004100d000800d5480c202c5860040c104060b00b00581c0c100c4108444580c0d200005482c00c03008408a407088281c4c0b0382020b040300c9041600c1440c1c1c3e540e6803559100c0384400404541b01c040314501441c00f84210a0701940c19154085655114000180074210080c07508030446400000304060001c4c1090700d80005d403000e4121081942c45003080ea4024550ba254880080c01400510142510214005000740da03001d002c02802e50a00f6550b8400c42a0082d641c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 611826897 1250 611825647 611825651
    0x3050322080a1109060a0302030c01030911330708040504050402030f160609140315070903060207080711220f0908040e2205100504140d0f0e040c021002030406 70
    0x109401c24107010000c24948200502c00c0800504002c1c8810500000c2019200d01c3c4404801c00240c0c802045240c841d4000f46400610041d1a15141100702d6603282c0f00d0f900000000700601c01842060941e20300d92043c0c110340e1900c3c0004c1c0042035101e21880c0c100800304803060000308090f00b0a43c008940140c4000e050302c00f0701d02d07030080003880c180300c842000b03c0c9080c8003001017140c65040080c10780903100454582c0e81006201001c40d545180a09119030210011030007c0c0c1190b1243d0100c501459210364203558410440c1001c645a800c0b101c0c0541c0d84c404580c9600005140c0300c401c401c600c40c0715100180c0300c46503d03002240148260180d810702c003501c80c001103002516240c01040548543d85001c80c4d2403c00c4402c80b013184400800c2c402c034100c5250080008a1000941030b2400121103c004c00c0a581e645048542da40c0d07292054400361203610311510708a0741000740c4910039481036039081e603458040c0d01000165810303c00d0a5015822030750388480070512a80003560b02c503003d4880 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 611828147 1250 611826897 611826899
    0x92802041e0c0e011704020f090c030f010b030112060e010b0a17060901090209010e04150218012d0509061e03010806070309030e090a1409030705010f020403050322 72
    0x81000d41c0c0104110700d000c8400d400c9800001c07246880b50303800ca035400d85000e40018000e0000a46540320b29011101c00f440c1c800c00040071503842c0032183c2c19403080a412a0034500300b01c5103c900311341043d5032983c0c1d996400d4001052068150003035a0480d40d40c02e122008071036190725210000c1641001000080d521020054036948410b0076500092800d0340b81c1c4129070304000049410060302a250105c2641000c3c05000941c0e40d100d00a415141e005c0c42c00c0156403a80d1520b80c1003075114880c0c0181d41400494410700b4a00319110074105041c003030320340c070003101840e6003004000240307040401c014805c0c141310329411510850242000000c042e0046180c0100c00102c0a001c0c1c00f0ce04410740302d40e0700000140f241e040306100040e000540740c01d041c8441c0c82c0319a406010407200e01d000034028041c07800040d400941540160180c4032030341c982c090b82420400354054a0354408581694590b007041018243c0d079400e071084400300ca4026020b9810224000040e024805c110866100c000d110300710 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 611829397 1250 611828147 611828149
    0x726120307260717060d080712051c09030e09040210030c0c170310091a10030b040e071502030c030d0b210d0801081603141e0601031a092802 62
    0x240c264050405070715a8984440d56013441d561400d4002e04a500400c400b01000c0c0001d54418140c44110b035000b1017a07003403007561000031075181c001c2c010b8028000c0c02c490000c0502108903409500803d0080e521001502034031001d2000e03100060350003d4001c01c00482000c1e18034407031781c07110007a08020b1420300d00400c400d03200d900c0a0a0b0303120007d500c50b8000403c0c040140c070f0009844000300707101ca00030b000d030f040007016002e01e81e8500481c060045082212080b0031a1095204906100d40180200403461b01d551140e40c0c4d6803554011242030480740101080c1a40c0004250313502c000d6500000d41c541001208100064100000441e42106401204040050503141171461000d07180e0024000c3d003800301401841c030340060b845011150452031181e61440b400315418010f9a401c03c10081a0740750380315100c0c1c64540c0d5007010f0b11942c07006000002590101007a29070489005101c0c204000d030300480ca4054420b4281c80302c01d800d60001c1b00e04030046a11005c0c5081c001d18842d144c01070a41aa0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 611830647 1250 611829397 611829467
    0x5100513080c0d08100311040b0a17010e070519120201091205010f0501090207031b020a08011a10020d080f09011506080901060f0515070c03050726120307 68
    0x44903512443d080160365150640d0300c001e1041c0d1101c0c2c031405241a03145582c0720725628a103d68017041c00355403a00c8042c51580c5450100c1d100500340ca4580b50090b24510003114000c003440b910450190160b011300144501d8990104461202d00700c12010750b0610300070017101d4038009550201d050005038040050071700014001e001c0041d01034400400e480a40b03240000032a14140c01041c8150303c1800820082580300c1a03103821420030703111183d80040580002403101c1c049900080d01c40d03003020400c020380500042581182d4405a460b000340801880062761a410492201c0001503002c6000070341325000342100f50380007000d4000014180118800b5148411074a130030a80c0842c1c0008140301e0300310024400c01c00188810a440034103035042c80002048030601c00008040070b400400d5803c10711100351170110043d035104040b90f40d46607072155421084940515640d0044040080300003e40346c0104000c3c0c1a00c50015400e880e5640e5100280d40d81c100500d030508400c480e40003a0b80c80a0360b41 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 611831897 1250 611830647 611830657
    0x806010f1d041407080f0106140307051315051c050103020d0f1104060f030308090615040f0f0c030c12061208390d031109010e06190909180510051308 66
    0x2640ea43c0891b03d0002e07515244190180c3c09101004104002d41e031a40f8454810b03250032503c1d038581280d86c0d03442c000010b1000b04c81504604c5050840110707001a2a801c6401021015074119075095003581481c142001c9074000d20000c2d4201850407604800940d241010300c80c203521078610000f101d0032040c0410300b114079542100c5903030040c0510600a0642000317041c1d0384015500010409485c203100b00080da1a9540c01c1e1901403078a807017140164492903003001404900700c0f502040710003034001005003d0500c01400340c001c41c4404080004c081214003d01096802860004a802e100384da10504103a000c00f4052085031800010305115001038041080081d90481480704000b05007e00316081c15041e14044003410300d0040403003032403009002512403d1100b400d00810903080038002c0303442c501c161042e440158500080000c030441d00b0441490a880754000d04000b81e44501d41c40f210f002d188940090026403210380300441d550826003210754460104903e0610300c040940d102c1455400c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 611833147 1250 611831897 611831911
    0x1212050a06090e011e1d0a12090807060503070c02010912060501140d1106130e13030207050609010503040b190c030b09130b01061409090702010c0806010f1d0414 71
    0x250309042011100500503e4100c41001c0000c200c5132103c40d010107117491129004004c0e0036110300051043d014001c04031503101a051042e04d8039080285065003100402590710000300340441008554110001616001e86903035485940c5182c880450965021102c2c40e8200c0c10894681c070f01080c000d51220708400024890400802d1550608682409120484102c1e5004069200f042004540b01840d0110130354001c5e1002651502c00c048001d103842c0072600480008003001d0207100a03c0e040008124106000b64203840110b5119801c0007118411180e000307001841c244049804503410310308598016021701014001d168000005030142e6003501c40031000320b5584c0031807071141d0409524003a48482440e14402d1810300e580c0d91200f81c945c1c1070041c8410000303014400e06404d081e4030704a60321000c00510310251860200d1000f40a0b140c44140707203000039100c1020518650250540400b000d2041d100c00103c100c11440c3c080a00400d40c41c0980e225480318240084a2070210419010b440 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 611834397 1250 611833147 611833151
    0xb0c1009061b0e0a0306021c0507170c0a0e120a050d0e13090507120f170918010e010501050a02012c120405010c11030a0c090507030e0102090d1212050a 67
    0x10014100500e8040200145040c040f0000481c25a650b1311a084019a03a028100507152061040d003150f02d0041c200c01041740d94030303000030710488640002d0144d0312080c1e24440300913955075814401e8000d000d0009110302080840003803e502d0720303140210b1170012080307070100d6290b110760b61a024500340c0c1103e0210045a40c902091980d4141200c0c0342845000440d41805010241d548480e0b880d41244904600d051a003c1c250080110703c1c240c180700b03150400c40501c2d03018401a04411161b001104c16885111b044504640f100300000906040300c1000380e041e051680b0703120055070361b54481c4401c0011556181c00b1450300c00c11405030341109805c4403084c8400c040c04105154030301080c01c0040500c0b104184410815030b0b92281900310303c10780c407400100e00d000014011a06d440e684581c010040324034400c01240d0018a41d1040f885860580c0c0d041c0a6070a640030303e24200d00c50120b800c1d811105409980c0042103100160300c58110f1280b820414661400c0d401a0031124292040c1404907 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 611835647 1250 611834397 611834411
    0x14090d060c02010f02040f03230708011d0105060d02060a090902040e060109060206010b09011d18060901150e040e120c0a0308160804023003030414060903040b0c100906 74
    0x16509120300c080c4c21100c05000c61610781003029810041c0c46612000300b1100313100b031141c10300207021180300801c80944811030300000c2d26006603502820b00c60802ca00d0768000307260b090418030701c14010039020b0a0068440c013424400e5030203002140c0c4c04810315506110101400261000307441c4003c10080c00035602060f212b04080000500407035a42d41301404652011005101c4868403104542d019002401d11603031450180d100045007824580c41e40d61312890545000d003c8125100705a0b1041c90111040d200c540e882da5a1072074240f0449440100103290209191001d05090f4496150341c4000d80031103100c0c3e4041880e004143e440140c9208050b08100c10800406400101141d04844090722140911080e0b40c1c00524185000300041d01c5803144040008004100c651151400104c21000d4241010145460ba540c2ea00c00d51b8111282c07001c04014400044002c0b0b0310703500620142001d1071a0610b0907030f50b4031280d000301400c00041c2c06658031040e01a40d19115005442c3e2080401017455 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 611836897 1250 611835647 611835671
    0x80604110403030c0c06020a0804120314070b0a1d0c04050c0c010606051308010c120207020a08060109020913050f130c05090a060914060f0d0302010920150c0303040314090d06 77
    0xf02c844c1d1b01c0380c42075502c030300c0c0300c00c000030500020740302602e5400170b2500200a0364201203e85d100c44141c03090003144001150803d2001000030b29124514a000c144909031181040907102301d09a41507403d04e42010400d8130b81403820b48c00c210303081801d4080b5641000039100d03c10b0308403100ca5002c070b80440c10028448400004412170000103004080c001c016506110402a204403200d078013800d481a400920501150780d0340c40400d0141000701c0031a209581c5501620000790f1142d40814807850964030754240c00016805031603c10041800707120300c0d0344c440320380f2904c038681c40c0442110a07426100c00890b050b2a080c2d880d901c240700c0c4000218150780fa0280680894510841d8088401409010010142c0340c801c80707141c03d8807040d0b400c0090400136080480c01880c0041c0c00400742da0720020307041034030752003144040b0104004803001070001d042e001c03042c2110b00c10a0300d00c000540003807000801003806400c0090091313020b01e908901d4a07041000087d0340c0c04800070b0807103039a661810a4611 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 611838147 1250 611836897 611836913
    0xe12011b0528020a06050c0309010e010b1309020d0f05011d0f0c09090304080118050715080a0203071b0605250801031106090604060e090a050c0901080604110403030c 73
    0x2400d5032608145182200b038455107401c070b00c00003603074082044403100c0840040f4420090140e44d90b070090420440d0b403d003e801d601483e40250303903103001036003000e00001c2c2040040c4100369410100410300c4158a18008588028082c0f400082e6444444521110f001c0341d82040581c01c1c5038070500002a4420040207104203441c4c44031500401d030791161000011b0001b000030327020003440c02201c12550715603500c94070f503241d0b01c159048107055508103c2001c0501d0604208090300c0e81c4100301b52481181c40301d80806421902030950f0000404640106880c40c40c0d07507000b0354116002c3e21340b41c00c80f40740540c20020036415000048415580d540208858001c4101001255401420001281c20001180141407180602014001c00141c99111005544440c00ca03152800090310068560799100300c040c11610800701c1d40da01076030314240001ca4001e030f10f2083c988a0742480d415141021600e10046801c000020500fa40240c0d50b0f000c10000203040700042c1000314071a0783d400800c2005440d04842c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 611839397 1250 611838147 611838191
    0xe0312070e0a240c020402130611120c120a0507240c020613111219050f011503110117160314040506040201080705130e06031618020a0e1201 62
    0x400d91046440410800c00110281040103c21300e0018600134a9000140c020302ca46020001c10001c3c200c00001c803990000501d104c410010b0081d03d000c1c00e66001000d1041c402d000740d0310780c503401a00b0702d400544900c001820a86c0d401e45061030400c810380c3e50b1903041c0b0080f40b8140d1201e01e031454204015181e5401030b6600e1000a10142c0450f080101c80c050039441503110052021400a501c2501d5032074400d80f100d060311118040b81c039074030709240b03810a56254001d0103580030301a03a241004455414081c4040c400707662400880ca15143d901c60f40c20074010b0011880c104001c07400c81c0141e00f11030395a9240150301c401e201048101e900d01c000317411039101503441805090820700300004200042207080e030180d028240b0880b0b983d10544110781e180b040140c1c098008c1c160b00e42c00f09034210440b94040c440d0b007040d02200d000c2d030410a50344404c48170520034200207008055001041041540140c0b10f0404241000d10005011500042c50a02c01071a41400c80e90745034500c500041000380241 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 611840647 1250 611839397 611839409
    0x318010c030b010e2b0b041b1404020307031416110a08041707080118062a03240e0a051311060a0507140706090602010e100e0312070e0a 60
    0x18140c07215002030000c84819008511500d17484484240e081030174260208110b4210442c00c089401500d0001421030041d40d06a40c0c941d0720401d001c4c019124414030900345d8205403404991031503948c1c10407004e5400103150408068843e030000c000f06084d4000345001e031100c032446519008201100070300a44218100f4000c541c4450016400b1400403002c45050761038a0038001c0d03005420b040300f5442e0120350b0340904119841c164419402c44074114211076550310030101448200d850480c03c40540e882158801044102d03c200c50300800e00030390103000d4032400d03e034038842c0011100701900200600c582c02641003810010800040140c0752241039400820105001a01c000c1c94580a156142c80e02a036405048006a4031000e41d001d00140c52034142d1000116407660254100542c0f104513600c500390104030440e0000c21603074010b000d0307a0f6410030024010102c840c0100241005880c0c10880c4441f5808200810401940da119007944a030415843d6418645040c40c244850480680d00030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 611841897 1250 611840647 611840651
    0xb1306090c0515091c1b0e01140108041a09190b04050d090815041e0501020c0106050303090105180a1203050307020d0f0813060f050109090b160e011101060801020318010c03 76
    0xc030303005a607124041c2c003400450020b001030740c3e034040c9002407152110300c0301b409072a4203140d80003800e95004a017050680740b2821752100003407440300c010340d170090080d140103003280019506403490910805550740c0c00b07602d8201b00e81d04500d1100e0400408249030200b996029034000c100070900c001000703003010182e403a26042c6602441c00034419140e40b04800740201e1004003202041c2030186800184d680b001c2482001c5007101102c1c030b881c0c1d00039070004000b55038a50910200191034900441035496401c010b84038240340c41d056403046404241c400c1010766002c5d10340d8502280828a21040e1841e0b0ba2080c0c5130159a03040c00000030f07107410040c1d144041004000b03020040183ea01002d00ca80058a545106500c4a590300d400405015400441042c1d145032800008d1011001c1d0410071030340c0c0c01999000c1050302c03400403040042020500b002d0100d00039030512405035101d50824240c0b008540000200103460314415400da03882a02c0384820451036914644d04084d003889102c003002c400b4182 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 611843147 1250 611841897 611841907
    0x91e030e09070e090a06080d050d050a1e0e0316030f080c041208090f031005010f0e0402030601050d082203032709020c010f020c060103110a030507030b1306090c0515 73
    0x20f08120001800034000c2c4481808210600816002000a4032815040d1b07a000d06010348003d02503000b008885e1046400c0c4008251080c500b4800c0c4030078003401101d40f00c1801001070801002c2c2c0b07034403885204284810004840c44a80b020104440d1034070903074814141740700041c0f006150b0800030700b00008241041004111329054030b20040a8107a0200180e0f441e40c0300c80c0d000405880c4003429081c0c0500640e400310071900001d60099041e07406918000301da0070384490031030314200e10031940290194000c400612041c81c203a904284e55620500380c0c94580600076004220004516002d550850501c4909104240c0c0100725456214920212070302c05440840300f00651101e28802c800304140d0000f05140062000c0d00403850361220404107641c0c1e582c48902c1151b448209210544814070f0103842d080f02c07881e101115808882c0c01600401c2101c1c21910381070a2000c0c0600280e100204001401c80003175400d000d98218240500c240040c003038a094103000d06041c4502c1c5444c205541001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 611844397 1250 611843147 611843161
    0x2b06060b18010813020405071106070f09120201020c0d020d02060412030201061a1206060f07050c040f020708250c0b030702060702010b030a08071403030903040f0e070507080d091e030e09 82
    0x1e0304d00f01c0107804a501180a403a0360343c06039071166440c03140309454003481040005154100c03111981c894030503618480c1c4c1c203075500d008031801c425248009005030400d004072a501d1a0601c49003450350300040c02900024156800a600d03644a540810f40c000b02d1001458107154085c8a070900400c80c0b440140003061981808262904c500c541100c1900e41c40d001090080e00c6110903074044880d0488803565920480c14860703960f90b40b200461384128241205821040c01c18025102003030350000c00305084c0250304440e94a4121202000105120844445008102031032200c0c401054101c03003c036070342d00b031100000341481c00c01403042003035a0500c4845840303510b00281d44040150415004c0c4e443c2c0f0b04a18040e100c106040c111080c0901c408420f0240c0300c07001000410845038008403401507540e84064840c200c4008507040da010400501041000c108618014524002c1940000850209542c0c1e00f0f01081c4c5100c2040c11060f621080c42c02c00c15070404051264218102c44c0a99140741c282 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 611845647 1250 611844397 611844421
    0x280803070c0b0c100c050c070b0405060a21060b0904050609090706110c09040506061809030d05040f02090a02090a1208030a180f0f0209152b06060b180108 68
    0x100c161044403600107600255441c081c013840308a07070050781041c00400001c1c840140f09030404e49030403040307001303141000455401e03075002c540485c1c0300500b619051684131902500e420b209000340414140312030143c054510028428800901118448162556a03010034171085a1008107441c1c000c62214cc1401140d4200050200c01c80c0c2482c64400300802003800103030300b00100c49102640118002c8240720401c100802c00512801d001da0b041c0c0b40c00003810700c01d0a0301c1d05050796a001c06810420071122100c4407504103079401402031065104018003a07002c00ea0f40082114819025507010481507202c3ca00f01c0c4d001740080c0b800546203e04058140c44240451002404125500b80d41c2d0034204220303c502980e2458094115070402c92089a034107051560300544042244100f200500143d002031b41c10b520803007800005041c03442c482c150408412029050740d1685a40f0744c0b0748102c07136400940e041c050140038040780c01180b80c0360015254440e03a040c0e00c07040494144910703a0104107d01c50030b4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 611846897 1250 611845647 611845649
    0x105060d02040b04020f030a050a20070f0309031a090d090b0301140a05090106050a021203090a0308072016210609021f050315040c02100515280803070c 67
    0x45070b00054980e001c0380020020b114500c2861000031021040080c1411250311003803042c8044101800b441c40300f140028240d003401c0802d00d00080301030148102245c2d90100d2810114400e05000301615180d490341c500c0d010f04200c1b40503e8103039800c01c0004000c818000c0d5104d522190030b19800b2581412800c580d00c0c0414000c19100c240c12074112041540d4103a071050086c00050608641540c40e16001003080d444030303081074050710801480007100c5020b801202e221343c44000103030540107400d03a000c0312010809000d480400460000071720407581507900990b08014401300406000018102c0956101050741c4080780d88480041000810704144454070b00c0c0660100000802d0034891001030b0840741c104402c0808182ca1507a2001503d130020b00650040880800c04d14220300c290003000141c42138145100c2c0140c0156000c10124400c40d00020380104c440c0d05034442d5031080102042e00038514000c19500e802c5200607200515042100810107000001c0286180040d030b911525035011103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 611848147 1250 611846897 611846899
    0x601020a140c1513050d020f04180b09070f09060b040b0d06080706080a0e0a082a061312030b091b09041515021504080c0a0c030b0a0e0105060d02 64
    0x80220441e29010500150741900310061070080d0900d0100101c407600c0d000810b000508080d9148046940e02e040703088852015402003c90000302c5141090102800010081c603ca84d03403014040310000e1082c5603124030418080d401460118940082100e000c001d60784020143c51400d41c0510250b800e0908582c00d0310002c05026549a045000700f030000c05190b44006c1003401044004a00544e2144105015040c0e000b401d01200200b8241c041d02c800e02030700c00816030303c030411455071010700c2041c84041800328071007045c04142316407030b079a82000d4084504491300c1138100e03455000c00032010114045010103180801c019044540402e20100001c0c0940200225202000000071000e0040b101111800b41080c0a201e01d00550040c110006014400407000e1554010b818503100180000d40380c5005015000c0980721901c0d0400d840c1d20800001082e8001c0040d1900450031440402e002140300c2c82c0d80b40c0c5545070200c40b040866840c0e03034810798242d0401d024050706a484800aa6846030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 611849397 1250 611848147 611848163
    0x705011e08100b070b01140609010f0f0302131706090604120e120f010f11130b03101d040203010b010905130509030d06030807060b0118140a0e0f040c0503060601020a 73
    0x8510b0a61045040d80d948020146040002e5407000c0000d8058080c3c104d40b403d404c5d000c1412401c1c020841c036030099610450024507100d00910400f4450922807220b101d007820010b00c2c1040900c001c5000001d9504004080c990400c2580511941000180e071f022910038007404850410707950311002d2000001120701003103000304000119540b0040480290030000048400c1d4100203000a8003070286070a00360700c2c40c1d03c3c04080217102d5503101e0855607000103110701c0b103100d1801c00c09101001c0d00302400e80507444401c42c40100f901d80300c1d0300d0108000a01115a02424034041c0304150070342d28904401410009181010070150311001c032031032200600107002081a543d0084001c6c91400b074081e01e050f256080240000604c440c4400034201c803401400c0902441d003040c0019103100680100100d0407402030700c010401d9002542054140180c010310b096030365a603070010140240300c1039130305003003161010f014801006155075190b0000d0100350060096031900b100081d4461035258006881d9103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 611850647 1250 611849397 611849401
    0x1b06030c031515030405150105060f040b280203041a1201030609060b1c0b24100207080105072705010225120303060e13020a093801020705011e08 64
    0x40d9440440e80c00840f141c031481601c0b490b00e400e2941c0d541c604445150102c29543c400407070941000b20403100140550700710030303240c40e107401030002c100d6009030000e18100b01c070700005002082c070260000390b01030119070042d91a54203240502d241c241100c0b2143c10301c86810402502e1425040104904480d04140d00003101d98003800c041c0060310849000c00d2348000381c0071500071a000015101c1c50454002c4442034002e648501490004064000d000750203002d03440d4070200280303010300e40282d420580d072055503507c03951100414252034040e10700c20b0100743c107032007501c840741611300071941040c1086184006040c54203001039110382001503c40281a8450005c0624901100c01d0200402107110b400c442d0b68094200180108458000c000d10811904042095490b005861844a6400400c2c0c800e429180180c80c20081401a264000281d00d007031018401c0180698281120b21203100e48140580355000024202180c2c0c2d0002e0303060003044800a640540403c03005401c200c0b19003002d010035 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 611851897 1250 611850647 611850649
    0x60106050c0c130f0f1a1206010b0a090f091b0806090a020904060e01080c01030516021203150904050c01140a0c02090402060405090709050a151e0516051b06030c0315 73
    0x74000e405140d8902600349412a80714084a1740841009040f4024081e40c006c803080410411b00342955051006a000d00d0052041080710001440410001e08140d50304c6983d4141e003101a080f554851581655030b034a01420030411024064110840c1c1c1c54201c00600e0154001103910101420440046038041b8022019864a07030054010b410942c460b0300e001c0da0350f0300001da40c600400290500080c1007a010626040802c00d182c2c0480705a60003500c218490076203200c0c1346400c018900c036000b0b01c10511000240e1a220ba896008a0081d005030030701e000900005032030900181040c1c4050803041000030082076001035940c061660440f031852040e1075034000200700b0300a03504240d0780075007660300f40141c41d50000741000c1110001c2c3c0b0040003459407820046220a5103125400110b002c40807541500b400d0700300c009481007803d0030f02a040c41c0704829484160b40d0000e208854a5100f00ba001501d50100503607601548400c4481c940345140c800500348090002902034605014800240402 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 611853147 1250 611851897 611851901
    0x70c08091305100b071208150d050307050d0e1311130f031104110d0b0109030c1508060915010c0510151409040c140f09070f02060106050c0c13 63
    0x8521000304841079981000d2146002040155820203030210001c000098490221040d9081c141c1c2245211103640121141a141010000e20f2969504420050001c0700e40d102d85c150141c9500410040d5110b54881c64041d00d0304451103408010701042c00809090390b5100d4400912154008001103006a110b80070000741e801000034031818030389020b10104030070454400b0b1004990240c4240c00250b0700c030009100886260b048958403d000c10864000701403190341121000c01d2062410f11002503482c2c807034681160954208141d80c030f100580202d002c03030340880480c1c0c1051044032482c4003810071b203c04401c6103c01c1e0300780a040c060030840708800d01c241801984090f4010070342c1404680361a4003c0b0115960b00d000b143c03000c41c0d404d003540c01c950500b42c6056100703e44c000d130803141040c108051000c40864442d28030750b0000800074114020b40700ca0902e140562603d850b0040440d4001602070309120058000c0e001300081407203107206070391000139a80c0b920401900c4240c00d00112000401c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 611854397 1250 611853147 611853157
    0x6032307062006092406030604231b041a0619141309060909031d0a091407080112050d1b050313030b072613050a0b010602060a020a0503070c08 63
    0x1909001c0c807420820341c88000304003408240c0520317042c4100100129001600d000094a0081d0107500001c005000170361601c090b030107110702c1032451100180840702060314000041ea031251141400b1205408203080500138401c0d41d980e40d51058a0420802d4086845801060415801f0380045080140c0190058500d211014521006559201201a10303e1a5020640301d01024589004c4001408842074421140d509034075580b8130305e40c1c000a00591100c00c4c20122019030050b040440043c2c401e61300c5c030401d0a06001301824072441c6c60046000f030318034007050b841003c1c82d0f020207880c82d00180d401b20740c01090031154108900c0403010b01140002e10340e04000c004100d40320005207e810718041e01c0d24038080303e111f04404801c90791414811243c0c60a00c55580076415030f8032084241d940c0d10920304680c0514040c1d04140c081859403551450140c3c4000142c44a10841005001d450f0b414091b840e4030000c401415868003150940050051000400b400c04000120880204211004045030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 611855647 1250 611854397 611854457
    0x70803130b0903032a070318091a030607140a03200a030504050706030606090303050c0a0f0b240a050915030303151903020a0e0c09060d0603230706 65
    0x1010358603042d000b40d42d03290b00c01d03540c0510f0108401103c2d000d107180d8216084218459038521030416040355010340d0142c5111030403500f110200c10001c1003400c11841500009116240d4050110820300107160070900050401410041040b942910b0480146e0031280300700000d15001698810350011508039546907038060600c4071000810846a0354547c00c058065401030003030740d00701d030303581d0300290100ea80707520844022942d1000b04102090096001d0001072520500f500e00320b104d556241090000180020ac40da850540107104980701400059040c180e4410b0641c904c4528090020707182c0180c40c41528402e24250300041c44040b16904444003190b00070f805c03031351030341442a0840e170801da8600669000e2020345008428400104850b00300b1203030094a43d403505800c0165054045000400084100c80c04214541c1203465410003010740e00141e202c00540079042d460000e15504560b0743c0d40145e140d98003089400c079800030810008880b03203410300503081718040030341d0310000300044030718 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 611856897 1250 611855647 611855663
    0xb18040c0b070b180f0c01050a03060909080a02060a090c0504050403030e2d06011211010221070309090212060f04150906060801050604060e01142205190501020307080313 75
    0x20100f00400071034a9400b40302403c042c62150110001d0780c65450642010040c000e900682c3c1072203030307540160028921481245070204100b910f550880f0705541280400b2a01424006980e10480d54103114941e00060709581c10310010040b5128400d0540031030055a2003903690354041410036000340d02104d0801c010405445c0e400d0320044180040c010410740390000020518030080704640d0204845050b43c2003034482c00713050145038883c0c400d100f0142171240c0c15440350420b40c00c44480101c08100c1b40b0610151003e950b81c2540c0740007821a1034992040280e0750043c01500f40c20326200c40300c40c0d8040300030384000c05407001100004002d00403060300681090303494800403c030710140f5003014041d11815118104036036030351000d1200c68495849081c000600380d01d4104400d40c07203070768001c07003103a03180c3c43c1076080c000e1080800b40c60800c10032140d4200302070310404012504000c2203d001b424800000e5809561400d030010b500c80c8030300c01000340822400000614070b002d1401189044070341008031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 611858147 1250 611856897 611856907
    0x60f050907050109030510020d0e12041e03031e0509120705040b0910140a091b0207090e07060e13050405030c0c0a050f0d23070303030e010b18040c0b 66
    0x4414010101965800c496004105000c50340b54020304a140480e544000141000416104550029000b501c440741710f680d1610702d45514000200000503540910f0300b001652189405590004d4800081849140e860003400400100c0e4104501c1e00d40741003420025045441e240d40200c84920039a03065983c003007100ca01800119034001b407140b040e1102900c08010901c04d02080002e024000c4036245070a52401030280311001200c9041c0001e8440900649035050b11085014180e40c0c545120721100c1d034400b0010011264100000001000410070401c00e96400d1400503450b00018011507050000420785422952900140c82d400c2ea0f408400c10040703800c00c2e260450b166030040c1c0c4001e21610500980300841e260507103000045500007816500882028801d02c2a521032219050f25110701c0d104094010304482c0c0342c5040044185009800410300b10324025003102d040c0c82e02d90f880c90b031500d11030015503265507400d035060000e400f54909140d519454107031403426903a00024104200855 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 611859397 1250 611858147 611858171
    0xe09010b040303080609060d0f050106180f15060207060509120109050616030e100b01120c0809190c06080402121c030e0615060d0605091515030f0c09040906 69
    0x1e071055920070307614000325440d144200b0200c914192109944102e0300001c441c0042c2e800702c00260b0b401d208034008126a076442603600c1c610320840076121800c0340c071000c0c02c114000c0d06120300c2c140200b04c050403650241c2042d5009642e12881c0c05094240b04c0001148121a6200120f501010210000a20844c0300514100351030301410745030042c2c21420b000c68500c00d54002e00071000b803140302d0002006200c942010711b40280c01946802414002c004030949400c84590145841000c0740e511628400e05000b15054500120044aa2980c0c42c1c40c07009034001944480c100000c40c0c25600c0d060810380c40360b0000814140c2240600136041c41010120001800c0d07881c01c5000810f05500d04104d424211825642c603180304071b40d824200a00c0500c0200140f6060018000b030102c24000002c2c00c0da140c202168032a002a100c0c4503010401c41c907510141e02e00740404502d40407c1810403401c1d400c02108607090ba40c0007401282c00f180011840074900c2d01c4541c00003002a4000005010901d0021 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 611860647 1250 611859397 611859419
    0x30506120709020c121e130e1e0106020309010905041104240f031a0d1502070c0e13021e03010908030c03060a2c04080c032a0a0803070f0e0901 63
    0x41254140b0340265000c0c4904800317900140c4510480c01106030f060b0700360840d80c0c40c51a901c521811301456000140c04a00c014802c9185440b4000c4c0366220840d6502c08a14a641100142d100d0f00455004201d1400e207642d0010843c0210745003924041102c54000360041c05034042d54001c888040b07400b1400c5103035002140310ba00340652040c1c81d41c1d041605000411016210007480c00a880a60005501320504090700301980d1103010b400e03400e001007042c6518900b6640700007000d903414186d030301c03050100710120308007141c001c55601d005c048051300560126003120078501c0c0801000e0f2071040c010080d5142900643d0310f590344804950303500d10309104031500c5600305030781b96400b0703444003d0701045a40b010308100354001d00d46000c502c680048501800c60f079843c001e01c215000c0d0070511071050074010400142c1f4050102c40000701c1c0345000740203d2114281d52011005003503101200020115103001c084030b0300242030389070540d035004035110f0507200a940002b1558112034081b00015802c0141 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 611861897 1250 611860647 611860657
    0x10905091305012306061e03060a0317090103110909070f0c050d1106060d080d020912011104030b0f0f0103020d061401151103340f03180e1603050612070902 69
    0x4d0001000588030340007842144d0288082d0055030704401e841c00820b4411351030255902080050844e80055125500c405211203080145020700001040d551010f46c0c242c0500003015840440203030404155a00081084101400312001d000d11045039480561080d480a14041d81183c105e411604c80d5480040c140c0c0b0007070b120840c4038000e02d03012a0313a17440c0800e005e088040d08414168105003c10b1788150003988240c28044d8401e45003401c0030030008003802140b203410540c1010f6078540786581010b0f002840001c107042c0000d4000810421450594244941542c0d0141d035500104d0806107000306c014814880000200024400002034075941c008144a84078400e5462040420750100002d560780504002100382d102c4401e4000d9030114100256094400e1001c8459240c5c8032a80321030125050a0780b0940000c0d680340c034503d10890341001c042d4003c1c40d038140240e680c2d00e084214400000742e202041010580c484020a40d540c5d00c01107240d5564800d02c0c140c5000e2599086034000179440 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 611863147 1250 611861897 611861951
    0x408160803060a090c021507020f07180b03030a02070b1309021209010b01020a350f030411100518060f0f0306240f07060f050403020c01081501090509130501 69
    0x103c65000c29020400d000d80d03e4111000d400508008106078540001714100800b0402184201560250101d80c1009004002c00b520080345c404443d8003a0014155402259600c1c0203a00030860080744070307030024806084800802ca0702d5120380c0c0402500020b580694404000c484c0007041490b665100281e000d80150b444070002c104490f1503900690315041e94fd9800b80103c0c4401180c0001400030380d1400c901307075110320140f600c0d801400741c8140580d0059144e50502c080084204010003100c620f03094181c00302198104411169100300415621030314510840011702c0e581d41418a403106403e07100341404040c000c1d034403240e20050f042c0310b40d081201c0031442b5000c4803401000c4d04510340010403445c40c0d080ba0b518944481c030b242c0d8503e180c1c480c6404440b500c0e96080070071000d140b1840340901480c071a5002d0141400108001091040007030030462404c0d4503c01d83c0c03401e50783c00039000c0c82102c5094505103441d0fa036650008200c0010711201408650a0060440b020320182c40030300b80b5a03070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 611864397 1250 611863147 611863159
    0xf070b04090c23180108010f0308030402060f03011212140a0c02030a140c011d01020a020d03020c03011802040e01050903160305040509010b091516060203042121180209040816080306 80
    0xc0d04c001155058001e01c20204414071408041c0041005d000003168860f0000e0041440d0001240743c2035100e5000340e01510001c24124408810030000b071401c3c2cad120f8170542c170700f04da181c9014541c44170305880f400003a8030502004803296021520b0a1140c10109a0408240055440c01151042c4c076007031041400b80c0000c0402504030000d040d04ca010905800e01070b8020440100d25a09000502514600640561090404030304040d0740134000c00715920700140621054480c50b2061200361031404000c50781d81d0741407500f00141d294000003561782076454003601c40d481074001c0c00d09441d01d00c6107400c21074001603048000f14800b200381f401440d081030f0030313120701488005c211340c0120a4000e0103103002080e84000301c0040400c01c80c5d009550890b00030b400d00000600302181d01c0310991440961880801c46014000c00d929079080d540d004d40b00c0c1da84405020a1030201c0f826407081603103110080c4202c034401e01140a001c0860103848070b00302d80d04c0a24420302260704188103160000c031400c902c240 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 611865647 1250 611864397 611864437
    0xa0c14040c0512060118081903080a053105010509030a170103050706050d060e040b040b090a02031c090512250608060f1314090f070b04090c23 63
    0x16210b50100c550a25404820003000c0d150751004503500072402c40c1b1004114030014011483c40410f200303100c3d45060f45443c0c3c0503685024603015008c1f5600a2140050614050421140004544500c06680f20310303000d20100c080c1c10900000d2036483d1503000f0307000358608010090790301000001810501104c4d01d44000180c0040001811090700340001441600a03100c01c22005000c1c0300540907011340c3d04000324100340c850310b080b00a45d500305c8040c0c0c1c0c80c810200610043c0102d03140c890707403c65032000151041c08555000709540303d04681646c0407100d511445605c14922402c80080a004014547d80e01c00b610a11025560f46003034880180940384203050556001c15080004101c1e4040d40716580351344e0f690010440c1c809003200c52140c106050b68039402982c0c070203105101d14151400714044250820050991804910045146e1643e11501040c48000114402c0c1c80884110349000302d07002c0a6020200e801c00c60741d204019280c001030280449034903281000e8100e582c190340e2100010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 611866897 1250 611865647 611865671
    0x2130f020d0902090c04180b040204030f0f061b0c080c1e06070201050702060609040204201c1d0a0b09120d020304030f0e010906050d1107050a0506010b09091501020a0c1404 76
    0x207100307d00c14007000c0001e00301c1c01d070990480c80d0041800382900500042c1041c0d41c82d1685901a01c4c503603000c85032540882ca0210402440d841075031106c92940448400080031800d000d4a6408210009011100041100440710204000215210902c5018440b640c4040d2400315910442607070b215016509000020f42203602c00200c00b403269030010b0021006880c3c6800340b2000304485c4120f0000100914240030ba0103203c82c00070b0000c402d400c50f040fa81110079000c3c5100310b581c80111a042c1501030090b08014441c00240140404d40102010000341c4034403014510345840b01190650b1041c01040f003600c0200e25a0166201d0f074002c0d19240f04501e0013035404c540c8440c00d41000750118102000c2480b1051081003c0c040b021101c1200051945e682828441d55800c1440101c0c2c0c151700c14403000382005000c5c00118010f00d15541d1040c03c1201100000303100720401042c0d078554400150700c04484da0700c2000143d80c00741d0031001040c0820f880d2052945041d050408140c0210300b48145000b030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 611868147 1250 611866897 611866921
    0x6030b091b010c0203031911010f02090604051c0b0405100c020f0703031d0a0f050f0603040816060209040c090303020c0d0f1b0f120303062102130f020d090209 70
    0x60001c0000c05031030740301c070703040040d00c914094103800c0c0c2e0184818040c3c81001e203a1400c942c0c403101c40c0c0740c8078001c483c10801071040c25280484040a041c0340180031040b115103910040d5803d03180c003295442a081e141030020f613406a80c0d604042d03c005010420f00c42840400300e50407442042781c40c0180151031408004be0383d91108241211125030100404002292140301d42c00106185012018001c9022500050700340441ea004200e2510441c01c0c1045070307162014000240d40016260b11b0308610b801e0b1616a030303074040c2c0c00b02805a083c080e0821000c011469040b900f0300a8020020400c4e00000c0380000c01000c0c03240030031400b5220b00c0728078031035a243c06030420b03080380d42c00000c00200700c0c125544c907201c0c55004001c10441c0c101030200031a003510b2819498000d0004290044030456440c00c00800b40d500e6a8050032440700014a00e0440c441a800d02510080c2c040e20030100e0761b003000300310311f0007000180030903d9003e102203448048592103403c001c820074000c0300c1200c101d8a0301a03007004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 611869397 1250 611868147 611868163
    0xa0f0e011a0a0309080408011406120607050403030528110105010801360c0b070606060507020a06050c0705090c1308010b0906101107090f0c0c0b01050f0d0501060906030b09 76
    0x20409810b01400d99410321076003040001a118689450829580c4c100345800d48403101c44085e10790b40300d00304204407424480903c0c90340c440307e10000e0407130b81003069000e4580d10690201604105001039080210f0021024050007000060302c81107940382c4011000b01203220f0741c07554030b83c15400c041c000500007405029007007240242040c0c480b40c0c1c0d0211050180c3c0d1300325560b100129141107852a401142c002b2a041c0024083e84032210b80c0d5800e286814030490b2000c2d000181072241c00d208038400340e1950408542070780e1240c203002ea9201c0a0090701407a00002c1c7d030040d0ba100605104002d00300c00c010015100c1606d00f40d440701801510703105c4d198281d4403401c6071941c11a0503603002030040d191412642d1032031051400c002510350501043e542c2031081542009480d142c8600340c140c009041ca1140c80390300c083e40c0c500000103100310341d00c50000f0700042c45218032803c007034108046203039035a040d150070307a49d804030081021503035950b4005e018080f280700689492500341c0000300d000d10081079640c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 611870503 1106 611869397 611869439
    0x20301060c0507080a031403190608030c07050105030c0d1e0e0a1a0609070536091803120a09080a1701050301060305150a09020a0f0e01 60
    0x207850703e0301503800b141059004000800100744e10860002c90800304200c11079498071161040c4154180f050401c980f150302c2d009000582060010052581803500340594800c03c4da114015503080c04110346420b04446c08014030891400c0e40c2d071140d141c80c909040c900c011100ca100c00b00045038070038100c900c800d900c02801d01081c000e40c4640b684490320403c0403010305180010115080e154094100810b10074041102c00d01054610000e152080d001c01aa1030030000009565a0140c40652750600034072401c4042010300c140c3c141401c2051502c2c02c029450400000d04502c005140104029400d1303a0700d1076038000040c4008028481d2034403990320042c2040410f1004443c00f041030340118441c1e85068000c100051b40810f541c1494403a400682605a981903200000ba015880c1c00951220302c100010402c0139101c0340c058252100444010456030b20b07034071509080900320500c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 611690647 611870503 := by
  have h0 := BRFrame.cov_init 611690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 611690647 ≤ n) (h2 : n < 611870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
