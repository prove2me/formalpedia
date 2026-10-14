-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3655
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:17:58.16143+00:00
-- url     : https://prove2.me/submissions/134314ff-2a25-4f5c-9ad0-65c825bac18b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 657194244 ≤ n < 657374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 657195494 1250 657194244 657194261
    0x20703020106270e030a0f0c030c0204050a0b030f070308090105070302070b07050307030f0504150305040809120c01020f0102120a0b03070f03031e020307020121060f23120601140103 80
    0x81d40c100c1443e81003400c0c40c3d03010942c01d03241c0700d040c01d04514501e400c4002050300d0008030700b6201c40321001d01c8036000300e648140940c0290104001c6030210310260f2a18442c0f40c1c00307102c07643c6010072401c000c9004e06140085550b40c40b011540003060410204040c0000e4600340d0b0b02c24604155680841d0904920382010754000042d05840001c051040010001c02081e01901ca61180b0701c406140800641e42030081c6d05c41c00307003401d141e000c030b140e1841e210307071700403940103100b07d294604102d640300209100c0300c03c0c41321442c4954802c600340002581c04019400d23645101000940ca80450040c81d4158504050304860807280c0b40e0308846025a03007480350001400d1100c1c9034184e0341e40e07a07080050030b40d400141e071200e4003403103040f1041080348044200d880194040e11032031503031258074030030008003281d0209040205075500008151700400150400c02001c40d00c104a510060301c86d500351180c1c3c1e1586100d4441c5a00864498119502081c030780d044541310049000c0c0403003602c0059000d001e111 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 657196744 1250 657195494 657195509
    0x6030307020402180f0306160c15020a02010c0305010909080717040b07050c0415030b16020c03030f09090601050301051e030a0807140f030a021e030d0c2718020703020106 75
    0x200d2480300044c4801c141c0d69040c8011100300040c0c100f44000e058a0790001c2e1010102c5420451002c1c51907802010101d9406104241c1591240c201d002010100c0c2c0061a000c00181d440c0c010360780340540d140c080c807405040313088010089041c0c241e030b404510f80b01d041f02c0200762201d000050401c0b0742e02402550000c0c01c00070700503a07490101d0715080351644040880540b060b0b1620841d090056044031603842940d0748040c0c29070181d1542801600041c8004076000114880d000c0e14000c2901d00340003610b4100d2910203e15114035a880420096650040c541410040d00b8801000182d440c07401500001101e03507001c03026007440a02003414589001c20140c9403110014a240400c006000000304800c1c0c8241034420b0900348803107080c0c4902c20002000010f91000180d0715554075840c130400d2203403520408513480d18400407441006d603100d8040701c40c046008000304a52001102c20f880f0074013454500f01401d1182041c41014400b00b65210030840700d80d002c02c002c400c05000354400c20140c00034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 657197994 1250 657196744 657196747
    0x10e030406110d0305060603060105070507080d0201140f07050f0d060f0b04180c021e070302120105060a09090804031101030216060f0f23130602120a11071a06030307020402 76
    0x4070744010b0710180012410541c40e1050901d0315000510034814580a844002c003400e02c3c50304d0b02c00044540d50030040007a20203014401c00020484010805031003154500d4001091200c6501d8012010a900038100b01c984441c10081200c400e60041c1141c0c40b0360402d000320307038441c0c000c102d0f00d000400c6d09070001249258080c0010441c42a240050000c45424800c400007043c5001d0015003501d0b8200125809688aa80040210880b00045050411f286021117101030f60b02e40016035451030031107449030107964903024014941817000a503800b0b8454401e042c0040c0115541e4040c05225a120140c0905081d0049090f180e100c0e404450307a210384c3e042c50100b0904503013064030007414000400c0a07901d00e40402c40d54000da4500030142c8030540490b401ea0300c1e15002580d021b104800501c1500702c0354109020a00090041c0701070078215000101d001400e00d402031a00b400c807100303803503010180c03607090007400b002030031603c580c002da0f000304400302c10381d41c4401020038907501411100a501900 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 657199244 1250 657197994 657197999
    0x70e0c0708031902070614011512020d020d09060e0f030a020601090b0d060c0f020c0415170f0a050106030302161815080a08090f100f030b060909011d0c13090e010e0304 74
    0x3440c1c10000d800e555840c45c00505998886524812702d01110030440401d045551500e01d5420503030290038940f00143c0c0161501461901314002c0b10b0b00a84104c40070307540c802c6040c410100420401c0c88480a0303400861400b041c00c41c010b0742d41c12051007107501054695801c69816118080c40858440e40840180841211007101038034018240e0b40304030040c072038401180590f02c2c00380519040d000401c001c0c2c114890070661207442203904603002c011144903001c1c0c4060050000c04c0500880342c0110000100c8c036045250084c1004142d140c00c0070100c07800c1400344440c84440c2103803001d043d070a460024001c41d60080301182178005500507803450045030700403c2402440c000411a40c00f00300ca0040e4007076a44000c0004107400c8001e0007000581c00600c1010300c034083c6c0e000302c00300035000303103003e040810200c002000220260850860000924040c20b00c1b00100c500b426001035000380c8103410720307040140c002d010209911030991807940715000c1c503c8003030b0203501c80180750203043e060301e94075134 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 657200494 1250 657199244 657199253
    0xb161709061c0b0d030206150405070c0f02180108060708070e01120b0120210435030d0605010e0a0e070c020d0501020309070512010501050a14120a050105060102070e0c070803190207 80
    0x507008ca95050302e01d10808001c106a00d0940f1a941c40b9410710388074240e00400d1604c07248684401408100d07000351160080c54042031054090300c4c001c1006030002c0006241c442e80080613004040d240ba400c0c0a040500a1402d0382c024803914424905d601c8001415801d2000403030300c080c038404482d10b004038040011554558046a405010011150102d04107100c031100e10a85105904c514520900da0350002ea041640054003880c0c08280f01400726070161103084041c0c00c650240d181030400071394643c070411555800c45e07002e4240c118112014111645010241820014010060310030800c016849008650314007000c125250b030003000031510b900c0c048490507915a440d0061310b208080d07411400e40a0001401400d0590f88060f01d4440045c1c0350881804103003c503112915403012010b9840d991b417a41c1000181803180c0036000105032030030b2180019040000e142c000c0c42c80502c0c0c1c1030402150071a814201c6003010340c080c106503a0796485100d1005602c0d0016045083d942c000100c00c0b0512 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 657201744 1250 657200494 657200503
    0xe0a060e010c0e0a18110f0a0c1e0c030803060301180f0b160e0603060109030b0709180b030303010513091e03090605180d0c0b161709061c0b0d0302 65
    0x2c2000c0d4481c0c1220314500010045121340350300c00e10f96511000d0442c6600b03030010307400402c806803013a041a402c12402e800c4800c282c1e08101e007076100080400c840c04090003080240007064600d0500d01c01d000b1a055102c008000d00d103400090030407003002000c2410340c0c409500003501000007124100d0048914508400090a108819107069000e54045a40c0e1250410306001c2003d00e0f03103c0e44401c800740801c4c09900d403c002c1c00c003418007816a40020124a00e03440c1c0718071a030038540d107620321300781421041901500380001402e401480e005140406440000c2100c0c1135031000c85080d03140c001441c2410018041030740c0018100703a042e0450420b03e040048603100942d101c0e4640381a80c58407950100c43c140502e000d43c10021a038070241042030b04141e103c0c034480900401c00b02050649134040c22605a0042540d81095407603680704005000003006820240052022982d00c0d02c8a4030001404034020640c017424047e4240c0b480c1c82c4219000c0d44140960040509a1890b030525810041d40302d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 657202994 1250 657201744 657201761
    0x2030a0804030e1c021302120f28020a02010f110f071704032d120509210d031802101d1c060e0d0519020c0a090b030d02031206040e0a060e01 62
    0x3424000000a080f1041802520321a448440e60070855558000c07100c05a050060554030840380c00cad60340710900410381c1a200fa59030405140140c0c0d24000864028210b0360700011003c1200d15218803031125031148422117030109a101905519452241050341c0790030300541c5800050000001d00101304030110501c0c106e00c00100130360b010142c8003410640e0220881c154014040342c05203050a80b0381e40103c0c05424542e030007600d03140d111504c5241d041c0c1c201040e4503078500c00d940418500c000090741401348021080310a0780640400d4075640c04103a0203c1c1603c03a04082c485c0d14010031410b0844030340506036140b0018500c094071120440491075012401c0030a80300c550501941c0c400c3d22000040c0d18804d09890707511107142c078684031a0080100c1d00c84038140114002d0080c10051a075404400c2005800311000000f0981c1e4018201450144288880030039500309100f9030113164010030340d6650240d001d0380c0c04140308059120071414000d946000801642c03400031081d0494030705500100c3c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 657204244 1250 657202994 657202999
    0xe0d0903020310090203100507020c03160f050301020c06070509061c05010e0c0702010c031404030501050903040e0f0702030d0908040915090c05120a150b03040323030702030a0804030e1c02 83
    0x6680703d00e18145083c4c480c85030021b9051b5110b891f00400e40d0803207600c00baa211b0070342d01c10389858450080020742001804c81c000b01074001025000c0c81000b400101074070080904400031860201c00070041500c61400070902810b2050105500a464654108403a40c03020f000c40d88140e65100000e90400034003080c0603102c00102c0020001d85062645021582d84980584400401401070303641200ca50600391107440c4081000c3c000000010b400340550f0740180b4010303000e55250350902034003200c407680052042c0d40741e02004003408640f075000f1044580c060808070b00440c454041e0704107048036201c0c65008815051810180c2c0382210f0320885c0c0401a1580c1a0042c8941501c22008460b14021100440641011400440c00c0c990342c0d680f100160084001498051a90b20349500040d42c0007160250003260701841c5000400c030b0b200c58081c40410305100101d040d81000c0d00c000b5503c0c01608035002c1030001040c003144c11f25019010602c95024010003284074800246840c1100328041c0c1c008a0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 657205494 1250 657204244 657204253
    0x150a0e240106020c0607032304050d050303010512160b1323031c1d040f090503070c050a0e0f1b030a0209041407080c0d090203010207140c01080405120a030e0d09030203 74
    0x5440d1400e0740403101644c6c1c01d48d03219101c00d08070380d00c213501e841c265100031540d0f403004200000d00e98941d4209004854040c20245450358584014040c000400c82400c0030207030000340804d2000210700c1c01d05000d960700c41c6181c5444500703a002210303a800c0ba50308191101201050001410180244089109081901641c131081201c0d0f9841c08440c81712514200801c0e240e0b014030540e070304d0315658000704900092000c254404110490402c0310703540001501e00d6000060801c052104e10310918004150a03500b69201e1407421100341001900503021500703940412000c115218080c00d001c58410b1040c90a06079a4101040050025800744150602030760030701e00580c0d480ca01440607035211b01c4080d164144940d0325007500100b154408407001d4081e40c2d8074003400026803400d2019142c000e200303600f244d0240d05186c40c1c1c40d1070005985000303810405202c04000000c0d0300490300c4520901049480c0d5290900881e0540c040d1641c020011011310075400b55001184e4490b16820403603009500b583c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 657206744 1250 657205494 657205513
    0xc060a0b0f10080c090406051003270203061801200901021b0d020d03110601030b010906170a06050703090b0c04290a1b0204140403080603150a0e24010602 68
    0x100b08040a0340314000300340c0d80c0c000a1400f4000b2402090340c210018000a0560348410000701042d407a0a16040001c2e07594100d2400802010000a40e01082545030501410300e5400607548141c01044c90f480c000100030164850603007500300e003066195a418420074154402c503052403e8011105242c0144075541d0041c485071103990703618030401c0d40600708200c0510545c0a1041741000032004404200348048211a42c03002800154040c51066985241c1c82d4581003440003564045e0b00169451005680c0050b030442000820360040c0c1e0344034202052613035600307200764002c10503850042c00a50019080044101d101001081900d0b0750311840c109400300a034501440b820050321000d8140400c02103440c209001c0da601800c000000180010681155400b24090740ca00c0e0200141c1c4403088004d11041641240d03005074092003ea0040903400f02c080b5084a1a07940580320859140d0f40d10180d40348900305120600c01c656000107110100c0c0080e24100146890920500b0018060040f25 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 657207994 1250 657206744 657206749
    0x3030e16080a0b0709030c0e0702011506120e0c030f0f010f0605060a030e07050409050a0303050108011a060708041a07120c0206040314070810020706050a0603020a06050f0c060a0b0f 80
    0x5030540790381d40000c0c90703210040d41c0d881e10742941c064106000d1100101001000030141483c00300a40ba00098039411820255000381c2134880d411131128a111b01840c0074031011ba440700c00401710000804010400d103240358441360920b91000b41058042c0074034103846c040604001680b048128001c0000c1002c4440c1c10b0900b000c0f11468003030198010350800940d02d54920a0300545840c046030015640348564650018081b100c124204807410303000000740c0002c6c560188951401840c1d0f890007444190103c05801c0fa1008800e10001c0c8100030114a00041c002d19009486c003070a01480c56480202d03c030004100b0703540040b002111a400e005c24a401c00034411500a4201070f8040c00342810f16065a4030900070000385d0080c1c10040c42820800aa000c20802c0b030725440400351600141d6449032410400182ca40c0107022600e41d90a2543c20001a100c00105a044400e5450402d84484010a104200d0712490300020f507184507480038028000c1141d4010800c2d41c9040301c90241d800c490005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 657209244 1250 657207994 657208033
    0xc0a12240e010b09090702030408010c09090510050108070513050405040c2108070602031305070e160e0d020f0d080d05061c02010c0210112b020f0712030e030a03030e 73
    0x1805411201440004c3c0c3c50b04084003da81c1040131030040e40d0510340c0750741c11542143d080540b59000110f04040401864003144140d0b0740055852802005182c01c0000107041c00c00c0c0900f500c010090000f64102d5085025180d43c0c000d0680104184528140341c180b502104800d400380c0c14820b143d11000342504803070001518a080d90000200d41000c4903621908000c0d04020000710f143c110514010380000c00520108000d842e00d61440c40b25400d143c41c0c0900a606428114000e00400ea80f84444954581e5540410303264100d03459281681080e01188205000e00303002086c031040401e5008020803150821441040159104540007000d40c0c16101c0e51302c1c002d500640443c40c807010980c0582055001c100e0f011130181070140c40c41482175181450507250110184403160502050b41844003081821981001680f0040c080c0f10030094955072903121520507510304070040109482054012140413900e40e1008080d01c944401070305000e00504081c58950303209008000140c00e00562a82 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 657210494 1250 657209244 657209249
    0x27101b0605310c0302040513051f0506040c05030f0403050c070f0e060904020d0f211d0109421101141603090602070803101a120c0a12240e01 62
    0x83c01c1c401c1c2461602448003c000240160710420719120684010800c00c00955481c21070fa904413000586410781050304650010b020079124504085080003040c4e8890292500001d040050500c0c076150303841c041d14288960354100500b03000300781000270341010400c01c0c10100e0300b02c4614554569101420031a40e500d00b03c030000e501c00c44000c10034001c98500785003050180c1c419038050b00702c4000300c09001c02d0b241303850320198002030800c104d090407078090100360b09082c20282401242141004007022442d0a5a41d088030340300343c03200a00d40075a8a8155000411811950310442d400c042c542c01000c198960450308510b40c240320420314882c869540d113034401c1d000440c19001c80320050804402510780050192000c0781c00344810408224554001d600802c200141403075810318160382d881035010214400f00c9106c0f0203000040850010b4080c0d0340c1d102c284800d60aa481e0012982602c0c880e5141102081403881c08450501c0305030506480710301e04084010b034811180da0703103101c601415405d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 657211744 1250 657210494 657210503
    0x21020606011b030210050a15081207020d030e060f0406031b0905010c06060b04120c0911070f02190f05130b060414011e0527101b060531 60
    0x902d1402a40100c2900c5040d05480391040e516800f06030441d413400c0d074200303450f014004c1e6a2101d4013240c001034820380c40010080c04020f40999100b04008004e98000c45102038000c5507400803c00405100f0304100305100f0000b0100744e10b0300804440740140382c0243c080c49000c00e00c0c0c5071005800b105040022408000c10b0381d1040000c0c0d00f030800468980b480e614041300d5a64940e0030204003440d18102910260010400e030004c14222814400c900501d60b9000e590706924141c0c0000542400c01c3c101e903071254102c0601d80e5107000c07030b101150750790000d40007412898460f40d101040308140400204c04a0384101c441c000c148419803000f000b250102420740351710800401040080582c150203814000d02c0504040c0c03100e043c40e1412002a075810780214001540001c1c50741d803101c0080c5180d2035544031806072000c001402c02c0c0829410860300c5072950501c0302c01c0b06c500d9100c04a540c0d6094007a0b5220800348880d040480340d40000041c01d460400391200340c07140ca004940100000d83c10000d400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 657212994 1250 657211744 657211757
    0xa0c150e18190e01020f070506160801050607021f020a02041a2211281103070b0901020c0f150a052401030b040204060206060a0906080a030302030a06030b042102060601 74
    0x6658104100c003500c01608141c15440f0b9185003414207081c40500b0480303403021102951030f00545481414807134010503a0200b036000d8401c99000a502c0102c507170550380c007650090383e81c00041c000640c8602013022404100840d0031956040d041d404180d800149100b91418440440721941c50000603c1c0c1c1c0000b02d0b00032203003940003aa20110110f02005450b040600010042c42c1411041c017240d01510750080031800c10383d400a060071821203a0322503401c992404050704000380c24501c0e203a02c04c010010301100999004689241c03800e5045884000c01c4600721004181600e080075220305c0b00381d50700503040140d0030005000248602a081c07091529108401c0a0101c044800000c0042c6140310b41c1096503610140d0a41d40b243c0c401017024100d19001080c491a000c0d041151081c2c103134002842e880d05040d0704102d0000006600b03a600c80d49800c0250f10b80d540e02c801c0500604042d440580000360340c0c01404141700700d5001c800345c0003049442e0f80610000108080c1c0e541c5105a03080c172f001940 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 657214244 1250 657212994 657213001
    0x30706020d23070c0e0601050301050a0b0a140409060602070806060306180a150b1e1026010303050703020f1908030a0e0d050d060608100905090a0c150e18 68
    0x4500001c1004040044080d200742c0e24040c2d00c0301007a001208121001300c0c480009028072907407211380c194400d0092814a19640c100404148030713100910a54901c6a004134580a8003401a80003025900c4c4070001aa200d543e034240c2d0401030981c40c81500050301502d8000324a06401085440c45104050001e005075114882500c0c00994500d45205d01ca00a450489001968181d0ba1309002c0e104120081140300713440b0300b002000215140c0c00c4140240882e0f80c06400c2e181c00000e03480320001070400400e035031010b1811200f41c130902b1007010301d0300d10360500201c10950010301410000d8040c0c1d00f11854000c0e0360540507030340c40044071600d1220181c40b00340e1000860b50001198800c0985e907012031044141500c042c40c04ac0d01c82490700c00319402041d1402070b0f05c4607214000041289103042225428900d100500401d2a80100550ba50b1550300081d43c040341007041140d0701c0c0d80a0040a0415501c02800100e148000b44d08000551520303d070f202c40d1f14050840ca005407075041c1d425011501c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 657215494 1250 657214244 657214247
    0x4060b04030f020f1f020c01110307052a06120f100803040302130b04021b0c0301090c050d11120a0204060504050606090d050f0f031b0304060c080705030405040f0218030706020d 78
    0xf444042c107038050a41504114412810305485c00031814940003040740460f00000500719140300f200d016440c1d8028032900001c00c200049000b10354002c820140e1040700c60100d0050034aa010158a800c42c00008450401000e0103401e10700ca9800420303c8145030300c95007d14101e40005104481450344140406c0c80503142405141e229501c8030140050a281e07400085000d90300900549030b51041010031401121070140400c4c90f80f13110031030003005005403a0740c400324542424000d95015248404000781085020003504000c00c00081020143d1101c004500c1e5940d04524801c038015402c00d2400100307030416003d200e01441008100380d0038240208244043d0b24250042920580310b64492400319410034001008400c9400c0051030f034940f0450150b85040340030580120a6510402c000c001071940510484c003407940c410b03400355075a0382c1070070100d2079402a5080799602616101c540404106613074024404c40d0a080c110882c04449a0300b01a181c0c07085128003030158003c0c0130810b2005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 657216744 1250 657215494 657215509
    0x20321090109201f2c061201090b010c080405091f08070314071d0405030d0f021c09020a1e121209090506030a080a110a1104060b04030f02 61
    0x6000300c0000820302c4468640d04180040760745511041c2d0114800903025040042c0900b080d008a11600c40744681c03040801440a25035030030010b00018a0303c200a10520b0444032285002d9004200a44072803401a0b0300901c20300a10401d00e101380303400004116540121100030710340340c00480c801e09088c034040500008280041100c007110451000c000b040107481178506020b0561040100405415481c042d401e90b00e41c0100a40254170200c1b08200001303a00c000d6105030f14018000d050b42c1e8840f840c3c5507203140222280201098103102d42e00120098584c0a805150102030050102c12441c81c01d0608a4a5855010b500558400c405101c6810701c0d407600d4104482d202488107407076941d00840600c2d01400c1d0310840d10005005810080da0390b205c29202c4c050003001d941008207091880000341c0c0c940381400d00900c070803c086150a80311b0300440c0c404c00313030a00f120181c034070700d0702e5a03d404400490590400c0d0304c91844e0000201d0324212420564050b00d910441c90b80d0861200d03004c00c40e48 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 657217994 1250 657216744 657216751
    0x60809120324030d0503090d0c0804091d0f06161e110c04020c10060b0a02031e090d030c0212010e0a0618021323060609091f060519020321 61
    0x40d04031607208055983c80800c91010f9002a03507443e2912800c0962125040c40b0000b503000041040d20010280460010310882c5c01316644030380c00161118108048031661406003003841c0c4540a03003944c1401000020807198411030511042405440c01c2000c29501c6c2880c1d4080e80750000108800500e0a60142c60070390000703074440086920761651080050182da0102e440061643c002442080712030714107001c4c05010744081c000c003034101640150002c0d60b07405051030017102c1d40c2920030b20105106560080341d481c0900504018115106820b001d0489612981c04a0140e440541c1500a2030018403403269220780100240c0034045294440304e000e0a02004007030044026010400c0050740e901c4103490049000e814082204c00b2041c2c90300310045040311110b060140d1b000200801039840500301d608222080350a09425142d2101200c052a0750b0b1402e40d040380c030185001714101e6000006041200c040b40d000040806c031904040740c40340a24034441c4850394400d007001c0740605a0410703641e403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 657219244 1250 657217994 657218041
    0x320f04030c171303051c111005070513030809011e210e01060e091002090a030f0606051005070507090908091e0d0c030b06010206010605091c051203010608091203 71
    0x8040c0b20f0303000341c0602c081c59841214258400c00b1b603101c60324103c0c2d5111943c11040d0810400c1c035521191400d4484249003118400540d640c00000d65403409041603601808003544408801a00c03450143d81d507900108455011a080340c1d5850f02000c0c401c503401050f2403a5030ba900c803414113404510308000d074054251803400350f107882108001400074400c95005103803c1c184080c2c2424000811424803018000c100801e80c0100403c00e80342d100c490111007103981c0501941e40340c81b003a09101000700304079080a83e000d1924a414100b155210024041c0a07000e84d00b6507440300e9480e0216401c58020080080140c6814001c03c051441e05c00c1100c803489084002c0315103000c1808000400c0c401c41ea00040b10a000112018030130b000702d81c9445075004800b8002080503505210010740a4000c0011040c840e09011081c0341c213030f002104403040802e5206003100e42c402c2001030a0301c4583c209000d140e002400010002d28070480002d13a42050112103103000340355480c3d1001025860758001040350 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 657220494 1250 657219244 657219247
    0xb1207121e030f092c0433060b070f080a09030507080d080702010203100311011101061d09030a050d050615160302010501080c01140d320f04030c17 65
    0x4001c5000c8411400300d18030039565440032401007040034020740c506403c001851500305284040040c80b58280f000d0020403d0003602481da200d01d072444040403412040c01e20381d003400094290149801c40d240700c1d6450607610074071055848962402c034600403804003406081c0b840ca0040041441e80d0b00805514074540780c4518060340b662111880c0a10580c03000b48503a020420482403254002c1050f1303084004c0d440250300d98241203401c03040001071408081c00d02c25070104da1600c541c0c064060003143c41440c8000b84065030346c64200f070320200362050800c80189403580009800742404000c9641402c0217448031401d00c0c103001c540c0c00040a000703203010b4000a0701401e03150300000e558054210a0541c107620100081503150090a582041e80300700740340d40c44218002810b80e0072061200319000c400b4201916204944a02e001030451000b1071000340448101c15880d0300a14070712008409000384445205840e4030800300000803040b1806030004851a64041c0020701d4860356810903c540c0c3c1c1e40e00d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 657221744 1250 657220494 657220523
    0x203060d020613060305180c0f031f02180415061407061e0b0f03030703180e0103120f05030f0109050901060305030d060608060607021005030a0615030b0102010b120712 74
    0x82c4541d008245122540f8441c035410041c00d40e15000b81644091284000c2e031032810300800c420750759404c1100280c401c84445414601d00c0d28208008102d40501da0034001c0d11062070745151000f58889042910714480010303100c8410f0803c3d000d0940104901c04009407124a0a08103e0309191890075079240c4441c05c02a41001ca10940144c000020300e0038100d07041c507604480020101d40764054514080d00b0700140c030140980d40802903a120030f40601780428024420040b07221016082e8020315048905800080184100080325006201c101c2d21030780c050101c40e15080e1090f0000700c904445160b5014014800021035030401d03070f04003501d4000407546649980da51415a0042e032500740000b0f80d200410031901703034442d404030b80241c1c00f501c10600e40300d566000f1035980311181840d80c00380000080070410950003603000340c0c001e04507031545880007031096400070003800e07003100154010340c20b1511400c11032801e0201e072104201d500b401000c10511300317410b40401e0320380000c080d140d000c01000c10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 657222994 1250 657221744 657221749
    0xf0306030f0b01060e0d0305090409020a0f0605091503190207020102010e010c11190503030705160b0103050a0b0f061e06070f05010203060a060c03270506131a0705100203060d02 78
    0x54031410340c07246840700010342c1030020080005c01050800ba20030218103100802103500030041307561103003081e100410070798071600210301e041009510880f01041040300005810b0340c481d0181101e210220b0710b0b081c0e01d500386208141c0c240400d84075443e4a00c40100c2041249010384c1c0100200d03881800041601750881a1182c01c5030814071000000c0b440a0b103c80007030f490144034000c1002d8400c0000900541240c072501d54a000041c000390920070f0004000020303940a80124014aa000192168541c5c4074a8820346914010008075050074140d008180a41c0304c150700d140c0b08841c00742040060318640300c81c00c0d0f6542c211583c0c645c1c00dc02c0811070350f008161231500a0021038042c82c0003580ea0309001052142d0301d02c0c5988840f0800c0420b030340d03000000c0e40c00300c40008e0345404c1c03014442c0e6400420200800d40441d03503019030ba0003500001c20f04640f0100002020480c6c00310b03d6441035468600481c0200d900c40c80000500c44e4101e40002a0b9020041d8051600400081c0620301c801d8901d502 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 657224244 1250 657222994 657223013
    0x10f240b030a3e0c0a080912030708090307051c02010c060b0a26010203100b0309121602031c0507031404050a170d03110403020d21030b0a080d0f0f030603 68
    0x61420fa140280794200302c41400a14444895400d1207011518100c20300ca140d41c3c0b01d40c002030740102811400908101150b0f251080c00303220300c00c0f0b0343c10381c0d0781c8803010315100446602c08a9160f000c0c1c0200c060002c1d0b00c1c0340140c122400017903a113070300e100104c03560342c0111010f1014002c120341041d1340703c081c01c0341c1d0380b00d030705039500640724044603112a1004118640d00303042544561400716070042040004090040340c0c81001c5868044070691030303032220390340d0704d0030024064540c00d2282d00c04a80d00300c212a000e140010003900a401750340303008450600c99a0780b4003032010070303d011420402080c40064882ea44101481b05580005c50a01c2c3c3c40d000000d4503442a6030100c0b0242003125081103852109104041d42c0f14810f05003041560b101314030402c1240202d01c4003a21031044003d041040c09403030300c040c9440c920806044500104620b0014004003203840089000d95061040402c54100005010120310859111b20040503d4501c084400c0b941e64004442015250b400010010702e0010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 657225494 1250 657224244 657224291
    0x90b01121401020c21070b0f01031a0105060901110a05060a0903140a120b0607060e16051e040b010c060507210209090403050904110c010f240b030a 65
    0xa540003540309403800c015614a069100d4800264810004d08030000000210070708422203a5403401c500c825122a4903085005007140508882140420030101c403141500a41c10307a44503141080a50b16007154005124a0034000c4507001101002025055805680f9261003040d0303a000b1200e0010aa90302c490500d2800c3c0d034180c034a6a00c50912a08164008882696803818a8021420700d014000c00a065a4111101880840c1d503881c50f601d1a8850780f00700c0b100250441028081998414038003980d90100c211b00c124000c081c9040420701d450400c800e8001a074030300d81c10003e5055804100402003c130110800c2c14031000031a084001800b83c02601d10901e02c50701c0f01101c020104c41240c05000061498140b02c51041056003040d81d00c2e401c0e480d8000b0740600c2c00d02e4a44030001c000c5001000d68440740e140c4808007049901d62203405400040e81f41401c0101440103840000c41c9541d0640910605100c440d0b403000c050105a40c4c0ea005158000d88108020a0002c1551407900385003c115 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 657226744 1250 657225494 657225509
    0x3090307020a030b040209070c030e13060e1e06010f08180c10030b031608030318030d110409150b0703080403020c1c05210409020f040f080304030606090b090f0a090b01 74
    0x401c005c20740c9495840c1c0c9070b01500b1404d241c0b5040320140d8000300241c0c13030324511034810848039046049026003540903101400c0c03d103031200c086040040fa142e02d28001c201491005882a10002d804c0f5417180c050b42c0d0383c02110762208085901d69003a0506181c9504040510b10b00c54404a0310701030ba01e01b01e03516401800d58500207808004d07042410304104248480e0010405200402c00c54100f0010440758011640d07d00c0b851522010b003161801c2d4030900300c2d442d540e10300781040c0f15503c45140300148115615407a041241c4e0001b0950480802040d114892104100b48a1500070274002c01c0400c3d032252003841910f03011005100000c1c0c403492100707400e8800440400107242001020488944244000100140f42c11070f80c1d10700c1c044920883c001c240c007031a00400d44408030f540d00c1d002d44001c0d2001103400044e6940300e001c0e0036980d030094841a6140e80c14581c00142c105120320503000700031000b9100320b0300c1ea55044d810041065003c0c00c51003490740da801e01d41000c6502490940c2c0070304000c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 657227994 1250 657226744 657226763
    0x6090a0314010b090f0a050a0b150a081602070317041a04080c0316050d051c020d080c0a1403060d02040912110313060c0c0e0112031b020307090203090307020a03 71
    0x210901c4a00316203982c10680c0c000d00301c9000744003c0003046240554415219000440c040d03440f24030031400307400340340f01c0d40360000140b208820400c041c0002900f1140c801e075444140d142d6881c080300303c140211440040c0036800c408401d101058444c14103100c0301c08901035281c80c241c0d980e603070504101001440300e18220710201e02070000070818482106d161404900406d10181c00c50080c102000c698072400d84180e01c20111182000410b000f00600e110a030bc0c42541c0321100c021029444031a0340c484034000409107400a07004c1703a0001c1c203039840060150b8800141401c010b041007204d61025000c00d42c0100740318041e6005945500440b11554414140754480001000000c0c0c02001c0390407442d10542c100780119200308803486c0c0300c0804c0b582d40b490705008820302c0d41005220000d090304001401000040007040c034100540c00554518881d6403901c09600c040030b501804c0380300c0c09a000354540c01c55102081b5903440ea40186400181da10250b0b4035040f41070380014801c424a40c41161015030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 657229244 1250 657227994 657228023
    0x801061409100510021203040c0306050601020a080304061e09050a121d1005130f03120302040b0909040618050114130203060f0a06030c031a07030605060d0b06090a03 73
    0x10304842042521100780c8607a0710324146101ea0318070000749402494003901e90100040b1400e0f10030042e00004562a0496030340c2c07030820303007000714000c50507010650702181170a021400d203510019403541220f80140d4240c1c210f40700e41d51110060581d104000142c1455025070038060802c03481081d82d91803140c0020400d00d1050f02c1c000d10425400300f608814080281408143d440b0b184600004a50003200c0510414084410a444a009500f0041450366504801103043c0141e003000c42c00340c074061a540d40a080180c0d00440982c41140601107003000c06025416050404c1e40401d40c2140c8281d03008500100c1901e002d003403007060705200766401d0791a0f1041c0020b0010072030b4007a800c005100002e003e0014142c011a81d01c290280c4480001900d0308001260160181d1081d80a5503011441203c0c01e9604c4c2402c8180b103004508038003603000b01d10081200140603108510071684084c00300d0741071840c1020800d004202d031546007500139a0800903040e0641d00c1c407480d0300143d4031603600d0030324589 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 657230494 1250 657229244 657229259
    0x62a080a050315090c190e0a0302060c011103010315061406070b0714030901060e01080a02180a020c0a0308060f090f070f11060901060f0608010b090d060f06030305180d0b0609070513080106 83
    0x10000d603543c0c0501444107451f1040381c8030383c514a401d4035019200242d5690140426a0042c59083c203954081c0c68040000b0082100010740040c4844541d8000d00081c0d40300e095200c400100c1c030407400d50150f42040820b0000301e000ba1013982c0504541000c03100560130311407030b100a5100322680e50031030355101014000c01c0c43c4080954050f2040c440100003048240d408290700c034009004640c0846c900781300041d82c0703c050307030100c40b49418540150f5000b190540341c080c140c80025174060340300d0b0052540340c0e0300500b4801d54181c8690310125105116450301c55050b50192250000e90081054040c2c0d40c2861017010031600307020340d0001c40001350a5151048424680032590454001c01c11800010800a4045400d45018100841d02d0540d8a105442c0001c004c1210744604c0b030240d41400000020f140c1c00502501007161042d008900c45404d1804002d10f0f48114100104200c41480c08101c6504211fa9000d40c440040d0800618100c0c6040041b132120b54a540030b00c00301d070b454030414070000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 657231744 1250 657230494 657230527
    0x901091a04030b090f0d02010630030302090613150801050d0305120709080a0605071b020d060c0512090a0303060b190f021006062a080a050315090c 65
    0x30300d012404109080d25464100c101486544400f401c0885041e0218218600c248100030080c00040102d07201440e881c44040d018200c03601c500b1006801c0c10401c07000003090040079519468000e91200b081040c651740c04c0d0000c2d00006041a002003050144904040785c008090014041d00e8ae4101668000781030024000c400580016006007140d41c4103d000076007200607110100c0284a02018640e078900046428164035403001009103d0b14132030100b0b100d0194070607401940160345000d42007109001d1031030b158466010013074100d141031070329401040c0503512140d0101c906150042ca000e502c000d032848000b000303407800b000303035005240050105500741c0319072002020705403e4603051400030310740300c3e0040390f6942042c02031020f01d050043c10184203110b60b5103002c840d2130040108a4407514002e00c51304400c006060305108404150032100e8a800340f40381c0055111100918124000d0012100745d040a0803543c1d03a40d42d115030060b115a07480415a10584c07000b40b03040d0701c60001007004041d9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 657232994 1250 657231744 657231749
    0x90c010e011211070b0415060b091305181617070509043302090a1e26070b031e0601020618030405031c1103041d040f120302090109 58
    0x6000850101500c141d81081d041118a00500000216501600d070358852501c20031a000740104c080303c04000c204664201030001152121030204940c540b14040d0000354482d0761941903105040c042d10010b10400358221951024158654001030384942c40042d140c0142083e04511007111550148455401d0040303540c24007a85c18010b01c0a9803401d404900f41c40c1d0003500250000c02074083c000003514542c103280000c04069034861a00c5410b03c03030640002e4224400b000d1103000c0e8403400154111f051241403113520314058001000503c0d1124003925204603400060100303d8403590741ca00e12200f030100e54018940200100d542c0d1070004201241030840e040000e803150320480c28080300381da0008449a100142e942203c0314404901c100c0c1b07185d40901c0c0d20280e818400e840e4001d00681c0c400800d015043c1c0d950300c401a10340340f00301105403640694041d4000c50001180c82035031107040c0b02045908240a8151410f80101c1520340c004903c1c010070b4580301281d00001c901c20316591045a0a00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 657234244 1250 657232994 657232997
    0xe0708010f023402010f1823030f06012d090b130e060106030b0a08190309080601061d0114210705070f080306030c130e0d1d090a060f030605090c01 65
    0x40b8a000310300304218400143c0b40a810070290801d00c0d09250702035504480c401d40212180e580e090740d81c418000304e40b006c184440b61280c5020035500f4040c04c0020b6806200303603c0710050045070303007000d2084941000707010782725a040f921010700b03440304122056160058500c44c0c0010880e50700440c14408030b1507000900c11706c254034000101c0f182e14000700e0102d065504514010a00b43c9914001a04900c1160003c0507680075000c40d050207102c1100801c0760052007a1500000250350700400c4e500d4200c02d10406011881491804c0f9a10456040064403000141840008042241c0c11850b01d40c00594174003198000e0280d1000c80083c03c207014607480320940ca411454800c00760b44001182002210080c1520000b10100304a03076010300500c3c5581c000901b982d0a04010b141181004e00401d0900303c0440c01031100b1403a4451060035209110340c13210700b140c4900345015090001c4084024034421645a4410002c100f681d42410680c00840c003030b040215803402d10039040c5043c103007200b120343d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 657235494 1250 657234244 657234307
    0x50306060a05030a112b17030915130b0f061807020d030203060f0303071505060301110426010f0b04150302010e1c0206030406060602061003080d0e0708010f02 70
    0x32995070f000400ea00116400700110b1001c0c8000d101142650307014050305840c0c0e481a83c0707401c0290070940449080d09000306102a01c54015050f03180c00380c8000c1d40e094020382c02280412480383c882c05a2a81c128882203100450310100c0e0312050840078090b120007600c2041c80d010b02c8241c2c03038108521007481b5100c000f007a00e541040308020350781e01c03141b080d103100303064000c8001007640d514a41220540c840190580f984d91120b840c211030903240c00310000111070700d45000301e4840d0405224600101160480c820314207800d04981c410000840c00e00c1a0071982c0c0081d907000c04400078010341e803c00c44418000b10340300c8e1502d0f08010585821034401080c3d0742c162041000941e034060701c86015800e0a542440301000d403803080c2c000c0005450360103500300c0000810300c020841c1d40e511210840f00542c0c2035030100c0e00c551041d8100d08449210240100380d0074030542440f60300303952151100003225411a6003059441c0c14080c25030703151100e05900b0950110b42802ca40008042c24168041c0240050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 657236744 1250 657235494 657235499
    0x6080f07090602061603060b0706020a1205091002031302030a1b0603020903120a050705010603110f010305090c0f010e0d0b01063b181609210609032304050306060a 72
    0x95585200900b0421140c1d070301703607203c2d031702c4c070301960000d8040c0007001c4501d50350740790701d06110001c5d40c003114024000405019116003424100e10806c0d01550707400e0068495200081c914102039000900300f405110540e4005400603501081055201071003003261000c0b006112010351090a0b80e03a000e2005e15004204a030125a03021900060b5040140901c544070090810b0440b014011403000500315840c0260200c24803040410040070420202e4064140d4540d070001102034590603909846990700130f040c41100c1d4600504500c190010602d464050300c900c001c0000c0741800e00781002d545a1400e803005012855104411122003901c941c0c004004402c1241007604012041c0e0b8030b07024801d20002502113075500d4091442489030800b40c0d1650034140643d410001784105904200815041c250015240200307040b030348000040032801c0400c01a49071a0f0801030b2010721070440400600820f070744000140c1c4821440305980c2d001c0001e86442c01c140900d0302d0840090070300c512625940508 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 657237994 1250 657236744 657236747
    0x60c1f091703070201021b030403020f0406030503090108150a0e040b060a08120705030d0903020d0f0f051e04091104151e0536090a02070c0b0c0c03060106080f070906 73
    0x9038031072440036010603589030340d0500f04900900035120101c484076001d505107220410300102030800e40307000300c4410b04c10400240801c0200d5042d4400140709410038020015291702031003183c0c1e072003540c60910001064680000401616035500240e82d0f81d0040c609120500468419841d0702031300958400040c0341c10100960380d25498000842c810000021303121082217014026104140b690000601950000345806521500ca144003980001c8403000404c000f0340c0300d07506a521218068864a2a0100040381700d0440b0180c2a2507403026542080b0009500c1d0b5140700e0207800c00102c10031651200c0c00c14008d190310002800205040004030003d0f4410042c00c1c03d01000345110b142040c5a8503d549000000d40c0341d556081c508426070750130000c9824400311100900540d804513041d060650328a0b00090490040150240c00310021600c140700086c6030000824405010340c08650140f0110b0000070f103424400d8012500090b1440c0a0200311a480354020b904454a410140c6809062820 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 657239244 1250 657237994 657238013
    0x714030903070513020904050708340f0302090303030c07021302040b0a03090f0c06020d09050d1203020c070b1815030601020a02040b061b0313080316060903030b060c1f09 75
    0x251610400d040d144200201c00340b581100c1000c0d0707010b0030a100070f1400c0d17900500102b90440f242d00c080e001404a074030701c07a0004504552411001100340081940022003126041d01091100b014140c2c00c0120040a540c100042c604c1a1298481c0740e0340c80b609032062003443c620000c3c5120401e40144030501482001e5429a100e080c518540014074601600b007940e2403100390322001d4680c1c50800b0010450380e601284003420030346c107502c64900581d51400ae201610b0304901d009492846000c004030f06051003600102a003402c2c6004450035140c550000740b01640c003107041c01e040c5000004400310a400c08482414009042c20754943c25032918100207512100c45190092013540d48500d1450035036240c1d02900d40310b45008401403410720184400036560781c0031b915507511a41514400180c40e41c3d001040303803038030022120442c0081980b5a100005414003801c100d084c1a15013101072003c0d22088050103100740000014982099007441caa40120110150b09034010305041041010989600 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 657240494 1250 657239244 657239249
    0x1a093409090606171207020d14060a150b030402060307091a0a0210140a050a0f0c0224161805061207030b09130305030c090307030b010303081f120203160605071403090307 75
    0x17440507514039940c40007401c0c00c40c420700010810350300d10810f1004031200042d41442401e0600e000c00ca240380b504a903848450092080502000c0c081002400505000300690f40104660070861001c03500c03840c0a02440032101c1000e60032000200d0b040380710560400240e03101c05a0303400200149501070001180e201c0e00241804603882c2c4030b00201d0001c4c91140e0105030785211081c000c01454038401402511a01d6000d0b0b11460340b212405640342c402e80009038203000b5603030080e01d610345003001d000c10303031b031103400900d9040f82001854030004040d11108018201e560095a48803601d01d0032500140403134070340780c81c1d43c0d010f46201c0d0208545034690124100c0b83d01d41506101e40c0740d90b200c03141a40c0d24420045626014090014000104400390741f2145c180d0b0b10035260101103582c1e10705189200c0f40c00c4c0902c6203c0750b00d00182009907201e04c01545d09028006000e8a1040810403071640d410b48080d44084001389002070258244006c107500d0b224140d4414015515243c1e481c800a95240c3c03850 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 657241744 1250 657240494 657240523
    0x7151d1309052e0b041107030f1e030c03150609050d02030709090507051c020604090b0f090108071802040f0603150e010905041a09340909060617 64
    0x450310702080c408200185451640c09901d00405180c4034000c0b96a1085100c024003412030070303c4c03080c43c01c610300f80c001c0d07410000c1c20713540700c0c3c0c10700c040d948080b5215a640c5044000344208400000309511701500d800841d5007c9840100344894242002811100e188008a410a104c0b80c07003881302d198048180c0003155001c0760969010300a5000003400c00840e40e011300c900b03a00d84401c600402c1404101d110843d1000c450540092004100d0041c600e1050307040254803c00400041c0240015a130140341200c8001e0001c0c02d15245030404505115000c2e00304e07a0480c0d0080390100154490745401c51a850409041942481e182048030070016000380210400d154803441d210f5404007901e25142c00502421540b82c0c0d070703940e403000c07450014203080d00c05654030342108403800042030240d6003140c0907080503c020090401c4440051a08c4800f004a6098095080004c80343d400d885002d880090085010f000510305100e160050884007960321811051031010114a508000810b0030201c4a291 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 657242994 1250 657241744 657241751
    0x13091d0f0606060a18120501050709030305030a11190c050105100b0715020c0a0c0e010b0306031504050f070303110d02160e1504060603021e0301140103020c0c0307151d13 75
    0x11180103a49243c00203080e48000c1c03d20380c0c07000075103058880d1000740c1d06d40258001c11590301c41141c2217580350150300020b0040760b020404140c505545071310548600388070078081800c00e02060320a41500941c07503000070000c1c0c0004655000c0c41001c1c41140c3d001b00040110032013640c0742c000c2c1140a80242c0c900a40100056000c6000d0590150100c030042c40d405030681c0c040d0b82c2149170032201e01815005940110061500100b00c0103883d01c1107900488000380142160760b15994103001034000280100e07454041c1c102d0b0350100d00410000000510710036200c80c020041c440800610b4401049000070841d4070511054084402004680c4183ca007401014501e6030340d12040c600100c00b020910940280c903150000440551503800f03403689040c0e031220381d08802e8051506250500082c041c902d6800860203245034258080d074014840880070405a5a0800c89540001d003003441c01e41c0106003e60901c00d802d008250700601e1980d10101251100384c4541f113071404070b481d00380e0103502e10849658 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 657244244 1250 657242994 657243007
    0x614090301140f0108061b0f0a020c04021b011b0806010f090503120a1211030a150302030d020a0201021501030309050607050312010807080106080102071e0813091d0f060606 76
    0x10290010800c255050380400c1260a1110083c80012001d02c921503541c0162400b203100b062260710700981645485115a082c4001d03100c007404654080f0243d041036228600c8090010740f11400544010001c8064046100ca610400749007540c1c109440c0c0584201030401d2030b141a42c0025030146c2042080ca85031048016000084e0b03001c00168004541c103114842c0c01103a170b025444000c10703101015030f07514042e087d600c00d9540c0c26614500c035805281d000a10014208840a1384030601d03200c0e42420520a4994940201f0f0509003000d8280005030000850320065580420502c2e00d2642350102c1c0c03000ca0340c03442c2c030001c1199902d4005c1c5031081c40c00059a005004080040e1035000075400100601960365131423040d900c091620845d4039650803c5c13800141c80c0418800d940f03541d9000106459041050b404000f0b0760780d4040002c0750611070070b0120f007a9901080d0307124005841c00b51400035a2042042685541040344400e00350b240d8003820090025803c081551900910103640c004c0d182d45 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 657245494 1250 657244244 657244249
    0x1090812040320060105010905030a0c060503132f1c06020901030e010f05060f01110c060a02031201060c030305100b27041103011811071202010f1a030601060801061409 74
    0xb101603e0220006554601020b607416000c15501c1c120f40090720b0b101e40c4503a4500038180c46d89a500b1003c1c2c80001640c01c1009494001c40c02141e202d40700040010b5030701043d0f501e42c600e05a80051801400c612840d0070362170241c501c5030007c2c921104668050303401604540a606807443c00000401c0325802040300e070a80d90090b004801d407402000c0080c890340d00c01d079444800031306044400a00c035a1031800880c01950203440c5004a140a03200a0140011201c0070f000341030f4044500c880c1144400c2090441c0034208010b07103400b8040320356030500d0412082c10020300740c910203050111220040b13502045540d619000320703042d0340c202c900350711010a04002c0d5400ca0444165001d50800c0c2040b52800400c0510b40085060700d10001080c0d000b100c0b0300d1412011201c1036800300c20500710400003540422980c1c90b00c95055480d91002094290500001c00706540d40c41e5004a555406004825224902030041d82d000d85024600460590315205008040c12210424030614400008032120320342c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 657246744 1250 657245494 657245507
    0x10e031018020d080d06090515040b0619090e060102030f071506091e1a0a18023a0e03030118060b0304050a0c1202030307020105280f0207050102010908120403 70
    0x150b001010007402e03045600701268541e0102c9041203103149803910101d1461124861035006a18000741c801e01d02c404003045c88001c01003c0c42a5600282c180800c1c1031059030318280c2205818241e590401207441d161401c1c0c08410007404050541d0000d200300c3e2111126074058a040b9071700420603405d02100c40742020010192904402c000d5428080c844842440d0004564850340041c042045140c00b1030419221480e00c454002e6400220200b04001c1c450b0700e2502d6a5081070900300c0186015108010100e42900c0131080c5290b103a00c1c102440e0700300d6411890380d0180401c12038140311480040500302e40381d100502840490302000d110b862551500ba41c07294001d031001c0d40020307540e07050a080190740d401020305c0848900c82c14a03804241880400c0a1160066000c1d00a504265032036005403a1604030651060b003000d554490b00c01b040e200005250014401d6403110020358024200c001d080a9003500924196130400f0207440000d48580c0496512081a29149005444a00c0d044904 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 657247994 1250 657246744 657246791
    0x11010309050709061805130b0702160303170604050403091a09041109041104030308010b0714060f040308090c06041503020909070306090f1b0804050c121605010e0310 73
    0x34410b500d0042044401580490103a450003d030421000b00281070a0f42038078000ca548004440c01e1502d030301c2c0041d980e1440180c1003405801074404895400c68410f0408200340d03c141c0000e650710b5806e902162200c00801e801840c2900d0030301491615440c080c1c00c480081c800c084a4104d80743d0124410110202034407001e50b0002c0060103844045141d0143ca900020f44051246162139611500214000101c0c2d08980d80354892121683c42c014400f4000c0d08a80d80642d1403003a902d041101400081c1320652060888401807186820f003414014012400140075034019400000758040036540e504c113903800c840da01300510200703025520044020b0b01805010b580c00800751014891a50340640194007582c0d40b002c020810001907180c01d4094074544224040010304d60303641003140034410b01841d944180600708640036001d03080c02081c1c888408030441441303904000a458180d80c400440980100803d107403444041c1c9001000036182c03005001803081d2585c0d1000d80c0b400b51010201410030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 657249244 1250 657247994 657248003
    0x7171909050307051002070e060f0907021b010f09030f0f080307020703140c0a0509060301110a1115011d180a2922020301020403080f0712020a0f11010309 68
    0x45681400005000404180182442800342e0500803070b0307906182c8010320951606a0040542c1803804181c0d240411024041c81d4100310103006103001c2e916400d0125018524560080c04003180340d0401c8805405100503440c10800020781c05c0e55400d51246540c400d0b80c1e0001c4002446400c2c07844c1c1106040b05041300100a5a008010004075640110301801240d01030642c0d00301403411020503036154001660469888550000240401c0c207085034160303407000c405070000030720000d8004180c24030340000c6600d000080c0c0d948a6160b0016041c0014222244211160820383d41400302816010010800342c40d0707008040d6000801e8188600341c1c401c1c10040e0b5030280c400020307142c100303460003842d81075200148507a0424016503081f81400351612600f003120740780c41503082c81604003a4940c5840d00c2a0f0381507409100c0400483d1034840184001e1000303c4609a1700c180501d00f0195068190b1007078001e54000d42201004030703202018150fa031950100301c800310f4402410060340100f0030b8000260 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 657250494 1250 657249244 657249277
    0xc0a021c080702160b1602030102090d110f04110405010311120c0d0c1d100207030b0a050604150806190912021501050f150c073201030c050717 63
    0x520180c11100705070040c480350707081e9001d030070b207071019100c40070b0709841140e03d01d48040007007007201c8810080700c0c11103d00c001c0015282113070100000d104101c0186040d07403001000704c1005c3d490b250031480b00351250020f03102848024550b42c1840700c0303801503205850515813100c80701500d008000045803000600004a900d413410500702c54501d41d00080700114005142588117203c107030094150664490b40310100100c000e03180700c1030041c0213521619060542c0328085001c800181307864501d61107910020310000b440e150140400054404085d40c03080e0b04030100300280403441010038017941c4200c0b845444000c40c0500c0e107181004025180010740310380d44040c0d44400665010844d2141070803402c00b182c0943c0d03210010810031001c00d0704656400848011003403130544ea004003400d42c0410010680c0c0d002903403a40300d22187c680e5000004052200c5c0c1200c902a0b4404800f59223240d0b10a02e410091030b889148082c3c018803d191000d0103105041301c100a06441410807200051644520427 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 657251744 1250 657250494 657250543
    0x5010e0f1f030902010807171812120405101803031a0904060203060f040c091206150314061e04110321090111030903062e03080306011b0b0c0a02 64
    0x5000740200c1000f00e00083c6d2942c04600c0540c0700e00950884000298001c8109481d0700310b0030003100b280f480c1480c0c0c0d1401041e002c840d010a5100151841d8a01d52103400e5091406141c0300d07003009040500d00044a16000165401004e0340b10b415080591500340041d640007607514100102d203088032400d50140480e4108005c00000d0b401a5000c0c40c026140c0055a410100411040d00c0d0050039000003c4c44022080003400201d80c00a000e41303000720710000d0040c03021203088200314aa500250388480313165064944141c0c0801c019644102c90203504070040244e01105042c1e8140a000504a8032401180034441d0781c0901c651030007a00c00004101c0c1c1c4294001c4520400d404c0952018041526030191010f00040071040380c4500d40300030068500740e59801801c40c061400900640300135003448000d00d23006419603080304059400b4250342d50300ca2070b001000410700e044009112449071103120107c0c2c0002c0c4c0040c071094000050443d0b854503190014000c03403610b400c040180e0f501c0c0d060b40114 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 657252994 1250 657251744 657251747
    0xe090319120509120904020702040905010606110f03130611011410081506090c0a0c05061906050f0109060e01020a0c14090702030c06150609040e01060510030605010e0f1f 75
    0x403480c50107000603062129a5030380d107881e0b4403640c4000020b4583c0c0f1003080144014982035000307213001440284000740f81c117990345403182162120341010000c22501c0d42e02c0050280100620364804203100b0046143c008912110048031400344203403020300060a800c0c584014080d04800d045441502da0b00d801450318036070300b01440813903101e40c01c2a40141003242540d5070022a100e446401b0241c481c00c465100c000e014107a0b503012401c08400c109040c12420000744c0b090000303900030342010500c0344206140d001e00104960707881c0d01c040c4c802c80c040c401404041c0d8101c8050006c1ba1054100900600040d03c0180c2c145218618000d15000220101013100c40d10b070f1222601a0800751560865030b640d402042c0e039240701d1349a641c2201ea00480001d600f200400302510304070303c00070b8211230428030040049401d5801040d00e08400b0b03511038200b80914104038030010041e0b400c618007444841c2c80c2c00006006a200901068050350304107003102901e40f51a08114048058004c42c2e19640100050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 657254244 1250 657252994 657253007
    0x1e02210d020a021b0102030a170408120c19170402010c03181211010503190902040912120510053a0302030d0605010518090403020c090a090c0e07090e090319 69
    0x100c154107419035030650602548000141d4023050996243c045181440159000100307a008000b20307801071082080b60b8580080c83c0f00c035800340003a90500ea0700ca01d2507208e42c1ea0043e101e6400102004040da800075004a004440701d40c200da02030a040301c40000900701150036440458500c20390f00c400b8040081e03064415507071a26203c2c080c0c14030300702c8640c000004444a00c0156240201260f200441e0003150205605c0f140c1e80a00c0200f0000d01604503590301044144010589404580c08845419040c1014010141e000070004503c0d00c030b1a0400c0e00050002c10b41c4241940d9001500c80018004600400d201c0c0e45807848440840002605180082d500d5000c4079110001c1803c0100001e2503500420503909200c4031810701c1d8551414042c01d00c411103100038005e4003188194240014151650200e039401184103030b2000c078620a49041c04c5c0f41c0260795a000b50340f124400c508020a841d846000c41051302c0701f071031040d151521158580e80c55401103141c2200c142c103128000000190304a40b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 657255494 1250 657254244 657254263
    0x9150905031b030607110106050406030f1509030f0f0c211205010b07080315040510090c1d100909050f060427030e0406090203010e071e02210d020a02 66
    0x404039001181503204020102c1c006055964041d030020f80400c040c90300524440d81d826916100014215948000040503548a40e00550b000c946d0390203031400b80900301d02c01c249548013124041c444c01505a03402000200a0b002807010411425881c81e6100c1c8128061003003150041c1c4c91580c4440c602000c0502070a00c0d0b011900412641501c0e281804601d000e030700d04a5408422a074108074a0362680390044c5d000902541815440300706540c080e9455100e00341c054141085001310003414910510f0803100c0b015640003d00600c404d00c00e40e0220300e004425001e0703800b9030780242c0310485c0c400181d65100c2c6640190015908080400004410840c4e01e5881070104827001c0c0207513003485038a80b61170502c0403a0f80c03456122541991001c44e000c1c1d0240509074002500024010f656100d400c02281c0013078210141c0d82c401241441145503100800c0d280d16020450480e110120140c00070759185580400c181015440c14961504420f1000a5950b040c00d582e00656885031182c41c029110280c5a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 657256744 1250 657255494 657255499
    0x3060f060309031309150510051e042102031b0a15020f030706090b060f0112050601050c0102070503040306050106170412020a02100e01090f060e13020d020f120c07030f03090309150905 81
    0x100014107180c501e0000003008c400303445507464405c40d02d6501c4808200b41e0500362008078100000100e90191289490700d030310340d80420030491401c500c101400d00307880000b040380d20701800d500d0000c02d5031024a01d070308484070389174001d0328040e8030a81641030a62003101000d00b4000495944c05003c01508084441d0303200c2c00303460310f0941c1c41204124049500302c150341d00140c0c503544203200c0c25400ea8071154101e030b414145182400049002c1c242641d010800c1250710340c00c00700381041044140c2c002c1901504107820200344990090038024141c0c00024406880f0a60070800301040c24024400e0751002c80d00a08080d0751000d4140000d89911403901c00140001c0d1001d800040290008038500c054800c1941d0b1050007114050401c489501e850060301055903082000b0302d044841d520040c102111080800c41d111144214400807001c0d004001c0840e44c07108020000010f548003020b81005581c03820001155009800c00300c070154110b421070b00c500e0301c5205010030034540043c2c08070100c4808 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 657257994 1250 657256744 657256781
    0x6100e04111215030a0803160e0a09060f080f0c13090206031005010e0409050c01030903050405090f2205060105061c062402161403121201091103060f060309031309 72
    0x212000d142c0e84040c10b03217001c1c1c5042c0043c07001c00d00881210076240c81e404403c0c40d00d880607403504800281d000c01580d01116015549001c00c0004291800c03250004100f600064410100207600d6540c0701c1401d204558420350400e5000400c00030170703601500f0a42d0b00035041d81e03268506070307600041d480039030301420317000c42c40314440006c851601d4042d26000581c0000a80515650480190007030607291408405111040c040460240c8071030b94010b01c00d011812611030075040a442e000340141c00200c05c006101b200742c60000104000181490444405503030065465118051541c03a0442d20592030364450b08208000a10107105181301c08440e051101250084413000416640e56400000240c4038000348942044203045644002c146148042c0541d1071501002c0e50340e4000354803a02c0350201c14004403005102c40001407140302c0171800211822859402c040c00050340300742064010900c5000700100080c0307104030506c2910070644c1151a051121034039030241f0000341c030818890403048a403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 657259244 1250 657257994 657258031
    0x30207090f1a0337021309170712050f07020d0f05071409010528080a030905091905071b050a02090f06132c0c010207080606100e041112 60
    0x9010a012450320b6600002d03000d1440c142031980744003940e13070002800d085400c0d054140540c03900c4851075040b140002c0300140070756051601139041040d030405200000c4003400346500250b680106960208980d0800d691a54114100a000f5104081009401002d4540a1401c21560b01940d41e019445903050307400043d1500c1c081107902c031485108503800303401d51004000a0502140d1080c0c20b18038656010118440111841c00303c20340c503401000c4551254503c0b07024540d000304902c0180034201c42002c01400c00703541d101c000b08090040c1061540d95040420140c50007a03191045004064011461420050415a440781d003d0300c4142e004c0d01260001400040000c0c47c11440750344014650300d90f800954034080c00901090260103448822820400360404441c49204101d0549800510b90290680002030900d15a40d01c0040c25074400740030b22401d556945a40c40d100d0410b0b20300b03c0c0a2035020720008010b01a141c020850060001500d410300101880c01e10788542000b0700c01c000201c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 657260494 1250 657259244 657259249
    0x10060302090a09090f0f08070b010b1215192916150b060d050702010e1c140f2d0405032802100203031f0e0402040207030207090f1a 58
    0x440c8401e03940d0302a9000c01d06006416250b0702c20715143d03001d0741c400000508035565201c0000c1d4022000c1c0d03503000c00401c1e90010004402d0709035015140410b0710a05041ea500f101070124000500251118915055000d0700703900c0d0010100d1601c12040856040c803580d8a02c40e82300c0c070144680e00f560403110a400407c244185030103c3e5002d010340054103800b600c90f03072614442c04030b8246121200d039445006070b040c03941c0c0c7c07000035020540c0100000191400d041a010f0308444c0b000c0a014090340010014000f16558800d1000401c452800d1041072139484074002d9115225600b030214a00c00007180080c00a40840c50440f0210000c2c84003c0c402c010040d0107171114000d500c141603055016210b0b56104010720080100c19603601c054080061543c0c1d0300007640c9260102c3c0c082c0c0103a00c08070800c0f01c482c40c480e425420381c10140b0941036489061804410001000500181c001c80e0001200c034101442001403d000301070b0080200038500c00c45038800090801d441401c0c4488001400020aa1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 657261744 1250 657260494 657260497
    0x207050a030e030d050708180d12020607080117120a120e06040c060c110d03050d0207110f040c14031e01030c06030c05190e060904060e01090e0703080a08060301060b1210060302 78
    0x10b6081447e0a051405545c100722441088414607900490100d03205000242e201c0c40c0d406103607076140c01501c1589001e400080407250141e010a0b0090442c080c110035441e00810380c0e40201e031032842e905a031001c5032502602e000c2000d204005559181c240e0074208140b000c1045400b807482031055210780c0b66184400c488031041d031200648407010003460803440786007140f13911b0f501074800d0a015003812601c850f80d81c101d8000c01000c0d6021401d440410506240c003440260319142c0c100e80030440c411450000408160b5031201c1c3d040da00a0000200f55500440440011001440305c0150125038403894150751030aa14441d44000c00d05001c56000c5241c000c80c281c800d03c021820107011031945001c001c0392990100c1106540003141001500e1040d1031314002c2801030b00040a070f00c05ea95162501640440301d03200c1030441550440340f41480021604002c40341160841e103090a413503254400001d0050409510203900d446000852210242c06885142d100380324180030290440e56440040d001da = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 657262994 1250 657261744 657261757
    0x504020105180a051302090a0f0b040e0c071e03030c020d171e010801020c120c030f0c030c0714090708040b1614030723070b0612010207050a030e030d05 67
    0x426401d015000420403464200048000020b290f1001c0d60b5841002c01c0c02050702400c030709107145c2c002462002508100c005d942c0208400100018181d140908a1482d80654010919a1030001010400c01c3c51454290343d00641c01152540b640020720384103001c6000d151000b1004641402d4480c1003490002c0742e00400ca04198507205001c8454820700d1000c00001005c0e503a01c046200b0340003686000c080b16040c040c010400005a0305c01c140c41d20545080072041c204407403c3c504015000c611030000c0141d0b84022580704106407a03618042c4924158041d050202c0c0d1a841100d000241020030400c1200d140300e001d403501b0b035141e111000d04907400c5c10100d0b005000c4504440203d10bc4d62031180044141c0985454005074aa0041c072000070355510590310000080d04d0500c0044041c102180b108500c1d90301c0c3d01e44140b410200e03680b6641c0c005001411a03120300c11042100020840a404480200785d100017612070501480c90081d001c0c04803568154041d209100206003030ba405441110780 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 657264244 1250 657262994 657262997
    0x21c08010b040e070c050f0708160311040207080d020a020114180d08060414040f02010336030e030a2d0302030706021b030c060405010b100f032c060406060905040201 73
    0x18043c2044600b090f01d01014028804000951014902043c2d0921840426180c10f401a050032450311365400d10700170380d03081c1c6018000c008038010070020b110002410580385083d58003580301d11942c00c003d603682c00380500000f0264000a10107200c50390651000041c220403541d0452552158400c4003600c05400c0c04c040c100d81d000344c20090303043d40280403a940c041001480481d03050810b05c09002e421509807401c40741c100c8418a810304660b054011100000310100100d100500304142039500ca1008a080d90303c0010588040713800d152003100c0550700098054201c802603070300c87c03806441024510311700c0b9040c019201c820358101c08103c5c1281249680541c011401c012540d26880000d5011032112003c0500e580300040f4001001d0010b054442d0420340540141c0c83d00e801c000e401d40e8119440141300714114040c1c658002e800078000030200020707280014205816216070034001d000d2003118152002c50040c41081040005901ea1050744110428400e50790380c0c01d880026074000f40e0b8001d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 657265494 1250 657264244 657264247
    0x22030f0209060406051302031905090a0b0a060b0c0307050c010203031014060d0903201606030914010e07091803050f0703032004030623190b10021c08010b 68
    0x262070280241074001d10014400038110356103000007007003e981c50300d030484004e40200400030710841000d02c051100744441c0c803d1000f46041c201050f00d403040c0712030051641b8203400101d0000c20040d03002002a06052050698801400c00b8031340d52038205179011122441200b02c1c000440d44044184d9000c0c1ca0000d18160465081454000351500b200462030b1700300000340107002040f40d540c00b4078500703540030342c0380c9031481d0381c034401207110030b120100307194401d80d01c00c40c0501c4043d496118188120f4101d4500010300402c40d1070303c440d00d020f10b00754000fa19820070449900552003c5066402c440c0c0224041011030021400c001500840d05001341c08100306010010318582610014900f540c0710b458001003044070003a07000340c1103000204413800700c0790100b424010084148a0f45001010030300b90542c5030301700030204140c440d400510808809020400003000c00d0401d41100100b000020300146242004610096032207940c000c0e80d03003030f812200901c070030110b000724451410b0311681445107 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 657266744 1250 657265494 657265523
    0x14100e060103020f27090901050f180c030d020304052d06090a0806010b0d0c0806100e040b120d03051b04051c0f06060608150a050418020a0801022203 66
    0x154001c2d0440165451640c0d010003400f075515224000c2c20016150440c45d80109921319814004855001800307000240e140500b03100e03214507101c2d01c80c0c0d0300400409400842030500b181043c24500b503103c080e9058440e0760302600205401002070000d94500703a4002c0f21004000c2c8031300d45d45590070a1825032400702802078203602e0408100510b418880503000d030140329034078050340e85042000d90281c1c1c418200810000070b0080300b07004c0c0000140003441c105a0034205140055542440c405080051000c031101c00c0032552919044080c44280c000c2000c03805c04203035403442d52120040348031100000c2c6000d001920b12006840300f00d2041c2c2c200721086042500304810b01070440c0222890a0900e070700812070400041c2140c48030f00304a4400e4002155062420708080e110071700107000310f42d00348003810085005890f02c0380171000304c0300101c3d004039000b210460344256003490001c0c081d400c00407000b40814541e405400428403125100c0c21800c10f11141e40307060710032081038000100390807094102c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 657267994 1250 657266744 657266747
    0x70302120a0b1b191116030317060a05030a030507120212030c07050c061c0f0501051507110607031d090403090b1c0f06080111070224130914100e0601 66
    0x183c072250090040e02c0d450f00e80303804020703900003480e81070b51000662600800e1124400610104440c0c2100701c03144090b640c10342c0e40191075224030540c0101c3e410003660000703006540c0e002d201c0d4010f04018064030071024142c1001011a840144203842d41d00c00c06d044191821310009403c084038035000b100c00d045469403c0062580e40c855030064030a44180c4503216034590303070100144181d1030204016905914000000c1060b10144c69081d00e849180100401642d15a04100b000280c0302c84e08081d41c5101d903141c2108175103030030b503100d58108034041602c2d420190441c1131180511070088d60382d07800b844800c04008802e18100d0707000b400500310241c2007060310b420001518695070a0a0f21040c5080c1c0c80000c24121784e001c4030303101007840d2116800c1001c400c082c412402d42c2a460000d0511702050b54001c207801d50180c0f4080a5904251810005550342d08401d840390198145180d01100750b41e520504003400301c0800d81e07954020013401040e541d8603106440d074210ad040380e014001c1503464500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 657269244 1250 657267994 657268021
    0x70e04060204050a0b0910030b011d030a0f0317090606031b0414040516050109050d0b061c0b06011116060f0e03010207140105010501230f1209070302120a0b 69
    0x8803016502800046801d55031250f8038000f0b407014014803616604040204440044068668000d051800043d5040d0b6640b21a2110b000000004181c050404401c0800e140c80100309000e0b115806503e00001010f910245c0200c121a20454220245d146c0e580d80e20341314030040c2c4580b0741c150300010040b00a0000310104007240071008000103442551500c03420000c1e18111402c4440b50800d061401e03141c064000864060a020f21f0300c402d841c1d0814010036100b204525028040b0003840c80010103581d00c0103001a0a500404000700c1c04400714904018081d0080e2019400b01e1001416003840f507100088404a03030481d01403216510f403903d9005d80f0154000d03440442040f80440391040030b510240020000180300d042090100210418a40d003181c4040e0440c0e410420000306500003202c5400903c015440d005c84402d6032200c1d0080c810206100c3c8440003440b403403029080010899022981e002224001d1b2011b2806000000845480b80c2d2008002407002c038816000c034207600039084 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 657270494 1250 657269244 657269251
    0x90b011e0906080c0f0316020d0c030903320f190f150f090b100605030112201c03201005090a0606080d0f1422090204150e0a0305070e 59
    0x2400b54070b0309076848000d080d03680c0304865255051021704036950b6603990400c050165080741e45054071844018bd0740003010141c8522002d001c2041a90100004004100f1680c80c508904001044602c03042c0101c5600c41c60820300225050140001000508a0301500d41c01c500307600035000d03001c545036035031401c20070010000722040503940c0b00c29003039a0040c2c520a030156075005040385c00c1c0a15151090340c2c2e00e8680c5410007410800184010001c0241d451131350181e0b00d0f4400c154000e41e06a84a0301c520080c0356000c500d41c0715025030300009141d003090300c00405540c000e42e20360102210788181621034151100d4401426070040d6844a0411750315480560000d0038002038495510403525802c041d00c14031340007000d054109031603030301d406604103c400e4801c0410781040040107549400c03801c61405049a5521207500c40039400071600ba03910302a501800003041d086460795241d0340900e24042c0c0d2455918003042081440000c1c526001c0c1400084980c030070001e00310503083c40c165010042024 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 657271744 1250 657270494 657270511
    0x102120a090c0816050405010b071e140303010e180604031d0609180106020708120403020f060903060703020d0606030605150a110f0a02010e240306130501090b011e090608 75
    0x5070b03000b00e5050340c144402c42c00b054201e4480d01e5032900b850308010403180107a11115110fa410030880b03001465200f4a002c610340c0703017941100c178503005051042e0a4012840c040342103020000010403a102e800036100d01a01000c01000041812500080ea40715403c0d01c014001c43c04442031100b0401548810007102c07600540018101001d02c1d001c10b1840702c1c1c4540041d08141c0660051180507030402240e8000c00d0080c3c01400c03104035400396501c0390b01c2580030203030044805026100c180d0316424210b44a90300081c04550032442d0015005000303400a03500c24071201d060410000b0044d100b4050002980c900400104558240131405c9101e54400302465042c00300310408000700a00070b0198600404241c00944004807076403000411041180411030300c5070220001d24401145031039210740240c07800e0b492265031f0752112000610301b2036611300d62400301400c100000c0769030100e6401980081c002038032a6680c0880603126480c00b041c004000e040010408041088181d01c1102a1600500d40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 657272994 1250 657271744 657271763
    0xb0906100618090f06080a1406091203041b050d140c0f06030f0702010e0f010203011a03011203080a2705070608010e0a02070303140103050604021201020301050f040203040606050d1202010c020102120a09 89
    0x3c9880887c108400f40c41c0580303241d041c0107121442080306006d6280d000ba21240504001d0700c0030341c01c0f0320b03080c00b0252000e01142200845100c52800c0a8140006072400801c1050040480e15108015112902e890074103070280d08241403031030500840789520310304014031141c00c558408000c1c054000009055900315902d030f1000310302003982071000710f01c41a0740400141c1d032513040400c009260111502d132403850b19020001044131411703036074498417160390521305103510352980c07001c4402070894000a480301440c00721005940d908081703600500a403245082d102995512801078805d2007003441000880300440000401104061380200410341c441d003000a00194681501e11050500740c008440b542d001d8000e00082d407412000e420b541c0d0b060354009610f5507040c003011070b8418201140080c041e0b1303004404070341000456006680a80b4000d866030031444074609202c034a06403d00300341c00242d440d00080c034100700d01c1030084402201c030308001e84001d5150151004002c02d101d10066454008 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 657274244 1250 657272994 657272999
    0x60a1403250b1c0e0a1101080a110d0b090114030601170321390f0705010212010e10030b040305160b0c0405130203040c0e090a0b0906100618090f06 65
    0x141400036143c0b84105034590318039a08003005140403070700034048603883ca520020301c1800081300e01070500d20080d400e10303240c0455121440c20304098001c051003103856a2012508140303011090340320705a0010210380c101b000781d81e6901d490300e1220324030080b290985c01000050000c0010380141910301c1304910102c078034000a404c084040b03010507803400c07071000d6a810f0511442d01d22242e9190001c11144002550706501c2242c01d071107540c1a00c0c1c1c1000d00c610041a10a94900b401c41601c030070640140095646040c9181c048110710000d0080c24621040040800e0b0584070504014040d039500c48910300040c0c40e203481c256550380000d04503590b50900c01040c000080d090898442c02505000001c07525035007441b080058034801c0c0e100079540c807031041c0100408102e803551454211400c8806100b0541c891480a508008007902c025040c0c9101c1c50500c80c4075140007031207600c02e00164016102c0c05450340800c84030200e40192054115801341c00c24131034414240d00003080c09255482c005085503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 657275494 1250 657274244 657274259
    0x8031602030d0c0c021e03100e01020f120109230402011409180f07050f1c020f12010504050606040b12090f0109150507090b04090e0c0603010e060a140325 68
    0x1014092400f00042d0325034000d50442c02c1200b4516080080f0400740d5820b1158003002c00c2d44c8a94040746180d8003030300c403600103074000d00a6048541031002024825520301002d400c0b196445800e20078122040c0c0340840e6103000d000140140c041807118418083c195440e15001190901401441e905181d402000f060206582c0c8500703043c460314039440258138510b13045000d448403480060002040c080e0800c03000e04003a03556401c40e040b42c81c00b01030001c2000d07034106141000780601285240408000a8002c16542c10750340902d042b03800c1110709000c599a00400d02a07079000340e01c034594070300364103010f41c03101000301070b4400340c3c80100d50301110507521a800b01c05003511103400040e0740c10034142001d8800300c04e0b2400713881c1e0b200d080f900f00b50400500e4103070700e8102c1e440f423441181c50180da5480403240848091180c0000404c004048948950310790200d980d18070400d41380300d481685000d400081c0890183c11242d41700500801a01290000440e040c1c046198200240c0d14048002c40c08a0501d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 657276744 1250 657275494 657275501
    0x5070f24050711121e04081e0d02070b03060405150603070302210f01060c05030409021201080d080403270b0c0102120907050901091d071e1208031602030d 68
    0x21a0040d80428a070800030700141c6621986194800184c002c01c003800c00701070103441110182541c1d14510f00e112000c01d81c00b0701c03040c050307034110701041c1c01604808a42e040f00c042455006150840544940d62a00203007640d4030105031003840d241140034030008010345000d9002e950701601d4410a030240724003880004100341d00c01c4071070001083c2d01194040340c280c0350300da000300f214a03510518503281c01d0400303e010107554148203c1c0c1c1080000141d0034200901441624010911132400b03549811210741c0481148400f40100e10a0788a00207010200c079229410f41801290540c4500300110307940074030910344140c0000e5142c00d000e00090001120304d030100090000000d007800042e11511604004612200c0180c401c1038160722100040c0020381d600880d841c11038005e80c80000c1c05440f44031552068040240269440e40605d0b0b4000400007018652000900d01801c0047c42d129111031654902128442d40a45048001e000140d900b080c280c013142c0301c1292900442f03003003110750788125054 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 657277994 1250 657276744 657276803
    0x3010b0a0602061006030216140f070f140d0c05011d060412140706080708190507020f01051e040f03030e0a03120b0a0303050a18050d06051905060105070f 68
    0x6a0180d801c006070b82d071402413040084e01c1c0910382545030189a8aa0011941410101410380c190545400d0104c0c5410094400d0404480c1c069640c21562284011002e200300d00c50022500581d03041d81c0010b00d010a440903042340d00070000d941c406c0c02c040046440b401021040e680040d00201c0404941d6244005403009000d00031821106500311300e000b02c6034210004401c206944079481c1804041c0d0852200d075030101d030342c0c03810401668071952001240016010244580c62500701400441a4080b5001000b10b08520080c0207988600c2104070600755240c200c0d280e118440d2011400180050448000c7d0600a14001c070301d801220b8441820b10621141c00c602181e003004010068808600583d90081c4048821034007079072a685000d05188295807400c0100507640c00d1600004105003001c8016050141840c140800c0901e0440010101070b6000c40c4118500d07004a01102200d01076188152411b0303603014146081e0b036480759207007d00d4444c1211480f0600c0564031401d2a07c3c0105000c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 657279244 1250 657277994 657277997
    0x50304111309061a0102010c090b0f040e040b0a0509060105100e030a050111040303180f0519030510140a0908272707021b0618060a0302090907050a1d03010b0a06 71
    0xe241041345014280d01000103200d90669041c07030f582c0d140340da400080c0c00044541e000c000d0f9580c1c2c1c808075001c240b00d109a4214140300c055090a010a200303030480310310302c00d4140c2c160402094540d265820790740c6000340b0801e40e00c42c82d0361200d402490f10500b410013035014060202c61503803d05603500ea09680d501c121406c1e5504010408209140c2d210100699011200000004c814103100c080c451502060241d1801211292100b0340314803040720390440110341000503143ca9a070101240c10103032410034010740080110002040e00c1642511130000c4040e84541c14a2600c8080700b5100440303811030403504070b00001282181440d44460340442194801a00c14050010440131445101d58000d842d00d4110f5000040000c000307003035058006022002220210744502c6081c1c1644044248607030040e4000402185140d8440c4e016005031290b40012110099103640352202290280a0b03c0441d9000440d031320003012100c090550885910382c4e0260001c5020000000400c85034200d1703601850 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 657280494 1250 657279244 657279251
    0xf0c0c09020f09090411130e0303010909021c062c1e030403060e060709081f0e07090f1505010f1218050a14070b0c1c020a0209090303070e1005030411130906 69
    0x44031b6141c4071082c81488030030f0090400080c0c8802a05d0b96482c0014020700300e26070b5442d403981081d5940c80034005202c0c2c07a010079480c0f03181224940700340a0107001080110400c0260032070041c00fa080c8580928a200c0700c03000307054540040b60035603c3c00d40791b50300400031404100004801300f40340b4002e441034503079510000c024a042042c0018158501e5a21444007074200380c803440012100000d85c07210074003006001286200d50034140e541000c10f15030003000c62514120260101034465041200c041d65145104640c071035540c0c0040d80c00c0900841c904000a86252011065164990104001c54402e12144c0d10a0030159201407814003071103401d030341d00f001c9140a21201181001004080c1c035844021905200c8850320b044d42e03072203102e0500c0f00c0382d4121226080301288204060020103400902188845c20011806034a86d88180c0c0c0c8030000a4a40420075044d01780f8840480740640f9a641c0c0516541d00c649a11948008000c0150b9101031050409030300040180241c845a90082c1d8001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 657281744 1250 657280494 657280523
    0xd080313050607210e0d08060a081b0a050f0303070f051006090f05070f0c020909030d1d0d02030405010e06090d080a1709060c0417011b030c0f0c0c09020f090904 71
    0x505404007400713142030180307043c102e000141000201d00800c00030070f2410041801d40701c4030002500348185030080c3c0054440e82d8551101348156901e41c00341850151035560140d41c5600c10b0149009a17014160b415030300070441400000c0c510640687c405005109403101d003404002201c080d251554080104981c8400b07040324030b24101d110301c0b80c20100500305024519000040641206560100a8487c021020000d0300e454401c2c4125014502004010407960f40e0200d00459822040315103e00113200d00c0d8a1100d006000000312001c1c0e070310503103990310a0750691003003005c0707580015440c94000171441075900000792901d01625401001d40c540d000e0340d0350800a84650700c800141080a60f0340310038140f00c9031a120f4812a019200741c5070001c50200c1da0340e60001d01400c40e03600240800c4800c800e80602941d850307440003140003134075603800c1584d82d198070080301e90200c907401c00f4280a095510400419045a000f45069442d040f4440e0030964004002000301c80112801c1c0c60400b0360b020324 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 657282994 1250 657281744 657281777
    0x528031d0a02010207150509091305070b0406080c1b01050103030806102303060d0b091e0313090f1104090c02010b120a0f1a100e01050406050d080313050607 69
    0x40501044680041c520341600d900000d44e914498468070f6459080e41050211452083c0101d60800340c4c06032180c0814113001e17245006d01039010009588a0042c10720200d000321030281100c6c02c88000f0740d11021141c54140c10300840354426101206d803080c40010741c555080b0280541c41c029030280d242c41c1440d28101003442030b241280c442c1d030b07030405c60400c6102084030f04e61441c040300c0120305681607803a0b035640e4020419403841c02c000600000f44030800c01c00e6041c1c0008255454203081300b400c880070900c1c0c2000c3d035500e000300ca0f00182144c0000509004c5001c25501c113000c2d04101c80c0000c0703020746491401600551281e0031407c0b01c4d80c1c48102181d40650240141c011b10030301130b80c4600349202c0c904c00b11511482d1041000b0700d6030641c00906028090400d00d070070740307104401c0f038180c945050001c21111002164450605507072042000010280b406202e81c408580c005040002040020759445402d680000c0c440300d11032a4030742480d40810703410000340f882040c06484665904001840 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 657284244 1250 657282994 657283031
    0x6130e0d0e040e060408090d0f050c10112a041e0501050102031608030c0403061a0307050306091b0a03060e0a110603010315020a033b0a050607052803 66
    0x490081d403c0242e10f080e40e01c0001406984280c0003000700b5215005080010b80c903003104040505030907600314400040c09004038811100d0380c0701716541154200703d810280e6007501d4140380f11485800c0360340d6204041c0e4119145840000815088440c1083e10b800010100c03038a0105080341c22200e945420590380061080f00c0c05000700340002d5091200300c542840c549125080021b03d14400400030910840482007501c019541c40201880001d04018080020f0042c01341e40501c0382c0300e407903c002114140460300a001e00c6281020785400d0409007580c0591400503035903240c12000b11000000420780b02d10408a41c803001401812110b1a1800c000c0c8007001d00342005845150200010000911403500b0381040071001c00c805078590034008001c0c1c0051000041c2d40d01c80410101c850300c40d840c82d140058540c501e0f10300308000b140f1804500c5d166118201200280183d0212001c1203031140214042e000220328841c1c800701e4015440054035200300706d80c0c0008046a107507840c0c00e090151301d00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 657285494 1250 657284244 657284267
    0x153f0105130c09060b0910020304051302073e010c05160f061b02013e0f0f0307020904080d0c031a0105070b0a020f0c031602120303150906130e0d 64
    0x744103008081c102035080700305d0702c15442d0316480341c100310203900f080b40e0081c41176500900c00201038125200d1300310202c0029600141c81203c003038000005401d201c10b501c450b001079850110441118440c800b00c11550204140102c0a040c003103950031050000c1d204008002602d2214072005032007910b020b42d6a540400150403103404d01c40c000078080c5000c07101e01c0d4500d480540910b0100382e00c029003104d4488290b243c049400c001c18030084d10701102c110b051003a01c01d038184141182c1038903010109031921044078410403c2607800c00c00c0040050f15100c044507030003d01900c402850080c00c4558541119051103040002ca91910489440503010803241050740d40203003403492500e10240c0e40c0c1c280c20440103010342641540030510000c0c2c0a4000c0540d076007881680103c03a42c560005145200e403c941d520128441c11000c1c003001218040401500d0040c9000c443c01800d641d259000c105262000800c0e443e0040c030581c014030781d111660f0158034841d0301208081c100d4a286803200078400030500d0f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 657286744 1250 657285494 657285509
    0x1805030a110708031c0e0a1406010812030105090a0216050c0117010602031e0f07110306010f180903050d020d05040213021c02130503030c06153f0105130c 68
    0x40c2c040082a0021045880711510f000c101d0070b07100b1407403105000900c1110b50300d41c6140b0a200035007080120300b800d8510890300080c112100c1e0713071380ca40e42141e85802d40720100d0310003a001d2004100c1c0c3d050212080d904581805405400e01140400042405170640419141540000300700c100558211001040c820a425002c000540c103100c0c0c00380d9207108100d54208400c07a043c00700200408800e069415403048810b03450307904d20403410094007201c61403c8441c440c1c0240d1307000242c3c1840001c0318204907070800003802c0340c03000103501042c0101203242054003071040410801082c1c10a5100421f40792010400c002141d0820340103002082da040e1540c407075140d204004001d02c0800d000d0041c40b60296a900141e507e180b4815011303444d11103903102c0d50f054840441d50840e040804100c00d88154940007403c125141c0c6507040041c01e4421000403030101e0030350503070019030745559240c00541c0c11031211001078064404040c5400c50383c048032240560380b80140842c0420480805a40050020 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 657287994 1250 657286744 657286753
    0xf0b0a0e0c060304140705060c01061701020705120a18270b130b0a0b040305030306010216030f06110c0d05031602010b030c060a1202120406060603020c0601030204020d1805030a11 79
    0x99070105085110113030000c4d100c00703842c54844203121402c20451002c5c2070094801c13501c0396000852140640800e001e8800d24021260001904031014404da510540d0007c006200140f149070ba43d9050768040d04100003004000c00c0320125034686081401c0080040d8403c802d40e103548201c21186403c140c0e5202c4103200e040441d00f4401e641d500000c2c4c00e100c4210f00b8002407001c41c0381c0000710b258166a10048200801160020074440040f025513c0749100b03800b5034840502290307040804442501008041071100d041003004104607611665603484140102840c040803000c00628100050360980d001400003c02c004030100081c03510a07031121140028000449900c00081d01d0b2149404154003030200481c5200380c15120300140d40001c1441103003150303100040c40c03081c00943e50031138003a9059802e01c00c000513580d00c44d1003107034000645140036182903400c1d83d0821029501081c25101c806480c0d07000000e1000186200a0307025100d003008641e0340e045400c0203021404d4100e00680385811 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 657289244 1250 657287994 657288013
    0x50a17090d112a030c0d08130b03010803040b030c04030f0c23030304120f0209070908070e0408030a05070207210c14060406050a090e041415070c1e0f0b0a0e 69
    0xda140e44400f00002e00010300080100070303030110f464102d401855680c0041e1022103c1c040c400100001c0056503540205140b40c0e54440003403c80c14402880313143d400d43e001304002c0021541e418003450700400600d81192a1550b207445500985414110a446000d0b594904122089030020b40071001c0100c40403d4403045080000241c481c01031b0700c1115104505d4001540401142a4490600660050806400c1d082c64440206802c1060048180780d02c1800400b1440c0c2182030071140c81aa40402081c0c59641c80808110140c50301a00002c15881071800c0400c3c0c80285040f09421202601d1807c00e020b140b90804444001d4140d01040020004c040342c3e18654450f841200d00740c82c8141005540ea1402d80780450b0300d1281036000010201400050004010500304c212030000340107012908000496010203040c010180c9121000c194043c40c0140000e5607070710a040d05110f01800307170314001d46a031034182211440d810203c600340100c0e010005095054414508240c20783c200500300b005 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 657290494 1250 657289244 657289273
    0x10824011d04052409120906030123120f010b10092102060304030302030402120c0a05131b0504080d02070b090d02031e01051e0402060901050a17090d11 67
    0x192000059031001102000a002d100c81007098403240b48140c5281e4142c1800410711054001080d52004458010544101c42504101040c0c1d1f0382c5070001001c841c916480c0c120b204020708008a0400c07030000c000d110000103540d6000030a40d00050304c101500c1e00d814404822401c541c03030903202e42d1043c0003450715104040c8d0700002000c20f44d2003450324002c1d8020007502025171b803e41c119000b5030003074000040108040c1d050700a10300a6100307640325454640450362164884c28049106034020030803180400241c50700251480c08a101d1f080009401c40c0c011000f15484c52103c0e07440008520001400c102c110010004650b08034494409000d086040c0f2109191510500503094440c0d81407142e203405558050001d094442c01c1003041d41c03180c00c4060003a5010744821a8800b0440020020650503181e1002440d4400d643c028a61841d0503942c000646070358004400301c004000f010050040305684035803001c0d000e0003c032402081d000c195000c008140040c000c54200d12a000000300801c00e1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 657291744 1250 657290494 657290519
    0x150408012d02030601020f1b01090504020304020d030806060d09060e06060d08031518100e06150f28050712030b01050d2027041103070804051501082401 67
    0x810840700075a40340c484c400101d107003d8141c1c103c16014000e10003000c407a00c100e800c0b08000410281c80e0460166580c804000490104071400f03034002c141d00c0740c0701c070000344250b549640c0078400501643c01c05078410480411102100b1041700c0583d9100c0003940a48010040340b60320000844001a103811503a0396541d01780405003a1036404904024180b0507a075808850342000c8042ca10a2081d910303000f034500828602d24480d082001055501140b100d0038001a260341ca40e108804841c40e00580001c1d2040a43c0724800303c44035000d100f80c4010284a0046141d100427080b691202c0e00c0c0c0359a0f05004040354569140b1106240c58407400c0740c441c4c7d8101c0e0a65051182c0000001040da000c0118443e080703142c64440b17040303c440010f00b40000050300c1400100d01603000c215408066090081c801140d4030710f02880305013007041c800201241c0c850b66803168407038802d10a40d102403c0703d0100324680d80b42070700700c0802c1c0d40080d8540d03503c0280301400c01005d09400c0180340d210703516108103410761 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 657292994 1250 657291744 657291821
    0x1103060a06030c05070204020319050a020a09031106090612041103060103240e0f0102180a06020303040b0a06030f060e100515060c1c1e0c022d15040801 67
    0x9050f210001d00c0d12407801101915070180d0042d00642d52440e03c0a1038200d0302c9803000140d0102c41c646408074640709905d01c02d4680f48182c81c0c03106940c541c155101c40d01d554039000c10695120000b00b12410813503c1d51b102504807021101c804e60040e0a1500d0301e1b0880d6a03100059074041d500c204010000b00d000c003140907200780c403c1700d0440482d031b81c0001d91a000d040241201010703403150344a4420411015401040b41441029440b11020060320030400030754000c0c402c40c1c0040c1c1c070034404280402d050b0400517030084007201000036203980d40d035154019204840000d0f100c841d83d40c1d120801d100ca0900c40401201c001d160104410300c0c044042c0c203490001050642d00035500400e02948148041082c0c00010755020081c0300f941541200041c210240c0c041200e00d5407068070203100b00280504545400790b58000d04040c0c4984003030b5808040c0840d074007110301014103007141c0d0141e1074650345102d034082c01c04541025034540c20405001e00b51442e1000046a050707491148405a10440310401076 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 657294244 1250 657292994 657292997
    0x40507060e062a0c0613050103270503040603050f130b0a14040f1704140f011e120605030f060a05100b0f030702010b010f0e0d02031e060a1103060a06 66
    0x1841968020442c540990781c0b0004140d02203040c0560b8005841ea00e016492010504032540790300404240601c0d030107505100800c0d418456020310480d130294100f49447c224001c40d080c1c00c076603014240b89600f9003415059440e5040000c00f400410b038903009259003d402c205240c28141840518507014010128016002010410200d03084056540040044000c8034081e80c520b814941043c250644080408881a02840360584030703209442c8141d404503000e198510640703502c407a0601c6800d91407412050704025034801900c5940d181d15034005850200d981d214203200c03a68640d19070440300d054203d24820b40c026401404003403400520542d0100d0000000705690700c0314040310340c02d21b80540205401c1a00031495082035420400918030510150303000b40401c054440c010341d0800d40049841001072441c0c0200c08640c106100c21246640c40681140c402c41c02d0542d070b0ba8032445680c1460700c103e41000007400040d0708240202a01280079212581c0f460402d2000101e40d849540720b05c10 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 657295494 1250 657294244 657294257
    0x901051005070b370b030d0801060c0503190302090a080102090604030f0602040314161a0d0207050f16081011030f040c05040903080402030d02070e151c05060115030504050706 77
    0x144108880030341405940c0213945601e2985984100c102c00d500c2940e82d00110141c9803001100041c503001501a12030f81041d107030a009a4200f40382101c081844040a44261204109003c5141c0c6581074480031403036550781c0180c41c0c4285c2c2c0101302c60038415510680d480d0380140810741c21681e5880848080300e5001c90940c800e40410314000000e80504c1e0301c0a06420001c0d41602400040465078249403038503007007903ca005840e000e019114503d600c42500d0368880c14808440340240550060440c10b010740119003041c0c440c110032034130341384402e40b000821007020002000000020030420719107295080050001208032074a40d1a01c0c040180f0141c96581050081401d100707150320040d014000182080c4000c200e241805030030601c0943c4c04030700034440c2c5510301810394404a11542501c85442c41561152030784418507149442c4180140ea00002e1100410102200c1b40f080d80d140031b200d140500010340c9000300302040e22031010030310401d25091004000c0011400f00355141901e03a2802e052 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 657296744 1250 657295494 657295501
    0x4030b04260f0d06030609080a18060c0312200406021509060a0903090305160f0501031e0e120309100b1203040b0a200615030a26090603070302090901051005070b 71
    0x8070f02070226030b03201400a030307c0d001c290018050403a00030300f251216521054601d994040400c00d02c20184d105110010705a03180c5000000d2184502c41c1480480c8840400c852004052144400e5020f001c0011901400207040090507010b01214440d00075003202080c40317242400199440e10700003016203440a541d00241c00425000310000005150044c04130707a07096101100000920321a40104250b50310518030005056209001e0101c0400070105098910046c81c884040075019040a82c2600d01803030842c6a00410030351b02035442245060010101d00c01030401d10000c031480d03503030418069100c40d8203140010300c001045a045600c401400c555802c41c10004443c11000441010350b00310f66a15003529109000a15500a041b100d41c01000070064a080513a9001d5410b00140301d084600c5600b020f0303006041d1050407500502d00202d2814601e003001907041e500c101d03400c00100358003082094640c1030101030300e4013504060303078856492a5a00d00180043c01106001800410b601002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 657297994 1250 657296744 657296767
    0x3060f1b0f0228051902010e0a14010809010219020309100804051c030b060301090e07150e09150913030f080408070b07030b03030a03060503011503020609010f1404030b04260f 77
    0x15860200d42244c00c3d41c0c42c24445550541800b001c012060340043ea4070010401c0030301d4580051000c4075410030348c00540050420043d99425001001600301e55424071181d00048441034200b040301e0b01603400b841e40c1d210000100a020402508a1410010094108000075200090600401c14007464491100241c40c008038060f080700403542c4e41000c004000001e500388142c0120143c04845420398551907203540740d82d0f200c106a1090303000040c1c44c0c49401d010358109200803e8100300d00b0464041000c005502241d101300d02a2001c0c1a941c28008146040c160f018a81102c62110b5250140036420591154502030103181406012000e2020118241e01d02a6005462864018055984803681042d002e07009007094400c041c007035400e198460301245540e51429080d241d00510750350500c1c001d003004407201c9020790748030820b10460480503407000301d588010300000c600c90008180e1500d060300d021134001ea402c03d50710800300040500b520b654840b09042c1d8080303a4034091560b4031002030040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 657299244 1250 657297994 657298063
    0xc0d05010e07060e01020114060a0b0912030a0816050a0e060306030a05060103080d24090506012d090509041a15131406010c03020601120c03060f1b0f02 67
    0x10708051284003800558560414141602c00d50241c008015200203100c01540c0c1d00c000311080383c0c0c0101c210f0700500030081110080c042401d000b9052a900d0202004c10350b240d940034144003008a5464004c10100c2281c03034090518003400b51171701c030b41440c1d01040050035280c02c1c00d00c0306209100100002da0b440e02c0402c03142604517000000c0322019656030901c01116402450400740007800c04030900b048001081600343c00f6005042c08a8210f41f5185410380208800b600d92030400c058484a078505641c0b0350700d261503551800c2d1460808034040c03180078003010703280d0740864040c2e02d1400030003000c5000b401e00b085400603507411000c003581d0b5004590000c010a0700103240d0007100684103807a07181043c1d02c03840c0e203540100c2001106031075120042d1402d0070540c7c1c000b00140d020100521041c030000740c9915142d40f10f210350f80902030700c1303941d4001070307554695460700f030103179903e06071031040c1e281403000113940d000b508100c0b208152141c402915a00404042040090301143c40c441030000d020 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 657300494 1250 657299244 657299261
    0x118020705030307120c020c060f0a090b0715050106030504110d06060b0a0206090712051b0102010204031203050a0515030a0201110a060203070f081612050403141c0f0209030c0d0501 80
    0x1c1901e50320700d030850000e4007148806480e040d0701840c00d04046600743c000114050040d2005200605000105041d0980b55200040850400020380f5000601a00d106c4c0a028014458207010398840040c2d07520b0b80849505070b01100825040200f4800413aa0740a0501031411003910003424504007400c02030003a02030750b80041c000d280009201c00d5020b0380407030418091000842605d0107155605003807002c1d40314456024007590072210350a140c0e810549002000b8003410b00004d0304107a904d8a80048448140a001d00400d03282c80c204a11401c0900c18241c1c42001c4000382003104c6658008682d0350004004000c1c107010300003043d1203011900304400b0b980242d01c540103640e28a09144001c00c00000400000003140b960004a010404400e00455480c0340c0c0d940c13403000c400341250000c00070380406413055080c03101943c250389118030040e004002403145482d5601c20010304005c10300850b24000d511031412441886214a46c2d500401c030701c0112401282d03107041981003400d0041c010410b00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 657301744 1250 657300494 657300503
    0x717040b07020a05040b0f06030a0e03040b070308090604110d0320030c0607050f0304030e06090406031b0f030206070308061207081509030901210e010e0a140304060801180207 77
    0x10800064514890009000c0750388250b9083e00100ea84000b80002d40c0e01c801202c079440a0a0760250f40d0600780600950340c8030040ca040803402c46840403c031030456201ea00104d0011000040401c24140c00c101d005811280e03440040200b0300c0c1988030481c00c440c40741d145520491408001005143c03248401070005000c038181140004240416243c1e254040414204a8041c0400003540d00d80550191540440314102951550b0b99541d0126102202100d041d6440303070050040d810305456500c81d180145101d0813100302000001d800c03030b005102d40ca40c800050402c165200b400141c4a000a40e22195810305101405403200400902c00c0040003060080c0d88c4030b0340c440040c000300e00096602100d03031450b040300750981716260b40c0f41e168402c0d160011302240211903441360280a4242c1c03c1c22410350444c001840b41d81005215082d41d117004070046560303201e0102c5c4424004144165400302404400451801d454483c001d00440c0381445801007150255150030312850258044910302a8030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 657302994 1250 657301744 657301747
    0x90415060e1501111b10140313060e030c1f0b1f0905010801030b040f02040f020414090c040315050402030a0212030d140903040530031c0218060717 65
    0x5201602d00480100b04028000b8030f801d104500d0455001c1010441c2c00c0c92060414017241385417081c0702c00005010009010044401c1c8070845070304250014600032101041031000d4a821030604806442018014543c3c50b0010010145445800200da0180c0000c000100c1400401d69603d02c0c0205030f1101d1b003e40013105900c03c0344a0b51b07408692100941c41c5500c61854003500c1c2c40c01100c9504090000601c102038032008100410f14026481d0029440184081a084000070707a001c2680c0042d40101001a141507015a540c50402501e0b580815074042003400c05195031104204035403186401d00341103a580000c1015920188100b5031900c1c0c014041c1d1001007040c110065690b0b2240214000d101c5c5840e1a481119a5400c1128015040300c4e000b1070506c0e04100c10044178825508040e0050b402510324600d5240c0400003407405030210f5005162a83c0e044140592002460820214807074030400001d00300714042020284908000e40e010b60b12102949400c0f030b00d02e83d030010102c000000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 657304244 1250 657302994 657303001
    0xc040501052d120f071a3c1305102a0602070b0a0f06030201020d120603021306081005090a030e01170c0a030f020f0a0c1b061d0f090415060e 62
    0x6007000111010b08110741c446030b51003004040f06c00a91038601603e000801030501d9002d00b110416041003e1a5424400d604036411002210307000402c415241d0013010840c07007030071100302c2011801000240c82001c045040d01d240240441d56544511400344004000d0454541698151030503042c1d0210302156039540c45c1c00c210500304070841b0f0300c4032200c0c1480005d0350180c0582c090b82049903410b80080c5440050480c003aa24006c01d131682d980782035603a9500101582d91b071440341d1050a40001c0c0050160b0800640d241000c1d0381219924156081506010504500081c00030707120b5058908507000310316820040b1030790003030701810014005080042c0000c2c08541c0c80181042d1005031002c001d00800c40d1001001d038000c172817042655542c18402006550b005080d8100310512910402d5001590703003000450607940c540012000070300141e00794903216100c0719980144034080b140082801c110100141122030020001403841c00740d00d641d42c280c10340d150040e2001e08840e4000a000e4503 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 657305494 1250 657304244 657304279
    0x110405040c03050d0305040605070e13111e03010503010b061201150c08030a06080c010c0c0519031208041a01030807200d0b0f01060512010b0c101a030c040501052d 72
    0x241ca00b5200c0714070f4500410242b80c000c0c024980c0904006d041242c0b0341074a601c0e241d000700b400e0440d02184100400c0070741c810740360812490001e8542c004020f07490b541000300b410308403089603542c80e009241c00c0100891384103068034020704540c80030890390000070100c0340446150144075001080e800010040c40750403107480d004a0103960b40f1000301c2d00302c080300400440d1040b000c6400641030140405c0e0030320250401401070707411440181104104140d903503540119203082d0b003001800264400d001d0004200000d440f41d0200030344100704207555411034854100b548240c0000809440403200000744290680c05020714419000b080313440d418503981081107018200f203071059003c030044000840e100d80100241c481d2104480740b00f2500b6801e06d903030b101c915805050380d07103118400c421019141012a01805040d0011210010005907602050501c0d21020119062080f0b003004c006021680b0b60f4000048003040056540049100440c40244440d00210380c841d08220140c41001c6281d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 657306744 1250 657305494 657305501
    0x3020d060c030c030209010f0e03070509091005010801020a08011824060e06070c0501050f0408010f0b1009081f02090315070810060f1116082107110405040c03050d03 73
    0x40076a28280080d106508048013288646032050780230408541007059254400c80e443c0e040d008015040b642503503161400070300504011100803905502110203130b1560015401183d00400c920002507080401d03001c8040c0400d541405182c83c1c80c894030117280b0702d054403a00300030040d102e4500500840714510800040600050269401050a1350103182c0d00d4140070080300e071101e421149451000c1d00340001101c2c0c0381d02000340c0b0010480140004900c410f82031150703403e07070000341c103002901c0c41c140c2007805103207030340880140280b0014400c01c0000180108400350b403c041c941000c0d555150640c03091009000312101c868040c840c8042151a200115800b28064842500c0f103004594a0303041d00c110213501806030303000003074600d04031002d814060202d01000e020201d0a81d5007401031041c1d21004942c4d43da00c1100d4990040c1a664000701d00b021040c04049032402c01e56103099401c0d06c40180c580f210408460044d541c1700300003414011880498005540d0110030359403c2402d10b140280035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 657307994 1250 657306744 657306761
    0x4051c0507020307061b06060b0d110301030b0a0c051903050114030109050709111201140108310309031e1412070f0215030a02071e121211070503040807120503070b060a03020d06 78
    0x100c0d240140c6d8000c64441401903374122507100148001c96600c1d5411580074100040d03441c0d06000085c40b60000700d100442c1841c0200c0100d0b034000030750750b140052503440036401d400340c5802a4034014010010400203c0d18006450302e101c80419002000700c207903502e078070900041e00c00e8402c03010b0000c1f5240034407840283c85100300b6070314482d00d80c54a0302e10303c00310441400715100c0c4104400e0000ca0080240c9503a0303100c2402814140b04d031a03500e8682c440007480c8003602300e048a441215201c1040800500c0c151105141c400070708030441c84c0032000100d4804d416014142c1c410144650086542d0807500c1d4505080c0ca00c80c00e51a4144003900304080c2d0050803040b1903a20b0f000300043c100e501c800700f0092041d070700041c0400038011042401e880c440311411000014130f44498600c2d41165189006111661240008581d25441c100c90b8a08040e41d542140300d846120401e01004030b14008161803a45401400c904000e80300c2e4400903c00c0803a42e84025040110495050284911507019288 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 657309244 1250 657307994 657308017
    0x30e0409080405041d0a031b0b2d07091403100219020d0315050f040f050106020a1b0e01030212030903120405040b010305010509012c04051c0507020307061b06060b 72
    0x211440505c00c1d518401c081d4170050038158054800e02d000f191040c0d510165482c5894180381e030b02c03041c03600c60800b42c0c0fa04440fa500100e407141030303582064940c000c845150803a000201006403c080000034a091f10500c10000f00080003c100c0d8240d6509203c1c0388000000d0100c115655180c15503039800151000400c000580038801d00100c11074003e008003c156080070354525804d80c100f00401030200400042d05400c42d03039480c60704d2001000c52040030301070007031074005000612142c0380c11500440c0c10340c0030744502034414504000d5610040a00344c1582c1d4112030b081146610300042514500580e060658140305242d14007058010080041054035001d83c0c090003c03100a20043d400d483c002e102d00d80d00b002001004001c0b02c3d0f140c54001d80c411003030417a1240349910f0500c080203104001da90030f50320f039006020090340c000c07440300c4803103401c200c0c2d400c0c00380c2000c010790008ac0d00c1d54200d00c920b00a2000c400d10200d00402c1c40d00c201c4480d80d61044041241d0b5440d0307030404100d60040983c989 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 657310494 1250 657309244 657309251
    0xe0105100b18040203180703061e0b0d060207050f0607090f0b0c2a09151014070305030a060b03040b0103030e0d232107020a050405040308060d030e040908040504 71
    0x1400400303890441d0144046070038100d02c0000c030300003404000d500040c0003c005064040c0b01a4848906002420040d406090007042c5418080c103e20000c0201c841803080c018580013950141c1c1c0c03240d003441690b05400840050b00c91065050590030006910100309031400340c102005041600036000c4419642d401039102e40b16500c5404242c240d01c107240304020f05a100450035201a040f8000d00580071118800c0c4c030304103501a0300031072212a81030307581c90b000c1c2c032024554503924102210030b06c041540c2480d1170001c4407910180385115100c1d1107806420418000005006903040c0c0e00904003c3c00340540060356458207003800f0051000c00e000807000211100b9550741d2900e05009134055268000881e45901d800180060300900e001c40388034040d03401550840240c001103503001e0503520352071040320359030782c10745204001c0b9500f4160000e0b80300d94500310a000100742e109140b0360740030706c0649443c06a81c2d0035045c00d407441000001c00c581c1c0305041c00060b204101128010b001120015581803 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 657311744 1250 657310494 657310499
    0x6040308031e01050f0d0201090f2403060302180c19120e0c0f0103020d0e07030309060e1005120a0b12150f06030303070f14040e01140a081009080d0e010510 69
    0x1034201800138850381340d02001d040741a03001d51619204c01e65032584141850301e652542c841070400c007001280c1c00106e041c0030070390240801040310013408101443c035207400c000d40340c210740c00203848014484242c0322031103d40e000200e000c42c40804a03035116001c3c1d108645000b41c50316000741461221400d4207101030810f803900c42d20070310004a403081d004000300742e521902d0711840114002d4100c101540c3c0c485d81c5440342141c00d20703420300108002d14042d83c1e03100019410000003800c0c92008102480c0101d03d541100d190083d4003100b81c0349a5507031400307a450907442d02c1030700742c028110703685e1640e5000c049001d09942580c40050307d201140c0e202c00c1c44600399038884030a0400b07e081100d80903016002080007c29061088041040140e0f940c20503502c1e90390b5890050000b90031607007054840c100140b0040c40540300b0702c4150000803004440e070415407170800414035107803034014004006075038840402404121140c81500c407900382c0f20300c080184840c2c811105028060a8450045d9240d00c40c402 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 657312994 1250 657311744 657311791
    0x60b1804210309020d05071a0a020a030f110d030e010b010206040203030f160f0501060f080c210703140d08060909070e040201110f060f0c1c02030c07020604030803 72
    0x45510841e00140000d8441e40c84418405816001080200405642c0c0300400b0050b910084064005070291004203400c50410f6103201604807150825000c5002c02d200080007181d0010b400c1c40b080f90305103003c0c09005a82e180c180d81c4a5200011903645000d0980e00824440c1d05500010050708450003c0c801c443c00c40d0016a102c040550f000f03509a00204108000740711140300030402d25800c0c1c00f05041c20a0765494101c0d010703c0095003251103035181c4408106203007881c038040c000350903614042c0803290180000601c02d146d580c1c11003a1189084d10b460300344918140300600041da00010b9203c891090b1081242d00c4000100c48117000c1031404001c581c0c2070401c800082d11803002c800047c1440f508001080c02440d0009004a040049440011030895403e00405041c2e010f035600416060410b010f10141c000001003034049110020700442e00d8443c0842900074155091060050b502e454809103000b90f4031580c60080c0d00708900081c0002045803510003035103e012080555560031940950 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 657314244 1250 657312994 657313039
    0x30f09070b090f040908040b0a0e030607032315040f0618060501090b0315060c010c0201051f0b0309010213060906030609050417091813140a051906110403060b 70
    0x2e035070000403220244000e41043d038811054580291103041c2015901d40e0320701030b40d0b44200060380004003041038003ca281000c00070709400816908007440782d20b24254030521400440c007540c903c0c050189004c91000420000051819500940705100d12202c1401440140c44284101c0c403400303040b049074103a040701510404055640c145e469030380040c40d1844070b901e05c0d0009402c0c103c03545802d05440d01d59036a203c000707249082c07880d000401c0380c07010b60070041d003110307001001c56084030140803a00602e00f5202810307030161990381800030340301d0b01c0d84100c26009020b04120308400701d07090030010075107a800004240403035040740c1d010302429850b0200c00e419503606460040c61020040044031b441807a49024082c0c0000207484113041040410f140024043c05607401d0300c081c8652140041030205100450200d60252401451112440d90710710b44d81d03061014000034100c0882500380100105078001d0011032071203840304d94507151207041201c010007459a81030b10441c1100050540d00450f8107 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 657315494 1250 657314244 657314257
    0xf1e06110405330f120403030e01050a050c031305010e071e14060708180d1b08030708120c0c0106140a080c1302030a020c0111070b060108040c03080703090803030f09070b 75
    0x905052044441c2c034180b12594000003035601c401d4805002c03681c648417880805a200b0380c0280e90116030440007490503802c441c40070b020b0450b650b0901c1d08200140e4100700440341c1100800300711081c00d400500300706004106c400d00d0004580242d840028290303445020314410300d100030301c3c000b80099584500030041c5001c044201d410200600c01e4001180991001c0c1c25041444803000d501a00c03500c0029690400b01e1204030780c12052103000201428165001d480a001c000b0011442e0107099100c040c4240124180d8899115800f4001241c600c03050040d075440759808402031001949801c8009070350450000c0c0c1500541c1803100000794201e0005120784406006441d000d001e914080d111406984028100c0e00407903006c100d29810000244541c89801d100045280c5e10b9080d24545200e84c00c1010309110704020541c0c043c0008211502c00f00800c50b0f0348841c07003e80d665524601640c00c40312560014105005c0801007102c494101c05006100d0707c0500140d900319529001c10480300d01404 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 657316744 1250 657315494 657315559
    0x605060d050706140d02070311160b0904050601020319020102070201030b150316110f0304031509020907030504061418070605130902091c031d09040f1e06110405 71
    0x82c501005581d00402403a0b0b492503184240510f032044109203002a1fa2280c601103000a000c41c0380c000140710184130041030b03002031600000c00c00b860810302070326034081d810038284240d5480300400c05680c0200202c64031030020b11249181189450400703070013034100300001c1e40403e040607618002d034a40740402d042c1d400c41040fa03080c00d586a052407a000007004e81e08000900200c100d0569031107508002c551911400000150b40e10707801e5141c19905030031450104080d240c141103c0c200140d54440182d6403186e03a07464000f540c1d41d5141000000340071440c40e04e41d00d0310049003c1c020748013020500c0003205da89007400c603907603036595080032103c6100ea255400c0e814052541c0a11040e991600200001d8400030700700c80d150010180301f826186c032241003c8010901c1d4a5100d4030720341d002201605003c00c100c410300d1840c941603da102252103030b44002020ba0b202012545881e14421b230803000111340200302004680301521003500c80d0b40c018010344d4410520301e0340c9404a400100844070314803182 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 657317994 1250 657316744 657316753
    0x1c1403040e1302040e1009060e0313051e1f020d0c2102070e15010207090b01050d020304030c0c090c11011b0c0203030c060c030406060909021e030f0304120605060d05 73
    0x2514540344101c2c1410030100d078080c0e1102052400b1200c00c01c10020410080780000400440c14646031084449003202400030b90000d03c901290000482c1c90001140d4040c4c6207841c1508050b1417103001d04905410b50741d4040e5400309804081036054000c6956400d0039002c90788d0300c1d44052000d0b600c4006d51200103041c4201203480840100203901083c42c0000d40740122000541c0b00c4c0d01501401c00100c800d200d00d0a5a0145250f43e0341e4108128002003070164001c01c400517640000034110300c90900440c06198000002c9000c051090080003800394014055a05403030300c0f02c3c10000501120104a000501d82c00d0001d5821001840740320541c0150742c8035125241034059080c0c82e502c41c044000d907490b000c144617400c075100082c45100c1c400d03904420460342e203182515041d412aa4190001410300d8034280ea2940144c4854071049c03240d0390107220100d00d00b5002c1000900d012a05010050340303004c00314000858400c40047c21f0070181c420f1205018176a101c030240310400c0710303451000c1c103550700 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 657319244 1250 657317994 657318001
    0x405040b0103080c0c0d0501050a1b0207090507090503011a1315030b07140705010e07172e060801091e0b07080702030d0507021c08010b0a0e0406051c1403040e 70
    0xf640004000700404035082d50b000c40030020016148408480f030581e4143d4440c410000848414070412800241040c0d8018080d02d00e054000d5489070640121108960303a0804214031760300490640c0d005210040c001c0c003aa00e411080703122120140b040513802003070f51840110800600c1d020f00030172950b50300d1000300120728503200d0045c0508094048014841071501030310b50915100c009119403800303200040750760008a150a450001d66a219080300080c1e41e4258400320300c08102030100c4c0603a03400303030320f1045210020a811000d080080c440407515268000541c0c45043d084080e000e809020300c803c10f881941d90b001c10b914900c04000349480002c0000800d000c3c001d041164105000c0d2040f20304080d800700090040301e1060b200c000160740030000000407244540300d0b00c03c40500754600316000394540412a46980a46c0240c10240180410f011029486581c030142c01010010320001800f000c1180c0185d01c031403404010790300e0b484041281e003001304002013103070100d40d18003006030300594 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 657320494 1250 657319244 657319253
    0x20c0108060f0405240f01092913050f0a0608060114070501020f0309060901060e0115020a061a120102070c050607020d0f20010905060d05070516031d0405040b0103 72
    0x40200150780c0041824407000040d26644212441822903800d0b8000000c41c0e070100154005c20000c142c1d00c504104800e4401907644600301c1012076580429901504980c2d051040c61561050801c1c142d6a401140407044083d400304100c04940b816a0145540b40e98207081c417000900728007981c400326a080300070848651049032414030440d0740620042c18801103030745103402da90108030140e40700c95011090050200041c00410303044101580200030f15450301140503003444051040420b102214046100f002d40207201071005d03590b21010801840d90901c9401030614050300406001e01030310514241100780500c02c550440d6001780365885100d01d40300810155030b01c8044101c0c1c202d0555440d400010758075910102600c2c0c81071480c0c2d004816a405261621107118403568100440710707a041105484120841c0c181881e46040803401d075607600000e139241e1040c4003080344001d038001001d4082c1030f400405081558000d0390711440c0080e9100c20401605d1003514003429980c40c8800400018 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 657321744 1250 657320494 657320507
    0x5060f090304170610050904170f070605092b080f06040902040c031a06070804350a170903100f060810060311030604081204030e0616060e0d020c01 65
    0x300c03440100e030302d001c2e02c03071590100d00c440c20081c94160394071503000c3c042c6051a0300700035000b0303200070380f0003000f02c0c9042c0e02c418107080c4082494844420002030300303400c0030034200101d4840a030040f00c00d002d5810f100003219038400b4064249101c0078030f0380c0d00c05105020108880213081160780d581d012a611081800444460003400082d0b00075614004500140c4641c09148211161034800040500401c1020301201503150a1b0703174850f5208010003070000300400c059405880078900d24551540744914a0320108041008541035250180c2c412074034524001450b00000e441a10001100d400c1e60320f13100501e00330341e100c0650541066000c1e408420181c3c0c4038420306204603d01140305548c40f04010b0400b0030b204040c85030281c5400c0309000b80b010401101c001d8000944c02440c1624287e2140d8215000c2e09090740c117240c030448003240c141032003107030640000740740101560fa079540040001242d038030f6150348c1140c03102d04100340040c080700c0124040710503c01540191221000401c01110031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 657322994 1250 657321744 657321751
    0x10c0f030e06070c0305031308070f0b130b030f0103060f14060f0102100609360213060509010b070308070e0a18140403052101180f0e010905030409060f0305060f 71
    0x100061200302e0118600c500880011401580031f19951011410448042c035416044243ca907803001c0f004000540090390548110b410314001c10b0b407601c10701450b1000c50455503110b102e512101100b40884525050100f90482c0c0c8101130800924448a56500030b8951002902214005050000701542840342035000ca0700c074148140d4410200341140315045404542260320003590710741004002410306007050450030201c82c5070744040700101c0307001c1030070710051000240030381890400c0c1545010710f90410400b130702c0000d040164540c0c40b0440c50000b40c001040c207a0001d106203000c190711a0150044504000001d0a0070162500748071501f515035050f0030235240c01c6e03503450714005000c4103040e010f507000d9031295071459a91500c40100d8030702da10304035468100340440000100306031024400c2003101d8480440c0040b034a01181002c10700281014454603101e5420702e071014082040200080003681c0082404021458895110007021481c60000074803644c00036010803200484070084690 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 657324244 1250 657322994 657322999
    0xe032a01110a0614070e01030905120c0312040305030601091e03120c0c140103150f151202070309180c1704020d05100e060609060105270a0b0c0c010c0f030e 69
    0x101d0302440d5a44a00711440c0500300c0704d0244084c01032090b0303a940294051040340003442c083c800851181c0701c3c01d40381c000c000302420304008002404103000509000f41c0b0002c0c1c1c0d100301202d403030b0710b424203000e070460788102d6585000a000403c08a1200c060541c5503441186074000c500b40241180d80b6528550703425508181842448051080041c0160740740b10090603040110720b0312a4a8000090260303054141115440451044280b040514120040c3d04130745503401c01030342100b040c80040ea19041d40301c40782c03000b4900002d81c0c10709064002c02c0032030840700c802816080c00e00708070311304034119003160303042100040542641190307400e030710400950402c4c0024403604880b240c41d605c45282140c440c049662654841c890700c03138035080a1200c550322140c16500400e203481c01800090251040000140d40c04640500d031341014113001d401c085080c00050841c44c007164690a84140c04d401c84001c0007500d104d1030b842d40c21654400c41100b1541c40e4408801660709803aa5420b071800102d50070120b4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 657325494 1250 657324244 657324253
    0x9110307031d0f1b030706020a03050307170a051512070b0912010c0c0606051504090509010e01020d0902040b062107020307022709070b0301091802060a0e032a0111 72
    0x31007070500400260700c6443d00205114450000e0ba400603803058040144243c10448040214640201c0c604d1801645490700c0c5540c1c0c0c0c0e80c4a030a88071013603e04504880420038404101d507800c0143d011500454040100d80c0c6009404030805c489040210160007454100322403c01000404002504059400400c00721b08030f004e03403c8890071a285204900c0001d00c81c3c456410501c5007520940c1c0240c541900c80218503c41d400b25a04203128900c50b0b030400310b030f0304e9001407840003003940420710750044840251740c1c4191552042c00500000003059120710716280050006e460120304444440c2c4c035a46a2840c80344098107040d200c0c01d0000d01080660104007d03810050b43c40c642203681e01c0a0203e00042d8607445e0710307504181c8400c01000c2c040c055001140034400c0036031200a50341102d0310074902091035583c03d818044150401c840c000e4001c140030400b84c80c0d080e0892070403404103c0a608641852481a070300750090000040d0003480d0520000404245511440c2080c401c0101042207a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 657326744 1250 657325494 657325541
    0x6100b1602030a150501030c0f03110f0414070806010f0e130207030903050a0804030c05040c021b0d0503030108150f010311010e011b060f0b060702092707090203100911030703 77
    0x44401c9402d02d44c0c081640c1c5c5d40720300600801c00d00d489040041e0048480c408991800c580c0c03114207910500e608907119030141920582c02d55941c1d040980f04800750310030170a20341010b92000c0c203440406c2d030343d240c0820440d00303c1440491085500761100f007030080c202d035006060049e400009500a4400b5030070000034450100125038100440044988a0a8056500d82c07550a02c0c010501e03180d04500c0c8602d04246085d40081d41c00900c80700d102c04030a04101946000000140c0f1111010300002c0242c08048000201842d01250000c1850b103940196510b0741e4404184440200090100404d403c0c0505100320040d40f0a514000d0b2858060529011000d14113240d111412250003007122140c0d102e07414124441000c1c01401d003200000c0d5403403424040a82d0009840480c01407804112122416600c1c072102c5c15030369481c08071f0700b0190039100b4060b210b4074054080d5004507100c2203540c452002c0010104c0541c450260801c40a40c140b606686a844003180a4080314020844c006d0055109 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 657327994 1250 657326744 657326753
    0xf1811030708061008010b0402030c1b0f100f0506010318060f2936061804050303040c0e010e0106030b13020414011403040503070f031b0c060206100b1602030a 70
    0x5070003136010580d1441c019152040e03e03404e40e00c4180030b07140100e0060042c40108403121040e91205412000318031400c155480d4400c0c9410001d1314804168820803940b09840d00141c1e008142c0481c0200044c0581c0e61100010340c01d84001ca0b00314140c85180c1100301000c40c201d684200d9011941803030200344454044480644200007205e80d0711640c104100190381494107142d0181c8400d404288014145060000580300980ba190780540d80840710340000d1090780c550046154003d4890124000c0c1d09050138402d68079002103034101c803940728141010a000e9003110f0300798100c0b038a404121001d6800c03d402100034041c4446256088080c480202c8048112800580060b201ca04030300144018002c00040080d1000d40186203d418100284004503001000311501c16800c401808201038440c9411030f44210f41031800c14038410609104000c010240041c0800c4480c3c50742203503040d4454644610406a961280d0070700c0d81e400300310740e0610100565002e0b90540c00142036449010103a100c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 657329244 1250 657327994 657328003
    0x2130615050405120f0d0c060908130f0b16020f031618110c0d0c0515130308180a02040b061b0708010c0203130330090501030f1811030708 61
    0xd8080200314046014051410510008030704150301400610085a080301010b4444032a0441d520800c952903100c4428811107801c603407003065001904954604c0081186022015075001c0e40e1a80ca840100020b0059044001d5078608510815440f030040003030b0b030811401e00584245240c142c011014003426000c600d8103820b0041840b4080403001d400c1d000041d0048404855843c03040740c006200c20b0008160004000100720001d013000b40300528a402c3c03140c0f80c010454158007000e100c1d9420000c6685090603829551842901c804031980c880c2c05815912144529110718070741d10203c00700c000740c43c203034001e2005403901603c0b0500e400380e072210694446000300f006290702d5000d0a400c0003c2c4109228020030001a48051400c162510b1103c65001c040c0f4440900350121400380001081c1000101da416101c0805840d5103000081d0000381c007421442c4103181c04246441c2100941c12842d00499810413240e2261006200c079561300c204e0103611651099402d4881d031640810004410007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 657330494 1250 657329244 657329279
    0x3070302071e110102010b01030c0c06090c050603180c0616060b060d0f140601020d09030b060f0406031b0e010f17120a0216092009030114070c0b060913021306 70
    0x10043c0d00114000180c00c2d40c1d0001100c078105440c10800300d02c085d500180b40320b00030b60300c21808a00001581812044c60209810035648450008240950b40b00d50300d00020703002c401002900e001c03148203401c00085016850804811140ca030001000040f040d50140c0c00c0d003c0024145030510300ca40c3c3c10007046078844a1600d4030165904a50340f1159468014a079100100b4401004130003500da0008100c0b00080c031006201041c03000129007283e8600c05a00b0140c14003810802407507640381401640f4802c401e480b500d12508240c00031030011008101c50341640c2d2445000501189040782980d1044803115038826540140b0300035002008440e80100030041142c2c6c014000701802501740200e0000580c00b21000514003c0720f80301151800c51100000001c00100c5600c503104000840e000d41507180302203091203415001c00c10707400d403c0300c14001c010740074415035007140d5128028000103500c10313501800e00c210007680030401454548110324500b000140e010400c00c0d65150a08000007144 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 657331744 1250 657330494 657330503
    0x702030708070f140301050106021c09051c15090201021b012303060a0e070219150e010e010e0c0a0302220606030606031103040f1506030c0b0702041d0303070302071e 73
    0x300c0081200e00f000d04c150458401c42107000300041d504d04a4085d554882103845d00840b01d9204500422482c002c10018000708400781850302080c2c2d100310500d0790281b60a20032200b810342d0959402c541d04542c4600743c003859060f0010140b005080c122010852240d00d0101d04000c0d211082941020b502c001010308120380d01c1e1426181e0401d2403c004420903190001c161103411b13881040282d0360300190b090081343c039802000170200f01c68203001454032181c1030130224850820440c400d1614056000c0840c258405000300b007a94151441607464155040d20681e01c5075a0000c280b001d450045d44049a16101c10314140c01b940e422180401654080e0b0701460100e0f0b501d450400044e60503000356454858a1400e0700c4c65850a0303034800c4005072000c50090952078a00b0908100300c4030b90342c00070026640180c9004199a90b507990850b6680c80100128002ca08000c40750310365580414580da074440c3d04070b000e107065030344912044000750441c000650740008080702c802c10b45602010aa100c2d40d006 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 657332994 1250 657331744 657331769
    0x1180609020f130614040902030709240e060702060d0c1803050d0207050d02060703030911040f0b0f0103050702030324090a020307030b061804180506091f14010b070203070807 77
    0x45003150140b12080c0c4c050000d028500344411001900402217800351100c0703100050300c80c0c03128401203884d84a50340216110143d0121004070303001014541c0c0c03e0b21061035961000424000b000e00040d401040b0300203400040510148a4920b000d811030f01810030140360002840780040502452030b502e540c03066400e134020300c120f000c407681e050080304040c01091316810200c0001d0340c0807484511602c03201408159031035015504002410818880340503000b4410300c100361082c40d090004240f6042c0031881810780303200d9083c0e194001d000d038610880761500a035086071707681c00301d05000c1e0898144070701c881c1110b007403010410350b0ba0381402405103000040040c0c9903e41090302a085600c0566001d100f46414414030180080454a080010300159030205481c090030524404003e039901006000b8003601040200c548000200041d8090030441447d400d0403540061808603078001d8584284280048018001c80034400020b0503c90b10281c100c4031455507404506040c0551034001141c107400d0f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 657334244 1250 657332994 657333007
    0x307121e21141e07051f0f1d030a26040b18010603050c04020a11070b071514011512380d06050405100e01150801050f01180609020f 58
    0x384003070002e044800030558980b40898142d210808900c4000849042d01000501c00082050a00c1010f2100c0d10090205160180501116014150ba0100300d14101c0c5043c48240c0451360b13816000c3c1005030b030000591314014240000b2941318103000d4039669000c0d600c0350340a400c00442c928451280c1e010350848650b0b41041d02e4200070048a01c03070090100c0c0c0c10711600f80089031001c40c4405d45036608980040c1d9804242c14255400100145c0211085c003a1400025400c01100000d1045a11a04402e03895101d100007007412540524015907016148500602034110745151076841c050603811710100b00100e80d000c070019035049803004d0300c0c00d5810340a018070f0244403581c44004680c641c1c5500d41c030704e0b82401c080341084c1403403100540016145d034041824400c060040c10020000150240165440d24040c1c0c2c3c00390501c518900d0f11401400e000203940c0c2010710500b402000141704c0c00c105a46000e0300c0550306202d0003041c0703d829036202c40025910499100610f14580200f000d95101c01c0f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 657335494 1250 657334244 657334247
    0xd0204030b3301020c2d0a1a0f12150a05040c080f1e04030302030403170717040c050a140301050c0a0f1202070606060c050106050307121e21 62
    0x42001c2c011164807030003040c0005000c5255009210030424103240d00c940c182121004030325010701d20029039088800d200c1003810714411490440c014188001451240714003440074008104091320480c10440c213000c0d0072100c9100504010050142c038070420340c1c1020b1502d0120040d0940644001c007503460101c02444090502d4124a0018601150108800e0084002c0a400050020b00c40e48903010b0100c005184031141c050804c00081d04c01440c450185454075000c0c00035030041ea015404205002c155001007101503455610845540e035480c03140b251032081041c842d800c05001281c44070040398000c0380c5a05c494590b00700416440034141c030420000420305085850140a40400b104c5c10025140c42d941c02c0100b8044503003591030100e45009a0490b1100203000d03e0000602060601000046299100d841c8549441c00b400003089a0340e03507030042503903500c02c500c83c00440341d15560450340850707150302c980001000182001f4000000e107696108000c4001030403910714285800c52145040d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 657336744 1250 657335494 657335513
    0x1216020d03020c03070f0c09020712031116020f010905150d1d0c121507111501031502071401050c12090c030303011518081e0601140d170d020403 64
    0x12103450400b103250035806000140c607403041590103406034450507245010008460350210082c1008d036021500c40e0304d14a45860403003428000d84001078100501205880c00c1402152003115045901c2156588150300f03004480310045405414440400c0c00015903880e041c0c51034844a4182c81e680da515030440c40c441048440c40380b146e05184900c1060408000b10008428504060880d0000d1000c01d8440c2218904041d000100c6510509070081c08089900180c18048140701c40040d6800506119048962900240710181212810707003420354400503164002e028581c007807140f000b41e61840c02c2c9140c1c25240140c2c1c60520703204002036810003003465401415004840c040280440d281440e001075620301060040c450000d034103950140c0c03054000c0141000d0107601110807181d00b0303502e401d01380d161074407038001c80b50740c0a03844030800c054140810311a040c1c9044120b01480080c035030040c40b101c0512080100c0722000002c10710986003c1c00006004484000c1601580d502c0c02c5203000fa480 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 657337994 1250 657336744 657336763
    0x20c010e070801060b13090b280e0108030a02060705030709080604050304031403040308030f2d01080d020c0904171e281d0423090c010c032102121602 66
    0x5404080c00700301d0000d09006e440d001161542a00414005400300c0016280300d488a40665070741001192007100f041c0d054081401c480c43c08078003041d035a0341c0d00f807041d44a1146550032070060f0081030000f542140a08080e68102d485403074019409920392240c603180c010306440c15507807584017003000c100300480c0d9040207490b2001d0101440c2000d00d1907903148c8807400058940381c080341c0c4140c0090ba0640d1318601c01c844082c88807810b02810074aa0300c003400c03030500a00402c440da010703006202c000f840c0005400800c503030002c0c189000725a11070311080c810040781c1c007060010303030f000700304603411081c403000901040403d04412903500c4c68803501e262600d1101c40c4401c10a070700c8a19061400c250411714032002e91000034002144c28005c280050001c003000f150001000d00c1580c10003080c0503481c00002d20808104089801061480006440c0301452000c0140000e08801c1e4035090803070242200e184540014602500b1f00456600c9194800000c9415402c0f21562100c100a00343e41007110860 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 657339244 1250 657337994 657338009
    0xa11040b0d0b040b0603040f0203010e011808030406090c0609090c0311030408070c030203070810051807060c110d0f050c0109030312020703021f0e0d02030a0206040312020c010e07080106 82
    0x901898810145994054080784601c480c0d610980d00c50540c5841d0002ca07018400140382d1713aa03030b1130f0501d03201c070301c1c0004040306074081d40ca07145142a00fa1310512a026030b40c513028a288084c40b8a170394403280603620003002158680d84400f4504001500194504090800c0e920380110003400e201c0303914112124000507908043c180318400b0750821041003160f0300b2a4011088690302da0181c02c0c692004400b40c0d2000b90503110301c40340050484070101788807100c104185000d0005403540d07018840c15030401d0366075140a410032001040342601a101540d11184504541e40740544c0760340c0003840d210410141541c00c0e40283c0c2c007510412106000c050341c065000d080690744141103490003440c0c401a01e0011000a0740080c0042c249802003018400d50004080c16800070662100d2050149c0409210401d407841191184000c242c000303c1603406000c1154000c001503071352500c0449440341d001f4001c2d001250308000c846c0719448280588424504440010701415191801007400c6540d10b80c810f01 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 657340494 1250 657339244 657339247
    0x30f0b13030f0c020d0b070503240a151e02031c0c210609060b04090608030a05090405150316080f0703051506031203011d0705311701050a11 62
    0x7a81003020303000d60701ca003454903056146062000c1024031030308800280c050f400c034808003e645903010f0b000394883c9489610814408008011402d09038083c00500750380003004045c00d0000701d0001c0b401030703d0400280740c5811027415030030000158224114401c2c006800018450704c589511003681c4115509111003000545260070008000502081ca403070a070301c0e800060700130780210f9070700300001400da03c0728108100750b07a0781c4d0910100d0b81f040c4a000740080c180360b000215400301200381c0e0200284c3c1d1b01c5040c034002102080000415009114107192050707500302c4456514204072041e9121032080710b4091441c24010384901d001280c2c001a0340a500c800c0092000441c0440c88280c042c0316403084131416215034002070304102d606803810360180c0010000042204040b500300d00001101c0c840321907a5111032608462500c56a5129101054580554100c840050400e0242d40003107003d01d469154407401c902c81c99000c0440f0511142c0e440b0702c18004201400c2c46490b140582c03155005 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 657341744 1250 657340494 657340531
    0x17040b010e0f06010c030f140a03020301090b060702060703050f2b14090307020402034602030709050603091c0c0204061212050c0f01020703030c0e0411041202030313030f0b 76
    0xe10840040c40002c040080368900080e065004481710414551602300080d250590420000e00030340091007a42441c40c02c1404c0382c0c03001c2c01c040c001c44070b40980203000c0520f490002d441c00c0c0c425900421454042a10422000d003a004465805401015211600361001c1d00e0999240d42603542141d801688100c1b03a400b0720040a50000444405030f5050358051784944c1c6404103d03292100c50843d12a009400e0204000284002c8483c00800e5410100249002d901d45070140100d000403078038200404c280c19818001131070b10b04003442d030001c41442200d1107031010001191180c244031010310007040744680600114a85806440c0c003a0102070810b10109800e52148227030a0705060092042c040c0016884110070801e22400b04600001ca0007503554040301e150023801802d10110500004105510000c400c0c40c1c540540d0f442042164a160b08050030903c0d13000d1203c103039400c2241e15110402541030702076100141000210f001d00448040d403556410072140340d07400144144284c01000c03140 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 657342994 1250 657341744 657341747
    0x60e040c0503160c060501060906080108060f0402040906020d0f0f0c1d01030b031606120f0b010906050c1f051812160c03081902122817040b010e0f0601 67
    0x15a40e00110750030640300000f590610a132505410346102030b10b841d0401002007012508962240c084a40d541d4603103051380c0c3e035400700d203866503800c3e50014403507102540414003500d0550044ca0179140640c500514203a511000c5500315080781c0d007803d1203e80c90741c0c0d500207e0b06842c4907000700b0ec012403d01c0b13075000103a04825940c0031107600c040da0602d070740d403065040d10f61420003030150307161200306420b850144c4a070000792003c0c0c1030103954080c0724145004581c2680d1280224104950107031140c102c01d60500741e00382c0e420340101003024070324441d40c17000141c0d4400025420140e092a400c2c00180d9042400040c1c007409038000c1030f00321680c85107550000b440c6040301100c108282d900290a14280c0e9072034998480d040319480601080030114426400c2450911040443c1805808443e01c5070418040c1403500d0007021000385a003401410b220852200a032803404d544607a0b850825101034202c031828140343d409490a807800d0550b180148650201e1030000346e041010403140d1441031501000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 657344244 1250 657342994 657342997
    0x309070f08012c010e0307060911011b020d03020f0d09050901080304050108011e050411090109080d120209120a0b1e0f070302071103030a0f120c1b03110610060e040c05 74
    0x5020200c00705943c0341d80e00c890300f903010404e001c0d1202c0c1500e50f24002c9041441c06441d00860540708040f481056507810740c01402c0c012070403440d19408544000450b000c001d45142c04890540640c024502c0c01010300e1414451000c40c500d4907140d040b0f8084c00c08043c0081604160402085580108420701c1240c2c0c010b1201d50440d0400418115456480210000840015030103070b5000750a002090004690540c0a044103d0080c2e854000d516036400000307958801c0c1311501c6d00403031484100e4002070510b6030000c00605501a050307550505402c0d480c00e00d0020031090540b02d80342000148503101003984c0c14640e0144400126608a00342108590300b80100a44024240760b8002207400c10000100100e0498520040690346c603242404d1000d84005c2c40d52a11100017070744014132a051074014480d6a5528590350703140e0040d1031010005241035008200306030700703002c864007072941a140104022880740b540e5001c4003800c2490310002802c2da03803074080039501c42d030300380040158001d03030010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 657345494 1250 657344244 657344291
    0x1002030c070807080903030d020409151a180d0b0f0903040b16241e0908090405071106071d0117070e0a03020d050f060603030423040e01020309070f0801 67
    0x59410395100000c1c079200240340b144040844d0580400704088c41044c0b040d9028000311000507606102c01201040408050b00c040c0c060740c852082450026812061000d0143c403151481c00c2d804080b0501d0800020300c42501410101c450301c501d00304115000f02c0c0480b40c02d4002406100540c1828280018001503014501c0100101401c50348620148520b16007010303e4980c00103404548000a00d208402420395082c0710768000c0e80581e100900c0310000d07c5035490654005038241c2c10440702c40c0400001c3d142c080e1041040215450b02e040f4910010300c601c602905003a1241c3e1150410030020301c01417400e400c42c0038180009440b403100300d010611451603120032940b0380032807120501e03c0040d030328040940001c2d4101007010540c46c100600018010079082d0340500b140d040b550b41804041d543d100301e001c0c86a20342c00f103025100b01460783c44002d4031001d00003000031400c4d4041310103481c00c9070000c4891211300c0d4401c0008000d08012000d24038081c1103c0d03c024071500400880e03c0c04c0215484 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 657346744 1250 657345494 657345503
    0x303040204111b070e070f120b030a0218040303050705090d060c03180b09060f0115080a141501080c2b020705030a1d0f09060103090303060e01060f021002030c07 71
    0x241081d203101c4464004841c401c0c20304480380b0340076502c4100c0b0705a403200e841c0945c0072103503000004111600d000310350640c0c01c1c0725160345000c24503000c0c804240240c0300032003081d070b01886503440782c1e401603030b030720240c2ca17104404050f80907480d24203818010251440a403003c001e102c0108120242a11206242e00d000389d000400801c0540107007804130003c08165451f102d0894403070300c0030300800c88140c015900441400089403001d4607401e01000380b0907420300c100704161404503450f220035030240b0b980c19804561520009900800389828203056481280e03c500705801070501003a69607007200078183c00852070032001e4280140344d8824142040410403400d501d401e2144408020f00158040340d001c0e079481400c2e02e8481c2d4403040040c01c1d54802c6201c4e607010455850000005040003401a1428180205510f04584410700113600810201a080c0d04050711450045038103812140c440b4000c050175070722240c00080307041000741014402c03407600311424010024019a02c4040050f03c0c101c86c0c12 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 657347994 1250 657346744 657346751
    0x61e0510050d12020f0303010f0602060907121e1709030d08090d0c02060d15080601090c1d011b120e030105060d02061c0609020d0c05030412052a0303040c0608090303040204 76
    0xf11441070f03203050041c603120013080c84000b001003011615070907441c0882d92503400b00d5980e900c8030a0318945445181c0150006550060710301c00c0818050300c8895919024484d400403108440c0e00c03211a020319061080760010800260000913007810040842440d43c9460301210a0904007941511350034883e054400308001c0c08001c0c8150350300d050895404006a0504010b03118880a400c510001d482c070424001d406603800024a0003998040c811011945607510b103a00a0809441240da0300c000e400d45d4100488107411100c0101045d00f440300c510300601a02c2c02444960350000c15101c80c003d050740c040d9050409000c080d881c1c80f01c2440c9041c4d1b040381c00359200d0805000e0414000500403581c0c03203050401c0b00004940806600500003560701c00000e00c0800304888065034141300541d0300400c0174885104004c0300d60b12407805050f02c1e03080f02032803a40207810030b20b5a80c202130500c0c8136092540c100009100400880d06031350802402c2c5410074000c94070744080e1250b100c1c040108081e009949 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 657349244 1250 657347994 657348023
    0x1701090213090b06100e062217032d0c0109051b1809010902030307111c0b06010810090c02031201051c1202210c0d0302040b180d061e0510050d 63
    0x14600458591005403080d40c984108404121100d07054442400000e0021900480d44001d5a520b19449e00040001945464241807184a0861071002c0e075031b85001e14000303400c0e403a11075a0014440b82c0788510004c600170b00141880f03400c2ca00200d400d1010300c0650b403a100c010361940102080901c02540c00310101e5510342d01c407a4050f1001a10082d0b260000080c1c842c10000303510340d8800d124501fa2140321345115007103640c3c0e25522801c0b00c007801001071103001408a43c403a50059500154040690707400c80da036603050800b6180012060b8001d60008942c2105aa001d8044140100001c440c103040c21018008052451a89404050910142c0c0d9008031547c500811034801c540c84408038149403203145411210154204400c03190a2f40100891401600d20a0007030302d041e5145030300c1d0745140045201d09611546c0c41514444c2d01700c4200c0c070030705011079540d00c22082e0242101a09038031680c2088110b0b0222140244400e01504007240c080c401c0b0f484410460b40a640e00c078034540c01e5000f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 657350494 1250 657349244 657349247
    0x2030c120708040e0f0f0c03040305030f07020a061514060703050913090c060f0305070806100c0624030212010e06010308032203031d0c06030c0f041701090213090b0610 74
    0x1045030040d12a480301d03001880400462020f91502c1000d202c100c81c0c1c800e1f103c1084403506e0344800c0c1d1b00038000900c02c8c40443c00070301c80803c8480e04003507507004560010f0310039078448040c7c90281e000103900c1900348108001e4000c00c1304d00b00e10890b40c100e032401c0c541501543d020348107010301000280501061481540184910703400840c500381c0210407002004c0d903455008100a00500103407000030f0419000c10b041c0b901441985002c0d110040c0074418070341c2c1c801400c5800c451510030540309151120076000e00380750492048155410400f4030788460700c2c11401444294002e0001044603a0300d003811031081140080303501c505513a40100400d40e05d8940880d0f0000c01c444440c0e450040b0b5410444070410582c043e44014150746641440408a034030320300e0041c2c3c481a0f1210100d0b0080d07070820001e141ccd640107030024400d28020800b45030829450350b91011481c4070400c40c0b0102d6a5684040c0019464006403041c00ea06109001703101d4050395590f017003002c07a00540101c0c001c06d0582071014445 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 657351744 1250 657350494 657350497
    0x1a0c040b0c0304141c030807021203040f03021c0f20100f27060905012306090a0209030a0210030e15060405090c03030f0a0306030c0902031602030c120708 68
    0x41608950040d181d00c94020304603100d900500c5101100d240c90800e035241c9040c25240310958400003203100065144644041c1c841c0c4074020301e12021030151100c50210070103400302443c0101d010b402c81c100c02d081c907440d0103480c25020410820f020703250111030b41c403400d42c03211880c0d00b2488030b481e0109600504003801e05884418445114607406810502c1101d22956032145040104462702800f08000c45201c0382035001c00c014401041c5400141c0e5100400c8450300b202d4007481c03240000041c5100490740788162080f400d140c584526008a05020075890800c40c0f03e9000115602e0441c0345c0b068640c0085e076555014200213020710703103061400c0c14890295001d0b036500c01c6d8240c250b40f1080003a03206561021400ca4a580c07081d80b401000c107241c400d00240c07140d14040d0182c0190310704450321440100940003440d0304070405072541400320000d151074019600601502e9405620f074280b456041030710800502c0020210748c018002c0c200000301c0040d1811040321101c20701c594a4501c2e00340b040d084d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 657352994 1250 657351744 657351749
    0x70e01020c10120b0118060509131404060b011b0212070f060207090612020d1e02030d031a180c0d0b0316030308070306060c08030705161202010e0304031a0c04 70
    0x3490700b000c411400d80c101000c61501d0584000800c03e1085600055541c1c40d254043c0c405201d805402c1440035500800c018001503200500b4109681222000302c4103558024204420401002d8140b1007001140e01407031a40700c07024203011b040700910054582c80004400c102a104883c4410304e5130303d1a0045c84084060000803041c14421350300c88801a688580510443e402540740200000e021b82107104507810240d80149296042003e0b610b070041005100280800007a150003155401aa420000b0040350075841d1004034124100014000024110104850055480380c0b1008005204100841d81c01103881404640300da04610b48280108010703400c41c1e03050710501c10001600c40140004c0000c481c420360342c621103a6103107a82103040d1203c0340300c1c880100710b1015034100050f44e142c026550084052502909060100f2180041e915a900702524100c3c440240007400c0380d030a024400d10070340c0450003180b1b05442c1d0b54980e103ca0b0014100ca000714402c1714046030343d05c20000103e500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 657354244 1250 657352994 657352999
    0x2040203060d1209060f080f010b0f040b0a02150105030c030a021e300d0f032d060810140402040504021203030712150302030a030c0602040504020c1501081203070e01020c 75
    0x1c03c0c40b1442c5001c1c01c1e503c0c0301d004180c089030350102e50403402c1d0700c1240c000c0d2148100d081d5440a691038207846000c01e0b040000341001c880014007006c02c001181e0300140004203202d1b4007c01c02c00100c58150700401d40f040c2c112a000340c001d80c0c22513a15450005061803006e50541b000c00707888d4a00a61071038031120f1100c1c503a6000944000340d4288028900c4e00f001800003101c2400d252a940b00c0b07440c0d80e6410301d02000e2001c19501d0300c120245078080d0380003101c040c1400903e8039010b0000b155002e80e051041e4030051900e5900c0c0d20510544034200022800306403940b004100f080b58800c0f152500000082c0300030300c034544480024046446520040303041c401700034101c0b62217042c40c84001c0e01583c82c0b100030301aa1460518960300100700d811014017129000f9001e0f040d503041948044032501c0d85680d0644089408010000340d83d02c4a00c01027070000c85400190588020070020511a520182d01ca664513a1000078180c100016441c00c40303030804071508040c4171040500c0300503800d1444201880d035 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 657355494 1250 657354244 657354263
    0x50412060219020616080c1927060e15040e01030503030403020607020a0807020d0314031503070f0b041e030213020c010c0c0c06181502030c060c1602040203060d 71
    0x30880c80360003a2058078182075416409191000080740e50300400c503410702043c19022401d11030035000d4103015410007a040d411914107104100e02d480c00c05a020078200004410544861040218407510320541c4000c400e80c1c46101c0c903000b0300070f080a40018202c1d1050242c103407070210340300a1404807001409285c810300095a541e0074201d0310380d081202c040c1c026000c0c407800a000144040392826205138469085030810302c89800780051031030709040c110103120716001d20030403101c5520051480b402d0703040c81a001e04015841450300700491a8000715080d4044203040c000c8002400c03d4070141c4480302c90750f1508591000d08403981401c00d510103904040e4070706281101d0001c6030020140203a804d0000e01c15195501d00c200d0308968048401340c02010840001d01c401440365000d0700e03144515003081c00946459403020400e0444120284000d60301c0069002c035803840c14031003e54000c03003d08050303090012703044a4060050710780c000288a41d600100151440c1c0d500004011400d03045032286 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 657356744 1250 657355494 657355529
    0x4051201060302120303130b1305070e100e06030c0f01180b040906060503090a031d09180610140105070807060207050a0605060d02060403060e0a170301050a06030c080f04030504 78
    0x5030003804075000507400b40648000c181000c12001040b60702900d90707400c20144103031494880740c0d1282006468103030054608401c1d0310210314100700040150510103541a02401c09070150b100010055124001e088444010004555400f03d01e484001c1402e56010080081820040300c41c002401c0d1400110344e02c0383c40c00710312505aa0080c009480c0b8951081020743d482da201641d00340000c81b014107481e440707070340400c0000b480f0300303100c11000354902d4003203100d07692213030014204100448903801c400450f46014103003101304004007900314401d590401411428600b0004000f000c80e40d04e24140480021450301b0030219800301d940071a0005001c64561070341c0e2615985804400c04207403030850900300803610500d0001c01880760150b0040005d86012302d1551044081c1000a841c0c1c0703400c0c0a1010a100840c5036000f160f0241d441d00d89800d5503030b41c1440c1c20042c502c08150014403c040c0303803400d0f41d1291500201c5440d040701040c86068515507403444d04580c103114581082c94014801c00c2d42 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 657357994 1250 657356744 657356779
    0x40b09010e0f0a0c0b03150d0206090a140a06030b01120203150901080a0213060b0711040608030f040e100b0f1812010c0e060c150406140f0117070b04051002030405 72
    0x810f4501c41c4640f02a5490b1903682400d501180404d940710100041241c801000c9890030000c88900c2910180245041071404000101a4803055201801f280100c90380c7c81564030341418810041c020310b090030407601141d000003e050f012980c2800740401c1c1e0000c0404d01c80004072280c09090107009081c01d01c80d40e10f640e400d03500c41a01c4941207008100b800b0170103510b607485000345010b49194004940c2002070503196403880e0000d007076416070003560321030000c81d0914040c8002d2403903124400050755614600380c6001ca40000080c44095012080c00d000e002604640c4100e0700e4a0101e84405c5072108400030084c64054010001154000d454203481c1c1d200c00010340040440300c4086d143c0200118600d800c1c001d0f28400e010220074240c101712011400b640c14200b20701c0c0c0090103108000b8446004805110210600f580c400d000c4440140042040c04180041c1218030440d0401601440c1d10780708080e00540640d0040340c2c4134200f8003440400841c801c0041c5d800800e00105070896070a142801e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 657359244 1250 657357994 657358003
    0x40f051f050a0e03091504050a091e0504052a09040c0f2403050702070e040c1809020102100c181d1b0d050a140f071803020306040b09010e0f 62
    0x20301040a401d200c00a2804500d40c4101501400c001024514060b8035204104030b10300312001110b64081c0030b1101207066251b40f80080042e0060800000d9800c8006c5000d543e4005081381080c0c015051000b08030004078003041164110864220f640001d800c59841040c904000031841500407000c2c8040bc014841000255070890b042230810380361a03a2110b508030101c402e6040c01a0f40d405811544201e040e1190f84010340c48541441501c0040381c5400400311000801e442c15102d9180301c5000b809154100c1000214821021004101031122640017035110040500c8000c003441e6a240740080740e5025038810b034100c00419440c10003480e143c800102021036000882c0740a040b151000981c21b0900344031a036036100e69214042c0c04e2814134200308018240041c4500c010944a09c5440d2403000c150b1000c9000c0c8403641c1c64030100c1d00e08070b000288070740c1050b808400075080200040002d41c43c085191504030b80c00c480166103d5036120801409004402c2015003076200751510046c0030100481d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 657360494 1250 657359244 657359293
    0x7020306071d01090506121509040609020103111c0e0715030608060f07091a040f0e09010c0e0a0e22030f0207060915031a090c040e0c030c0f03040f05 66
    0x207141d4982c0c003001401100d010540f4004c042c4c0001040080c481441c280d4aa801d50100040300b4140070758410901041c00c180060350100c440f1b50b2210b010000f150780502940180c81c00200c0c3c407600b03003080880340c0441d4089420b04079078266074981110421500074010b80000e0504064900141c48482400a00800982c8685100c9004542c04a11790b110f50384c81290003a6800c0d96903420450406110030f001407040382500d03d100c10200800516940001481c00c000d1101a0740800a45040702c00b6a00b985c9448a43d1001c11217203003c41c2c080350351103401d0386042d81c0ca40300c01500070355a040004010081e82c450410001c81554074104105030b402075074201070380055426151440d41e40c01b000c1d503180758680141200310304001c01e82000c69110750b111007005402c00f82c107148003102e80d401144440764207890008061000142c00d010310041001c082c2e4010b48446900307451407820200811680c014103044000f4400d0000100302440001b0212070080c640020660b03962804280d000001180b641 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 657361744 1250 657360494 657360527
    0xa020301230f01053616020d020a0c0b070c090e01090c06030e03090111030d0c050a02010b15031f0807080703060c03052404020d0f0c020c15070b04080702030607 71
    0xc1000035203907105412443e040303c20241c00e440341583c11a920b8140040400c1045191402e0752142481610070000b80502460715141a034030045800d03180242090380300400e0700103541c00402500b00281c1c42514041c200d600036540c0b075032203c4261a02c240001c20983c1705800b1a81810400c029845040d0b2264070701c5842101c04402c0c90740d984009070150b80c4101021010381d04107100b0403941d075000745041d2437160cc049098914056030701301c90408070307120384459800149012418103000b40d02407080c2440f8610413103001c40880f28100c4282510720000f8020320b080900c048412104410801c141402b42c02a08261606903454080702c55440005210513545507042508000b07206000303216003405600c100e038001c000503400b61820b88000d003541d82880d41195007005482c80440d4288070b0038404054158002c0740441800300020710b495000402a40700720711808410720700440d010111408554007108400e5141d480781071401d49070061035400386d00343c0a00c50070030103501e5101c0740d00221f400c4c80 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 657362994 1250 657361744 657361811
    0x30d031a090a0c260103060c0903060e0a0b09150406111309090b0a022a16061107060f05180a030c060206100e1501050304060b03120d1b0915020a020301 67
    0x40d45075648800280241440c13800b40c1550050010490f41d0f00300042d00308060270030200e02c0c1d07502e50301c203011280c0a41d01c110721900007a8040080140940ca07441c1c010825500410340ca0182e004031107140003000d08000c21060756a04001c100c42c01402c01e441445510340707a03000c5101d03070342c004110243c40c0d0f92904807421601300002562444041c42074070802504004852034400c246141402c404001d201c01d14068401d002c141e2101012040303007032000d080b0952301c3c0145884186140707071626010b600650203000102c3d804801c8584e120007034070702c060540030421103103d264502081d000d60781303904003502000e81400081007960700002c40340c0c081c800c0619610b0300565510f0100505003015a200d41c0e080050501283c440e602c180003540e08a401a807001035240d41d4407001a2508200d110306040d101e501080c5100504140c1c4100745c1504000303804000344c90383d00200144884810302031741030045050f200200c026842000828042580a4000c000e01d18402160840c5400000c0c0070200c2d0250 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 657364244 1250 657362994 657363017
    0x12030301031b1508090703081c0b0f06090904140102070c2405040b0a03020f040f06020d0507020d0807080d051801061406070303020c0f0d0e180402030d031a090a0c 72
    0x40c030010740c2d8200e411a40c4200c488240c0d000b41120820701c003078040d10307040c41110380110119045c0c80080860985038140d052403144c3c1355410380140d80c644c00085102c1c00b0103540183c4a902c6070000c136140210110764043c000d070340c0c0740392680c440d00d28485c181865600c0859124200a04030318100309550303010705828540000381420042d02d044922483d030000310300348410004410240c018000a13100c9080250500b80c001b203616480b50031a500540648100203002c014094040c0f02c865034000c001d1500340d241507015000715400c1800010001c0403201d0000c0c0348010703c0110400c0e5191178242c1c40052101d41007480311158104010200380109519103080022023440813240c0340c0c040e0001409042c01d00744079441c01d40094010050300d0381503010f042c10300050406c045c840c1d00d0000c3d80075180d5201901c0130b101405200510011802d8401c0a80c1c014480543c0c0d000940b01c0c20480c0328940803c00f2002c803003400d03d032264083d102c150458856400d000707071019290441090700225075a01007802c42c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 657365494 1250 657364244 657364283
    0x120c0218060a23030f010c08010e0f0601080432060612060619031a041502031e07020f0706091a0a08040609030912081329181203030103 60
    0x8100350341e1990300c0454407504009543c41c40d500700829040102849058079603d00110b8100030302001a0900c0d659a200000245600112070501424290b04000044e1505071013050100e07401904d028103002c2014006000c01103100b15002c85000690a50700d401d00c140d03600200c0b450300c0e050f038410f028050000000d40391b0412501414000d9000700c000c000940300c06051124405500800000c4410349410100200312840c0d0b10f101c8210000c14407101f60302d000e0500031b8000b01c00907104200360f401001404002d0038588440d400715000e038045460350f03840711501607180c840310f0032a0010314004d100000030866080080f401c121140d000e4200c20381e10480070311030301c1c82c440c844420300441c01000118010030312035402120248e100303080c90102d85450303a40424400b084030340304031003411002584558030426070a4010051500b1000d500103800d020b410000c801c450940c1c40300480320701180c841d0040d100c3c00c1c60400c43c0c1002034080d00340440c20460384ea0b180e510900007a9940f500c481600e07540030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 657366744 1250 657365494 657365539
    0x601080d020705040e0f03041e05040b06190c23060919120c0b0f0114010806010801061211030a0b1009030809090a020d0c03020a0e0a0308190507120c02 67
    0x403000c0da001e03084143c10076041000501c2c0c2001c1740710051003030f644180c200d240208002c0000e03000b06500c0d582105108580b07000100120340199002c0d42c01d0410540c0c6548820f07041d43c4c0e001404130300c000550341c400c01d012070715103c640a01034509224031071000001c1d00c1501603003c00c006180c0988120b55120f4840d00d0380d070400108451261f09030031b140240410078130641500d0307a100c1403401d449844001e44038821200c40135924480712180041c01041101d0000320442c80d441028241034407140380100001c3c2c0500014412501030015840b102050190fa641c0000c3c040f50781014016241c1c201121f040d0000c20302038100c0ca02840e8142c608090701c3d801b62030000b0480c1d510000b11454034210005000141c20701500c4203100503005d125483c0711001d103009000991805690040c2c03509480400100300710840c0203a10b0141003481c0007440850710f40340407245038491500300580e8586482104503001c0c4142c2401401d168030000c6400b00055000c452404090300031543c40302a91303480054440312 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 657367994 1250 657366744 657366763
    0x3011e030206032e06080118290609060705100b0d0c120206040e040f0501050714160f0f0606030209011a0913060510031d0d0c030507080d1a03060108 66
    0x8a00240001400e20b4003505045a040b070003854030352107504c0c8011082041280d26000071011a54000042c4465500c12606203c511315840081c08800752012001521001801c140c145a1640000c40002900c80034111540d5a802400e0359580c0c50041c00e00fa80c0750074078520b0020400c1d0800100c3c1c000303450b00d150343c0745a90350400d405840c003905c0d20002c0e86200d071030b0100880c5c104400b8440003500580b241c0c0b0040c422402a8064200030b20f0620f0a2401c481000b0100014410005803120b5066030320016141048000460400d82c0c0c130043c1800343ca8550f001318004c0062007084044810040c03180c1000040301d100344c41004070f5980340d040e0204008080d04604441410502c034401c01ca14003840d0341c0a20100c1c42400046035510744000c42c610b890402c111038080794544500e101c001014105d41404c009001018081c200c2c4c0301c413802001482c00750030240402c400418443d05108849046030520320f903040f01001141c108000d240d01381402c1a02840c482d0003403800014240c00045001d40360b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 657369244 1250 657367994 657367999
    0x1050907020a0b0a1a06040602010f141b0c0a06050117100908070201050d09061a120601030201170711070f03050c030d05090d05150f250807030f0b041103011e0302 72
    0x7013603071010368480080544c00c8a05da559800d007034400d000ca45980b8024400b80c0880c1c2c2c004100804900180400c2d41c0d6a0111158104011010000c0800d15082d82c00317542c13034030102155566000c28801c00e15080024102070452880d0000004140817046c1001c0c1e0340c2e4034114281c40d205103180104400316012004050907944040088800646c4944000c000001903101c00080401c62500e411049400c002e0f1002d40320ba107000c51200e0145441c4030700715140450180188180d60440d4002403550095502d95104411110b020400d903a0003103040400c0070f000103080317586095840188a000a14901c0700b0383d01c5000705180c02c0114100801c1c003c90060f1592201d510300804c1d68148146441c050000344c1d01400b0307498082407200e5030305940c80d01518450080c0403c5050000801c51452001c00300d80400e0082205804a0790740c01c500f405500c210182800a100d003c2d640c06000500304043c202e5078014501201c4041e8010144040d40c140c0e040319070064800406004008034a400c58000a507 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 657370494 1250 657369244 657369263
    0x80a050c0402030601050c07060216050904021c02030f01050408121f03110a030611040816120209072105041502040b09060f0f1602091e04060b01021c030501050907020a 74
    0x28107820720741c004581140c418504180f405000c0750b480d9041c07a8a5401801c0180c10504c1c0048410302e61030300a0b070142008135460403031814190f001851302c010000840122990144184041d90380500030614003802c1100280400d1070306103420071456000031040c10000e4200e06c0495a204008014030015240e08505081994150f41300d0003039050140c8000743e40440c0e11040880065814016402e10104000e2015203490401c5003403070406440020b21103080c070420300d0800030314610f440c0030541140c041e24000071700c4d150500304580c0403500b000c40c0402c4458181c5106e0015210f030340002d10541c001c08101d84100d44229403402603210345c0c8103903d101602801810207614100004016440d1201426858007001c0440e0100680200e218001111041c0c0744003815400c0c80c40d0174540c03141c242c2e03104403002e800c0400030045618015001034007442d903c4c40c00701401d034020000c02640c800341444c0390000307015880004026180900944d4024100304001c5280d0900003d11022010350004880 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 657371744 1250 657370494 657370513
    0x80105011b1e08040f0e060a05010302120c090d120c060b01030c022104080609101103040b0a020c0f060c0408120901090e130206160618120c03020133080a05 69
    0xc2c0034004044900761000301040000041c0348100b0b44010b001031008580d840c0051502104000040c2c51a0340600c1c18907004205e910a4000c40c034000ca40d01c0381c041c0110365128103407200030802002089100070400c0400007142e454082e0041211400c681c0f0504040c0000b00c0345a0045003074030700400b400c0001d82d02c00740c0004043c20303d104003543c403c44d803001800e052545e02d0a115190120036202547c07a50440c1c4010340c80790f0b04c10300070640b071441940c0f1308a243d030400b95642c001028004041414503a03012941440041c405e05c5543c5181c0c1c8030200725016824101c184001c40d42c402d204844144c82000d5500705015600c0c010380b0310780b02058555407100b914103c0708800585d402892000740e040c10450510069a501d0f016042e00758071001d20404008161a000341180e05542e4807101854408501d10006000d0011402010529282600840526240c181d0140c4140c98a648041030a030003042c54501c540c1c071b418000d1994240540030483d50320030206480340c01800000e0840d4026600d0f0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 657372994 1250 657371744 657371783
    0xe0a0b040c30050c0304021002011e0c0c050106030c051903021008041403120109060605070c031e0803041202070e0c0301140a0305100b010216050a1809050d080105011b 74
    0x40b00751150790103150003a500089088030045039021122000216008420700c010350412880c1c0070160f51260008002c0d03100d60307a000d024002501c00c1140d001c1c43c5c6401007140b1080c030410303401251ba43d1110007070180f02c0c0c40b45014404251103001d16802840f908041c1c1c050141800080011290050f080e034402c0c2511031000c40d03200c1e000600035a80441d2028941300b01020400060101910b04003103203050f541081400d006a034810361010040210910417100400d04102c900d41c103d0340c1c03044002a40804002c0441d5020a00c0000600f15500110400040c890358100307508030080d55030b0a946003142c0310340940344104419215002d07614404d00041c842c3c40c0d200440000948001401c00c05811703942c0e030ba95440c003000d0940d00394011b0344460602c0e103a542c04004905245114040d101c0e402c0d8141404101c0c0c001240c03040151040300640317254280c03a9030394000d2242903000015200050030001008e0080c68003842a2800209002198441100c0450201c8a043d500c140451000312500d01c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 657374100 1106 657372994 657373037
    0xd03031512082b02070309050a05091911070204020703050904153503160510020f090904240c021504080919030c0e0a0b040c 55
    0x880400040c01801680c8014000d415800f020030000d540d0703c1800804803014400b0f89100241d90020f042c1d001c0d501c0c46c140c9409445184441e6a2041803192100044664075211892030307060a0410141e508255545038641071094141070141c0c00041c2243d114440840209400284028144c101401001148488417003500d500d94581010350610310744010b850300c80d11403000041540c1c9421b15101c10100303d10302d006c880c0c441030f04240302c1c5200c200f015001e81d100d1003104203140e0b4644480c007c40300d14902841c81c40303050108903000e008211401810855040c50040d040784011007454001501d4407003540d0010400d0024004080d007051a42050480500d956108100208003001d041f6604d0707100c182c03840401c4002006000c54207044e01c1e00000d0040b8226500040c4500044070018020b114010003007007203021900c00c000490f00350941440100c1c417038541001e00d41e0300e20340 = true := by decide +kernel

theorem cover : BRFrame.Cov 657194244 657374100 := by
  have h0 := BRFrame.cov_init 657194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 657194244 ≤ n) (h2 : n < 657374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
