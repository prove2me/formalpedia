-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1719
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:25:38.821858+00:00
-- url     : https://prove2.me/submissions/a78acaa7-a203-4853-bd17-7e67b7fe7e89

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 308992805 ≤ n < 309172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 308994055 1250 308992805 308992861
    0x19060e011205250e0303040e060d050a030305061518090601030204150804060c0c0201200120180306090a0b040c27050f060d080c1507050a14030f010e 66
    0x1040304007050480d5405855040003c00c0311401d884810f881100c550a40320b07030594014001031050f00d03c04c0098039040b0000414060807820300d680c4680c0f600000103000c8001030303180c209000b4181002845200919404509a810850680b01568404000c021100c3c0b180390200003050b481c2e400ba80c102c0e4050f04100b04101a95440440003038010482680d040700c0840c900b06503e22140d214019000c0019416503d40080e4094544508595900f03890196140d541e60f69a004a6100c00c080f0180240480100b040e15883c0f2200400301c00ba0713610035158066000702e0200491038a01082d0300300c100e540320110003a00e840d6410010401c44098000b0104520465202c0c1205525440c5101458003001c1d000c0c0996940c40d501801d40d1401600c0c09600310a10340104400151814054560b01d070031402200d50f0064400d08101075810141c501001050f0000f07041904503a2001c1260511425400854550b05100020700da5200c014454070390801c1285001ca00c00b001400c080c0030462860b0303d008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 308995305 1250 308994055 308994061
    0x50306090412140c010b120d051b120a09051f09170c0a080303040b0c0c19060207150b120f0606010e030a080a03023402010f05040e0a020403050105010519060e011205 73
    0x140d4002d14400016130b201d0004120a803d01f9080000d800400c00f2169403824107006000d15031002c014000100005a801340c592070011411450380036020b0060507954004009240105004294091819052001110003180740c40d071074118190354101c40700460400c1e107440f038000242d42810300c00707808560701c05962800050050000005540580e004a000e500c0c140ca5070181c0d042179209001e1160358582001d42e00c442440c3c113004007824000d00031035025190450b29600d2502c00b04078a82d004180d156242c410007540c0c100928a10088100d65004160b00d03040f84000c50303034544004010f0b50410400204070b090544040c49100c005550201c105520380003150009070103500300c05e036a0615901c0c2c1410720500c0c1c0c80350303042d443c0400c1101003c0014915003500111201303626000c2c2c0c0c805012040000041b0640c42804441c40784640c0a4016115801d51620500791407041e48214408c803d4070b142d00740080300f041c4a1008854a03402d00b501405c3c41400161034011109100c0c450032481c00c0c0c10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 308996555 1250 308995305 308995327
    0x150f0207150c02270f0115300c030b040e0304090b0625030305070305070c0605070513030c0806070201020f041217071208061f05130f060f0f05030609041214 69
    0x20b8582101d50340d0074410350940d00c010783c1c0c405e80c601c2441082c55500110013000720301402204601c00c00c01c0c030760f1041e81d00820782d00c480c2c20441004800400c41c090759408034408030f5603d8418081056030494090101c02090410555039024074000ea0a0040c1e507205400650341e02c07681110104500300006840c0000030392652001c0442ca50f40541c0840d040c000002c8400c2d1080c801d203440380d0a140c59071100005151180300c01050b00030032200911004000b031081c80c4581c0350301c120080d4800e51040c000300c0d0903d214203003440d00c0070780a0425a0300500900000113840d0054505a03420700741c0c1c00040511600703105044000101480b80407050019441c0243020800c1100b04e461040d82e107811070349444050500100e01036103035003030881204c000d03045140148900001d000d00e580141e0320403195515105a00c4403200150302a002081c0500402200240c01070480681c11500341001c0d821843c20710302041481600800c01031440d0000e4031007042c024050507004900d4100016070a44413101c03524 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 308997805 1250 308996555 308996599
    0xc05120c090d0b19090c03113012120402060d0f090609021e031002070204060e09010905070b0306010e100513030b060f030f191e0b01150f0207150c02 66
    0x40c0c1000808106074681080c00140c5c0030301c032003155001190703c115a03e1034494805070350f0204101548100c0c00c3c1042e079552141c843c0078061030f03c05200041642d040d03080b001ca1400844024100381110180718191440c01010a02613100780c060b00d5441d5201e8a80d140c55000344080003802e40780601d42000c0b00280700007a030101104600c241d492412442c00c0000381c0d400020310185503039148e8000501d450745d103503080d00944407461000e80040b500c2078403203424041a000484500440da07541e14070f5002400302c1006a00300034012490018a035050220000304a10a240340352400b586000c4a2a0340c07a5115900305d4500d43c400f4014068035980340c2c41d009601903002d40703c1c00d1152407995030340300c0c0921340411103400701141500142840c0d01b201d40c0307495038100810300603544248040e40d00030500e1700500122041d82e00c80d080110042d0b040c090314000c126405c0c5041002c01c81a18122143d59400288150a4841082054201c411172000c21074216071640780003508191b961801d83c100f414244 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 308999055 1250 308997805 308997811
    0x105070504050109063b180f0609070503071404361a0904050717061e010302210c060f2a0303010b160602180f040c05120c090d0b 57
    0x10340c0e9112070981d65102180e5001d41440b00148400e084039045020100382d40d403501400034010a81c0000200006c0050000c90b03210044219004c0c140f420071807810103450301d00340e024004035034440c1181030050300105203000061440c010702c0300c40c1a03250380399052030060720f00404081180036100f42050850044c48620090800c0325a440045541101e2440f401a481c3e03030303501c403400f00714105180f60800c002d442c03010300b0603955030040399404070780c0d03c07222241140c9075520b040c000c000a080031002407542400388150448010401c10040c40141d41d0b1041e000d5007184000d01e44051820341c844114140843d103601e042c0d02540001c0d4a4841406140142084035071016440244482028490840c40d440c501c800c03505400c10001403003104110405481040c034103a0510f130b1070f111160749020817680605124646444944062885407421441901180106603030170302a8403504140684540503026015030389400c1d400015203007083c0f110940ba044c10000746022158412030501480d19401a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 309000305 1250 308999055 308999057
    0xd090812010b04051302070c080111070c06020109080909060414180709020c030901050304030306050616020f040e1b0f030a120909110307141314010e0307150e0303040801050705040501 81
    0x400c00014926603400c1a501190805004c00380440e4049040c20000e5020442c201c070a4000c240011440000901c01d46c2107803503403200100c8d500d00300d42c240f6160b110507580c01403045a0620003c0300000c0c02e00c1e01940ca640c18251400b00a0f89c0700d200024000d8810000400a410481e80c10044d422010b5009003204441c804191080285c9485488050344181c4030449000e9008020704455944610f0045601c14007078600010015110400100c0325409091405c40d4002d88141c0c1005520b0050703948149100104c90400ac1d0340c150910190315904c070841d141c59462501142440c16444010081158000040c140d80c004140c9141c4040050001284e4100249003404003007900130300d9104034100008614000c44c19643c03045070031240030400403c6505801c0d01400714810200d10b140780303040500080400340d2144e50034480014211400b041e10103200741e00c080402c105c82c42000600c1410810070b864082040e0841d2408203103141309a60180000f58a40740c1004003541d0711070003901c1981c4007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 309001555 1250 309000305 309000337
    0x5011b0e1203070209071101051312081b0307020708060a060e13050a121e02060702010b060412021005070f260304050619060506160c080a080712050d0908 68
    0xd10003441901402941240e10561081181e400903150122a40d5440725142c600380300f09071081504503094580958901000420161a2804020b03100550780000103a81c07816450b14501034111814024041203d4400a00c1c000b000c55405403027403000c10060510102164110305103805c40500404d4103204104000721401c01081c42511100c00315034450b074005000308080c0c140e0342c41d000030800100c60a04140607411030a0b0704002140b142c00d001038480e54010f03207064506104082c0c00e6405942078144948410002802030300300d8540c18101064040c1c409047d42c00580c0030a850034401e10001030001c0d0034100d003800c10000c03140d507240c0042d1100d00c1910440c40e4010f069a8607404213882c002d03d1a040000024090303811041c0031616018125800f0403021350710404600d15902420001c0142e00301c03007045000707020305912000c00428001c0000c00b1004402d03103070102c16010712880100b00f20441010030420f18840d00c140c5506100da58410814090b4a142500040d0700030040300c201020 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 309002805 1250 309001555 309001577
    0xd060501020705130203070219051005060118031e0602030f04051b09040618060f0b0a080304060804080708040305071d070815010509130e0717070302130b060705011b 73
    0x4800b04071107080b1980039224604100084182d01c019400c0242400214410003c804444800a031802c40300d079802000034140c001d1040b50210140e0354000d128070b05000200400132810740d10003c82e1400c413a00f154003400e0841c601c000c0d150300c181860101038640d078004014006000300350594103010f140700318120b501c01c11a4441c4140e20b500740c09121540800b4090000d00031550740e4200d0700e0a14800d251203040003840740c0d500c4049600307080b40000c0d40c80d9031f1000c110b120b003402d0006e000580072920040d17081c58505030000b00a01e0000704010003414000c01c02404008180c000e071406940c4c80f80c145c2d21059240c000d841c048048100000c1041400c842c04079141500410306540030301300c203404600611840c400107498a502c00c48000303070041015441020b81501d01e2180c84651080d10000c8c0080618101c285c0c04a401d400f40205116041f51504100684d221590b03000c20b254807000103d0803c2c51803002404500079040050825420849040610809034000d80c0d400341d185e46403401952 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 309004055 1250 309002805 309002807
    0xa140a0909020d150b030a080409380102100e0a03080105011701050108062d0108071e08060406080105040303060e10050d0b0a02160c080d030b030a0f02240d060501 72
    0x900480c4020350021500f601c2c410100c0c00301854201c040b8410301010454180040100b0715002401b0b80640e0346550108051022400c1d41c0100304052130b120549940500d0790401e1825041104141c49000c0090040740f10a2640240043c20151050b41c07030030814600d5a414894031000050f60072400038051000110f860341c00f844129456014000b03009030141c1c00d010040d122540050045031f40241d01c00b42441d1303040503038030b049210451410a00c40c514072203400003408a2802400b038105002d983d1045146000211030006c3d40101c2628010042d82c5850010400510040e0481d41c819402e0008000516805400140c02c8680415050701650f544400994801080b03005141d4040780348034499020914504145400004000c001031800c020480c180d070b00c0094400c012940600c40c0e40b01000310172800c0c011152001c0d40c0d030605110704034901c00000e84820303140c0e00040c84041c0c8550b000c020364442c0b8403500f2190524907500f401c1103c0a02c00e011064000c0d0256501d00390a10001155079 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 309005305 1250 309004055 309004061
    0x406150e01150f021b04110c0c1305071d0d0b041a010603020a0c1b0902190f050702151b01050c07020301110708040e15150d15060806040e03090a140a09 67
    0x22060303406400c0c90f01c800c1c11260104510354a00503405501e6618040c60b447e03604008003410b00181000702001c40c0100240a6002840c1c1c2012108030314020800505541001c00d030084c0101c101c05540c1c606c4540000110b003084ac441c4003601900201d02080100a1030905c81500d0700344508402c5281da90303d1404506900c9a0140c2400154024007034900207045400c03d0b41d400340810380c89a61f000d40301c10040080f17800503c400c003040039240c0a0106516000680c00c00000e41c43d280c0980340800304c5e0040303407449991a0115001c00d10000b18580740201c81107820004180318002480f00c0e080c00700410f04903410044090f44030354038101c85844c6100488048610380f6601004031401c007032a00c2c2241101000003003000301198142c100680d025038543c65808410004180c526440d000e03032079400320494204908030b24081080e400240105c035041400540d018404650108824100d00d02481c1140030714180c9980045401c5d40110b080b5000381d03800711072010103680400c50f42c3e40d111890000e07 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 309006555 1250 309005305 309005327
    0x10050708090a020a060f020a02040219080a0504050c0609010e0a06030c110303010305150606130603230709090e03070614010801051f0302040207030c02030a060504110307031502030406150e0115 85
    0x80010b032541c4c1080018000e0b03d420000000c64015a0703101d02454001ca070590f400300311901020310040b5040d0101c15048880c041c0c01221a040401c85458a50384d102c0c3d45003450032446116000c0424a6000b5030f1040c0e0760440d1308140908064441036130b030174014018207401c190507001701e81e00c0000a0582013000003541e0490303422000815810011914101c2c24402c06440281c101c0010042d0540e030041ca150504004c00c02540c00050108403c800c001c0740441401461900c3d0602400744491140d1000091040d507a101c0030029001e402e03400d0140c1307540300e000c0380200315608164141000f0502c00038100e0403103800000a001c207650381b025007090325549180ea0686804c01440500140c10140d015140441c0b090500b0b0700d44071155000689829103c0c0700071200d881d00c41c001c100400002c0e0000e42e030300d0304007907000340351140c2544e40e160340c28500c4151040550b603001c03001130140280c40d0000d20f1501035103520408a01d03212800300c03508040902591b2168a560058150041e11490702d0300341d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 309007805 1250 309006555 309006559
    0x7030203030109051b0301140103150e060103050c0c0a050604060b040c08040f020105040b041e0602160e040602091203180114040504051e16030605030606090c0703090810050708090a02 81
    0x2207141e0070110b6100c0100806465825500259100d03900f17075010400085001c0d04010420200007620103000405603109901d41c4146210841030030000902c900010030f411078424240400c10743c3c2c07014245171040c011503c0442d400e00c101e51068003407050118a0768003540c05110305005480340d94080c40250b031194003410000407500c0c0e00046c0403c1d6032107000f00c0941c4c81403520074942940c0d0520714509800c9a005243c1d2b034108407200079071505540c40d00304000c12050019028030100f10910058a01032840740949089001001500300f0001c2d07411520f40b035000402c1003801e640c0383c01d001a03480e000340c04055801c2181c1001c91600b0760041558001420750566040c3c41c0c581441c00740301c050000a0000052442075160f03034100d200402d10070750310504e14221050241141c070700006094580d0703036000700d0080e0026414010755481b000a80c2d5448001220702594550a03407904440c006041e90000d0788500034a41c410b040d01c00103070800c5021310076079500c210702500c44903200c0340c41c0c100d4a44025 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 309009055 1250 309007805 309007807
    0x30609010e090111070c0e070c0b01050f0a09020d1d010911010e0d2004150b16081905040504050c03060f010f090806041b0b030c0403020d0f140115090207030203 71
    0x4003494008203119800b00720480007103000304c40103043c8541604070b000101c902d2090b200041c4218401d54126950002491400103083c0d00c0c661140c8240741030602406015580d1560b13035001c42e40722480c1c03400040081c42c2c021540c403040d40c100c01004100c85580c540390300081000e0840046014000c1c841003030f80000b134042e10514000300544840070705258603500055202c5682c03020039001d04010500c09004011060840d018001700400c8070700d44074961a0840816034140007003c030328001d0756000481d1250505400394581004202c81c0541a10901d03004c84280ca816804c503030220140c170890300191814403030740d2501d00b01c0040038002102e00c240c0008194030031200390b61090410841404603414a12850b607120700803141805001c86040d07920400c804202c002111807074902d03000810b6030300e005606505040d0b81d111414451071002034413402d02020702d801480410104200390b55031140e49841c1d4160401c0710316028001603a144541002c4103080040c9680c82c600884240d59495800b035 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 309010305 1250 309009055 309009059
    0xe07050901030b0d030f0201050a0c0c02100306081e010f1e050606040b04060206040b09070609061416150e03040f18060503010908031b16030503181603021503060901 73
    0x21109600000201410035407908044a00c0303442d100e0101805078040e944070303250506400d01c00303420340c0c2000d80b43c003450700d1808510303000055115401011071035045074126407540d60420102c01800f41900070b07480380d0040c1e1003004002c607100d004011280743c00200921040d00d980c12101c0c1211030b00d401300e0911110402e00c519182d40554000c40c1e000c20000c0010b42020380b03a850100180d04181c001c1d82c050fa0000c82880188001c070607841c1c0d8403480b00c100410f00c0c0b50400700001c012013440c2c440c12041c0840c008010481503444015036403803101d040850807545100e424501e8031030360354110604006252942c910440480401110309941c0c5002500031024034040a140c18007910140003601103569150100c1c1c00c2d03600f07014081c8041c0c020074081c1e889040640150300100070610800038600313000c01c180060920300916001406405091841e12507441403403c0e00d520340c4028080c00c09004501800d2801503607040440e0a40b4000c1d01c1c0d00244484001460702e107440706442039980030300e80c0001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 309011555 1250 309010305 309010307
    0x40506131106091801080307020a080a080f28050a180803090d02040e0303040813091e09050c090702012412020405041719031a1e0a03080c030c0601050a0e07 69
    0x1d002d9502c0240c540e04a0b40910311403d81404c0c0e0a07008502503400001d42001076161882142024040d00d0b8003814403101e440d9540b009904c40d0a2009105038004201c002c2510700450010460390565460305814202d548001486903018000075030210756200110081302c904800303188151004480212310f09038002e810448507020441c02244c0c05511091481c540c024180095030141e40324015050311074520300340b5804200d025410940d1004d107044150502c2d10218002c000c048281c80000003100340107420a1b50501c0c0d84442080d4202d461802070192403030f415800469484001c0d504400301381d401c0e000113650400b0300d02c190341640f20a1034419000d480c09521a81d08240303d000030010883d038010192031250800e07110070304120300d05140c034400c0c0c039054000c00c07079403079a01440c0318606698407002500082526030603400461030580c08003250346030b40707202c103016503041401e01d42c94038401852155250b00140414001d8041c08000241a00300303110494259101035034035083e0b035919008 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 309012805 1250 309011555 309011557
    0x110f12090604180b150a0f08040f080a1806030b011205180616090504060e0a0e1e030306031b031b0a0314060603010c090b0405120a021206040506131106 67
    0xc403968000000c100c0000c0307010081e40b81d024412280600070501030014020040d0007052100ca90411107401c1006007001684004480e25290b810f0800d45c00302d440da0704243c104c45ca0407100050085400155205200360000c4d250000501c1c5006d500700b0300c07030302d800048064420309154207020070b031100001d80c80c41805400c00303980b2861a0030013140c1e00c1c82c450f400524040c000e0361a450301172412540002c9065004080c00c3c050501550103102035494010300310171410b0000c02d503030b0307406d81e0354401103020100c1803154888400111002d4001143c0c1c101070240c85c0c5d0b00a50354a4420b2007103540b500f40603100001c034016242d40040c00380c003940400e840b101c000e110205800340c0d03200641c501c0c0440018900000082c6104680b00240303041e19003c0c091508451901e0360f07117418440381c0c500c2040f40740da040044506071a03050700c11740d019602805000d45400200c880084d0301240926004020702d0340001c000f0b202e07501507400c550039900c0c1c0307a0180c41c801020550180204001500060700c030b0a02d14 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 309014055 1250 309012805 309012817
    0x150b0c070605090d02040c090f0b09010f030c09150905090906090c270703020301080c0a0503100e072102180f1303020a12020106080115050901030f0c08030a0c03110f12 74
    0x180c41084c007506035500140c221024009a1b40209500c080180120310504070b640303020f0151008100d01d0550303891b0000c0c01e95543c105590b8109a00c514100116a104100a000070825091800c241180544029042c0302d001d00030305000300441c0000540c0c00c103001640900524100d40a091881d034981c052012848040c1000d00c81450f034048480940f50040c1d982a02c1a0219980103850b541403080c1941014504055140309002c8450140059600461600408460101c0002d0440c0446605a003080c00710b900c009000c1a8142ca003240380041c0042003007059108440c0896510300d0000015a140340c207940c20070040c4e04d200300143c044a440140b820f00b007402401141d0f0700403144d90307941c1168400e034040c4c03200503510307190100110780090094500360f070100c9e19000d00303813420100420b01d5020144000351a82c00780344400400d214060b121a400b078041700341629580e10a07032001404010b030111b0300700e0000780540440d0044c0070f40410300f940a082680068061004440343d60071807a0454 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 309015305 1250 309014055 309014059
    0xc030e1506190305120306010e090609010b13050d060903140f0301050d1e0c150207030305030a050c0f0f090a060c05061602161d01050126040501060315150b0c07060509 74
    0x40380000c404504108084a45d00e601840240d6032450984c00052001a403a51028040c6181c1c00600a83d0765403a0620303815074088041c0b460322250b81d04e0148018040759402607800c80e4084102c2c8040c801d03150007895001d0f0003900c0345080c2000000742d803030b540e104904461811078011300041c012881c11400f0b0241c25030084604510412590700100c401000e501422a10030845110030414a000c3d400d4a42413204140043d0440701d2840d24050194407000700b40a12407580c54002030401c1d0347c2d21080d180c08080d04444030b6210050150050159400264800d105030511500062500d101c0d00c0f10021490707101003d4a140d449450b554261080c2c0392818106500614041541c014240180d0000a011400d0b40d140c0e01e91042504014000041e00726030f0412100c0042600100d40c60880041c2c0045c2c41a0203c003155100d0800600410050300000c00018480207001d60608140d08001c00d03031036400345071807001079491058500e903100300c9580030780f180c1028404001c000e0040c00505888500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 309016555 1250 309015305 309015349
    0x3050910050d060b030f18120d050a14070c0b060d05070b03011403030910030209180c0d06080307020a031212050a020301080d030b01120c030b040207060204150507170918010602010c030e1506 84
    0x1244045422740156075803100c00c0ba500d0003081001b040600540c0084170005c0207507840d030304248200604540c40c940c0b0240a101c0305a002c02c00c00e07100c5100599456401c00c0964400039201c19405901d94001c0c03140c003100000c200d2240040340380200440701c4880c0001c0c205c150f0101d01ca0000c1d0042d41007c841030b0b42c00350800e012035540140720580c0e188101d11105e203403584d5400d1b8004002c202d91454201006660045c002200181c4403400350005494001000f06440c421800e02106c1c600e070091221b0500c5820a0144800d01c80f042c1c0280d030680d078600c415a0ba081d80f241c0e90887c115811801c1050005160040b210422443c9900a902011981c940460041120030128003641c0c4051011190241d001804001948403c8844c010f04c40302c80c41d0180c6031180c00e03190745540042d81220034202040005965856a41f5543d60a0400701c550040035029a511040607000705105003070713403000c03904002d414030a11102060580190a03107000c00e100a80320102403101413001008050b00e2018 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 309017805 1250 309016555 309016573
    0x3230a0e01090c090c0207050a140a080307060c030b030303130305090f0d050f070e09060621010c0905030717030f07052a0103060e09150403050910050d060b030f18 72
    0x2002c1c0118030015014200708907100386094151380c03c40d4078103d01d01d011504108000c2c402a40d40d01b4607602100c59100407041c080c00150300080d4214000d0340721300801c0c40006003507010002d0300d4101c0c442d03103000b0b41c50800603a8000014142c41c0d22085608a1100100b081458002030090700644140039028204044500c07504c4e01040491580500c10f4800d43e02901c51140081c004002c08005000348802514003414201d40d4290f84590152009218651051136000c06070308030f02c81202d00c00740f0480248524446a10040d21004031070080368040c1c000e1050202d41240c2101c03030710150403103d400861400700340c1304c4502c10681116500b180d084c01084c10164400c8480080c0020019500703940010180c100030007d401c42e02c03241d1215507140880d50810001400c041100702d01c1c0d1a0140b00b900055480f458110341302e205440280d035000d0800c1c02c172690015400b40140402c14505034081102e15261002a40f00e4003084507551040e1124200081e01c240b006005e8a60b0500c142003241c01c0c90f0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 309019055 1250 309017805 309017831
    0x70305090c2112090a061d06030a090201120b0a032a06020609010c031a04150306020f0703030506030609060415150e06180c0405010507150203010806090d03230a 71
    0x28506000c0c210300c42420240c2d41071280814002403102d08116021a45801641d502050b40455144142c800f440200c0001200565000d0f002d03d800c181c000382071035904e107004d900c50b0004000482040c0e0008049400d031014290b254424091030340d60040900d01c0580c40c541d15403042c0d00c1105001d02c1601e8441c1521a2904422844000646066006803403513103401c1024030b00310783c414a058810507003081c5000d418588646080c20300700000380c501080502d40180224030b2800c07903500040082e80f000600d521110308120150016500c2946c6c1401191550010980c1d6908251611200c9030800350226000404040300c4000a0200c64004504041d01c598000c5512020384d104c0e0018802440c10801c0d5480c001c0e80c46520301420b902c50784c1c04c41c245035059590600990140f2814414001118001e0221140322050030924441c1e0540d81c0c4d60311017460303d494500640da2003070240301d2100c3c0c4005041c024000c007010001d56070014010b8121300e01207501d503a04050a840034640e40c4014040e042 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 309020305 1250 309019055 309019069
    0xf080a180b0705070b090706050307032a0f0e0603100e06190306060501080903070b01091503061503030e030714102c0901060e060415090f06081902070209070305090c 73
    0x103006280c03a01920f528844c00d02c070001740001004106250000c810a004050300503080e04c1d0071074828074001032000d0049201c46000a81c4401c0c1d60b840c0c15030055480a00f0342e012464203091810399580c0140c81c004442440194001568000010300e00d00704140502c00d03030f030440c9030b50282d4000c000342c24400c06001c4d00854500b0301d41042d01c415854480501242d40c1240107183c1107000c4c1001103140c00301d01e489016900106002e03102040345c40c3e00b03030600b5024000303c00101458010604018451204100491081d034a100450104106031000301a43c5004144041101c600f00c015401e440300d21420013012020b60040f2405000903040c040c1c81c00280404d61210504558034094128051002000020360050340090104000746007200c2590722010240c1e400c5030090b040e0111009805402618000d07215048010b040c014202c0c0010382c0341c3c5c0820264050224440a41c000b40070441a81d01a48100300000c0d4000700e04001040c6901e1103548215440148102501c005072180000a504 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 309021555 1250 309020305 309020311
    0x5071104240e010512060f0403020c10030509010e0102090607110a1a0d1a0d1b08061f0e0c030612010605030d120501051009032405070309050d0f080a180b 68
    0x40703422004014007941004010203400740008032003501410301c401500d241d5070b020051542c1c01040540d80402c08140c001c21a03141581c030024135201c04085101c10060050400700e82c0070100358200351440c03d0805044c803c43d141d0400103030445140c034001d07498507034010b1904220203130000b1500b031000680b5113800d0130344004c16103905401d40d602d5203607005520640d0300d0000060b428690a0108032015918801c900e02c9240e40056240e80e400f600e021140841c0d03106a1180240380949030130050104c00c01c1c0a01c09681d40030100c50140b4607203a24030951000c1d07044844030702e11101080481c0e050f290940d50716100c503003070400100b005902c0300007003401d001c404d5440c5400b1a0464003020b00c160480c3c001e56001d00300584160801c1342030001c000700350760b0725440007a1400b0751a22042c0601e801c1e002400031449032261080c0558200f180000740104612001a5018025829101011441a1520f202c2c0901c10f0341c2c0c0400545841c00c4010040c03c0424001c024040c042c520400000d0464600790302c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 309022805 1250 309021555 309021611
    0x1020f070b0f271221060f03030d11070b01061707050c07061d03010f0c030605030111070809010c062d0510052704080c120406050708090f03060a0c030e070605071104 73
    0x12008404400e6500d105d10302400c41c41c07241700d140c0180c01c4d00e91400801d4801041c5400320100ea10f109441e46003d02d481000405014842c07010000300341e40e604508008840140500201d01c5540d40c01b2044550b4000c41c2001d0b00d1a030000042004424402e01c040d41c1d000f00b01000c2403040c884c4030030019085a44508100c810941c9074880c10143c3c5402d44180300003004244c0092146240c0c0d030002d0000c80c400c2c1c0c0c50041c2106000706006005900c90340c0d4419142e0380c00902000100c00098405d01c82e1503003419218076007120140d083c0841d00701401401c0c010460341650880e02424141040700b800f98650740f40071000d2001a02011214942c12020700031170086400695518130700c00c010303007015007030500d60803885400c100401560703030b104045808050b003100c5010740720754811001881070004048815407512544c030034005240c2079603001d00040001030b2070401c260600050a10b071186118031451012900c188440c201041d0f55010b0600110801000003e0714400b061500801d082e9a201c031070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 309024055 1250 309022805 309022837
    0x20604080a03030506040b060717030720060619031136041e0503030f060d0b34090902071e0503070309061809020c0f01020f070b0f2712 60
    0x200740383c02d2174800c10f00446000e42da4527140201503194a403c1c892080a0782108100000015912a10440c000c504840c0110500d1445d9408507220340e0392980155803c07803080005181c030042d45a8001d8407a01140c0e03000c5081004086a070080001caa10150000c0310300c0501c83c04030f840c501c082d600500c00c400000c0380746c440c414141800c15117440c91030071444070492151b00740d80c4400706030000141d0741c1c080d40e803840c8481660780340320100c0e041a4244a0080902021030148114040f0f500a50016242015402c1e0500c64810b1140c3c00c8800810900e030300854400c0c0018080c50150390000e0009138001c0400308030f0030302841c0b0308803044540f0031000e460542011400504155000c0d2071600205001c2c584001c0c1c2140b4400340204410b5988100811950300082844400d0b8003400a001c90103030340b030021901c03182c1e50f40640c42507030300607001200c10300e500600040100c1028808603001e041c21800384184880b5070059a000b12008506c03d010a12844220040f011007050041981c01d00d000000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 309025305 1250 309024055 309024061
    0x5160906030317091f0e0d0504060e0904020108070f0504080604030e010906140405040209030f0d050408150f04060c09030c060c1202010207022809060b030124020a020409020604080a030305 83
    0x8020310034025120803050194028813844520002c0c840b560002c40e00f030100c401d000c0d80c01c9102c008041e96010b0b03600900075096800c40c3c813500030303001c0c0c401c441041d159441ca54000320b040103030720380d41103c00a011804203008a40182c2c07103003810702301c0c04410f401c0c0a480c2580b0740469515200080700c08070001102c0003030120507540d2240004009003c541444600c1c011000d514480e24007480c001c6078022076001c03a011005039400c100302c012800d074030001da50282e04030303440082c0366506c1405404082e10480c100301c00c50100301c0c520140700340098034844256403036955500c0080c020210100301004418079000c0013080322410b40c2d000070811521580c0300b804c65481d01c21141b4040d0160342c1c3c1503910502c401805600d440c00c1010042115051210710064060030504181000350000d2000c145410b0300401d2112043e00114184d83c64007107020400074203040c140d60b40c010140207040041e000303031003001300506140c2c11050f62144000c1603681882d0311f40c8006e504e45160302c030741503001a4450041c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 309026555 1250 309025305 309025307
    0x30f050d0206100b0706060e0a0f18020105030406090c030b0f0a0522120201181506120312020d020f0a02100b060301060f050c0c060a02060a060e01120f051609060303 73
    0x420480a40140080c10043c68410303034101c03860085101d03590013030720001108010010380b988024050800030310110130707504201911000030300f1040d1040501c1807800440f402181030b0000c0c0c02080e2503050395020b00d965a1551703a44080c2c14159011180300c3e41005e00031000070f0245007024444e40e2590f22402d8285000d004034400c0e1100901107803480405441d60030020001404000710300d640185004510448016003280103003ca82603803117103801e11a08400c2040400503a0340e10305e4410340402d020300341d103074180d05541c0307000844004c0128407030144480380da90058010b4440750384240001814a090301402800c6079000b80300c400c006800c4a44400c0740b070925803161005900f001d0f0346082c1998149000079007002c0102d8020814040c010810b888201c504105070360306002c01410654441280c444065030b60070080e12880141802c02601044200c00d0200ba681201c82c0c841c02c14075642e10607140c440c25140d40c44000d403014002c0b800e040c0b80e078011042028009000e802d40c00551035241d814 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 309027805 1250 309026555 309026563
    0x50708010e1924270216020613080105010f0608090d0f1b0614040b0a0c0806190308160b0708100504020f160c05030f120405010e060d0501090204170a24090c030f05 72
    0x860000c085c0c8103101c0c0410500300c0c070006d0702c4015419541c103a92040c1c04021550102001d40c0100d115600384800401c2c0412218000700440740d445d1031341d60711a01c4200c4002c3d15503041039a4200090381903084012007500c2080d071140d03002140c1e40741540e283c1c2c803a00c030b00054460303c49441c5166050241030100704203402d00302c10360210802c1002c005481c01d02200074098200504524424041005500f0100180314000001594000c418503a225031030a10030403c00303d0040152055032141c00011031840c05080310030b1058003102c910251041c02c1004000080d04150491221008244116101410080d8401070034901a00b122a51a0318000400d440e04140c44c1900c551034200000c6e40514840081c107179000d840003405c25008440442001c1003281c06010082c00f8050301301000050300035010345c01841502c0300a4400c4038404034902c4015644c028070309008180020704000502041481107695221905c3d8807400705000707850340c0718110f4080103034006503084078040740400c1c10048108 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 309029055 1250 309027805 309027869
    0x60e0318010c020f011404080703050d081f03020607081902011401050301140402090a0e030d0501030201080c0c1e030d0603050309041d0304090c050906030103030201050708010e1924 80
    0x442c00c1450030724070754085100b03910780c3c1d880d181c1400f11940881040000b82030946000d81105400c44080c0d50b5213050660355410310303196030030108952401141031003007400204410389010061224805155a092161680c003601c2c05130b6005405105a0102c810140f8060500380d8040d800402c44d0211490003003000101039002c1c40c466890103440454940c40b00141030390290301100d9035010395854003803100140000d40d2815880c2d00002503071212150305a8441810b1364000c0c0c0e100b400c1136940e09842e11541c82040c104040e6030b80038480594580d0031030341e9001c900300c00c0303d0b00f030b44c0c00c020203005480c054803540e4100711a19040400e800d502030419208900580c80e60084420058503424041c4e51280710303c0c0030380301c821501d801e2488003a42c003400443d0a9020041c08095813981e49040090080005403807820029550340d0001a1403500104072038042c1d264403000380c03901200b410b1881d000b0900b20b01140c14031406100c40340103c08000400c1070003000c0c100c2044054103003051502d80c604000b1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 309030305 1250 309029055 309029057
    0x706020706020d0302090315040c0311040501030f2603010b04080105060405010501050406080c0403020d0c21080301120f02030703050607180308030c090d06060305010b10020318011b060e031801 85
    0x1403002000076581c00901c4490280301d0381070060b40c1c3c02103800031a09118090140310310010300c050a00080040d2000032200300e0303000e2102481c079000418100002d4a5081c480940040c801003045c0000c511503080300e040980c1c84d0700720005c0070050794541d00a1a002607100300d05042002c14100050751027130280c90341c0400100c43c04c0000e9810040007030b2950080f400340c0c001b008040800a040003d0700740c222009107400a248500c01800c41c648001042550b001e00c5001c00211f614282d885524140c0c11684141c0c4504201e04582c2400e0601c090380c44071410a40300c0d0400c0303081800c0980c40600641c40550300840c040c100030320b08060043c0003080104070400e99085c16900410100340c10006498100310b4074480640e607180741100040e105256404082c112900d4944000100241540304140303541c415aa4880342c10070209050381c69004000e541c1c414503240c0d010080c84c541c4100c042c100650b005951880d2084d003651524030460f60401c00000d1940d0001070445144021030006076000402 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 309031555 1250 309030305 309030313
    0x705010c05061b270f01030213030b0702031b0604050c0d030c03080a0207120c0b1308030f060d050a0f03140a0f0f230414041103040b1e090604020102070602 69
    0x200341e8590703654460040103c40f0104080240a00c001c1c580821100c05a0841145102c3d21141c44200580c0420b6494441d10810010010741d41e55402402601e25446e4006001e0740c24901d980c80b0b00d84a030100810303400460000300954101e054400302e4160712808080c0c001d100900e05803a115181284990303003140724010741c000080c000380c0d00c0010b0164550341440c090000da1a61401c40d0003a0081f8a0000c1c55200d000d0200d02070700d40c0c040d9484480b40c6c000c20144803d41c54031400c05d080d41c503050001800122040000402203005000703e190464000f9080300400d016a4644605040c010401198104200c4011806040d0f200c1515a81c0071041c42c0c0c464074180d10400d01400240764511480d090101200300c0700f04030740c000c4107215004140c0d01985048441c8240d8480c40640c050300880e000e40110442ca04864103013846054000c406400d2510b10b141c5494803540d1a00c1c40c001c6c5240c240c140c1810301c441c0e901c00d041c20058001c03030b0103100410040c00c0c00c0c400a400e0600a4001d0421580 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 309032805 1250 309031555 309031577
    0x6120c02070b190e0a0617010b0307021009300306050102060c040909020a090518010f0905071208160605070e031501060f110d200105070207061115090f070501 70
    0xc20100300c0303211030910f480e10314400b4080c80b400d44014512849080d4001806107000a000c3e810600d1819001500038030507000340e81741c45260704540400e5a00e1030040c0d05c66110f12070b800e04075600c0b00d01030b903004010f2498685200000a0108444400754400c242c081c030700c8144229405015500240000f40060140ca02e0125024180c6000e18800da0321b0315600d4802100a640341c2d404400c0c05080c0031001030003246000744031020f0b00d5007400c0185509610700055210038190034440c2c4c40000d5800b0700546a05494034809801040034001d050310010350801c14219404200d06c0e9500c00517201d040c02141034501040058038215440c90f40c1d0b8065085900070381640400100b016042d1071503400e01007411246100b088854564621550100b0f02c1140d941c20503944e001800000f520140001c140c00d00c4810768001802d94005035400e802603401000709010300b6006400a0a001c010002156400140c6060071101e50b50300b5191221541c0200e24501840722062120070040c14081c00e111031108 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 309034055 1250 309032805 309032819
    0x210020703051e09040e0c1528110304030309030b0f040b01060f030b0a09050f01050a03110402030703090209070306050411180f120607050c01150b072a06120c0207 72
    0x4031a10f440c0c0c0c40228544451641050505400e075600008054801c002c600b220040c15641c5a0840d610540b0034042490581454030700901151004007518480b0384403100c0503c80f03510000c0c59856441c0038070540c904000d100c1030b0204044c0004500a5a50445007403070360402c03940d6400041d22801c4990703450390401001c00e80441010341101c00a180000c1c0d20100340c1c8c412001402c40e00c08030395002e20500300c00101d088064001a0052091807041009640c0c0d0b0010010052010300c402040c80d60100f842802e2413410f607002d182e00820700d041c0414a56900d0340007894071101180d59402003952a20700744405d06241c840c0d102c1d09841c00b00c0c042e1a040d003101800104401035005540300c0c07140c00e490000e00c0e0b1030307041da8490080500c0003140e2903810f1061018005810510f0381c0c1106620b0903804040182384c0318461001c03210f003800c0b040e2038004107840e00100d006d0650303040b052049602c400403040044892285000304101d58400b544014564686010b03100380078210411540a1107040c00300b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 309035305 1250 309034055 309034057
    0xc0d020a150c1230181b080c0901140a05151c180204110904060602030304030f050a08040308130b100302030c091e0916140f0405010620100507050a021002070305 71
    0x2844184440d44c50001c0e010300c618000d8541c00300c90754003480e6002402d808100718520600b040d5030090020b80c00c0c1d29100d074182d943e43e5081142459105284400404c000300c2e258042c0042400e016064030900e6480b00041031074a42c0d01d01180324010030000707100d001020914403144a141c00c07081c00b0301010700c181d1690800a60f103018040d225555802d824000304140a080700d911040c040d20034003211b035941c00003a440390000c48060700400c280300051143c1c5480380342261003171050f42e200c40396607803101d40b800c90b24404014145440f015100c020040820281c03402c05105840c40c0303082109481c00c61041c141880202c50003280540c000b48184006556007000800360301202c8105c01d0401d03698100510314014620001c0011420811008119100c0020720480540c800303a80c00c008103820700c4c5c140310458109114802c002002d40d00000009003240c4500a000000d8004441000101300c2e01001182e40a072500e40c0411000100340001c0c42d014170100c21030f512852000c609240050302d0140217 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 309036555 1250 309035305 309035357
    0xb090912090109030501110702030d050405060a0f0e09240301050c0f070302071205060402010305160903080a0504030b190e0d020c0d021503180f07080c0d020a150c12 73
    0x10180045403488190f40714201c40b10082d034000000340007a00c00c141c800d4203603500900c4140c1c064024810400041402901150101c51014102d98504048034101f2039241503501110810400e0b06203014078140d0328181a60300074404441101f4250010700d10051701050144a140d000381d05102c104206d4040e40c4040e00c0d2248550325495540d007416180882c1050020f40104040315804840c1800740500059041d1099100381c038100440d450b010300954808401041010001d4008503044c0006000c080c050138116aa5003042410203031250346402912004a505401d8070301c040c5510410b9103298001c10390208000c0014069800c0d00c100c00030345a80c02ea401007806540800040400c6440303801c0390f071501c40e081c0c3ca003044c3c0740d04241d14600f41d01070b01d00110521a2140c410b000c56854400310b56030f011030302000001d056810b0705209205c0400b48155041e64007480003940020b14020000808030040b1080c3c0c0e0b15030820b4200c0c5000914100540745d10420022000d00780805030300e180300800300d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 309037805 1250 309036555 309036583
    0x503010c0525020901080c0108060a05060336060f0c0c0a1202120406050319051003060f0b0907021c0c0f0b0a11040602070611030f040b180607030e040b0909 69
    0x103070508882c1c1d8440c04100c02040080d00b00248500008041070042000700c07460109aa44440303689505040020b2a2901d001c0c060380b1020400c081001414154400300982000c1e444251703034880766468001d4a5105920311031025003060702002003103d42d01030b4407a40240019042070400503002955036440c2a0580002d065101202c660111719000301314454405e0425001c4503600c6031203040c0108103400035035003039210410250003031202141d48d020740751140c4050707040501030510310740315407001e420640144000f1a40e02e40c1ca0030707840e495104200d841032060790000c080300e07031007080782c203c2941c03d84216000300031f00c40f403602000030344489d0200080b40d000030203241c0e16114100794400500d80344e01d082110781000203000030041e402182401c200c40c80c980358550070300080b02203641c4921a00300205181a4108814480480001d01429183d408212074981a5107100c02181455108a00c242c001c148044810324003840c15018071000c07104280c0e103000040c00c05616542c0e907240b160074500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 309039055 1250 309037805 309037837
    0x303040323030711060601020111030703110c16170d080103030c060e06070e01020d03051005100909060902040905090f060408090d02060403060f181115070609050c0a0503010c05 78
    0x10007007410082000c0c0a8407a8035642640c83c180300d007014010980c040e001d400c0c41e010703403c00a8025030043c85854006458000d10340e01e9961100b2040b070080201c030340300d041110801e0140361880042000b500301a1b0b040040d815800c941040908110780a1240414809900080b091010558004ad00b1811281d140c10910002d4510f440c080c0041c00c04074030140c01c680300e0030b810004a594466828400c0342400c1c0c00f43e889002591070101d05941c0119010301e151625041b080009080c2000f890042d2001458444403064507945404141ca944d42e000e404447d0300440d00713101854007445003e420030005401400c1100d41d8140c003a0b06c0b43e1008002070500c1c0404155801680c86001001c1c91456000b4852072313440b41c49250184c01820384100c0b542d1458035041c000d403e000c040068045000d0340050304807a00c0800d03c8100300c40034840c8841143c241c0307000e2200340d00241c414041e600781e82c1c2c0f041000e40b0b0b45049440c280014104940c1c0701501c241e040130b0302c01e45003075000002ca40c01a001c1d40741030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 309040305 1250 309039055 309039077
    0x20304030b1b070f020108060d02090103081b060108010b030d05091018120b0a060f050105030a0906180812070e060d0911100809011401050901140f03010c0e03160803030403 76
    0x61403110b03070000c2000510300300010b201420080c8250b000030741203100f40c07515911900c030317042400300e0312481c1c2d18000e40100895006101280803103020f0591401000302c2e541201d003050f06082d0400702e0a2380070399840c1e910346807008414941070041c00707044003861803e1420100380000040b07032103003484183c2e81408803a01140e10008813066400300980005104004204030fa45400c1c80c40b1a01207900d03400051601e4000704103a000520080e0072104140c0d43d050035501c4000c50100100f2404600b150940d82c0c4502c05c000c01d0020900d040c0416003c0d1862585030019503016249444000340700408000050b0f9040c5920b03501c510036145c18050328500090002d4151801c01d00d0915004002c50f441050b1002c8002c2d203035800101c00d0720401500000b884000d20b9642c04001800d0b080c01b4503036024441030014030003c03600400113803000900070050784100001c480440e007129900303446003002501e12458400d6a003401c1002d04140602c000440707900038034040700e8503200d001c0030700300400b04242c1e4414 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 309041555 1250 309040305 309040321
    0x3111b01080907080f15010b0309030421121e0806010f030207050a0602120105031002090603040303050718030b071b200d200405010b03070804141002220b040303020304030b 76
    0x101e80203400c40d0720880300146503100100c0d94508100f0034021b0000751004c008108142e24400750ba007d416100e0042d800e15041810f60322300b543c17487c047d00030425108544c0d8400310b88201460349058442d0345601e0780c5d22581c22030200d640d2901c2054a0148031880c03050041c030b40d07440104004040c43e18640180c98003076500c2c005d420282c208201520250020070810002800810514102d60b030460484180170004041c000c260700450400c641e2183c000e00020b004039000b03402a0340e10070143c2c41d2541c07614181202e40030420840e80c1050b28000420070400c40225001910f800c080215601c03034000c1007d03150354801d40c0040c0c21030711005c10040a8411001c0c2d40f87c50081003003c0340d00240741419168130348410310041c940e03c102d041c41035081c8000000c0d2045884110b0380503210350760780c0d0340703180da030300c3d144c4104101d008601c14496100b00c140a204031910343c400750056012284070002c040081507510b04003030380540c111000600d0b0030841000001d800000311021030364420120540756841d492 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 309042805 1250 309041555 309041563
    0x1030c0207050f03120d0605120f03032205060a1a0103060e0a0e01020c0d1110091505040c05061309060501021207140c0604030b06040501060e0a03020103110c030c0a03111b010809 79
    0x3c03081179441404904aa50302510780c02c60810348c1c409444981c01c4025000c0e071266074140c404d1100107150403c00100c0c1f0311031000030300c0d0507001c5e0703031614061682c02c03c55542c1441d1410403900301000a680e401d03a1800d208440507540801042441d05000041c1049500bc0d24407001401c90f422041d51800f600c00507070307800e40581707050724210403d580810790480300c0602083e014000040703d82c0114130005081e081c07140320313602c1101c0d0464000904038581d00010070003482c01600a64030010381460010b041da0380c041c0180b0140001c140c0c1d00d100245031109038001e954142d002103055401c003c0e4107002d0110f811065600b0580c02c2441c13103d0682c02c00c611503042800300c840310354100c1e00016010003400380000403d40075500c01c2d14100210381c3d8401c02128620704180c1c0c040d901032074141040000d507100740c003c8080f0846c841c0305140342c04004451503107581d2004003002290341090360b060003499000700303d0b52103100c1c5000140201c070800101c6c01c1da000f025440610305010b00a8041482c6d454100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 309044055 1250 309042805 309042823
    0x30705040504030206071215050f0a0e0a0b03190827090a2711040c05120108160909032a05010e0610121115120c04090b01030c0207050f03 61
    0x3500410607420306040007500d4800444840c0301040e40c2d40000d10717070700710217208451000c0c0b09551f1000b149400d02c0c00b0030050b80c8000422643c802a40c1070041603070031132160024020190200005451590700b024907080072074001c000d41c180030940d8258004107003000212080140700568481031408010380000000481d00ca25a4002504508010707103d122a0311803811303280c41e0b80419580c801910302c0b90034a000e07403000041210320810380059050400d84c00c2030801e5041c50030054101466240ca03580085001d07072280009a1045a048601c000514005800381022550503c003405580d01c000e000f400a00013000c541a005000c0007142114418000e10b000e98401d008ac03084c2c80f4405003ca43c4c07040c060700c403400d20190000c03001481c2000540595080e581c807412140305080e9900801c101c003080c00329008400401080780200c0c5052410200d44540702051107a0b03111030420032006c2c111604009840c0c14107241403003599040d500000d468044900c02c40300542409100d00c0400e040402030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 309045305 1250 309044055 309044059
    0x302041d010e0a021f12050709080f100501050108040305040b09120d021b01090501210617030309010f02160b06011101092004060609170a08070503030a0b04200702030705 75
    0x3080203031007a940080f9100800070300031501c030b03840007400d04a06070040c0d0302281e05d0004a80180034035408407003181c01140d8040c847d801c0040c0751380c0d91a14414180160500e4030700003500705448001680110f4880c0303d0161800786400600d6151960f4080e10030b00c100d002c7d901a511000c112110300d940e40c5040c901200480300306560054240000107580c030808490903000c0a40240c02149855205071000002c89905948d101d11058000c2d80c401e081910a544032444c454507180f011035128921000b030441640403030001d5960f45090f138a11400c440c0324141a0203914010410a20406107004c4490b40d0301d900040c0030001c1380c40b5180181e44181202800010039420402000203104005050401c0402c008000400c000c2811003048200d03041801210041071301500d0510030100405890b5124070185001c4904680590700c9040480c1c110300000c8034035038000410040365010a0258180756a0151000d100c44000c43d15013242e03880070203000c8441044045210015540d0401c074141c014840 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 309046555 1250 309045305 309045311
    0xb0312190509150c030715050412021b010e0a050306070207140d020f0103051e0a0e060a050c04120c0e180d0e0f011409040c0c02010228033f1a0a0302041d01 69
    0x10341c028200a4003045406038ac90407040101600d605001191581040b6404e0083c0e4861003804001502c0c1d14100c00303111604848202e01c089060f4a00304961400f0f0b0546400070688140743c6040b01c0321030384d03010440754011040e00111000580710800c0d90b140b284002d0801244540d901040858403261000309140e82425420900030011540e5020340c41001d40d000944200d41e40d169800400e40d0010381d0744c0e0301008001c000c00c000703021444c80e410503040e204d0318100c00499070780c0c410780c034400c80300340d0704c0e010b0300c03906100c1400e040d800420000d480e038101400c000c61014120300c0059080400f4110160502c201c0d00c4203c1d110324900c204440da20100200300b00a44424407000030103148524804038094070424200544241e80f0703694070f8103060510310100a428880b984d04403400000c00c400f80c0c6e02c1007901c0c480342d8605182c804002910400030450b043d80611500440410b980c00c036141c00001451041080c00c00f92a00c2d842035050b04c1d015a0045001000107103500511342c0e0b88403c0d0f03500e0394a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 309047805 1250 309046555 309046583
    0x1a03070603060f06050310091104031a10060e0306010b0d09050a08070b06010c0b130305070b07080907050d080906030c0903030309031314010507150b0312190509150c0307 75
    0x1d003591184054411201200600701e0312003d0641c0d143c4003e6640c00190060000c0400008040340c1111034a13940f154907850515a4035035943d04144482101380925a0026080000700c000c1c0c02e03041d9006001c0c6240800d440d907484404241c6440060003030920030000090348510905550f040991900d81c0324003116020340d09400d00c6150350b00200c0040360920011404034940d0f40c400c4c0c0c10740e0f102e41c1d08140c92412988030300c10000348100f8419012403d001050001001050f14031031500d104038002d42701c0c0412071070100d448504102543d0881d0741321340903c4074242c010079460300a44680d000c0684190359242c0b10802c0d400650f0060a40f00d07685444000200240c141021002e007035440d15100040480701d84600c0000710301600c104d075050015a05100490108440d030009040112000700c00164414800001c6828083c2c1347d000e840800ca030000da00f02c1e410400700c0c402480c40c0c1f03491500c1400c101d020400201c000300d10707c513030044406000c034401030908070038000c55200541c00b902008403c8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 309049055 1250 309047805 309047807
    0x8030a0503090705010e030d030209011202070b040c080d0c06052205070806090d08040624060c02030c030105100e190f050403031d0c12010e1002030f07020109151a030706 75
    0x41e2048071000000d010301e100000d4654061000b1000325240100601046c0080f107500310000e40004240604010301d950104082c01c030f40d403006010117400341d05030803c0362809040c019980081a0301c244c038540e204000003c00240d020503250101035005401003103d4654111421504180e00300001100400252100401c08001450002c5900c0241910000e03550a15031517201d0f8103420141c4d000c0754042c40050006841079100310b00304140c03801c8040340030301c010103031034480340458000f1400300d02d40d40e015206501e0204600001c580c01100203125601e002c080e0540c00011520a2094003030200c40480c031210080780d07102600c44040c1d0402c002d040140c0c0c2c0c18602070b10040e101980400e181c00548036041030170410900706000104010125102100c084c4443d8511880302072805542c2d405007031542200521044030441039103070015807282001070102540c1d0340b001e40380e40705580c5000c90302c81c0000c025100013111f03181003641c001880141e0301a11106840036107035881c0c0c9030042101c04103a03a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 309050305 1250 309049055 309049057
    0x70c091103100f0308070809030102071a0a110310031101020f01050403020a020906240d09060501080a230a0b0c04240305090309011d03010207020a0311101e0e0a08030a05 75
    0x894041c2c1d5106110303943d03503244258121141c0000b418074401040310f03101142d0300b00c00400080e01e001d000149401d1641d1200c60500000c80210250b40c40c0d07070303010f12030800790030700401c103000b24181c0015155040010005804001c03500c0020104025403d10780040c0c0c0c020301c40c1c1d24100540700024026450a4540252103150a41c0c04a00c41e0180b0004a080c0313080113144101001054040c05000408081d070030b078940c0c0c21181e00800d146848007a100001800340c0201402403010a00071301141040d4900101a45001c0d002c591a960111031555000800001e00d08529038106198030306a8171010174403150303440b0325041703c07900c082c06100c02c5030390504031060300c04c0c024201d0381c00300040e4441460351603c920807028041c0c0010082c6030100f03076040c0c2155800c00c600800a000618048060340812541860742c3e00c1a40c1d014101900007c0608100e684820740b201c00f80b81601b29030b40c4095071010449410091001005200b603029041c07515128917000240c01c15400700c81d00c0303c205000080c40d03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 309051555 1250 309050305 309050311
    0x1090803010801052a1206190303120624080406021b0303091c020a02120a0506010b0a030f020913050414070b0d0b0405010303020303010b03070e0603040f112202070c091103 76
    0x100c07442141150205c0088000d441100304980c10100e15010101d074400302ea421000c3d103603990003041065800c185c4403440200b4402507101c0e44a00590f84505214281118036542c0041001c14040040c1c0c05a07080b0302c1400c4203000c82c641401505030b2103504028009000c0c0b000842200181c086000c40006000405503110b05218070440d15101c1c0468000c0340f4800b1602034075400740e030001e0743c400018541001c40d00c160f0303007040c002c4502c03040742619514034004080c0d104034254100000c0c28140329a00d0b004641640d0500442540b40c5508400829441005446211394065403140403800300404415442089044602254003442c1c4900004030300b80d0185000d6940c031840c000d4500500e00309805002c0c104c0707405401450079030b0b19142c520061940b00034249420842040703640b0802d642c1d00c002860086008401c4c944180900e45010700081c90610000303880b0f4010880c11041c0b140e5104003107010404150f50150b181ca20501d0f03d08151101500041c40035030034011440e46200002e03002d184 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 309052805 1250 309051555 309051571
    0x19060809121c0f090203030d0207060b030a060507020d0c050c0f0613030809010e09060603010b0a050409150504050a0e0601030303410c0a080703090c05060d0903020d03060b0d0e0109080301080105 86
    0x1915100384140c0f0100c1d0741e070072030003501600300340907a02500f00154041c240b5140141c2d00403076174000b601c002034200f6601c45001c403900c40e924400d0181c2c481d410000d1003042401c40c282680110140d40360540d4400a007008648144154101428a13850310010750b28400c2141099015098591a04440a4006100060014264132180d003103c2c130305611068003500c4090b101910356401d004112015510004040c03007845020840014196054801c5100b03103444402d000d108103090100704010740320301410203040e09040c8141d1169502c03002c038039681143c0c1d0504000651a0200e21007044a42c0421400c641480840c1c401c00007060059403c1509403080c043c041e803031544d070082e0485543c0030700c3c0355030000a0b509030001290035019070300440d50039011701c02d45c0b18015a500000f030402da0110400181c4075413962078030820950100080c1c9000c0b042800c080c0501410031201030600d004403000802d109407948805c5241c02020350014182030780014007180c0d69a12024094064101600c10407 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 309054055 1250 309052805 309052811
    0xb13090e0316020d02040b0a090501090c050424020f1501150311030a0e03090405040f0c0602071206020d0b09010f030309050a0e1602071512050619060809121c 70
    0x24440a102104481000d0810b5a0404030400c641d024041c607598070040480c0c016075540d40743e0f0042c0c1d4980035007900030040f1140110740e644c14004a601551b8030cc42802007401010700c1b05100140010034411045c1c04620700700c4e05c845404610881c41c0140c0c0042d04c200600425200c610a554a9051a0b0584e4180e1142001c4d58500c0d00007203084880d010341140c031410051022034901e42680e048000c203402d80c00c0840c0c0c10704000e8070000382201c0302603900311440402c0700c00040400200115090081031580060141e003882c2003040b8082080e0340000516140c0d0000f6003000d40e00c2c50341e228620110024240080ca9a19034502e41503505040c0010340205807480000241854605128026160651880f82881e21007203520b282c0c04203466800310946c0104400820046444010300f1020034043c3d69a821071811401004111140605818000d07000c044101c1c641c0c041c190402e00445510b854801480c3c5d039181b45107814a403c110b201840b541e1300288200701e48004519594642041c12010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 309055305 1250 309054055 309054071
    0x1057020109110607030e01050d06030501060f031b030305250c0b04030215040506040302100201020c0a08030a060906080307330219020c1e06040f09051501020a0302061308040b1309 79
    0x15540036800340240001e900d40600906c43d48110302030071380b15940040110310540c81e036a449094900d076030070290001541e0f80701081803180000c02d2000c0401070a0154111900b0754800904500ca0b248030f00c91260b41c0c0003900014400c601401d1317565243c01001800c1c0854035400000c4481d0700a00c000d9106400300040e17405c0803c565000c41d4101c500041045142900e994282300359079490500450540d5800e1040000b607000c14032036640150710412409030b59103032035020602211140e401c40c0002929045003404079034000021503410903040080c400980d07100f58460504050555012000340c00c1800d24003100329210b4000d4100c45140900d2003001480c0090100c0c2e80d0011405115445a076010006c615107103550140f51300e508000e8041031030b107512100c1d070100c0f50049030300100301c65035144200301e4100b521080c05503200c102440600f0034003440d80c900968840c001341c1450072000c0d8421020040000c68801c07600242003840c0c081c0e443c1c661100d080b454107440d52150300d50060418500c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 309056555 1250 309055305 309055309
    0x615120f0c0f030f0d0f030204091b020d11071406091008400305090d0311120a090e0a0209041a010306062f07080a05105702010911 58
    0x18414071820100010140d10172038040c211442845d0842000900d80e080202050145c56030003010310712078403150341400281011600a14042011580104000410228046224010404a04950340c02c03050050340c1070300d5000550684101080365600400080390f400307003580c0100b48036100703000c80c0d0115480e441d2030342c2c04d480718051b09403061a10311950148201c524039141385c42280b001d01a02c1c2071740c10030f0540404613140e08c030030010503408070384420f040c100c60b44020000340451000e0160f00d00e06080348008050940c0d18180601c24071008241c0002d8065603080d4190b030800d900040091102c4280303040c110003000300c5038080c140004d04103200420082e000e0b032590903044001507080c0345050040712519070186c61a0744d550350755000b5140000b481c41e800308000b04099008402030801e1809031803d110441e04030040c52103e1540c081110490300800c500e9100c106e210440010480107c50195403000440c02003006078901c8010a07400d507030703d0341503120740302d000d01c280007200b0b0741202002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 309057805 1250 309056555 309056563
    0xa03020a05040f0f180203120a0c030f020a02030604230d1b06140a0c11070b07030804020d14030c1212060f01090e0106050a0801090b030615120f0c0f03 67
    0x103034112203049410041030034a507008188203811000c2c0040e01508814401082d101c90700c003442d594100c8000c80100313618042c0301039064418440701c00d5282c2122414043c1480b0361030035000c0c0510120854544072240244081030280b03600401359800c5107420b1038113980d1107028002484e11032007050710f24001c1510005120b4080000303921405402c01d003615401040d00b06640f411030305540c580d46008030000d8070f440910b014500041012074041c840c0c41d00104695580f00d00a1044d609c2032404005401c540700848040325003514050449681e14000b05114205a0030010f200e200c0c0da80da11156000080094080301c000c03001980c4586502d526403550b6400781e14122030303600307043d44089841840e013060300007041c0303406041880303010750744440300e2484000136403260000c0382c0c00003650700460780d0041c10107000d440002401c0205455050120b90b4911004080c2042e000b8441d02c01803190341c948000316401e000c2001103505040b0755020683e1541c0b61051014081c044005410b203591030082 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 309059055 1250 309057805 309057809
    0x11b11061504050a02040f14034b0d021501060c020105030a09051203130203070509011508090c04020c070f060c122d030c0e0103061a07020609030f07090b0a 69
    0x64030140452507074004001c02044083d0403d150503500300710000c2e0341002480250700800b07401d014248001800d42c28503060140d5114030000314104205081110a402007003c05500c980c01071003481c00400341030703510402d0f19552400c0000d100d15040480b00f50781c0060b500e00c440582404010460740e84920640d41801c101c10001d01244003840025030410743c660000450368051030480740b2000c030b084800100756100741c3e17010f416408124494021360a04002060060109030b070342c00210340c0751100d5900c2c0180b035001c0140c100510040400c5150394100050810180d00600c1103580d846e02560f905d94404481c8903841c00030304030041c00600180030300e030300380c140347e07000040079440c106820b004035003000321242850000018441c0b80c1e07000580c0360381062248a40c41d00c0000c0c5c2c0765074205002d00501e400c4800c6504150400c0401d0290300002d080201e404040342142603220340451001501e01e000d4488045c6c2c051240c0b114040c41c01d10001800d40845030f20007001c000c844003c4040c000500c4d954 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 309060305 1250 309059055 309059071
    0x302043b07090902030304051801090516050703120b0604090c0206010e040314032d0a14040507060e060c01020d0510090b090c09010e1503060f04050103110d0302030c011b1106 77
    0xc01e204101500c403d41000850900c014152480c01d0b03150300015030488082040502410a10001400701218501c41c0c0c42d044402d04480f4040b030103003103c1c001c0082c03003036600003420005c1000b0140709104982e0070140c030030540100019150b41d1202403800040495024500044c440c5800018881109c2d00600340203680513960081d040075602801c0085a00141249440500c2c5485140a5040b01000066000d1a900700420141007410801094913000e00c1810b4844400206110024800081358003c8800701c2c180140242140e100050040c0154a14944654000140510300740e9044c3c2c01544115617100020782100c0d00c03540800201d03488003040c3c1d90842411800314641d4201a0003401c004074051500800c0c002c2c840020511000c1d94056a40c440c40c004010b000081c07402c1c2800318904101901c00300b10b95803443d254101c1d464041c41c5064091405040c07035009141c800e1044804410001c4002d205140803410703a40701c50340d5100640c0000800403554030401c1480811203502507022 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 309061555 1250 309060305 309060313
    0x4060e0a050c040b03010305030706060503390301020c0703030306080708063c01050103050a0b09040f1a01060c030801050423060109080d020606040b030604020d14070302043b 77
    0x1400340c0e04402048041c04128100409001c0050026002d03030080d03010310300c5400039545070107251400f4001d46200740c21882c403940109030b14100e0143c0d00c0c1038414482e003540081d55410804041e000ca0a041b00541d41c50301940005211004e6440014090302142e01c2503508010060756100402d403114030ba4054003074903400080104140180b000400b030080b10006100d4149002c400345c0107081002101c039406042d466600042200d03682521075158002c7d42003c00340401e400810000f072003490001c3c00140b13440856000b00090214242c0c040c03208a4050101402d50350b103170200a003403c03144c10f02c11400590368000120f2142002d020b06a817039005008a164000e681516104035201c00610a50400c800d190b00000c0c403d034108031214038000c1c40d4000d000c0900301102880255034030820401c0c001d034018802d1100503103e1011850559800410700702030103015401c00c90401e40181c0c0069403080c14450030140e8482e002901514206042d255080e40a485100d582e450812700c008280b66500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 309062805 1250 309061555 309061561
    0x212010204152d02010c03050609090a0f0512040f090b0402070b0105040b031507030b01090909020d0b040c030b040c2408060d0501020f0f04050a14030a0201201b010e04060e 76
    0x1008100e00700b60f00e402c1c80488225000c0902e85108418026249580141e440ba41c03100c40389901845002e40050050381c08826030300d030103958940e039402d04e901e00034089880305201c03c0c10302c141446514164400c1c0900ca5684e6542d40d072044951851030302544400034601724540c041c5107000d00c2144c5030307141d02c100010b0040c1c0c6080d0400004018050420380c0500916030300021085079140c41611510b400d0310000342022482000500c9048950003500411385000301d100013503030f40c0e000d07550703011640849280440d076120300e040101281a80e0004003000707940c034140000c02408050400075110206524205505d40c1c103555409891107500342c801058070031000c16801d0401d0151b88a150740131f000094540302803450f0366a400d40c8007a88070090300501017800e0005190103039620004000402e05a0800304480380026100c1ea00c22034028180001c0760005c0001c056202d2025841114181c1031b07aa50b110b448051031000c0c0400910030380003c0d00c03054806864030301441500b0589815980940581e6 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 309064055 1250 309062805 309062807
    0x1502180f03010b0d06020a090b1216110307030c1a04150e010b0a0f03050c0621040c050306090109020411120406020a110a03020f1c0806010c020a050a06030207021201020415 76
    0x10004040c42601952150100c0f501c5449103030300410a640f0400c001070350b40310f41074001000e900b03903500600e41c030310070401005050481c00544203401480500c01803600200d00c120a4840100403100380c1010301002c1002c100b410340148180040b82e0146000102641d49a006003190600445004010a20080344040032480baa4081c200554514000240c011281800943e240c14191302c00e1118102c00c1800f881001414029091440b00030f440e40c41c180207800000f02c0220000502c03404040c8444000181807141c040c00c0000245000350684100b400c04d444d00c0e60192a0100c000da0055080c81000000d03210050704a4400c44000380c0030700304503280c5a4401d006540428030820821204c20520180003105115049005110303030028003071050b034000c800741030030110302000e0b1408a800440004483e0040241580540c0918101d80504181e1001408030b00c40c41e0415070300048452000b0624503095801020000d00071212018024180c002d038609034441e82c001c140c40d03820754507901c68101d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 309065305 1250 309064055 309064069
    0x1060804081206040f14092e0b011e0302090f12031204080d0c0504030b06010305041a0709030606140111010204060903080c070503060c032406041a12090109150218 72
    0x4240020001700d00c0c00c00500e062402c0d240221074421000000d003091041d034140410810080103208850304441441c0e08014800910810020f0a031140d2235080c1000981e22824030001c0305407214818070240c003007864001b4025040740c012030b4041ca44440341e481482c40e0050707007400b00b100b802c4019498114500c018005541026008a85104081c40040d20030360300c40c000e68004212507651316860b140b81d0708100c000d400001d0042414141303040103100101e0441088007001101000700b02c4007071385a42108507107104030b80e400503000d68901030001c11180f050680c200c07181d4400343e0320140c0f540a504156400c03880b03144644000700b20541403c0000030340640113464402c050300c09580c50207541e08007280c04d241c407c13109140810000400c1028000c4003070401865814290702a0580c0702460000c541e00d032241d4010480b01c1030b803004858004411301021a803252003241c0c1040d20b070b811318a140d03c3c06008945802c45541c2900300c009006285103100b519482003ca1404589444401c0f0611000d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 309066555 1250 309065305 309065311
    0x1b0a0221070f15020d03050f01091a10020d0f08011d060d1b0501030615140306030f0f030405281511030304030804060f0614040522120305010608040812 67
    0x2450103000c00c00103442d14100ca1007402802142c004100c00c07641144000e0400080700243c00c01c0c0b528003800c4c4641e0303201044400d41510106400090403000c9130300d031510220002104180e101045484180d9081d50105619004407807a4417104c1c900e441c00e2405540200d000d010307040000440f0360402c2054a45030890079006400585038000240050300e40c00c2d001da80219401d501c2c8640103900b082256403600c5210010144421404000314240000900369075071920f140d02c0020000c0049400303682c0600240e107240440100b110300000e00a650b481d2650020311806200d01d150191400403002404c0203688403480011200300d4003405c161000340c131800a680007104114409200040b030342c00c20001140514040e0b12a4403047c60a13107400340175100e004107e1540c1a0070007004100080103001082001c000464003c6100e0782c41603880000280c54000c0020105824054103050250300124407656501d03075501444260b1300c4030b60507580d00400b03540041140c0c50400c100c02d504000c1c0c19040750 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 309067805 1250 309066555 309066619
    0x40504081608030106080c0405060702010807110724030c02070b0f040e090c04060915051507050106032003120f0304050f160e1639081b0a02 62
    0x4140300c1401d00c1c1c1003620300c41d51000c5414810000043c420b464008410503484040400042d240c2820040407842c4c50107800f074000d040c0246800401c2d0070741d0080359a1868024000d00700c0303100350f40e900580303450000d0245030358040345800302400c1e05842c800d0155220210842c0c0040000608e02140844180d00885840f07040b010180030104003400e03c080858024802d50008000fa01c05000400c000c699290307021a001e1464000c2190071014803040d4001101c2c402c84440650142e0594074030000d00c80d103003000300607520340348000c01041100044c5030002d804001c0900c440c58002002c0c90b54911400c0c1c618003007210140800c05209000c803009680c424811015903544101003c595480c144943e00104e1140b10845010b000f501406c14413030b03610266104006004500581000d4000032508142400e2011070140c102810050681106801060f128032140b80c05814100706000d40c00c1075040940b04121003004010228000400c2010560010402d510000461001020101d1000c030482 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 309069055 1250 309067805 309067807
    0x10020c030607030e0d03060e07050d0e0102040305160801110d0f020702180a0e01020913090f0f0b06100816030507140301120b0c030723042c06030a0203030904050408 73
    0xe4505100c014060340140d18042081c404482065003864160010141010b103400401c00c44180416407258000c0c2d15414110350720100c510140d000b0345240c001c06c045640c0005400400c00000207004098859001000760225032505800750a07070303584060b0799909103024003405c11420a160311680081d003e00e10014540100c542c04508044000302001d000d507070001f001c02012a043c0d008210030401c45100841ca400700c06c41c00100810301600c81d186c030b030583c0c4d01c245d24108010008040c40c240d401c03490640307040c0c03482c1c40c11843e0b04008540d51402040401410701c20f440c011160780d4003801e94080340303c3c081d649140044004210017401c24082180009044084000c2c0b60000c40c04ac00301240f4441182160342490780c900d100107804600080020020000010b034445000d000080c00304042601c0310b088000301d00c0340b902560704030b0782c05c80307100c01e002100e51000b00865580440920075540620f60b146820035458150041020b03406400c200185c0080c0d140c01d9020540c0140301d03074042 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 309070305 1250 309069055 309069073
    0x102060c12280c3908030709180b010e0d0f02010e030709110c06060a03080714010615030b090601020714091b0a08090c030d0c06050901090203030c07140415051002 72
    0x484160361244803844046021001c1e0413500c60707071000160f0224203e5210428042031010b6920b44000c510800c09400035002001083c400c0303105800b614018140410541080c0028040c100010f02540700c0c800d000c00e2515280030411304160681c2540143c1107950042c01d0190303034006442442c0041c034a00e5243c019a0004501480540714400381c111052120b151134501041da10391400c4070141c040c40c4609110300382080000d41c100704a42c00380e0341c03080402c04140340c90403030300e070251502d42c00804400304030403420860b19a040d400f101d006082102d520b02162a02001a601da032641c2c02400740054440b078500034541810790102d81c2010840501c10030700c14101c0c698010940021400c900051021020f20000b14020400e5040540c0101c0207400c90503c58a009880740443d560001d02143c0c0361000101402820740c00fa88099030054140c0c3c0e503c5842e41405500c480304d0340521003801c0008103107100981800d200c5d062443c80c2102030050300f5420002040340005603180c0e00740442c402c0000d1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 309071555 1250 309070305 309070381
    0x30309060509010e030718051e010512030d0c05030405060a050609012102090709030506010f05060d05040f0209040302100e010b030a06050402031002070c0609080c0f01031a120c0102060c12 83
    0x124000071f1051005900c9140c0d29801c92000390b420241c9100101b024084040b074004481140140c1150b00c01c5500b0750340200c2d070105041c154050044400340d03480c904030f40d1900309a04170f40107501c039511850945980b5600d8090708030440307005485098005008000600035045441912900d01d29000d8480611107001c1d40018480c1408030f0ba101c0004500c804100100402048028050502c010b110b01d00541000701003551400386030355245480d601e820224041c06490401c24540c0368001e031402d840c51415080107507070342d0b0310041c0c03083c400e910700850003d0350758043c0b103a2500310300c0082c0a004500d00580300c1201506000e40240d034180680c1000402103203642c801031420500c00d2017031b403401e40e10300340b0044c01d650f103242e122031203c1d0407000140000d641c420204c802e804000f400c0004801d010118002c400a41c104000303500f1102502161040304000151100c4c0d10809900710791140c1c0d940080c41c2c40794041c0100d10291002400c001c140c481c401280a09403680f88000001085021421 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 309072805 1250 309071555 309071563
    0x12031a120102070b2d041106074d030705060d1803030b090c0f0d111e0304050705031203180115031407061418120601030b010e0907030309060509010e03 67
    0x2907244095005c05142404402a035036045480c120306054200c03080c0b8254546099102d1200c52003880703400006100780c1004081400034861150f0007010300c14600246c441e50410000141d600d10034054400546002d44203c081580010500078014010040c50001445902d03004030862060558035201c000d010341c13804400d0f515035a4040d07940030850320801c405003c2600c1c00940301c070300c031b0340002c108110710070001c20103c91210152a000080c0400140350b00a1140110360095104020040b40004003000e1440994003807400f820035600e242e55101c040607610702c101b14448800302c40500004501800600703000c040981804008102e050b10000d1101031041213410403240e0380c00b045942d09a400c001c0000c60090b000a04001404c40328003d4003140c0c40c000d0307544102040b11003514000707150302d0ba0b4983c005603000d001d049a52658584c60941c282d0f0000740941c0c05245500300000b6141d80002889004480d0035848400c4150306100007298154000003030f25060007440c0d0501405914100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 309074055 1250 309072805 309072811
    0x18051b120624070308010617040212010b0307140f060405010c020118080a12030c030c05180102031c1407050702060a0806031912030f0e060a27080712031a120102070b 73
    0xb0b080310369103c2161402034040e14041e00042d040201d1036485015004407a881c2c240c100307404648402e42030b1054401140904400c0381e507541c05014082001824148081d406c02011508550491071f0300780f4502803013030078052403040c64001042c0f4410b020240d4000c2107200c2022403203080303c228180c0c27145241440d000402d5030803910702d4504e8801141c110f915214800b050240d80c50184814589981e004285025001650b89a5005580050101da0003041141c900202a491240791012018035010003403a02125010b40000c1000c002080c8600c41c00488991541c014500e60a06000120481d486400240241e03054420850f40b42c81c00c01c0302e113a030b441d40750784500d0100034206400b803801425120381c65060703440b175401c150186a200c030001c00d0113584945d00c5180001d00a42c4056080020030700c4151303c007070007100c20000c4801d00402d00c0c01000c2140c050040030000b00e030300c543c0441c100c3d821415200da00004241907121645401c00e102c00b0504841000503061043c95100c00b02055030070703 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 309075305 1250 309074055 309074119
    0x90d0b09030a030b03160303111608070e070206130f060f02070f021203090603010e0a021e210108030a120e0f0601031403030903120705120118051b1206 67
    0x2c195090901e926015084207213806401a0510646e00741203c5c20b0b0003650b003c000d09001e080d607d5103103104001c001c1440f4405014440748055075481c00281c2e101c400d540240d030316403260000010380060000039210b024400c51016803409401a88030b07c0c20b0241740d42400c83d1080d4899030308004100440c0041d00521780100b114581c20304e064410810071079200c0701c120301c10b40c100f4495152655204002c0d80d0450380c0c00201500c0e69034407408030360024420f100311503408046600e6905011010787e00540403c11a01d0f80b0381c4a640e01001e6188181d01003407180100e698030400c5080b0800d4810700d01c516850640c040d02180509920114a041c540301425085c155070003400100b050155241004202c070400101842ca1070500880c01030310707071060b082c20000c048070300d0004c291001d11840480c0d02d0384408400c2a020b550311050340000d80300d0020304180140e410000032604580c1a07145900e59041d0070402c0d28508010070001c0107148000520b1242c2c000e926001b644c105d03c28200307581d62564a6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 309076555 1250 309075305 309075307
    0x606090e0f06010602101a0315040c0902070c0b1804020d0c031a03030417070905042316050f13060801020415050a02070e0a0207140f01060911030c090d0b0903 70
    0xc5280910384011080c40251541c000001041041d4001c90071303680900b90f0020200f10210314548108442d402001076503018440c8000d030a05845e002c1000d40d00540c400e44001800e50340e948580c600303a0007103190203071044c0304000341008889442c0e80140008140305a01b00c010300f00c2c80300041d0072a0042400d0188154076860100c8082d9418461000c03070f510008011203c0d00c01c4040404e0f56800740d402261104c004c10518170200150811003039000700b00b904402c0c001454146401318101c2c420000304110780103008261200c890000c0b82303080c0ca15440f038003000c001c90f14003410880002015210150811200080c00c0d4054050703005803030140403901c0000d03984a207000c1d10300002d00403950125080200034000c400b00b41c2d602041c0c00c42200c1304a500c1400035103c4061003c0284901440200321440000724820000c4002c11200e040c42040c0000308031140c0c2c4e80a103001074901100401903a4241000002c0035150700341d001d0144000080d100312486c150303942d20340621460681e00c140440c0c0c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 309077805 1250 309076555 309076571
    0x30e040606051b011e020f040b0a0f0e0d151a041b0207051f05030705160311070504020a2a0b0403120b0604061704081608031906060507061107060609 66
    0x303e43c0401d2000803e141008000c0301c00942d0409002020000c0e4680e042600000c072403283c2445141900c029000c043c998aa45000489000c2d00b1002d46080c19008150b50328580d400358949002000313449604110b41c0c0d00d00503507100c00b10009258248814000903048412290141c03554451588170440200300380c02d901116881c043d2401101d40d10081c0718402da02310000300002c502c0c04021500720340c0e00b000c544a40355001d09544c540200c03214000062580d50031103040c540c1c0100400104000141914052501d52003400180d05c905601da102040a00e00a1f10b02d0021040191000c40b11300c0c400340c80d171003000e41d540e400c4080c4251000d50010301d4010030744400c0003180c0304411a0307510443c0c005160500d0204043d013407801c01b500d120040072103800058240500b036821035034009003400694400f520f0350b2800300d0301c40d003094408c010b10b03206098900303840390a24880c64080e2419034480c20304040301c682da0030024007441005055186e0050045100040d8180240c0c0082d142c5da00340891841 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 309079055 1250 309077805 309077827
    0x2f070f030b0c0f0d0b0a030f080a0305060301051005010e1201060e010608010f2d150903170903060105060d0212130201121419021201151e05090607030e04060605 71
    0x1080140841d2642e4500f0000c4a40e048034100c102c40561032102000700c2e1007500d000004044080c15403016080e2205014401c2c00c00141c600241000491034a00300705903116031042c10300b21001103d00c0c00307080840745406c0c4440e601600310b51b0340840d00200502644206803d08500b951484d51041542c5403513040144001c5400403c22809084080c0c1c2d21200585007440d25680d021081512007960b05816150030103221401005001a06070076803800120800400024950b40041c03105850110f004144800352000d01002c0f660399040003001018a0b908140400007540e100710340e079814156081181513100404203003918862280300d0105540a00036000250048031800d001514041c64584090340e199104210650090400f801080001c140803400100902c580c180b0120b03ca80300c40e000091000101000480802c250380d00c81d66a0011407850240040310540700354041201800a00000c2c1048030181003c14000d14080c400d600d11040807a0403114982c202e000000c40c0040c1b0700441b4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 309080305 1250 309079055 309079073
    0x60603080712110c090c09011e020f0c09040203060a0e160801091208091c1101060806181219090909050c03010e070503031608040302210d08072f070f03 67
    0x4040d40d9018041c2c01d43c01c0304c000358404800401d400b004900104140350103920540c41000e041c1100d4181084401c071015020b540c2c0e40c401c501e500e17007074896046101440e00304500c405024541c06002440d15446031800e01b80600341010923103031284184050094034040b603407951001420799900004511006040202d0545500b1404c901440f10b1f40062100a50300040e41e15240783c2c08010710140001c051034202c411501c4280074107099030909401058400001c40d420780103100c20550031100030042141aa1500e05521132030428590601245e2854410245c81e10090b401034a440004e207615200c15004552103100146e03003c2e0301003040343c07200d07043c244952035030040c1410090500c035188c400002c1e924031440c45610001210010f44808000201090340c01542d070013000002182c031900800140900700d0222203016200384200003c01c2400340c4034090144200381da5414003003100c858981d2402042400c00b03149010180b11101d4005000c2c0115000383c041e500810074030f0b514600741103c038 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 309081555 1250 309080305 309080327
    0x70e0a120501110703020307020906060c01060605180d17071104060b09010e0306160c060f1b030b060403080a111011090a0e07080103020909070521150f01050d060603080712 76
    0x100f00703003001440086038000040e01c0c41d083e811a014240c56580c140882c14600851000403020340c00c00d180480d426801001030704507181038244280c0c8044161040194000d1900e00280a0180441032103288070300d00300c020503039940143d4030f500b4006a1000801c3c11640740e6408100303103e00c04548032502e5a840421420420401c400410060600d44103004400249906100521030520b070140100031b5103030020a01001050800c0100b0303c5407514029408000496041c0024909880440341d881c00e40266801e503908000d0300c5040640c0d04109403109107a05039858118800d04003241383c503448602900c01d076902c5848003d500c1d1034461080c03081498154110104881c400000c20000d00e80c030107100ca0440350119560800390702c03070548642c02c1c1442c80d00f155810840408200003411100510a0402801041281c00350251b445084c41e00c1729068940700c0c40e0f1812100100413230b1a104011001c40d0340034180000c1c2803603403039542010942c00014100c40c00c031032100300001c040da000300c45413030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 309082805 1250 309081555 309081581
    0xf120302100b060a03090303090516060906030c02060a1d0a240e030d0209130c2c012705060d05040203070b030411060a030b03030307180504180803070e0a120501 71
    0x1070400c14000741050113503a4603581090b569884c04004e06200b03030045000c0c02c4e00601074400200201e01079200c907440c0d6000d02d07400b150b03040300c001443c01e100c0d10031640307091200d40c00740c00d558a640c48600098017160303c0d524180b41c0e200d0b801c0380308881d00b4002048500c1c461103400c0c1c0b106102e40c1c112a00164800d000120091a0038900000c3c0d543c04421151034501c081c01c01680d031b01c1b103600060410500600304450840c40c01014040c080d4005c0100c0414200e6175070103441d01040051804510194014103a001a0b01c810317544c1070b941c0010044031034400800000b00291601c0e900032901d01d8201c0313000c2d810420340712001d000650070180003c03000b41080e00c0e0058510f107081c1c1c44032806804003d142602a1000042c000240bd120707500a41400c503004040d25503d0819890081406811b45001032000801000004180c60b0070702c10010040140b03130b0b04410500058441038007903080101140d091040d0b1414107800e030740d10398003454007800c0c1c8a403070700b1001030b03490415508548040340110 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 309084055 1250 309082805 309082811
    0x305040321061811041202150304030206010501020c0409050c0907092d1d040b060a05210d091412070f08030c0615010503060603040302010f02030702030a180324060f12030210 77
    0x140129070b400d08890640d182d0240c5481800c1c10b92020035018010800c000b4050303a800710500ac00c255000c6032680c100c0d1403d0f070803a040c07000a5010401100c05c1c0c0c82004150750300a040601c4942045031146902c29403905021281c59901c0ca02c00c060b548442c4403159104201468040d04645900c000801920603002c01c0032040d2505119003624910280024000103401e00010b0f115a4070754403104081d11000c0c0c420209500f0380340090200300180e13000c4107598000c8008140d0303140d00c01c40e4440e08230f0340408940ca00030320424080c00f0b80d540c03101b0810031a501480e1800300b1026000400c05008001c4100150f9407862084032103402c091000c0c214018030011407044400d00c0c3c0c0c3c840181c94100c0c0c01154601c1d540c4e20b6a15040c1d00501040220345030a90000c010407140c40d40100240c0f83e000e01a407284c2c1c4c90b42100c0c890584800e02a0302005002c2020001c4002c14401c03401c0001001140e02040080c9068840c1526298008030381d00010310f010302502454105541881108a6011450018 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 309085305 1250 309084055 309084071
    0x30a0e070f06020312042a06110c0a1202011b08030f070801050102030901030b12060f0115090513020306010c1a101e0b0d020f040b090103140906010603050403210618 73
    0xa4507417140101454000a4010219081c4204102c140741c501c2c1e9050004d81201400b48811500c5a61078801d8202146510040308014003002c20300384445080144048681800c0100c504c101c90b501c00000d078100b1407036800d88440380000300b04580100b40107900054413840c0c2628502c12140c0300500c01d0f030802c18003c00411169800209503894a082400c020800754a240c4c0031581171441d03154241403074030030303c0140586079000b510464165400d117071408003030700d0040e0720980740d0304102d100e590780142c0501140c0c05090480d82c060768000f641454090121406038035001c0f01c01d810025124120800b01041c000c80c02002540040140a900d6464104100310f282030b4651410a22407101e0076140020701c0c03070a410182c0d0454519082d01e00c542521240c80e031821a4441e0003144040e03001c80e107844114420000120b0300ba9201d40481402400c2c42e07802d0800450251401400031001c2c411303910300c0345000e0340385040c0d89215120902000120640350450907400d5065040000c00e51528080031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 309086555 1250 309085305 309085307
    0xf0c121501030209070507080d0f1805060c07050c060c16090b180a0f0e0312070c0804030f02030304030b070305040507140a030605090c0d03120b0a0e040605061203030a0e070f06 78
    0x400e9046076012201d0a42c2c2e40d448040607900b9204241001701014800566029a1038a650000455101c012001c22400345c50710303085820003283e400044c1c0280c0c80380002580c0c221082000340720740d03442101030700d4016018030003103402c54212030340c0e041403170700320b00d80030038001e0b00000e0780000510000030207000604d0a20081440040003d030b10111070313605800051a4002540c0001540480841c810065651804950b81e101d8000d01700206412000358003180b0111f22601d40c200c03440d5002400d15250500c0c564400380e0303906c0d07a88401c03070f014007040c0400804a80d0350904148290050b071070200300ca103444d19000e404d160442e0000b200b21059038899411648807103061006881d4000c1c0006030644942d2455440c10a041c545254003031180c5c02c140080582c0282141030408035090f050290703259110800c060701c0c0c00c90051305041c2d0358440c0007402256194100039040400540080030150754903003224119402205c190490720b0300ea52000b46041300c00c00082000341505084040300d6414100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 309087805 1250 309086555 309086593
    0x19171201030602070f05060721050105030706120906021c0e0703034125020112020a0c0c030602300103110619030b011103090109050915030f0c12 64
    0x1500036030307022502e1300800c44454141c00351540c1041c112480ca25004030000d0481d218000344000f10a01610a0707541d44000b805030368180c801c000e01412105003484c400700ca103c441101a03003c92500c03640d44c200440e59520040c40404e007502c41020b88104d080b0b4814050f01d0300b403904038410703601814007000800d50000c0e010b07080000308c10f05000319550105000c1002c1c280c112881b0286002003003820b12034000d44004100c910402c40b074100d004585040f0220195030184006400b150f402c01d005c1074402e05c1039004281003d4907080008041c40070340c031421000392940d001128250b41c00142d405070700ca4080301c0b01c0507411651005c85249c4005000b0120b000c201031100600e6000c0071040c084403a541c007000e44483e4010344040d03094401c2d404c04010050403400407501d01003102c074804c042c0c1c1d080010045135441003040c1c4a00507458608001e000d100c1c5401085928005021001c900e40356078244001c0c1c440c0c1000100072b250b2081d4190402903030b124030f00b02201325644455a00040304042034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 309089055 1250 309087805 309087809
    0x18061003060b040f0f020a020d0f0c030302030a020c190303050a2702010e030a060510170d08070918021305060903060103121e02061b03010f121419171201 68
    0x40030559003407500100700034100c43d8200114142c2030501c0440c2e40482d583c00f604847d0559801c1722125000c0300310507103001c1c844c4020740c00001c0d981041c42c40424002e40003103402024200b0014581b00c0d155103078a091144c001c412140d04500300380f2b07003424541e042c014250400d401343d000300300548145c102c85808683d120314120004030381000200a41e8040d099465480703201505641402c0d8403898003a0003490116040d420000046002060080d21003072441c00c2c0e0000ca2000303100d6070341c184000791110040100548100001e0420218104c0a00b4010100c8400040c00260f1507a00030031900d0203a601d6900124001c00090088039460383e000131340b07141140d820903501500e10305449011281103c1c8040c0c040081504441c00d1480c103507000070042c1c8a0782041e5482c110000b400100c80303100d803100b8859040000d0740c00c0320500c542c442c15002d809019214084480c1c0e403101424645041804030304104031aa817441d10001c041c0010104e040c0010f0f0002d402c42840c04a032445000c0c4012418 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 309090305 1250 309089055 309089063
    0x6090901062102130204060810060320070c0f060504090b0301050912031302041509200a030b01090f0f0e090a080d02090409020301140703140124090314030318061003 73
    0x160034002c00e40d20741400e402c08041d80260300395076681c1c85100c041c1c00c0410a0724182c1c450041c2c403c001902034400c0c4103500c1da501605559202d0f0450803013201c40d1300c2d0026642a1800303101d019000030a5604d0a8200e4001c05490b141c0c2e5450300d2a2140c40f10845149065a80c0a641410200400108040f4a002a01840629041e280c0c3c4903401004018a03104d080250050f03c1d00b0442c0c00c42402e1110a481203880f180070501c03881d01c001e000b0000c0e281c5254983d03c2c124806010500c5014002d422000c001881031428075162a91841c000c4403036405648040a4140f241d102400304228030b00e10301d944040030f04001c24846071030380e0392100107200380c0400882590703010407544842e5030389800501c0b00540080080c8040c060041994240040a2b20030b440402e1901d940c880c60134003d60382840c102c851300062544141e02525101c14542816034401d410002880700c00f20014509580c50748230f452400c0011070b2245040000c00c86410110503142c08030f03038024801c21050350380501045041e240d00c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 309091555 1250 309090305 309090359
    0x403030c03051c021b2a0d210201150e0f250201050f10030c0e062e0206060d050d030b060906070510051f0608100e0108060609090106 59
    0xc0d0781000c603580d004168080030001884a450701c2e58500355005010264004540040102c0d81d400030150707280400c0c0700c81d030015200000c80f6401035122800784081150007509078041049550b0301c42c154100507520518001c20482c8803c201c490382480380501c480eaa45001545103030400c13034420f403004401003125825250040004521031800302c003000c030300c0000c0050078050069070040a40644800c681d09044404ca10002074504408841c0c40000c4076000103030440ea280c10694220f140759001001950001c1a200c102c41c0c505208041040329001c0820306100303a9492a100241042400313040b041c443d0580070209004079901081505508145040004036402500e002c54058001c44d46501c1e404103003c107920701480404078042c030b10030725511000c0220f80c0d11146107030900c0810b0f4800c840d01c0300f104c81080c0003550183c01340303680000d64060f450040c3d0341e807054061500e1900340c00009907900401c09008103410400506500220020003d0040a0800350420820000d0000c202c8090344 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 309092805 1250 309091555 309091577
    0x10c060c090e04081806030105060f0c16080f060105060a08070804030207030206030a06140301090506070507080408011b1209030e10091d040201020f0a0c050904140114071d06040303 80
    0x700600007000140011526624107150904229000d900050401c84442e1010503d0b0081c914206c405c6905a6000400740350400c040740f04e105106800c240c102802d0381c03040042000010451000d44c6000301820b100030014500411031660038440c0c107038011405200d060150f03004154000c01196800355a500e803184856460303003000c078035103c0240d1000e90800000014003084d0f02040d0054001d49095000d0241800202d005260807229580c030301810b290015008a0100d81c071a44c024000c05000d40000c504098030391500a00f140c0f01090419203102408014618940d000842100d6200c840320b0b08006928040d14060081440c0000399441168002184000302d03000c1c10b061000b500c10700314102480c80c50320032601045076003550300364054130403012481c803031440002d41e040003075500806085401d407a140601c601602c0c003610449240500c91004c849882c800d101b89681d414190901003564140f4020240403104000c003440590300c00c516550310140c17151800c55003129850300e4600390700e00e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 309094055 1250 309092805 309092807
    0xb21040f06051909030909060806010305120309120d0504020a140f1302250201170903090d0c0510090303030b0f0d0803040602250204110313030e010207081f0506060405010c060c 78
    0x10183c810441c108514000c480b009040e8000c00e170304251340b00c42c0000c000701c0b516050216030b244000d1000a040c2c1e8400f4504006003034002f030245401c004100205c4d1004060300f8103446540d0001080f0b66141c954035001c01040d071500440d500d00400c4164180301c1e00c400a00e0118840e0f00440b01c10074050020320a0745411100c7d182d040769010504191806107030684a00c03055103800385d58605a00081400c0d04080c0d12101580300310f402001c03004002c1d843d02c5001800d0200742c8441e4a001c0d111648450700c00501900c5080300700e08c81014903524140310382d0545c51702074101d9504083c080d00074810031180d00d013145c0360a0b90010307416412140b01d907142e680d1031400d03c0c040d20403a401d4851400050a402503600140d41600803458070072201401807034003001031284d860008456847d041420700204201190068080b08140c0e031062060380c508688038603105141940b80440b2696400301204881c40951082c894035802c0001151071a01d010718040c0003c1080c981410040c24580c0c3e52200070242e1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 309095305 1250 309094055 309094081
    0x9010506060723100608010504020f0603060108240d030f2a020105070f0609050a0308070c03410414040b01020309090a1b03020705101b030f11040b21040f0605 70
    0x1c1c4442c2005d100d015140c1c011136001e1302090724200d00410f03418600b0401403411609a920848060f034a0102940d10414000303100c200c407038105c1405110312845610740ba21524030501c2000c1c043d031900205040c40010092261030103c0c101000d40c0e9403451300701441030000c0300c8000c1c120b409103003042c0c40e01e1607410f104652500c007010080c8140e1410190900f0001d000c40e54801481c001c1d1103220b00f13a82e8840c01620300000495004000840e01c901740713600440c0b1030900e01000d144070035003a1214002040140c0600c01e0b50b001c0c01c070703c040b00880c041241c100000907400340180c0070707103082c0700405480c80040e54034012012a140304542c46800110742c5207585c1c0c00a014907c1e10401203004c0321940a000e00254000070041da160b014400f11983c1205003402901c0b0302c4407600f0341001040d08034000031401400d0382c01e200303002c046d16850072152080c02d8801400150001c1040b0942d21008070400b1a141012101d0b102e4104400c0020000460f1501c101c80c494640c1107800400e540d55000311904d04 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 309096555 1250 309095305 309095323
    0x314090a081c0206010608061309140a0303050613110a030c1403010b0901080603010203100308090a120c0905070f020703060207061806051603060b0f0901020705060408010509010506060723 83
    0x852003100350704000c60b01a0105100c080c1841c0d026600580d03280c0744102c56a017811a01107030000c0c0e1038900910400740b42e5005100c000d00404100c403400c0d504c43e43d000d00344240307100140c000a499106011103881c0010020b050440301800400c00b140c0301e8803030f2075030701e0082da0303080c506240e614192186481e0149032a03c044451141c450307552581c50302d04bc2c8445400c2014594000303070b509000070b82d041c01c0504c200d902480d02d401c0d11080892031651950403e0748505071668000c03001c403000107104884903401c42e0700c1ca48101c1e81400d101e818290400215100200417908000c00642c0020040341c01082402c207990300158056560f0405e402c0071009130848000412140340a80413900034804c00790b20441c01a2091080380950f815000700450076655170b401a460714800810400c4400c0210400406140d54180107031890507688100049554010f86c2c0030403442e94642c03080040c180c0c0300707120740740d48440c1c00c403170003804d06a081d2107080c2c0c1c074882d074440c8681e265a8100b0300c8116042c10050904 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 309097805 1250 309096555 309096569
    0xf02120a050a03080a06090e15060f030a061b09050d080c1c020d0f0e0a0e10050306040321060f12050c060a0f02070504061217070b0f0402010e0a030314090a 69
    0x90a10700e0745002802d24504803000301c426441c140e03002c500444580244041d2000b03035001060027094100782710460700c1014003510352059545400710f841c1d072018407400240070b00400c40082d00656210036441500c22060310541046400c1e83e050245070786c1c4140005045400001107604c814042c10114030b0b0100c1d150350401d0747e403425182100c8065000408008920791552607081c10780f4482d07000d890020304940c005034000c80c801c03000c0c446010000e109552040010003950122070303940780400d0500d84259002c0e80082d02e0104030b0b8150b41da0418032294613100c02d400400c0f440d460b04981007a00c88050060340402c20014035660240101001560540180101082d50754050107201800c1080000607010160281d07200001d2245070605c00ca0303084954040d135203054814141d1341d511908901200848006400f489840007003074104035050711070540b0301070941980c18240005490701d11810401885880c900e00d0a2002036400528892007603600c4103400d071562000400a100300ca0580c00500e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 309099055 1250 309097805 309097813
    0x809010b06040f1508010e0c090301090f08070314031e07030209100e04230105270406050a05090606221e020307031d0307020114041d0f06010c0f02120a05 68
    0x810400001d001e440c1c11521140c102d80101351030342d281664a200b00740302d4442d1400e00740d0006242401c80400401c1c0c1c0500080000401d54000c0d900c0c411f02032100d41c416a0b0041003c9042010550040c0100e181e40d8a01e001c3c07981107240a9500c410034a0300b1810b82040d8406100c04140a180030b501505c4190b0303c02801e105407984081c0004188924003500244281d00301070000200c3d1341c01c0014901c040c4206c2980b079040b80c5c2070400b80100c01e40b03642e40b440d04d07045010351000c904202080150307000700d08c0303044007041302d04201d0885025508050300d601000d400000511000b952003841d20a00043c16005540940c8400d00400e4000c110842c1e25645100f41d4119200c040034056006500c248100c0e2400c1003142c83c488454100e1005004041400e42d00400c0032401646c0198250000e07014400f0910b450719481d80e503800e01010034601206854000300007071008800c0b40620700340e44005c007842d143e000d5400325160710050880c0660041d00407100110207800d410014005a202c942e0040222 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 309100305 1250 309099055 309099059
    0xb010c08030a050f060d05061512030d0608070b0a02101508100f0f09050307080f0d06060c0201090605130b09120a0c0e0c0a052203051b01080a0203040c060809010b0604 74
    0x40c040c2000b00e0b20440813042c1100040c0803481c0510707240440a410000401482e51040700040c080300807050860341c8141111a030101c3c2c84070402c001c1ca02013815040101d200d528041c03c0303d00d44281a0040000c8840c01d04c40801455030001d0888e00c00029074001054607024044a4502c01c0740c160400200d40c001d0504c2040e02c482c0f43c1c0c20480c0c852a503548104901c2c0c01c4140658200e445040700201207400c00c10501c0301103002c0c1c0d03000d40703942c0c0300b000c07241443d01ea80d0000364070403038040354865408a00425036503025980c011038240001d240c1410b1031490040c080511402e40d240368050f00201c0c44c400b1a84529a448600072216481c14550803a800b05420b030038550300504a601c5140d07000c10000c0c00080801007070500751810f03480301e901c50034180300701041280014141c100128460b05d40316840000450820400d18140e45038848411a141c0080b100040050a00030030a07000c1500400900c00010029260901110010301d41000240c035400601805001c0790542158010300c00b00d00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 309101555 1250 309100305 309100321
    0xd0e010f060608060f010507020904080408070f08010c110309010f0302090406031103101404140a0f060e010606030501031110050d06180b03010b0f22021b0f0307150b010c0803 77
    0xc00300c10350319682c0f00d412a5a0f1000100182c02d000ca10a00380011760502c001c40060510289054005200d1701c0f60a04042e1a50740d07041c07411040754000b4a201d13000c01c804001e0600d0a1041c3d2668aa051820200c18403404411503900d1007110324840c100140501e014803505e100303605135492030760b00820070f028442e900c0c206804c01402c84a5071f548a070003071000007100e5141a21461074400c0004060038a265900c2d298074800714400c40b100345150180d14000000520141040d1855512600c4005125100000d610303003100c040750000414140b510006102080d011b0010900b80d00b03040300d104c00c8240c1e40380d10485090040e6505101400d0608001080c2070400910000c031528041e00200121005101054203841e50310b90025008540c9070114481803c0200c0c005004d140e0509660f6090212451b240c02244c4c00b0442c410084007607030341c941a80389003e1100307502086a07440114100040c503140c070141151f10400000880381d40d81044030607030340104885441c01e1340008040340c45e480d1001e4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 309102805 1250 309101555 309101561
    0x120510170109053013030f1505070305150307080705060307170705070501180b04260f07020405012408070e0a0605070b0c04080c0909011409300f0d0e010f 68
    0x89031300800f08501006501d03120f080041d22140300e10300c182d03511020314607290400786140440d019180500d100388881a42c00b502c2c0906401020a03980024075860318241d10700140c200c2800d694803d81105504000c0f400000601d00281c170411540c542c1e4a44842c00b00352a00311080c22800c3c003002041c410032070242d070040701805409008000074003504640b48001145502d48131001080b14011402040116142215403001c0c0e0144400c3c41e10540040541c00c02150040c40c032034070354003400061482c11070030a402658014010404465030b207107000450b0005c9000649200810001844000340c0001d2081c0c080500419001d0207903400951a040000c010303500c000000d8500084610204642e00440401c407412514050040d150f001c07028000c2203820300c00a084440c856403a04c2a542c000c009a88280703005588c40b10003028829000d628648088420a80c0411a06110407464405034034900840d82e1a4074480308507591624034103100001000541440e400035840d02c00b04030101039540d4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 309104055 1250 309102805 309102853
    0x5190e060f01090b011d0102071a0405040e0111271c1a070504050d020105121302100e030607080c0c07030323040b0d020f070b0708010612051017010905 67
    0x1840300c102a80c0f161007090594100e032958600040c42c0c141c0d14442504424190040341e501441074031000307641d0b0540602c0817002501003403003503c4005010052480c20740310f94402080640c0003070000b40006801901c5034040d0740b04601500d0300c0c03c07107064240e6050100b18442a40010010101d20b000d00ca64074030415070030441100d0561828141c4524510180b080314032440b19540c81c40d1134030b400c0c0030610440e4113074070000300e040c0101440040e440440610320544104500040c4800c0d003280c40c0108907092030200c44000602c4210350446050f51404103590364400300c5070511000301d8445d51a004064461030194005034011035102008040c1d003c81c440d180341520051108090401ca00703060603501c40e6218203007552030204440b4043c24a241c0103464005400340d055410b01003151514108984203c071a84005810b00700140001a001241003810554640082003189450415850401c00c140038100d05803814641003800440250000d03054154000144d49002d50b100c0c40c1c0c600c200d1118 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 309105305 1250 309104055 309104071
    0xf06040f0303200f100e030f0433142a0a0507060e010518061b1501060305040f0b0405100212090c030a05120f090d080a0908011e05190e06 61
    0x82051031850200080d061060407094001c0c0c48900c51090080d8021b010a410401042c0014044254140180c10140006018140318802c2c4003920000e00d111215040d80940800612401c6a903c46a40002d54543d8051010001d070b5841c004002c030603150300200c5002c800c0c117000040410364000004145e13003040c0c83c490b03001c0f03642d44c2d515210240d5840c005030f40028005401031061107040280c5544915142c0800f0302044d107400600c48108210320001340c90000d69500c02c130308a11202004040180c0180120329080082c0d00385641c0b03140c07000c1d6400d4005031034078a6082c04a000d0120901400e208110308203003c6650f01c40000000009171340403940a000c9001d1124022110f080104602c1480755020001c1c010900e04800524882d40060030070090307241050140000300d03100c030b051440c0868013840340940c42e07600c140340081c04011940c1000031164100085045000c0c224185002c00714204980491180c1c0e544400040303019124100d15800fa0808a4a144030503010440501031084 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 309106555 1250 309105305 309105347
    0x5041719030e1302091302160c06090618030809010c051e10140f040209071412010503010506030a0c05010c080d020a0302190305011401270e07031a0306060f06040f0303 74
    0x119031100f0100d002d0880d2041e040548030600d0f0300312542da64010000e80d01c8008655107038404a0300e0b0300c64007006035040403011500d00e22081c090b480c0c01920001c0305024480c2190003440c21940d6061850046544181c140310a02041904000c400d200403000d84100c01c01585d0300c0118000200d036550424466000c42178a1310502110f020030040302588030380a90b5500003210b03103a0f0360038454074113030080101c0d04004d00645050302c4069090001d10f050300b0144104c11455041c14101821940058509440303030b407040d24420300241c0e503841c40004480007420000800012810200440c0c85010341030242c4910000b000c0840680503409490340c120903042c519042525000b05030202c0d00d0a0041001c0800880e07900703100303584111041c00e14400107281104001901c817480b408052015044600491802c50400207215030510810321000c04488011128504400200b9201d030006070030b107030044581c0301c00b848103a03c41d001100d0082541406c0c00844656908004045004481c801c0c548110 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 309107805 1250 309106555 309106579
    0xf05041214033907050601030605090a05060a021c0216060b0117131505270a0803060405090c03100506150903030d0504061503140d0206010605041719030e 68
    0x2140c0549201c0e143c10008081c034111006444542018140200d101d90b54440c003080e03103891440400703454070b28880c000410746941140340250a541e001440c1e03c3c0342c1d42c4a03000910100f0000614036800a01001005a541400070b002135010045666803071246800052060b181d00000030741080032078020b10082010410050044414030722041c01480320b03e0404008c030703803d42c00507080001c500c1e104010800b1907001050228007900c000320740890031041340b400411120b08940c00c03900006946070001c2d100c1e01c0360903958030350346010180481f4011599000080e0005d18100908071615500404403003016584500c400044c5c0000c8400d14080c401e50b8040600308002d2500350380c01140300030051350814000c011180000c0900070019600d050b103919046c8007058a624a20340914001c0c88980345014082c030059140401182c40c0c1d40c02c56001c50010484c40707901009840650302041071103c0e011a000541500e081c520700c60305011514035040803800c05400100c080340170b0005941e040c0880d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 309109055 1250 309107805 309107837
    0x308041805091005090c0909010207030f0f020a0311030c0307080301080f070311061c06060509040b120607050c0f01050a0b18060109170a05060103081c05060f0d060f050412 76
    0x41d0152001c114580c0001c261010800c11604a1640b03c2c07088000c0b41d03100401c010015036080c100395072032a8240d50006018046c141d1000000741c80403201e00b8070320310700309504400940d14401040d000d0b00300005802200100c0a06004985100840c14122134682c0d0703090415410680c000c0c41455968414403543c00c07405100800c05500b202e8105001e40072101112090003003583c00b04003201d0651078000c5801c06000784c6841a0b10160401c4ea4a142c1c9503041107007408215a4007800c2e44c0e1040420100a051002000410b282d000900e0304d020764031014480c15403454814200b100c2110f65007003070308110b008103107907024903c0403034112440e505050100050340b032141406e44009000402c030b09424000828801102883d00b4001c4088550030252601c5060409000381c1007128081800640d140074010f07111003070316001051042c10886401d20500050550340c2c010001401950b0202584081c0581030340501c501640700340c820b0060345480e02d0700c0361010340031500076800b007400206105503207 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 309110305 1250 309109055 309109061
    0x408060708010506270a0e22080703140f030106030903090608041205031e0a060f080303090a290f010302010810060801051216061218030e0f0307050a03080418 70
    0xc80340944100e10300214401d160f0060b01d5088042c0200e0805d80080505649844580c1d05c02404080741250341c42c01c00032020720f6100c001084055044554664450106003524101c40701c5c0355040c1000c1c0c074928000d03461070380a40180600402d5048001c000010016050340041807041d100e95140c41404d40c032500291007001041d0340140c440da05400d1043d0b80e20340034500541d00449000d1802c1d884011044121004aa044034100201070300c50b1010003901e849518100007034101d20002d035095103000107805569005a04000d0301d8891800b10780c4182aa91460a0f216040c081400c02000c0c580b90740d404249840c03c0c401240090610130001f0310740c002e510b0754203054600c0e0703030b946030116441c08003001410416200c2400071400707441d01040132242007019407402421540c84400d2040301c82030036082164800101e403100f100b080b114034800664851450840c00030111840100010890082441d09480382c0000703802002029001c0300340941c8030041c00c120740600c0c2e414141d03c0b178011000d03416 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 309111555 1250 309110305 309110309
    0xc090604151512020c060f0606040f0b0c0c0a05011407032d020c010207051005030405070e1f0b0702060304020607211805030c010203070f03030f180605061e04020703030207020303030705040806070801 88
    0x403582100021800000c000f1007c25049480108064206622802c3c4451030342c400d60b02604455800080c80c001c211028403000c018148201d5a40e0051490040040c0c0b8000c031005141e581c44100080450415003d030000200c00c0c4c2400764803050740c89030400c2d00ca01100c0d01501d6a0003501c112710305c84209610000e109130980d20082d0914010f102481015035980d007024004031402d004030440455500b010380c074818400c80030541078a14000480004180301002c5030400f6000c0b410810801c805601c1fa42c049a40140c0c0c15104540c2e11241030500040f00c0000c507070034100a014042003000c0d141d034446001528a074210fa5207a030032683d50404c05a680303180030052409078000388008408101d100003540b008600070300300071680700304006401c4120f0b4100c04509a0307509a007900700d401c0c0500e600c2140d601c40f10075207812260344241c1209035049409034203418070403600051039004051182e0140e075a02a40a0122920303801d0800c0c0180c403076001070041d02001d1007000700184030b080c407411200741 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 309112805 1250 309111555 309111577
    0x110d060e0a05090709020913330305033103080406180513020f070501062c391204021804082706031e09010c020c09060415151202 57
    0x4c9850b01c40d000b8041d41105121a5000402e151031855800c0c0301c1c040d0001007003a100324a2150b2501404005d07400b441d00c10101c0580600700800d10000e4400000c031011134102410481040c5e4501d8003000e4400c100070520000316191290010070041c1460190065607480e8071241d03280c540c0c0380082c100e084005c0c4070f4194070000c82c4416001124440d0300402d048110580f4140c0340c03004c25240d0509641c0190700030103001d41050503d68181c0f0001020380c40c2401701c0341d09044242002151603201020020201c00b4120b100b241c4442103c035030710304070030b81007107008081c5495202189022031580c0003120240d014408480b0814200390768012090721466100c007085050404600030b54200911040d010040881c488031107440c03c0d5584800703144030b095100506e54152006103502d0059220107000840b60340e04011504180903008a40d4010040058944111550320a80010b001c1c26200080c58030542c1e882c0404208080c810041c0b09025255855100c0028801c2c3c0001089100300301c8401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 309114055 1250 309112805 309112813
    0x905040b010c08030a05071803030903050d0801062304080f160902091e03010902090a0525020a0b0405011407020a03020c06070b0a05070e061801090806070c080a03110d060e0a0509 79
    0x1c141700590b40c0031940002c45464042c840d1403111719802495021b0760000d87c0810710104003001000003c01c40e84440c40b070b880c41c0c03540ca81d515254000c0e104e4801030604119030751014001f045850341ca04195401491503008a42c0c085048200c450b80710031241e2210307201c80788810000301f001103e034000c0369041e0001a0800c51042000000040203001c410344071641552182d0f4248003596810341345038083e5141b454001110304101c510150a0b801c000803c060b0411480b40100245801203412685c1607040100c2c4002039407946031050042c103e143c00407081068050030300801c1d03030340090340f24030541c0b1030b408540b401e0b41103000300701490040c0400104540c0407000025400c111942001c2c0d00f140d40c0341042e43c0850b01d420001426034100b121804c51034580c2e404500d00c0c96030301a101500411910001d00b0301130a142400602c01c0b4940e58005c3c050741c20010b002001e4510962240c01e000c418041c0aa4649000904000241032688144688128903001080310010325118041c002c4c3d890310300070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 309115305 1250 309114055 309114061
    0xe1621110d0f1208070e040501060801120606050d080a0f020105010b0412050f061f05010503010e060108091504080a080702011b1202040302120a0c0b0c0601050108040809100905040b010c0803 84
    0x80706039105640210b9074070140060078400640429035800101e211a1240b504500e01081e000f052220001d0030a071003241002d004118068224a071141940c82c808213501462410741400c0d006012140d1201f40c2009102e0405402e21040d900a0a9050400d0b60382c01c00e10046c00d01c0882c240c0382d080c01010902d0700104020805000304081901807281301d41c058400b000f07005010b107418101c040b100500c404910240500801c2205081c0314040c0c1402d00300141035505061030040e00780401015641404028800f02d4200341041020600b58144c40c4109000e5140624003500c054201100310000f02c0e06440204403500c1c0180100c00130550303007014502403d030100e802140d05007003c54a501145a08010100140e01c2d00400ca010b10f00340c904c010502501c0e107107040d0007140507503444031846070002d02c00e07900c14400208009045640c240b030440c00c15141c9003095802031180c0c0341340c00c3c0d000c1c1340a5840d03034010f41c111080408860b400c50b0108202d031144801961030280c0c0c8100100078090800c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 309116555 1250 309115305 309115309
    0x12041202240c130305031801090501020d080109090507150c1b0315050c0f040603021c0b014a030c0913060510120c032a0909060e162111 60
    0x2800481a0640f00b65043c0d540d25213403c3e040da80a61315411042d03d2003c00c83e030003540c00c4500303203009001c28801040c8070200000b00604100041c06130060550310344903000140318042101c20041d0030444c2054020582c1210064501d0240860880d582001402218156900c881c044011290447c1d500c3c2c20440304c0f500158010180201111380d0504144821500c200321800500080c0007152030040c2d03100c03a802420400036565103507241d20b007070a040095a541e680802c440003035200d5491080300c0782c2e1103910005202e82c065610918842e600c503903118403015124256144814040d8140c1b100e00241000744400342e00c0072110510005402e0344181e000039016401254441150259139000301e4440340b070b60b00c0141d91442d05880450f00d144050082c042c00e003004200c04a5014010665003103540c40e14640c0f001240b044807140c55465401d0821b00801e40c102c00b0b43c0107a1b840070781d600070081089440c110403860041903041d00d40d020118401284107134036018000e401040315552200c00e002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 309117805 1250 309116555 309116557
    0x2070809010f170c04030b0f0112081b03070303230708130501240e0106080402030d030b061e03070306080c03031b150f2e1a12041202240c 61
    0x10b40100315041025200746500d02151502808030954007690362491820a42a91180940007040c0c082e4000010440342000032120492940d02405164483c0701e48501d03001003100c002c90030103e80c000020322000701079155100d8103c100c50b1206e07030003055914800071401064103c0e40340c03000c150100c01181e880280c8440300e4150520400002c02c1d005000707858007100714080009151050399072076041c460728154540060242843c2c2c6403a58140c545034001a6407010400d0402040c1582c078040b9041c651500400c0310403002200ba0306100b5a8902407010655501c22641100000d113092008594002e0100d00c490007030703100400175403c041c9081000d03464086040c0503400700388502c1241442603010038007418418034010002d451185480c8044e4640726104081d005812012581300d84480c0f04d0383d04506040d1201041c4040e030360300c03a1010050003481007200d00d11880000c84100000c0080113080d0f82880c510310b43c04c0e1000401c00141d84078400740349a500091050001001030f010112801c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 309119055 1250 309117805 309117827
    0x2010c020103021e1810023903010e0f07050d08070204052802040519050907141614100603150e0c040216020901060f0203090f0414010609090f0207080901 68
    0x150224074036800d8402c445110350300c14038200110101e01007040900f45894140e1b81c0020503103001600c0c201c40e11011081c08460408001541c1815100c80403280507814005a01110005002080302442c600c5145036120001c5a21000714810b8003404145420517602c81c44c1ea007540001c40506108040d400c10010b0440148520710720242d96a040c441500c4900c42040c42a50503000140e40b0307400d03c0d00b44009454a0b88107101c070407213140b20030030890300d0724200154400458501310a541014541c1c001840c030808626404049040124500f403025269441c2d561450100840c0c49517605d907940501900c02c6840041c006612005402e410040c40742c204110202c0c80c0820b0301c0c3c03019007240002c3c0c206c0c1c01824000d025803034881d40c5002141008800940903003080c3c2401c10300f00d801810020758a11500040c1802503840c81c0340805551a21713049045002401c0e05001c41942c0c541a0050500466110340175269082c40400c1d103e41c203191084625050304040050f20b480c2612005481d81c9281c2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 309120305 1250 309119055 309119077
    0x9061e170d1d06030c040305060615031302010c080c0106090e0a0302030928090b010f0309051b1f1106100f050405180709020a0e0414060904080c07080604170702010c02010302 77
    0x41c2203429141d45030340c001e511840308074417055191402e60910900d0040010015802400d00140440c98800e4103030981c0d80c0549880044882c0210a100495001d03018100c014490040490050611a03040d0042c40c03c0c2c0300270b00c1c0d0801c80107100351200d030380e02c2c810710704c0160140e0000c1207014020700b4811306407041e028850781c0d8140510114401d21742c4140003580454949665045410495070f481b41d2000019051880c0906c0300d4207039911125118203c0304405480282000c40c1d5109a44801c500e00e108101840c00313801c21480d9400000c0d1000da9002681d99060041e40d0016421910741c6003840c0649800c2205000300034240024030008007005000311003000456030501950410401101d00502001074000da2260300b010343c041c240801d01460a4841c50810890301880341811002c1e550110301112165250b84450500300e00d588505000d646d0240a844e00200d042e0800141543c0107902c541400504040d214107142c410740100300009000401400c15100598402d4028220b07031100c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 309121555 1250 309120305 309120347
    0xf0b0a180c05040b0d060905060603100e0a06121b060c0f1502090d0c03030f050c03070b060f060a030603021003050405030a030c0516030810050f01020a080d0609061e170d 75
    0x1318201c0c58001e03040505880c40f1365449034010700040c041d82c080c2030340054080d1049420741c01e114001120000c02802259840140704d030028424280383c0d04940014000c2801c120310440090900a102940f241c0c49160720380d503001e0000580d14801c80c11565000e801202c1010700e811f45664a8060081044000e0305080c5c003840308007030307a554081024000d02d10452558038814994079000d410314a00f54081d0060041c14040030503181c2020080b5003090754000d85556075980c23558001360308048940340d015040703500443d42d41e148a070594000c209031f80c0200d5a840309100c0b000821010f07540101c038010803642003400f044000318040c8d0071441801902c1e04106060082101c02d0409540b6003c00542c00101c10b40d00f4001d000902c081c44601a2800f41e4071a4005840c0c0c0380080d58906035004000d10024000074400344a24040e0300450190280c803030107102d00c540e02e824070b20820b1481144078601440307800300019440352001080c0204030b4190042d044002450609031100c211340c200030444811 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 309122805 1250 309121555 309121559
    0x306031b06050708031510021006050111100e01020f12071e0e0d0f0b0c0a03051321030b15030411090108061303090b030f0717070e2704060f0b0a180c0504 68
    0x503880720314460080c0307a68001c0464604189201060f034ac81130b44018113102c3e000b86494010907011513028a00308800c407010540051b9000260300a01c5020305581d80f00034003041d480c030700d01c2030b5219050064003180da03542015014052011801c045d100070b2000800c08013080c04580381487c070b414035075041c090b81000c2c0030001a0f88440d680c13003100b00d8014150b80c00024031004034681501c203d0b60021031808052006251030340d034401c007159039003e0700207020f4026101c030b4104501c00d410400c00250040d100c54040c68a0101391a0035800540c0c0850309401d2005054490341011b480f141d0495000354010801515580c9012110300e050720016003c110003000003294011201c00218002c4a201124020918060800500141d07003013540069106450007030140d1950700c2842d04400c004210344513240000c0510303140c51009c0140c184e03003545c650f5840c00c10090010356032142c44680c11a01050080d88054010489030701c64501542149001804001b602c02d8800d03070042c8031044d454180645015 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 309124055 1250 309122805 309122809
    0xb040e0403271d0105130b03030c010c09030b0c0702100305061215040b010e041a13023001111606060e0c03061302040e0a0c02030d0c0306031b060507080315 69
    0x300b00700a100400903840008000e40c81c00c400e40c0200700303501c02001c0741c0e141d414900000c6070141150782082500b0f44882801585541c144115445a02188000c020308540314034060f040d100648000e4982841000004204990313090482d40150b5006144e500707a1355602c441600200400f81c011038103c95411590801140c1c2049007080803101c010311031401e8035140c9030202000c201600221940a02d00c0107010002e51044c0e030105013610900302d00078030382c2d95400421500358030100f00654000f51140c1000010054039401100f102c80340c0032001e081c0316044020500382c0b1840c1142d0749801c5410400300c0042102121204070540c820b170300100c2d020b580e6940e400e5100506541c9044541400010b0045500e0095401c1d4010966501c06500341450055520f40e03010f801418075001035101d098010144d48280201c4060390b8500f00f00300042005840014003d100c01d0004031042250751059825400791180e070302c01154002c2d82c4481c909181d40d50741480e42c1d000504290040440a500ea5410f6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 309125305 1250 309124055 309124097
    0x302060901030c0e061c0e0309100311120a0203070e0f060a031505060705060f07031415130e0307060b0a080a140102071208062805270711070e010b040e0403 69
    0xa50181c0f1040321441e421b8a0036004a5200143d0310130940d1003000400015281c0482e00064038801d0b0a00080b8500c40e03000b02ca03905c4c03065400000b4140714000400041c4050380d0b024501030006a81c400141c003a0803810f12004c14000480d681d4015001e0003106102c0740b080e00800300003035101e00c41540050b501c80100e500da03046240110b405803c81000c003c50804003944cc0c56001100d40b609000051032103500e8505280f010b0f091501040084402c001c0c15191914004050480104c08100d2822a21200c0d0344a4004100c00c4400c01d06003140381800c1e243c464200e1003507a141402500b81044187e90b030891a4010441c4102d065400740600f402160b00c0481050036203009440708030080c07510340704005225040c01d207000840310080e03603030b00030308000d12000343c2c1910340590f150b802c0d00404031514000758001c2c01c65890684540d1041011866110405441216180c000c54094685400e29651100400d0142d080301460600c000c000005128005a41042c02400c2001542d80b00001d440c8032 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 309126555 1250 309125305 309125317
    0xd0b012001050412030501050a050405130f0506100e09030904050618011509080a050a1509020901030f0309060207080604080702040b031b120a050331060c03021203010302060901030c0e06 82
    0x51079564008200c140058001d541c2c159078800c0c941004158100000102c0d803843c9401410700450f6201d00181200c000040411111a0804078007441600d01d0301c4d0003591980116080070808414000010f0f6010b201d05045005100c80e42c0510704104540050000604c0002c0410742c0c0800d088180540040507443c41c5406452009000e407513808155201600c0b207a041e6002090a900200c2d1980c08210301080c200d01075135020042c00c0100346031920200140a4200c0c0c01703913104882c40000020440d00701c0408201d54481c1d113072a00700725600d90080e610345489221300a100d4000300001000100020020503449100500018056041101080c581282001400804e084000c00c00b10586082c2c145541c0b03941080c002401460265034807541c030bc0c0140801c50301081c110096841c84491004502d0000b00c11460820380096a41c0a0040407400c1c0e1020543c00342c081c6400d4000806c1d2058112070507680c0140c1014134210782000110010308519504004101c1c00d4030400780705648660083c80d0f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 309127805 1250 309126555 309126617
    0x11120109020309010c14160204020904020c070305060907050a1403030d020c1b150405010c0c03170d0c03090f08031f060e0906030102070c0e0c0403121101051b0d0b01 73
    0x61240760100001342101c000191010610012801c1040307505200d20440c1c140c800c00a031039091980d0b1510203e006402a2001a580180080307200703500400006084070440c0d01400458a00d41c803210181500c9006c98014070f504540f0b160ba0502c0500c03295900d1000200e400380c12646030240d03c049902c01c0b80c1102041c800c494100400300c0d45540f0941e040702c0d071140021560034114944101d1201018402c5100f070606119102d030141052124840500c401160868031030744602488040c210120b134040030161009500d480111301926109100c1c0c20300850707106811007810186034a80610795040100100d017071000e002c490078061107030a841d40c0003c00b115110320f0002c0107154100600c0c0300d001422203000784c2c03041c002100442c40130031300c1030101d41d011000b030343c0300351a81c2444011510a41c6c2005c0d122800716030300748070100c0e8017090384100c4036105002001251603030910440c21501d081c0c0c1c03607600c0d08010301ca4a0b1544800380e01c4054801c105050211410b04a0a140d00c442540201444 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 309129055 1250 309127805 309127807
    0x80307081e07051801020109060516090e040c0306110706140106020d0e0a050f0d05010207150506013605130204080c030d0f0e01140d05060a0b0a05030a1112010902 72
    0x18040c40c40308098000d808804a52401c80c600b164004150b40590007202e10f080d00110044c02c1182d0007907001c00d00703c0c2c2d044041403200303150071a5203a4034240b070f01c1010000a28a05000111302550154080c055a4082c1c4004070039841c58885030054008000d070110450750401907100041c001c2c0c0f040070100c042d0726a40103248e625100001c2d003030281240801040c070100c04801000c0d0354801c221007058136000c4a01c1d90006580c2030100e81e5403500c14070020b1141d8400078448046c05101c01e00140c0342240320030705009642d60364004440c02c502691801a18401c0010842e4070b940700c105524800b2001d001d07441010564410000380e0000f204010301c442035500240a0125003000d06c00c8070400700307054006240301e40301c0c601d008014916031240c5504100c694500100c04da03100391401c000705c2d01503450b1a83c9032184017582c400104800d4441034801d15508070b0001340f00001d5820386480001d070b9203901c0d055986884000e0050040300361000b60002d810450100c44000321354405010f481044801 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 309130305 1250 309129055 309129061
    0x308181c110402040806010b0d02120a0207051b0306040b191103061c030504030308040816030e040e06010617100302040504210801050d08090109051018051f140708030708 75
    0x200c0a103100241c050340201c0c01007200b03120500e400a01e0a0445019400346d60b520a030440b0148003d0095645082c5c04410000901c080b21a00f034000d4490140074409a408a08111038020b100b010b01d100c0650b091b410110001740800d41c80d54040d6440140300e4070203420030308a248203908031010035100c9a0300810100a020480c201204001607000090340e15041908850314041e04500a6200003010000080009810042960240c03810000c800e80350030003c421a2801070050700310b401284d80103901d40428540040c40000b0b800c0d040310282c0c2c86216415203d60012800010010140c50100144820000040c2c65501c0b81a118a0107900603c0c0392002e407003085841103050f08041010042c3c400014410740e55a80c0c0e440d2041030388403845135aa02d80740310060728080300b5544070540c0048280c2805074641d800c03503a0007241440103d290401c030341d204e008021504040745203808202d848505100c40640c040e6000340b40129014800608084182e40c462506d98021242c0f400019109024 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 309131555 1250 309130305 309130313
    0x507090e04060b300d05030103080f09090408040312210c0e1c0b09031207030c021e0f07080109151e060312080c1c0c232a070308181c 59
    0x2984c4401c40303020002e03140000034048020310030300041c08042d00103070001850482e900c191004451000201800911142c50f083c24122480d40181c4416500c1c87d0f17108401000291069140909240c0c0801000d0f20140aa6107010018890b0032400c0b0f05000200d602ea191591743c0354013400ba20b40c621070060800110500c0d2076042d0032400b4180400c0c40d48107101c8e41c1c05511816124551064181c940000c0004214008900e0030881807001ca000405101301316000e00c5010070b00d2260380d0107400481e015190344800003400c841350048064002014516500d810b0304a54004294543c2c4614014103101c0d01414540d040f1380465000706c13840904010071080e410340002c2e1156010303410a04680c1800c0806801c07507106c1401000fa030007401d543e509041c600701d0084030f0991100301c644240c03070503084010b419101e07903501c440c40b0f126140302d0918480203204040e00c0f40c01d01e02c20440e0f012381015841e44e62141e5042e00213800d403542d68203014400d01d890f62903483c0640007021244e08030784801d91107820 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 309132805 1250 309131555 309131629
    0xb150d140c0a0207050d0b1b0d0c020f0613050a14010b060408030d0501150806040f1e0f1b0f030e0a0f0b04020f1f0c060e030304120e040507090e04060b 67
    0x40070790700407028180d21401141603c2e500c1039200d1200b2407942a01250f00c08c45000e80d2250b4100030125074138001486010560010b418440080745104850301502e6050501004103500c01000b00145d00c041e0024000410000700e032458096444004594806071a0025649811680240007150b0000c10090b0803c3d5007401580d00600204420020032080d02d80b0051103400c00901c824080c0b038403594440060703081d070b0f4008103100500302c4142147d0580510b4110107065240e08202050303003081030340c03040e550b0206941c0c00c442a00e40c40784a9801d144960a80c06803942009040362070064040400c0411070000c81c1c0e40c3c12038840c1014610a140c20b1041121500c0c9074601e503400381c1102c10791502a51410034040c1c001c2c00160400c02007804a51501e41c02405021450907402d000c040305010400c0581901e220120b0301c00e441d0501168154028002250701c115018800110001020000ca080030a0010b0700b060203140c004c526502150040303900d440e02100c2803050055070046452140c10040c07 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 309134055 1250 309132805 309132809
    0xc03091207080408340501050d0b0a15090302041d0a140f070b0304050f0a0305041e0f1d0f04050a02150c0616090803090a030209060d0606030602031602010b150d140c0a0207 76
    0x9001030300317a203082100090083c000d0f02d0300c8580c2240d07500d4880c4002d6403154503a800620b500748440100c1d00341004020300e00f55071484100d00841c03c003000d20351409c103801b02c11401c043c03034500101b4401c515a2a26115000018810083c600881d18080083c83c018131400c0007901011300f01d01d54074282843d0030b03854500c0036540c0c0c1069402009140f030002e42d00a003140d080302c5801840c0b0b4423801040e110103c125110360700402140000d060002810080f41500f01c07850940c44010140c559140721403100d020b5412200103240d03401140250005240411000e46a480c1c6140881d04100c10743e4915850990195032071204440e6441801d4076881c0d001d55010003a000c401d010303508010080c801f250416510380002441144e8580000d4000e450368603020800c80e4110030148007450340d03810140c000f588182c1d40c0c41040085514100300031401400b5038084000040c040f10a00e90f950020024546c0120071070364003050b103a0069080310002c02c81114004c00340c001003155180c14200c00370b49462015 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 309135305 1250 309134055 309134143
    0x90309050f09010b0c0106050a081b01180e0a06050414011401050f0d270807020901170d0c03030209040606080f2505030c0715090b0c03091207080408 66
    0x54039000d001c540390322008a046030042e4220703544558420b140c0c0d80c090f050f035070009900704145000000d900400018804d11000804000c0e220702402c2034011a40b049400c1c08481801d51046410000e06c000101c0140e4851880000010b1650700d810004061320000c69003208010b2070b40c4e00510901241461b0210070310801d00702245805c14071a010340c02c0307018051404254513610004541612014040b000c260701c00c001040c68006050320749040c090708555001da0189007800700200d5660000050031409840a10092403460728001c001c0340c0c0844603003c1201010340901004115407140d0084002910183c0c80e81511450018248419041c00404514400c0b1034851010139052100d1014107a0803103900d0403039074a50303a04c0038480b540d110f0300341c0080403800c00180043c0a510541e000c0030003c0d22461407a180c0351101d0503020342a01060769040b19940014600083c2000c0000040089a108a100a040c42c1d60b80142d5824081400d01e540041600003031000c40b02071201200c20408509 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 309136555 1250 309135305 309135319
    0xb0603070e06030a09080c100c0e0a090e011514090a0504020607030f09050a26071a0714010203010602060403021002070b0403080a09150e07080309061204020604030f0609030905 78
    0x100d103200030845034481a00c54015070001012079420007260700310109058100386183e99035001c00039403540e601d031407101003021107280c0200c03042c8441c46410b0500090000a0000d4519401c01a401300106404002104550340c0c81810740303015000f22003114020401138040c9a20b070102242801500d20000384800e140d14030340800c120046e514035050f5440a501031404180205a40c10152025921a08119440050328400040141548912140320300c44049818840ca0f18002d80587da02c88a02807841d500e48130700b40403c214200d4202410006000c2c000c40880240c2c040100da0880e403003a08804e0058020300200300a01d90100145e0a21200d000c004528110040d03c0750800359001400c02401c000d1034001003482000a41c02242801e604080401c1d045a2b2101810000745201c099051140c000c0103030000e0040e001100340c400810025289900d001805440300c45049001801241d11840a000c04004030700c140580c8041184102400074820003a03090103071600000d988910b224000d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 309137805 1250 309136555 309136561
    0x1908091305131202030705120315190317040302040603050708012307050307111903270b0c010e0d0302030604060e01060509011d0d0b1e0f190906020a0806040b0603 72
    0xb0840401210707641e000303a46890141c202181c01c9081d4840c0a0001d070251182100050b001a0418021401035408450f010004040e84003070203540280c0c280303600004032240c00f08001181c4182c02d480f084455180780075142949a1380040c2c21209690000c0c4c81e03d038040302c03091040010900c40d82c9051100c29071491000c1006025907201007100500d032800700f10b40400450099806081d20650340869401070311a1445c1c2501c0d4090042070200041e40001c5550b064088101e00c01090b4031400d0b610064216100c90501c9901c03075280c0c0c000205600c0565841072400d144280501101c0040380440d64003595a0404078104801d8035543d41010840183d0f07907004105503500941110310b031480a09040c0248409400414100300f0075501c0c03070750022506564102006480c8040900c2501207407003d0182c0c1c2025904050031000c1141c400d80e00b010b015000c10ba035800c1100b4411950b200d50342001c14408615a610b02c180c2c0c004e4078a407800720315440300340071003490107009603000420191015420f41c6 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 309139055 1250 309137805 309137821
    0x180a05090a0c09020a020c0d0629010912020d210f02010b0904030309031107120213050105010905120f030f0a0e01230f070b0f100e0f0c0307021908091305 68
    0xc2e81070f228882030294001410708a2a000f402108442da80081ca4102d441615040c0031026140520384c03646803148083d04000181c2c0301d280c40091190040e0f41d07550f0690705080701323102003490262059901203011f0507100d0015504240a481c12030001d4084962625400409454401c00a19403815039051a109088640301d40d01206d030300c07503003614000c500d121190600344c8a00d08060356490b00e5005250300030803a84d150303011368106e036031081e16400e8495114509980440300c080c000c990001c1c0001c00b041010740b0348240b440401420010513210040700070b1107400d02d198403009179401d02010100c1c0c440c018603048668040603103801e007404400302c2c0880c00201004180c41d000c2d18119400030901041c100300d40000c3d1050300741c0c40551220340d802c042d1400c20034090100c2c1d01d030004111408000c80c01081c940201405014088210250398440e18880d20700c0b81c00080844085100d8401c01c0c910910f1022a180106070085640c1039039840110184072407401d180400003c00c508280c1400310f24 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 309140305 1250 309139055 309139073
    0x30906040308070c0203010c0e030d030209131e020304050c0a05062b02090303030903180d050c010318050105130b010f050a1403031c0204090c0c02090a0515180a05090a 74
    0x316500d0b290400540c0d40b840c4055815803000400a0340662070f0100351350380c1d1034200b60005d65031007044003180c5450320350000480680c0300d121031140c0c000701001e0210f003110105820500c2000c0c0710103811400c05203c03c5640049810440707081d240d030303030011020844c58242800028080d14003600c6651520711503020468440d0340b440580044060800200070b4102c0f125410f8800c40031005007580e41ea81051208156607401c0010600e04d00c44040509441ca4603020110907480c1d50310102070036a8200c100e0064009080f084101040306000102c0c0e040090000c0c8500341c0300e02c500201201509410707042c21450010b058025a0b443c105c044018006039540152140485020444102c034980552000c01d045000756200340c541918644485880b0829a80142050301d1a001080080e4201684100d5500d04541c1e8081e4000342d0801c003080366076000340c0165500050040d60202c07072244910100b401c0c66000c04101610400040a201100545005054014080300010071402007992900c042c0c13 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 309141555 1250 309140305 309140311
    0x60f010e07200c031501080c0303070309060c030c0210030e06060906012106091d012d0e120c03070b0a0b090f0a0608030703120b10050d1d030d06080d05030906 70
    0x1c01c0100c15240c5480a8208110203101c00080c080d2a039090030717680c0c2003003005400e010742c03021400f038698048000e0078000305980c010344d01561006003031813a0480554024841c418107608103c81034a01e840503803504181294100481d6a002440c00d94416040c4d0500f07101500380d51041d10106d060000c260303840300c070303030035003000c1484410048460651100700244840d5000c410300600340481440440d0680700d80d910704079040c200a0080440c4441c00c01000803e01c5c290b140b80071126401c4003c03c00705a840035110050302d6040301c9900510314071015aa8000728104a16940001081d43c00c210100314040d4001c03c8000c000c0c00103c848178001810340e00010010750301c18003101d001540328901508428001d0039610140c0ea60380f22181002006104050300088041c6d080055144050504c5205a03d00c0b030391381d941b09400e2442d44000358000e0418036005008810b0581511909001d003400103003141a000b860005140d4581420700341071101307141d242c030b05002c02070080107041c60011601580c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 309142805 1250 309141555 309141587
    0x60f0c20060702101809050c0417030903010e03041d0c030103080f070f0f030314090a060c0504030b010e06040e1b13060b1207020606030f1c20060f010e07 68
    0x41903100000200d415806031040c040d60140c2d0001d5542c1c55aa049407090300046241420710985540f20700782c1809540050750f41e550030f00c40c100700070071081d020150240c2241801c002943d1400484000180c02d450210361410313015000003500700021a80c07082a41042002811a0307e441d2506000e40d4803580414480581468000514020302c00c20000881d8800d42c0d100d4180b5942482d5410034000340580c0c3d01c0101d002c07034034244c1104030f0310485280c0684a890340c403006000900369a0b031040003a1180401490501c5001d01010000940d02c0094074081d202c142d81441503468074a0801007a280f01004009060300481c50b140b015081c034040004072100192410b11038a0b06481d41c2c00000c1195500511f40d20311701081c4e07001418481c0c40000d005000f1a803c07100c1a0f01c509040546560182018082e41c0c1d00c20480d01d0040c0111509060076082141800034642c03880d041c1c048840541520501d6140d000b0000300000f488540c4500c60150018440440e03262030300300b0014220b080c1120000e8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 309144055 1250 309142805 309142853
    0x206040b0705040806010303030608060a290a0b12090c0d020d170403020604170d0801061704110916140913020304020a03021302091206070507200613060f0c 69
    0x181c125405070040318010001a800c03940c882da982e007002401065a40102d05560156101068000305680282c0c144060441026455101998214600450019070b1039070480070f031200005401c00003c0141504845078407059040b442e295034880e04114140c1c81e034600c80e4a1411041002d602c4aa0300f208450f607001c802c090300f02e502c0030b05030040d502503540002e606c00800180400c4100320300312030728902540314049801003004a2010f0300d0a0b02c00340202d600041c804001803034044040d500b100c1d0424040e86d810303c600380030340e4042207043c00226444400040c40b683c0a107450360340042c15181c43d40c08083d03a5800e0001800008080f030394144000345606030044040350655a03a50080c42c01164010508084a0076110444010f504482c5980d8400c0c02c152100d00b030001400316071244901d0003940c0706071401c0e00c0c6655600110703d9040080d503201803046401c0c0c2d05521854001c02d0700f074070440e07400f40c0400e280040041982e0207244103a410800e0341406100025070070030f02880840b108003208 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 309145305 1250 309144055 309144061
    0x1401080a0207020a0f0e090c01080a15050a080f0f030a0909020a020c04050a0605040f060315091b1805070516080f130b0a09120c090c0c0f03080108100b010206040b 72
    0x300070340640200a0b40c01840700c040050f4080c900c1441504440c13400c51591041d40d07070003a890743c50700c55214030b1901181070036000130380c1e2481c250b001c0303e02d0204084c0124280d684078004134403038441c2500b124500b03a128030500c04407170b48200702800c00140150003d40c5001650350005100440303520550a800b0b03000714a000341c90b402484600c0c0d007400007400800140c58005040d40140106200366070103a4506944124038031964000d00c4203a03038100701c082c5041007800745110024580c000c0261342c402d14405410303484018500c01c02d001003400006e00e800d002c49840d401c2040381e80282009081c04000c0200d4110360160308085101d560300407246540300c02070107105481c02e02c6499150754031041051340c007140710b0084034040c246030075130347e80c40a06540d110110710b103a070701c0404030103080c182e4082d408025010054000d400140d2443c98885414a0f1560b00c500005280000490100b0404801030005840c100020916080c0300d0f00c090100340042c00010b5100e490190020340903600d04400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 309146555 1250 309145305 309145321
    0x1b030c0213140f04060c0201060308042c04081305120a060e0f0708071706071b0302030708180108070807090308031b0a081906050609060901111b090603030301140108 73
    0x1c100304054844080c60b600d4030b41401c071480c14810440c0d085600c9854050985400340c414490312082c1d07a8401e05151409040000d69025514800392020b81c0344000f80216029a00c0129550b01540c0f2890005880d6804050601c11404464002034021001e612450201e00400107042800343d070022000102c401c5031a94071401c103150b1543e4440d0500c6840400a4102d20000d0f0074012540c00c0d0401c06c40100221208a48800c800e840e00e80c00110300600c102c220700c01d441c186080d0144030f40112441d1080641c0e5031070305a000310445903681401c0081c45965540c101c00c110f64010403031724004c6158a04070102400c030300005c3c00003030f00c1202d0100001e441061114540d0401e09d80045c2010b446200d4100014148a0110380c0c0b4100038100842100c0c0400b0309000301d00c10750394000c10746420300c01200103000207074002c03000c91070401c0020031004500480070302c225001076440b803148001028894050012080024080b5030199000b0001040750003061100040011710034641408282c5a500c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 309147805 1250 309146555 309146561
    0x7020307090e0c0406090b010e06180306040308011806060f0e0301090218041b030c050906040f050405010203090706021b090c04080321180d050d020c010504050d1b030c0213 76
    0xc0340100502d0203000c001c1092002503c1904420121414000e17a6101e0014200340c5103003080007408100d44060403821490018040d208131401c4101400c0758094400c002441c045040c0c2e030071b4001c03c01d0000180803900d4401860380110071580302c00d000c0700345822030007004c030356031010914100301c071400030b8800c1c640c0c0a401204c10f182d001403540c0d01e03e2803000740301944404140c07000c5420b41041c1640150036025820010100e030740012201400c030303203410b0500401420081c5100d43c403541e68854181c504150f40300d0a0302942c05880010303181c1ca0503d80f114031340b50441e0006800c0d9402400303001c4c3d410750164030310040481c080e102c8141c80d840c1c00103003074042d001d560072140341408041400c0c55520351403042c8120a1100d55040d0030542c0b1151101541e031000d50143c1c500c2500696150402540204010700c0c86071403002005180100990500c0c0c21550144c1d81154260440040105281d90021001001b01c0c648050041ca03000580d402500a0782d2205000740184032001000c00e840d0200c4d4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 309149055 1250 309147805 309147809
    0x61b030e04150b0f0901021515010807031103041103010605061602060901030905120310060f020a06050603100f020c100608070e04050a02090f100801201308010e07031a0606070807020307 82
    0x865058031390341155403501d6140c0003403140318014450302c000030340b81900070210180209204000d15503114903000044400d505c00800c003405040d11081518031413028032000f98800d0380100000c00c2181c1a6a040500f5034002d40c0c4154480c0e103041c4401444d03da00301c01d0884500750f0490383c4681d54100e020058001e041c1200740034080d4000c042c3c040300c809110300300031885000c0264030614040d454603802c4d0b444840311080c24005900183c01c4000040b101c2d0f0101c3c0d003021004045804080900e50380e80191001c3d4616090b9950300403031701c620344100070810001d81e05000c000a0115a0500c28080d95403a80c901c50070a8080d00c3c2d10105061110501401c540540c0190044015240c01c120300e8aa016040e82e48030740420b091000004c1406042c070800442203116917044010070940342c0305400d160030242000c0b02c6a06403001c0064070381d009110300c044a41d5020080e280451440c205081c803086c814020040d010b4403c020003071280c0c0c8600480780c407150302500e103513100d004c03d001103440d00e2440e03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 309150305 1250 309149055 309149069
    0x2102003040b0a0501080303040f020d02150a0c062009010f05070f0f0b0a09110d050f0102071b080c01020d030f020903070e06030f010207020901060806010c0606060504061b030e0415 80
    0x10311061160b42d112241c070442c41200140b0150b41e80c0c0d001a640c1388400c4401414000d004c42c00d00e0300528003c2a0105a1400103040380500b4010f20382c504801d510250300000410b00501d07195040195900070b8580e00d0350407001d45205400c464152103010b1280d400d400b41017014403084072100e507029009840da0b198114050386034024072403805042c40f40586405031084668540040d80c2c6004034040d140800c3d500c50317a4080e18240303801c188410103480c10000c465501440817000c81070f001c00d101a0036103901900050124004081c102840d54403140c0200900340c010204200700c50360001034141c0c0040d52454001000ba0035504030340d0003402a059820740c176000307803200020903610100100f40501000c8040c1e54441004c0c002460803072180c214002e4000521b02c004100d41c80c000d2841d5540001d0604104003000000d6071900c0c100e030850317045070b0049000840c003801101e40c0b050302d180c0e0051031060100380100c082e88000e0100495003104030300c910348424a0036029070711828584000c0100b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 309151555 1250 309150305 309150307
    0x3180b0a02010c1106040201140f0c01141b0a050a0f2c01021225111f020607080405060a0506040e0d21021216021507020d030615021020 60
    0x240c240c0080c060100051100002840c40902040400e4085021400703580d050f100c008241c02d00d50365118541d0041c0a004091600510068074050400c1c012400002e1480300b404049281c100ca40d01008000c0800101e0031800c00d000035040c0f207800404445a104e0079040500d03200401c88400c5030950140d00103c0c101900140c10441e109404100c0b0702406802602500c03056540c0f000e00c1042070190000710400d45034581c0d00200c0c080461000c0003207040c01403500f600c8012218006c23690744e40804240740140000c2c01e0300200f9182d410311540d45c21002c3c501e00003210782001d86a20381c2e60703031005c0c040340f040c40c0d0307908081011075a45500c0031820705100c0080d903180056600c00540065645008171950b4003108298125241c0c062007201c00301c00400d501c0594940b6642022941003c030300042100b513200701641484a40b003011455482011a580201001450742000405442f450303403020b540504104d188100305038011420009248010b80300254101c8480c10a0800e00c225803c001c5031144 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 309152805 1250 309151555 309151567
    0x90c120f031e0e01030b042705070b070c05121c0306061b0b1f0f09061508091207080d06060305041a04020105041211040606030b0a0501020a05070303180b 68
    0x4003154015180c240a515440341c001c003841014010301c0d41031544280041c90f00704005800d0740c0a0360041c420035002800000d110025440951501c0c85d5900d400000c107840d03085e4000401a003008110301401c00d151859080490654030818203040c0f5010702842150110003001c40700074204801040c94107005402c1052002401000c2c4c0105030300e009003c002607010440ca032150039024000c4607100d5001c01810300350365540d104c40315050040240800948401c0b200060f0b03107901c003c0e0f008040c00c401500090034600d801030700508800942c105070b040c4803140040103120500031610f0400480760418030380e80c50b00140f401d01101d2140c2460032070041d241100200700c0d640d05074050f5201d03500c070b04101407003541c0c085c080a80b1000d003110000c0c00590204800e20103030b0480c20190000a100d000c080c820604044001415240d407a000000001d03a40d088810852810494080c0141030a00261604d40070076118903803221182d01014050280003441c4011041507801810020701d001b001c0580c82d05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 309154055 1250 309152805 309152813
    0x60b030a0f022809050d120e1908031c0e120d020702090f011401050c0d030b010e0616060f140f071b0f05061b0316020106080a03030501050310020a020d03090c12 71
    0x9a00103c9000554215404545414400740f1403000e90381101001a02442030b01d41264001e0105107101d800c01c00a2030003100d206410211400940390a8021315250604140100c00031402034518581d5981030564048214101244810b203004e503130b10030b20b0340d10890818810081d1080f079000940000407041001901c80309a01420f059824049404258840c0240119841e01420083d410580c008490080e202c42c0a40d11030b15021006060400c035070301c900d0001481c6074121003864000800e0104585007041070a02c124414980d402c00b0401840c007901e2140784044c4c400811010103080343c3d001054546010303009140c1a4103038542e66522002d03039807070540000c20031804100c0300381c4501404038178503101580c2119603104140d0009411981d80b29031003a500031421b506c090a5542c0d4403408101c9850500083c0803803030107900c001c078031949400c0500d8a000c002402182100d8410300c0400b200303660106040c841c4400c41d2a0105201d5140d05241007c400c182c2d00c4100c050014590350760802c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 309155305 1250 309154055 309154117
    0xa0920060f0f03010302040608010221060102150c09091f030209040204060911040810061202010c020d0b0a020901170601052d030a09060c09050901260f010915060b030a0f02 76
    0xa02e10987d014040c00e50b442c514242030b07000d00b004165401036200a035249000700c074252554010014812030318000070403909182003076420343c1c5100040c940080d041c0503500f00b420100307410001100d1000b45070030025504d41407410040c003000744140780e460049015503846030032903006450761000802012440650701c6110b60321910035400705002e481100d903503103400ca10943c0c08840354007451200c20240d030b600440c0c0b440400c210882e800745d260003000001c6024800d000788220200d58006a450b441c0d41d001401000482c28424040700c45e1000300902640c0c00b006403081000400480c40f001c24282a2841c4800100c40400040b508003200f0000c0030b080c43c3e00950107150140f1000c11942e203a4000480d040c02d1a800751b160004a8040108064038819140c0c00151081102680c03101022188590074a1403208100d411350303442e0600c117410701c411495083d0301c503003031903104000c10352601d1010b010b2800b00801c050403059607100b600451820795011039184002d0400c0303504804180820b03201d19 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 309156555 1250 309155305 309155309
    0x30503041e0b0304021e01030e07060f12050417070c080604060c03053312060108060403020f0622020a080109060e240c0a0e0306010305060f0a0920060f0f0301 70
    0x1460305501c0000d290090400b2a80a81e8024000e000e804200c0c50f01c04514030301d055215070405594200c5050442000e01c00c5501520182d551110443c03148003006000c2507445d0551041c5a25202c00d01c00001d21044e401e0341607001030341d00070f515040306003042c0401020076030103c019030040c2020441040120307480b85080e404030f62010851501c0c1c2c0103030b0340459a0160382110b11102036020035140b801001f00c902c10a040c00a003031078000c02c954100340d0300b4902c0030790100303030158062400e220415405008090102c0d0382e0000414407844c0c4158050f625041c0b6001c18810350050245100647d10350061010107462004028061841280b42c404014404c49409400d140140408a0040b422206244c280d202040c1400366158542d00040d1840340e11004c24a0140001032500c1c0c500c9440c03c1c4983d5000b075000e41d029084529007544048031508004040c024140d10303090302c80e000940c0b115151800020305e28066480c2912200115407184609500e0f960814404150042003d900100440c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 309157805 1250 309156555 309156599
    0xa23060609060d240e070c060204050303270d0302300408100b0105090109051306090e06040303050106021f0c091a0703090506120609040c031b06030c140d0e0703050304 74
    0x5080d001224044c1882103003070081040c44403280010440d114414510302c2242d03401240700514051741e07440000d265501c40c11651070201443c03000403408900121200780e03040c1040d265084034803030b240c0d030080d120b240150803586504142e08582050200311418070070f90010f60301901e0b9a035a10791864a0781c803c860021480301c2d608252900120354031030016504900c4040c0c44802103d400c02c020080840100d12400810035507441d40003440c000d05000d1115001c03103001c00b4080a080070308008080c2c440c1600310300c1c10740d48100071807021030007568603001c2342c10702c00000094804641c010458110b021a0b0007241d111103070115060203025418028001d907442502c0c0c20750301664403420f22000303000c0c0600c200924541c1c48c0000d20030782042e90000703a00c98401d407a056900c588956516001c412141c402d05a0f03c610400f0520503280c245c49440c08800d0981424000082d032030309400b070f003440b6510369504029100c003002c2c1501d510800112025560010a41b521103440700403980054401d044250 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 309159055 1250 309157805 309157841
    0x6080c09030d031a0a030c0b16171b010903020703140f0109030905030d02120409090318090207020f040902212409070b031b090a0b120f0a23060609060d 67
    0x3e138031403420b410140304072a400049160b1041c5420b1001c442c81d0054403a02070b1500c515010140010301c51f041221030101905203168980c64103814250060714143e084000c240e2608405101081d0001a00b00850764021580c080032030303001c0703942400c10315082c290381c07003541c24039031240100b642014613031040e102c081c1c040ba0303941079034050103d070b8498440c0e0400d00000030802c0107001c80101c0f5042001f9440c02414410301c5000046650b00c1c103409507031300540324650b01091040451030b000c40000c501c1c6000311802c0c040c0c10703010780009002c208080c50100130070065040c03050031040c0600c51144140e00d02444002c0c6000b00e1340500d8203050b01152603046502039458049007010f11041030700d0240c04210303503800e84003211071400c01c0729501480b10550b2154150314000f403030071070440040049807000d04501c07609080070451840c2e60f06014280b901000d04200040c5c4100682107011390300070081040043d49900c0d1000822620300c108038601d5007140002030003050800361a0410b4041040b801004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 309160305 1250 309159055 309159101
    0x501060602061623070b0a050423060f251808010c1e050d020703020307030908240414060907080f060402060f0a0e1f030b061306080c09030d03 63
    0x142d00d080c04203401c1c500c042880580c44204e4098041000344040e010300140c02e260000c50748400100d51001c9030140e05854480c0200410403040010b284415010590002050003070480d1494850f100200701144c00050940050351401e2032a10001058480014840c06195100c000501c2d0703055200182c048840440300000d00c1900500c9443c10a1000d5030310500d80140000d034074070340700020010b2031042080074011484011414070042c0117540c82500210741c0d40000f4900034040c400d440d40204842c0d0800421039060804902800c48544044688030006544900d00305c010692549507201ea50700c100b2082120800d4002030305002d0743e09032403c640003c43e003840c0c0e490341c0e503030b084400940040007400081f60000491010702000130007420004d020691540100302c0078091102111031910900d40548561a05441940c8030440195106858001c42d04502030144540d44154000c100c21003001804541d400d00560700141001000d07181480710fa24001000384c00c0807046d40c00108100a05 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 309161555 1250 309160305 309160321
    0x40501050901060203041a130f031406010602030a050a030f021209060f040201020a03050726220b1602030703061b0305060d020901030308071403180705010203120f0a06030609050106060206 83
    0x103924101d0f40541d005519050030000035205102d941000c070702030502c0030b002c0d1a500c8070071501000c018200c01c41811100510b107040140c101c107038001c0c8440039030300600c005010084c0d000c01103c2400c10706040c0180d0f541c08211044008008041040f107001d44041413850400d1440100d840c0a4071080c0b044910544403e00250034184059070000d025074030004868001a000e1382c054041180102c1e0200068841c1c0602e480300300c195200801c1d00d1442c00608006014403d0061040250420342c1900465085c24104c24191003a080c40c10005442c0c0381d01c0c0021594200070003001746502501c113100034031040b50450100884c4104c0980403d0428000940f0703820291001214260010301d034030001e0340703180c800380d1350000302030314a07020402d0a8801d80c18200c94500103501a0981c0284482c8090030415040c1c10328071603400860454104100c0300c0c0160b101a03041a401c500d00342c104140036140c4400303080080211ba400100311a040031842001e100c0194030400496106c0d8003550240c2e42ca20724 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 309162805 1250 309161555 309161569
    0x1d01080c10020601050103091e0f060507030c020a060e0c06040906030201080a0b06120703110c03030103050601050a0b0301140102071706090d032d02090a0e07140f0a0f0212030901020904050105 85
    0x81000040c2c3c04040104400c0d8840d130023480e4010b0103520000e91081e00c20502c5840700c0c0c2072200941c2c0003c0c0020003a801c0105900c01c5c6580000607140401480060303036002034441e1603008010303100c240c5880e403019a100082c8210303103042d0401400c25136204e0344e07900c18a0150800d4030080e40440c0215000600c5004076015141c0d0f010001058286041030340d4121041c44078024000707008040d90b5003108030421072400c0c001c1892003011070007152650b2440c9421850407005800c03083c011080c41c401040000d40310750a0b40d0540d03401443c40700c115021000103c5c03a2000a0b401010704140821750407060b10004140340b8040e40d03040c410fa03526a41c8544c0305809580c141051800c0303c0108651580280c095080104907401c0800d00140ca400820000104080e8031a00582100b002580c240400c0541110f900004d850580900724202071803409140c5481c05030800c24410710000c44107119205109110f41440c403254680040d03124204180500c0c000e401056140d4011840d00c0000701d5a860498 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 309164055 1250 309162805 309162829
    0xe19050f390a06030c020f06150415050319060e19060e0c0a0b0904140421030c0f0c080c0a0521070506070509060c06070305040218070903020909071d01080c 69
    0x3620810120786800000c5004020201039a02140204007c410060300705124003802100404003003031212005000300412a0700e4899280780e0302031500c004105640340403e440c000d031501d0740183c0d11b2600d071501713010010742142480141d050058018500c1440079074400205020b000c0ca00801440250400b415074440c01c000751581d00c05080070080000001500003808800009000801d1514607048a407002d680251001c03200d040c15004c400c0e604002c1003103000810005840d0a200c203117120100a03042c681c5a120b030904002c1c41500030424840070104480a4034403d800b281ca020030305003411500c9135100e40350714194184c68044801c0400c02d180545000641000c06000070351564101585d40d580603195090300b007001404618418070041c04201e21524203514042142e07d050310401c6070301420b202c6460140f0200c40148076020f40c0c0070f0842d50035264180c901060300d440c1e04102d07030328000c200c1d40000d0f541030701440c204178105020018039049446900032a4028411070040140340c1d0406 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 309165305 1250 309164055 309164059
    0x3031e0e090c13080102040306020703031104030b0609060a120308061005040e010902030a06080a0b0417040b1815131502010e030f0d0f0c020102120105040e19050f39 73
    0x224011640b90081e4000401c0b400400310100442507656010039030a91300650720640c4d00700c0e4081049401e050b0540180200310301c68452580c0344c2410360b603951400360b03c050401d40c028902000000c030f55071165500c5601528250503886500512403400910100c000c03100540682c0000703504141c0e03580104141e500b501c4d0280c03402282c580c00c011280c4001e400081c0507000d42c9444101c00541d0f610248800840580070341c024464030710b010b003442000301c014805101c040c0c480c200170400040809a069034410004040080e0b0454600800107a07018100039040e2180780c2c0014486070490310406105003110f0703865961400c0c52200d10703c01e0b0b007294184062070704650010000f0a00c503c100600824038402c803218002001541a130456040302c40c2c681c080e001603940015090210820200700ca030051500301d40500c055003800041c5a1944010b040600c10b0003c0c1501503801c111007170108868514010049482c81d45603080a215426a0001e8010511380030008841ca1400d001c02508604480 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 309166555 1250 309165305 309165319
    0x10050c0703030b031c090e061504031b03150903140f120417040603020405030f011b0e041808190201061409070c060c180e010f03031b06020403031e0e 66
    0xc640701500500403c408466250050010301c0d140001d004403c1d40c2040803954030340c0242c1d03040c18850100848060072541c8a9542001c00718915640c440481c0d0503260301034001d040c40301215584d1105020a80c000401c0c0c1a141002c02c0041c200c10b502c0740e0100c600a58612043d0b090341007400c0c00d18800c00c881d40760f4213081003119600c8410790b83c4040350420300c01e030b070320070126620a140600d00ba04680c110744002500002e00f0041407608121250000c5540c900800ca0040101c14014003004507455036418400d00a5003040e0fa0340d03403640310b50b880782c14046401904146030324205070f05070b00c0450490030450010010f10b94041c41445942300755511201c0310141504c0127000c0059106004090000304540d1450a500060b402c2c019100000c0c515210300100300c03003001c09035a5100e85038010003410f4050038010072414180c110404100c03a01401d004c1090358200f03519001c820300140001d0a5180001400009c15601025005081a000120000b0801840800c45054000c1c50000e90301c00e07a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 309167805 1250 309166555 309166567
    0xc010e03130905010b070f0c0e040308041403030907181503050f01050c030c0a030b040902061b0c01020a0510020d02040f060503060411070f02040519060b0c150601090b09030109020d110310050c 85
    0x16215a80d80a07c41c001d00d6a04400c0c0d60791551a10402003c683c00c0300054610020b1000b0403c0d410f40c0c020710305840c00f01850451a0440807140d56143c0c0f4400d43c619072540d94014802800306038440050221150180b0796180e0f203a080140e0b0b1703001c0024515910750302c0d000000b05009880415031703000e161031070003591924010030780c00c5000e1321590103141d5101e6074480740000160f84120051007840110110100e4028914010500f04854050b0141c1035412003943c0c40001703140410070181d116002d860040c1c48100294a40d0300900540c0c20130034507040704a5001c0780c42c64000003e144151000c07a0203001c0001c54200c03045190141c10070080003420805440b40040c9015000b49a0241c68808035810003410000d6420965031294841d444403100000c400d43e00710000d00101000c0c0c07100c80080c42850411500080c6066240d100c1e003c101c1801042404182d642034002d0681107070010002e00c1d0b000417605111040044c4900610b1081c455a01c044400403114060544201c00b41494181408 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 309169055 1250 309167805 309167813
    0x106080603070e07021624080606070318080d0206090c040903080408031806100311030601080c060a0201110a092408130c080304032102060105100f02030c010e03130905010b07 77
    0x4240500a4001d40c042c4041e11b403481c610441800d0001e202d0b051004400c0c81c40942d207180b41c03800c1030280e074082140d03120800c85940c8410088902c12a410300c0c003900c89021600c42c10851100b20f402141050140c110305414260780010380600411081042d82c09602091003007108440c03000500034045404100010082001400030b154401c600c00180c80f10320102200303040c240801100c0c080f080d002c0680090007071021800141040300f00c00d500804c0e003135040c075410070b036030304064800c1b14410240000c105104500c01e411401500d8400031000c1c1d1107412401d0082d1522105002e42c0031121446201c034520b40784883c2102d2003c40164070344c030300c086e00c403010014020381c40e280c415a0b00c11141c2a0000344071608100500003140600d000180c0e282d001c1c0c8807200c070030f41e0b8218082d003154401c00c0140000c0d581d0942114030144142043c1e4110007540b18107a066000d010a0480366500c1c00018081d1400084002c01c240740d81c07102156400707030f1103c540500b159001e016010382c0060902a40e4009 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 309170305 1250 309169055 309169079
    0xe010603020a020102190206150d020f151b06182a01021905010504140a122613050706110c040209010c0f060e060f07020604020d0201180e040506010608060307 70
    0x70b840d68400503180122804a1600310414640f9110040c1c1c8140c040121038069520080d0192800f2500200c40904540010f0039030300031260b0340d51282d108550364045001d5000c0440d409000308810134003030040300c20800e03600c6001c1103034110303c1c3d0204000320481c0c0f0780c0b001c25403607104e55410300d010342c29011100d50a40d458040c60a041e06510580c0c2c5100d11a144e00000300034018820b500204d4140761914115104080b000034144159000f00d24010004000032889500243c0c1d51814000d011800d070030556074404202600f80c0106044410301402007411208986171501510807074001c156504011201c080c803403003d151103074000300d03002980c0d454213400420900d44140341c810040b0200381c644010381045051704945150713945071741c041008818000181e009042180c45145494014000703901c070708000704000e220708026212002107a0161411410000040c4062450f035074480c0c41e02c44a1441c00c0c0c40c1600c0701c0c840d03c000010801c0c450509544200e60140c042c04d011450043d143c0d0341 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 309171555 1250 309170305 309170317
    0x10030c02061b0409020f0301090612020a0e0403030603150902030d0e0a0b0d0e0706120b01021606110f0d0246050705040f0219020c1c06020f070b0105190e01060302 72
    0x6520390400001800444c280041d0004510709400156654503098480b0101c4030075501035402900c5241101c0d0140c0e855006807001c80381000c643c440e17296500d1804400903c00d5070801030590150500c4420b2102e4140d100d07010588c42a01142c10380d81e00e941041c0c07000c1c142208160341c0901c54410600c42141e4100141c60305082c100e0b0042002050206d200b801c0c0b120503007150002507500d807010f00025556005244200c2000e0000e01207130003100b4801c0c01013101e04e001c0e10303017071050f449001410344038200003500c001e4001780251107011101700740c001c1d00d40c41042d5414404d41150321844400020070031420b03854500b0660000401001c01c940401c0300b9000840668503070142003030010f855120742c00b5a8100300614070780140c0d1090b1098005040415400a902c21980700d039071014815101e21010f00e41d0b004c107030030030310541070315a182c007070080e214240040860000100b8580d04014070001c0e46810b0b201700b2900300504a50020302c81003682d11a20031420380804440040040600990003048 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 309172661 1106 309171555 309171601
    0xf0b070504080706080601050c01140a060b0909040210090801090b060a21110f0301090809180915040f08070f0303060b041206020901050405120c10030c0206 69
    0xf0342d4684078001c02c4140481d40307011030702c2e582c054025995416180802407119050b0348156032501d040c183c807801d070b1040c102a8049211003000080c0c907001d010241104190350b031203400f005590301c10808000140140d43d600825641c0e028000c038401c0501a401c1c1c41d110741055020701010101e41d50100301e820400c503005140c0c410340d0701d8900c00340b25000f400b000604000e4500180c1558401c180c00350b07041d03280c103070f45208201c601c002a100c4228210b40e41c14001406c0407140420020444164034580c20030340d40001c2c0c000d00804110307040313070068600084009041e42c13160702d0303540401c0080c1c40a10704400c600c0304065040c0a240050981007540c9410030b8074020024a0410143c0c1d0002c007030a03008206c401031030348228156001418028941d40c2e40380b09518020b5228000418424010b8203034241c1003034154060302802000414650080902d03076600e024503d103100c04855540c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 308992805 309172661 := by
  have h0 := BRFrame.cov_init 308992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 308992805 ≤ n) (h2 : n < 309172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
