-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3842
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:50:08.597996+00:00
-- url     : https://prove2.me/submissions/7e709d90-bd69-476a-b9fb-2b59e33f90d7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 690827338 ≤ n < 691007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 690828588 1250 690827338 690827363
    0x140d0c230a021c0515010b070b0402130e06070905091015020a0b0c0405010801120c09020a1206080615030d0e060f0d2c07080703060207021c0308160c08070311030d0608010207 77
    0x118085c1c86a428882e0041c9400200b24880104000c5000760381c12520042c40845643c90004400003a01c030140352000413a0460f07418400b01c10b400100030401001c0c25540311b02540703015264040030034518850740100082114003841c182d4401d0200c01c0001c2d61001c00c891540c20000100d82854000d401050b021551940000c10018882000740031801e500c100508050b504107142440070390440f0820f803041c072650300304010a1211502845002d00200c0300105003c0c907100b4103400c100050281c42074043e0300f040d140e000c00113500c0100d403804900250b0700140d0390b40400c11032171300b2403080e10b4440c03c415140c19200b4485481042d804140400c210104608860348005802e0300d07500d19104502166001300c004100042113500680300050000300b40700c110407018500245070181383d01040740000e03503420801060b084401034000442402e8644032a418405549800e40c9105505010b07050140429900d015000104200c5000300b01c1e000381880015a94400c86010b50050f22044401503007005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 690829838 1250 690828588 690828613
    0x70906140319020913021206040b0a060311210403120e0c010809100509030d050a1b11010e010e0a060501140a0b0a020f0703140d0c230a021c05 63
    0x4100c03000c40601100400c1c80d64403120030007440c0c0380303402200300d4480d03409200a2007180c0d40e00110610101c6480e801507a0b541810440c1b0b640814003c0ca070600c16454520719201d6134075a82490b0b819035441c5d050000d090b40107a5078418203030080e02c5204aa0580d6140e0354400c0603041200d00d4019442912003002c1203080e903d07c0c8060343c003008110001e903840101440305543c403036042c0507002403240d811346112014109010090710000ca400302c0c050783c000500741d580c500c2c59104035175000f0799054040141c101418101c42c4440210a0319104003c003110f2045490042035100400c0c2050307160081241544042800d0f44800c03400c00b0503503229141c40300001d41d110654121000189004040c01c194904007040740c00302d40c2240000700214410849540717408441001014043c1d405a0f4a40a210760b8910442d480c0c10030f032250305010895851101400204900c01c070310020401d004048043c0f0b042e1800540c688070949402a40c407540c5000d6540d0320300070003a003035045107001d4015a500c102089 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 690831088 1250 690829838 690829847
    0x180f030a0e060f30091209150c01020712090f060c0b0c13080601080d030b18271c2613050a29040b1f05220f0c080f041406090303070906 60
    0x600b0300f41c2c0700e000c0c108a01107072494204c023000312001500500c242401c000031009400c980020700110740d0312203800d1602c4801d540020a0341c00900900c07140ea004c040c10110300409503000e000b002091552842c0c0441c45001105003504c07050592903150000e031039903503c8030541d0b5240078410300c1b019000d2040740359901c52085c0039842002401400c084064800c031400b240301c00c000105416070280c010741c46088404900c0c5400e800e5071900c6001002142841c520340c000c8401c0d01003000003444041e080c2c0444985245106541400d19440305500c159200d2401ca080011940c1d0004e16900580e0001003c110412200300e088400a8640580000d100303030b44114101c41c150ba000d061554610700003050091504400b090f000410115890840c0c2c2e542c000c20300e4022140c0512842981200d080c154408141c8039090701860300144c2803080c51342d41c100c041d156400190903c4200320b002d200280030b1010b001c80300480c034803240c011981c2c0ea241415090703450b900152040390016140c40000102240f0a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 690832338 1250 690831088 690831103
    0x6120319090321091707120201030b090a0603031418150c010216060b1206010b090f04060e0f1f09020c010b1008100b071203020307020c09180f030a0e060f3009 70
    0x800020902c1c2030900c7e40d2071030600011403040b030405484e040440700c41e1300d034001200d001e05003d00e00803032102d0030b40c940035190b05a503044600e084402401841d4040c01c88101d00710707074048140c034039002d00c3c00c450005018074070450b0551000b5600000e1002e02c0ca42c40403808130308a900070307034040140407040c100700010450001204619640301c074005004201003000208000d801c01007403200041900008203056800e50352000b89e9442c2e051040040c040050342020b07a01411200c01039400b151100d00c015020086801034440b0f191340410382c0c1288100941c00780704c1c1900700900c200c0644c10320700c20003014002d04988011100e88800b400058921000080d20381c110390000005480c485507800803002900700810090031031041c03000742d14680c0c90300010783d4000c2c42004640d03401e0240c4e01071124540b2001c0115880c959008120444003e94000d400c3d020f28101112420f50310046003050380201e003e001a200c800303134403008440009124484100c04000e43c0d62015180581c3e81c410380301e4440c0e45 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 690833588 1250 690832338 690832379
    0x15281409010e130209100305060a270206040308040e040212060106020304060c080d0617010b01110a02090c0c010c030b01030c0305150402090409051e01050612031909032109 76
    0x4424018071020302e20b08050755100a800348124920040e40c0c0015031001d405541d03013040914070000500c140b24050042ca42e0007070040005000110302c0da2005e81d0034443e00031050100522032100f400441d0303200801c42e0011604004120b0302d40d81c4503201404411401d40c2c040744100300d4070f0741803a00c140c0d0103e19981280d034a0340156003007a00e0b05030706440002584000302c661100802c410311140d14076224810160000e040201816040c9031201ca085800c0342c0b104505010744000d180c0e100c0760001032a0310550350705542c1d448442d2aa219a000c2500500780c3e01c28040d42000c23101d150140d8598007100011000b40d801303201090001d001a422a107098070b627204000608826a02542496001060740c01d80c0030300000742d41007182d01c4040c10441c600703403880000c000b12001d807039501ca02406002d03000300b812590b207107034108807002050750707442103495494106819866000b1054054000d00d0b0007941c225224032100c4200d2056030381800c1c1c2401c0f40c040841c141c003002003112610311901218401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 690834838 1250 690833588 690833599
    0x7020706081906030f06060509090102090609040f0e06090a1a151021020c1038221109060a0c0609060e160801090206040509152814 58
    0x2c450050040c070b8031a40c01d00785071040391905000000101c604802e922200d000d0800018114181410451114006000c00b0800e0b80144255842ea80c0d8034003c861703010900f220b0028003417002c0c0c0d4855001c2c1049081e4005240591020001803010100321000c959219000c003140b1003c90399983d508010081d550444656000a070703030010f03800e100b80c003c0406111418680007400203054500d014840f00085034124607004506480001c80802c04816418102603041c4083c1c00300c081c7c0760500b5164091040d0020400e107500032501c1e141491040200f00c80034011206504041525081900c01c50a01c0420344c1e1820801c00140000c010030381d018240c00400340703480d0801d412400c039405041d40034151801503550f8207040000b80c0304d102d03c030038a408c40c07005400c5910041c190341c103148000d1360001041d6414100d9090040e50741104072400e4803011249a0f46945a40c02c80109150902000e103401c1148222800c001c020129040200d0220710668920610348440e1603204190030104642d4204 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 690836088 1250 690834838 690834841
    0xf0a3b0709030b1b2a0606030c0d0609020406090c081303090611100c090e010f0302090a2304080c19080f0906221404021603050901170f0106080702070608 68
    0x28152880f0302d800060080000d180c65007070006038440341d03010741d44c10120740c10503003102840040b01c00e401040902c00e0202924440c078104012036102c5e103202000a208401c280418410024103a002d0314010760082d1003003021503143c0100100030002c0c0c0c2d03107980124180784001890104003001895440758142e540d4200c2e60316000b42900e40386000300c40c81c2c841d400703009040440c2c00824424150f03c1100340d074034015030078901b01f01c511a031070068010554585401b0014000761701c9100b032158100c400c103180055603041c0b2465090f854401e1803030415612240a0a01c428490700d5006001d030f0200f04019207050320510340c000c01c0c0741440450010540002801000d61041240c0043c0094a00250002d0310308000b1510000000c091141c250401042000c0705000c00101c28501801c960400d480461400c02040c0c815070016071842002002c00c400010003801691007041c2091031008404080c82890611190140600740240240d1300003889803c0040c104510000e201d204503500c40d218903516 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 690837338 1250 690836088 690836093
    0x5010e0a03050f1629090d060e030306010f0503090327030a14100204031703070c0b011805070807020c040e01060b270603070c030c0206041502011d0c0604050f0a3b070903 75
    0x102d800400080364000b88a0f40b1401c00716030240104a0127801441c050f5030b4900e049170015081620403152402000300900421100f600000219101c5e801d0010079007503440071000071441c0110500300300507014090340c4d103032500f0003002410b0740c0000301912042d120071301310914100f0103e02881c0300103055062001e10000d8140364110046410062501d4804100d48580d00c0b00c8800178000c0c2d020b00d0030184680c4411440301a0b80c031070180c0103080c03450540315a080090b4020742d2801c111401d1803042e5031341e8400c680c0c00042548041c0007845054a410707240c1010740750119030355000c4089001c0705c000c0d500c4460790340c0c9440000c4038400d0300c80c0d480f03124810f2496103080b100c1910888040b078002008110110382d04014100b22089010240d0010a607100c030b0b42c24515142c0c01c1c0c00342074800d03507002c17100304110307507032070109560a880e4161002203000b080030000680400c0c0aa00004140c5150803d4407250411920483e448407040b0010303502061894504402e00391040b00c40100103070040c03006000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 690838588 1250 690837338 690837419
    0xd090b07020d0506090615010e01090527150a12170c0316060606110a02031b0102010f06030c03021c0203030702040207050f1507020709020301030c05010e0a03050f16 73
    0x24581d0001d42440410b6815541c1e183c03406100780c0b0810007545c040c80030443d201021856003520b0450078a0100c04590800d00044c20100300c80c000e90344104c0d0415031030f45e02d000e9074281202c4a04414031400e607090a1000d150061034088001c014050a50408089a440c03696014019030b02d03880540c0e00c041c0c3c403e8440d021400d800c00d00c01c500c0c3c140020000216041d0b24a0040c83d48540140c100240c100d2030900054140080e8010103411604482c0c400009a5400320750f1400b21003071079002e0480303004d0300c0340100d00600000c1240b80c245440c0450101c00d1040c030701150b000341c80c4240c030b40d19080103504c3d5250400104111000f503041d8070800c0008010705081d0043e040c4180700b54121100824a05850750618000001d1212980d0280040003c1c075075040086100610034050214555415a119046648201d02425051183c0c6003030010598640b040c04000543d080303020380b200030390504d07901e54481c00c000c0080324020030381c03d0b008035071240000301080031890070020180308641550102c1e01d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 690839838 1250 690838588 690838597
    0xe1203070f031e0c0909090606050901063905031314060705070918021e01080a181709060c0c0306061e0112020d0e070302040f0204120b1003080f07020109080d090b 72
    0x10130007592540002c3c06c0d01c103034050144194417416005c2610b904160038860003441c141c0c03204081008088c4400068110400c8609084a095030b060b00da403c0700c1c40d1101d03c0321a614400600301d20000075030440320000d030052102683c4d0340c000c6a05500440a040200502480743d002d05a50040d000410051013180d20030703400028040000e0111500c5600010b0b521060101520089503c551003a0310781e6910203040c40e80452448130400515840d465050303142c01000340c004000f1121000501c01d050384d18000d80303000c0c1400400d8640e50744002e042e102c0c0c9a81e03c80c00c0c07450007803058a0110b100ca19100a0000e201d03074401044d0700389107502500456201617941d0100103c00e6007040007800451843c01003a48042c840300003002c0e0a859441404101c0b2941c40c2d4007032007544107001c103002d1402c0078110020140d0300a140e03044152100b07112005407000a91000b450303a03400040401d07800c1501400352250304e000349c0310540095aa040c0680d00d43c800c1c80071400019501500a0090380d07102009003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 690841088 1250 690839838 690839861
    0x150602010905062a0d020d06150507020f1302070f1b0501210b0a0803040303080f04120804060b0a0f1503060605090103020c150721020c03030a0b040e1203070f031e 72
    0x101300310000d00c0c08111881e84440040e0180d980c001400403480070050081c1c0005286e2403204031000044820006c101e4050b603d4028800c0d03020451044403a40c501003075a04c9946056070455685400740f800e644a640d011070221807203a0400e11000c00c2c01da50311018011501c1c1030711110164085d070010580c502d511450082059030355270b030382001a511882500e00141981c0b200450340e40d03045083c00703840080b0003044002c650032804e08010000311141c0380d0904480c03060900440507141d500d0010098260103040e40d4012540a5000070b4030f0f41026481c034100e802c4078691080c00b001d0300b00110241c514074000d41c004a4000c00510019503c02e900420204170706078140d83e0005002103084084c1e036403c1d20686c001030410210100200311140100d03600040d0f080046290031a00c05a160302e90000a0410ba10a42d81d800c0d200c54940ba9600404680250f24040e241da51284404905d00e5800507140c9200068480c074043c100d460180c03040d2030204030f55543c1d118080303a4001003a07000c2c01c1d005c0c104 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 690842338 1250 690841088 690841141
    0x40207032304061b080405012f01060e0a02030f070e1c08040e160909020d270302061311100302071211012003070e1c050115060201090506 61
    0x10300300150464541d52985020545859540c9281c4a030003404039241d42841d4212409030000ca10000c1e40d8203085504440342800c000205080d14010a0f0140010820040501c124200b145031591700c10340c004020b4401c0f503000404240c8030480400200d0000b100d04980d00c000b000e0108401c5402a022094001001031070b039000307900d507200c99481030f50302d0210499041d070000c0740c103006c2124a61040c036400404d9010b8800410705101008100c3c0b03070789104d0210410b42c002050380c000700d51508051a100d00141d01000248510b6505408010280c50250011b0090340003050100b031540d80c1c0d000540da0070289440d1124050b10401c1041d102000d505414103a0030020000060008204040c000c1801e8840c0b91030715191100d95070a40310b0a2202ca40c69490040c400004d011007441500c0e040703401d80c41c0944003116518007269106020004160b13030962200803810070040150000e0300b04c210041601d00090769540002e03800d8848842c0010120341102e00010414450081d023002c412000400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 690843588 1250 690842338 690842357
    0x20108040605150303160c060203070b040602031b0403030c0c09063506070f140703050d02210c040504110901020706050703030b0d0f0501240b0906071a090601090506010e04020703 79
    0xb81c6141c0c000c2c007850346030074002e1201d082484402c1d50141f00410716070002e1450503e49030389591034108c00402c01001c0d9640880880c0360280507a03068074983c034032986c41582c2e45403241005001600f003548121100140d42d10042050b110b140038a9040342c20040b01d10b1082030320110316807140c3d07000c4a03501c07400840b21000c20000031000c01005014810a45032644114401080103254030320002d91148240d00030000240001da21500b1100d8070400c501005844113400c660018400d5a888140d42442e01c0c502e05000642a1090091003202c004803001c101e549840b0141c81024040d800c0d84601517005900308216942c001c00040c0042c030b11a103400160340c0e40220016440f507007003030302c2529681580c08110003007003401d10403036164401246120360780341e005103828005080c080c041c104581034040f61090160711480709840c212a484150310541540d402c15040ca9082c003154011134600c5800c000250b161860320855000e1007040e940c40581c1c1c0404030603c4040c0d4440c5404508007c1d0081 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 690844838 1250 690843588 690843631
    0x23030d110904060f080f0a0804140d02040e06150a0f091104080d030902040b18072006090f01290919140601030f0b031009060b1519050304020108040605 67
    0x203d01405842c00401c640c034664108005146880b40441156100da0702035400d107004183d094050340c04a84111989a103100d12050100301d11134850040250820b00b4543d40910343c0b03101240040c4108410780c18609042256010000302003124030502c4100054a101444000040d810040c2c040c401d0001c6940b4040d6554819071402c0f024103075000009540d814078400b145054042c4000b0741e0012207003020080d07141112103010302c802814107414040c03000100c00e200c07226680c60703200c80741c46101a00d0b0503251004003a40c440c1d014150f881c0c0203520300032203921951000107050443c002030f41014020394400d4400c2c05642170018002c01940620101d80c141199164018034040070060b405036203450900a00240a98030b1840b40c001c4107606284130801355403070001d400300403040d508070b001c00c500e80b66040204c000d150141031650007800200c1c22041c811509001450000ca24040e40c07500c1400a00c4e044406c1e01050324003d0001c0c6c184800703c2c3c0030641a400c81900075440c40101c0c0381207000107 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 690846088 1250 690844838 690844841
    0xb0a15060c03080a02070b07030b13020408060412020304081504053d06290d0e0607081e04060c21090c08010e0616110a0303050423030d110904 63
    0xe5000034006058401031500300b5501035030880c0c010001e80425401d20321503507656190444003c19000400d55030b0310040321941c0d641214400e07188040d0340700b10366a82d00c40341d8041e10341074101c40c1501c422880342501c01c1042d05c0042141c0480d11f200000d00361400c41141c80300024a0090000d1f030315407007a141031a402880e20b15a0b104040700200c00a80550410b86944c10444600e070744c011030b10341c6444001c02401c0003207202c000184a00000c0810555a43c0740150690b01a8104030b44044d49441500800d4800010321240074540302d0f03d803500780ba07a86030008043e0703c190f400c0e40c0900c52107010224001030b07044d030804002d00d0901d04200035000f01460600300010810780729201100d45404c000c1080c400c122074007501806030034000b84203c02c511104a03950706405040d03800d40d01448004100580c0c07050068907034039074907001074a0005280707040050203044180c80036904260501005a6000c044480f000110110340c030141d401c0c150ba80c0c03200c1c4001d0841c0c0104095048080043c1b90706039489 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 690847338 1250 690846088 690846131
    0x303320309100b0303041503020f070c0e0f1e060d06110a1404080d20030c0a1e11060d200d0501060801060e04020901030f022802070608040b0a 63
    0x203a2645022403030145020154404054400e182800860950724040104c90a03200d000382e10742052006043d04a000341716100f504c6030003200200d4120108800803001c1c1049610308448500c1c55180c404a8040903c010344d0395218070011007c02c08001d0355104031441d0b003c20700900c0c283c00440d032790700c40c240bd0f5050b1000e510386d60304000820790a1980c0210328a510300c0442405603003002d042800d881c1c0d44424003481c00c7d061040c8103842d01940d48204101e81000c400c3c68041d6919080022041555410450b500300d44002c184040d070900d01d0881c1c01086600341d0031000445c0c0c0e4802c80f4061000755488091100742c0b803500c5003886612a4640b610241800700c0140c03500313940e05184842e071821254180c11210030000004010043e041d4440e0800a4000081b0390043c1d5548d507a80c0181c000b400820841800b80303001080402d4550002c80980c00c1030003d140c10000c02080800e401c0340c0319811401404d01040042d800320340030510145096074031401d190000101414451030085a0004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 690848588 1250 690847338 690847427
    0xf0111030a090e0106090806010b030c040803130501120c0c141c1e0809070b0a031407052a101503020a03120207050906010e0d0303141003030e1206010303 68
    0x1144040108030f8181c0c00300c2d40105075a141086c48a4100b000752500c40c40d041c4140b10785107102001240300d40c103000702120028095003045135501c118140e1700c2d520500b070034403c15000c281c01d80301c0342c1142003060017403048403400340d9661006420940c3e590310100380002511081c0e803080103006084103010f440c8007aa0f01032030b0748070381e142ca040c140c00e00305444807a045500c080014800c280b01403010001100d01c00d603808445429101d0519440440c000c0450407106004001404140084260860003d180d0800303011440310b90140ba022500d400c0e841101418034181d4850a00040e1500c166400945e0303e201e8207031289a81a0780f5000611a0071241e0420b50b910043e00000300b0505404100c1e0304002c06064410b000b591914900107815035120118181c001c00d1141803140c10144603030b01800c08103a903038906214505100c00d0442c800400c07800110003090035082c0d0041c0c10301d8501044184c28541c04c001b0442a8250340c2e04071012450981c90007102090500d00529418402108640045 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 690849838 1250 690848588 690848597
    0x1803031d060705220e0c0d02120a0b040f09080a050c07170c0111060121050309041a15040e06220207080310440118120810050f0111030a 60
    0x100404a01c0309491490740c0001401c4c01000410130300300c00240083e80a1100028252990510180c10300030b807188840c000e500c0a101e00400c504101076a1101c05603000940d410000d981c0d902c40002c040b50210100500000403e2082500d040e1007100103100d8030415a0544042c0c0765100d00c8048078241c000c01c124030a410160030080c6650380051120b0706070750b11000900b1107514040510f03d07450404006014a4411088906c06004041049a100c01b0000e4000c11041c1918002104645040e4404510850036103480052001d0071206940075580c01c0903100c402d68660200304002869080b61202c4503084004520642c20794502c00340c400103000c1c01040d41e0703138585883e0000ca001c590b03030020b80b4980e02d01e61218015019500001180d05040c8041d02d0410f030104043c45c8500c2010011400c480d800c1c0204e211518800c14010100715104005101c0c058440002c299a03c2d0381c00c4500041a60103100d04101d1803900c4800c1c1e6030000018141942041040703000641144e00442c006408107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 690851088 1250 690849838 690849847
    0x2070512070e09060412030c1115091209010914120a0602090901120b070c02010201180501020c0c030c13021608160506010b0a023004030c0f06031803031d060705 71
    0x414041120b140d02400c09005042145490350360300b00b00c0c02c0200b0300c40040540e102402519280106250403040d442d0100f25184803100d010300314012607049442016030301401403414604602d0600f80c52150703405031035403540c407428003107038400c1498041c02240e840a01d6101040341c42e0300034009545001d0040c0809682d03803000740140030307442c0010780c08911441d40200440380424103624106400842916184000e5889800101e001d000340e03c00401d0b81c908919604410042c0560080c118400100e0035510b083c1c100b2810103403120741500140303412001c818000e24080c0c19503801801c100150921103894a20161035008032500954003080a451130720f002c180a01008105d02c50043c0f0000e00304c0c901c0c1040c840e45c0251148011174811250001d0b050113a091700c00860890040c210840c04071546480c0d0701e04003600104000d104505600c5111800072810f14441d02403119003211219110f103001500780d800701c0003068640901e800c0c0c454a6840592200018002c2e00d002c0c83c1c46540b10f5456 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 690852338 1250 690851088 690851099
    0x91a0f0c030304031d101d10021501050a080d0f090803030c091801141306080d021e0610151101060e01090606030212010e071b030f08090f1c0207051207 67
    0x80c2e007400c0d442c000084884178001070265036054104058a006403910401c0c88481004240300d0712854180294800c0400c4e40301448541e001600b80b00407006018100131690ba00c20520607410480e00504005412500280040c14000c100e1034a800995141400005a444500c1c90454009540a41c02540c0000d0711042d58645402c0303034210301030a100401c2007540b400941c00707032101003031a4540c0139030985180000c0407d030ba5072000c80100b41010580d00442280f98009486015135201444d100d2014541c02041c0100000d00501c01c4100400781c0000300e003020f038901511400303490070304100403854002e044880f1003801342100070100c10340c8951640d41031208100c1580e503150856401c251040c401c48645100740d0340707024110341c4c5d50404c203621b548921000700c800b0000402100380a83d1480a25030406074032002c550350800143d030f00c1c000151142240d80b03468204411005513140d0002040700300107451140e4501001555004980303a05a490380402c40c403d040c941c3c0c1500790381103010100003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 690853588 1250 690852338 690852347
    0x305071b0303090e27010608060a020d06151202030a090213050712180206030a0914060105031009050a14030c010603052803050307050f0403020d0f2001091a0f0c03030403 75
    0x140514107407245045c40c01c443c484104850071904480e80a800b401c9021101c4029440040903040750825601d4518207140c0c280065031110200c40d1086107004400141c0b007460701f017042e02c40e2640380e4030001c0310b01120f030200029420152001101550f038940c42030041c1c0c0c405482d1600d80480c5e19011131f807890311a0001d02034500c00715496803800d05110304180d54100c510100102654101d90b440d4507512060301c002c0c0103142c0f84200a0040c0201e0700320b0000e600340054698100d0b00c00320101da25042481e0b6201e003d07101070f2100208176a000002d40400194245c43d00501c403010352040740c1c14040c04030481825200b082d801501c007a08800c030b0700d0328220b0402c0c4411504002140d40203070000c5880d80c0040061200428000400c08007061700b103c404260011200215002000180c41c0c65650400c02c07500c0008003400c4440304030750b03070304140011408020f800c1d0741c61b0161a8046241e24000c10800894111a0211200c07803041059030032410f205005407100c80d541d58000c43c1c613481c19140140 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 690854838 1250 690853588 690853607
    0xc120f02030d11101505040e1c0e0105030c0c0f0d0314090a08041806091118010c0b06060d020708030901090b0106030e030a0e010c1a1e041502070305071b0303 70
    0x4200c01c0340d5102e000881c00107204c0007031200440c000180d410413140860591034164001d654404c2c1048450703900308a0005005d000b95840c10490000c403083d04005440c21443c1e0000e440c04a141131002440d10241d2002801d4850500c80649203500481c88940c0c0c101958460b40e040070a1380d4204135920b00c0102c03102154000b403031000504004070142c441d01d00d07500480c403502c0200d8844044914481980350803000082c4084030040c8403a0b9012140072010340c102e44d01d10401e595514013a0030403507200c2d00c0d07070a11040e0000200103031610341d00107001d80360b4040305904509076003c2100c00700162604006520401c8401c0000403107692510b00301d1081c44040c1e22001c00c260078000000c0d003404004c011203002c0519410a901d010003018016901070a41000140c40306004451030310068111101c142d00c0391000042e030040c840c04e0000d08603480c50040d00e000c2c1107009449070b09080c10000d6401820428000d0030803a08000341c60391101c003158070f5900c6195460032a041d08004140c4c01c0716100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 690856088 1250 690854838 690854863
    0xd201801090302030c0405180307050304031101020105061305060a0512010b04110c07050f0a0e0a05060108010b0c07030f0c0806040f030810030b0402240f1309020f04060c0c120f0203 80
    0x18500107107583c00299480ca071200c0018451580ca002080b140d590310030aa60030f030b10540703056070788038005030400c41d807207130003030b11040d1806101c1944034445984184203180c0f240b000189180c6a0004810b010001020014040e54102c1d015802c0820b86035611409541e951800304000b14284061209200589075002d225507040d00051011a26001010441005440060720401c08644000001a000a03202e900c401c510100940c14002d8030865a0082845143c00381c0350306080f83d0f41c551024046214201d02c058058110440c188002044440040d228500413112410059151102581012801d840480d03202c408140c009080640100103281d002810310380d1002d120b8550b0b1200f49511000600c000d100300d0002d940d42240140078041d40358074861700030740562039038100c3c01480042c1c0d10071702420554511003503001420803040c0c0200e070711000001207081e0401d4607005043c1d0313161040400448400c403031a0000319900b0080981e5160460080800982414460040c0340c1800b40d1026003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 690857338 1250 690856088 690856097
    0x80402060f03150d06020306010e19140a05030d1706090420030f0d0906020f01020a090b0c031c1d0a1e0302070e2701061203050d201801 60
    0x4010240e6540401c0d29140c032035041d0115500c2d41ea001c0015600601d0030314142c0d204c1403024409090200c3d50b070245200f14020389900320765002103010000c90074100100031a8100d81c903041484004844d482c8440d400402034041c102181d00c40000070306010002c10a03200190086050030b000c81e80d44200c031f07500035800b0b40b0040c03420b040549400806018402d100704400b2102c1c03d0710b088a842c00c00030342c10f01c03004500c143c80e80a0607890000b469805244507240c018480c4642c0c8aa92500c107208540081001d42c8403000403900c1c102c10040903821940305014140014030120103444c4000303e0b402400410108000341119440000c40000c901d91620400a5407080d500040020550031200f2480c41d030f040001e060249031850200e00d44400707a007000304000014414050b102c0349030080719400b10441e10b00c1564021072081480e08a803030f03d205001140840c1c6041c207007c280903100825406c010500081441e145500156400c000412160900781d000014000310410704a0841c1c10129002d281 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 690858588 1250 690857338 690857341
    0x1e040501020c010f1209080d0b0405061305060604121109090c030703030e0d2102010c111b010c080c0a06060602070e0a0513020901080a0b0a0501080d03091b180c08 72
    0xd50b5680e80d02035003810700a0b4180e800e584a0b025980ba900c00e440c0085013070112030424940081d003034020364600d02450b030800070000030506d0140509807240c0c1c40901414801001c080d4501c002d4000036241e1600720f1030420002c1003a411030290148041d01440040c030780b2484140900554010041030801182c21103405241c043d5404100301c001c80341c00d4682251401c40f07076000694100c000762070042502c5035115221031111012804000440116002001010161142642c80600200468032550007802c058480851440e402546003401898035413002981651050740350783c0100b00000659100d81c00030801c004041c0a098064203031440945041031a0903005400c1e640c0144c0f8260301c031521080040c041c3c480d54500303e08482e400a01413051940e40f0001245c9030700500a041c0c43c400d420b503000581688950050324101c81e6204000c05150118180807801060308001c101c1d01070918000c00c1083c10304001540c80900008100c5401611821000c071041320304120248003404040760 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 690859838 1250 690858588 690858599
    0xf050405031b040209061c050606040305070905090111040e10080129060c0303011e12031b02040f0e1f0b06160f0f08070b0702060615070204110f1e04 66
    0x744490b510005149080e244800100c0000d0207800f0349424941c01040c0070941c51a48003107000d5140d4800c800398400c103c00d03245d08041c481184501d0101800540c440a03040003075a10700d5001d41d038411100000021600301c07001c40603140390720a1707008156802002c0e09010614444555540081451800030040d080320050b8a20b29040c1003111000d20440c0808031507425103581044072070300ca0130002a29034940c1c450801c5030413107999070811441103140103c08107041020400500c03c07140c050302d5440004a11243ca503045503905c00c01280c000b502c1d10f501031518042c0707011340c50b03403612000060701c0601f60007503d03007158880000a4068003810719203400c0d215101c070b20403642452036520354040011940d0400b01c921881c185030040c684500194401c00348200074016000740e502c200310307200080c0c68405040342e40b003105984260384000003114441c4281284002800c10074800b0303001007410807420754001410313080006ca11108001c0000d1801183c00c1c2120102000100c2c50500e40c02c290404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 690861088 1250 690859838 690859843
    0x4060f38030c0306090601080607050703050403113d0c020a060809150f100e060117091005041506050901060e01050a120c020a020f0d0830090604030f05040503 70
    0x80840c0100020030350215050344052042280024000e001c607602c80c00e2505820380e5542c000d00c50350825010b18800b18520904c180304803809c00b0f8156803000d0505007103440d00041c91008010460388544944860940585900400c1c4004080c80860308646c1d0010543c07001c8a02030403c4400c20071003200030b44d0005983d1a0500030030744226141554059942020715031514480110211122002d00104414030556540780d070302c19143c4140305000d81d50b644031001c6888500382d46880c00301c0d0345a00449100082c03082034550003d2400101c1e4061110070203407000700c070340641c1c1c20740d4500d070102c11440e0340c4004c41c00303824010b203010384012180e585007a030018440c40d0400e083c181003140006600300024400e10100da680340c0c901004100c1146560300c040d645113032180b0100d0203240c0940d0714041c01d1500143c001e900940081d01103103002c40041460220141030522410300b00e0101211408500300e600010344907001c05401000300b4200741c1005046080c0b0604040304101080106000700c1d1001b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 690862338 1250 690861088 690861161
    0x3060b04030f02010c0f060c02070e0108061315091b080303040f110103141306050a1107020d05070b0307110601120206090103052503020a03050a0e0c131404060f 71
    0x72803094546100ba00c01203a4103240d80703038080e16800c0402c00c01c0d005d110300c95000c05d540c181a1340850b2200c1e41d0303400c02111206800d114480d0503410140c00a00c40e864500030311501a80b150390701e18206052400321900700c2e50450b02c2a508a82007581a400041c40c2802c24000340c05400000d50641c5400d54403d8a5409419001050700100170b0012065034000e401110309600d820406507a01d1902850f0209603a20461059443d24244804134202c50340754428030b940d600452414528024050b000c0c000c0003044180c04417064030511000040500c00312015500a0443e941c036003a1441611288902c0e24806801034105082c6030340c40040140c0d1001e080b60b010550a01f00403895a841c841c1c11080c0ca1003081c401070000040183c50003000d81d2581c01000000341030349007006152074401e4440102d4200c050f00202580c414840541f040c40c045040101405d1421408242c001c04c540414003140c20503542100d10503140c0000c580e80ca60140a080d0105020142d48031500d20391445607140a6032 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 690863588 1250 690862338 690862343
    0x4021303031b150f1503020109171f020a09091803031d060103030203090109143d09050406060c0b010317040b03040803091e030f030604060909030c030f03060b0403 72
    0x7144149003424045074003060803140c1d00802800c0341c02c155050100003600702d01c89400361311850148680ca400400c01040b801303681d0107a41d03500e42d660410906036a0030807108001000ba200d00c40c58a6032035103034041d201e41d4001480102589034080124054540d008a800000009040460402c04080e170036000705003203505403501040d0a480d0030381e4103154181c500c4c40114140900c2c0008401d15400000034402c440d070070f98449a4480d50b4a04042c140c440c185c21207580b010720680c44803840e0303a043d003091405841c202e01612100d103519030381001d01c0e005144048080744007210100300d07030b00d4940314290051a50b4104141c0d0080c043d039504403902414000200b03910250f141d60204070718a441a100070700340f0107501981c1c17400d25003400009500100c1d000003691244100000703103d08a59800740050307201000039410280d403003898403002e030801044150450b90715040081d08008a0144814907802501ca1010241c2c40e4100200319018158200d4145070a022003001141840800c4030112034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 690864838 1250 690863588 690863597
    0x12080f0a03090203100c080a0221040c080d080108010c0e060d09140d08010807061412061c0f03020601060e0f010c02061303140c15070f0507080706030b01020c0402130303 75
    0x8418000e500511145101135054803034094541031300031981d40241c0d1401c815460303031442551110704c81c0c0241e00c00d94011003a107200c052440c481c0006004825a081480381041d0b074441a120300300c2a203030008141314280001c4101340100018030382841003045c945070514282064481741d1001c500740d44a00108503c8250740c81480000b40039152481c000c42809000a0f182000d6045000411540b028018490140900d040001d405400340300608500000d20691a00780581d4a182d2100351a000b41202d40105801c1015400d00740710302ca9a5081d40c7c170642440491801d5420001e10b040c005801680a00c20000700141483c0d5805a16500000003464500726000092000c203485004450016240f0007911001004001c451200c400c01046540211458080c00c0350401c4603516000c9000d207401e050401c000000724042c41e0203100d0503402202121240395036808501d00d4286030b0350281001a540755403840d210b41c1d05201162814104542c20b60a021282264441b400610711004081c01b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 690866088 1250 690864838 690864847
    0x5120a06020f2109151302030706121808030105040c03110703020d26040209060d1b06110708031b1e101107050d080c09091302090112080f 61
    0x44040068450856004409549900b402c101c074225a4125940c0740304000b24156803441c4842d8100116845224400020541d00040b09005060100c02801c0000882110f9501e000540c8040101c000205015603901046030320b60389582044030711711002103501ca185811800e010841030415203054a400b2240040c100714100401e03401001c21581000d02c0d0b22001c100441415004141d071a10240c850301c1e81c90030f80c40403001c0c00444c0c1442100110311020342001041c09800d241850b207a216101402d541c42410701612106144c103c903030203581c58490542c1c02440b076960701444002c1d13030110342c0e80105003850520003003a072240200e1350651001442a006000d50317000400c089401e00f501200403134220140c102046890307440c080c146c20a9681272101c01804902d00e40c0c210ba41d140e8011000d41211507682d1340480d20301c103001d0070740311511200b488141195034508000724018041c42140440d1000c1a105002c420041640700c1d207000b010f00613000000c0360f02c0030100c1d241c440508220a566 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 690867338 1250 690866088 690866119
    0x506090421090812040503011d060a11040801050f090c0409022b0c0815070c02030a02040c091703040e010603090c170a0b090318060a05040b030408070203010c090e0a0203070905 78
    0x702011548000d01078841c071078222130402e2640d4001c20907110194003e02414507100c10000d1340d5020003030884215800080020352450003030b805a04002680b5440910b000e0340c400d642401e4800907614800146200030910a000000b04602002910141d80600c55410190000742e0032031401d0381840034401c02c1c205001d00460818408500c0d01398003540c100900e0380c0300d1035026a2403070f107825104c40e0f4030030141c0410540ca01503001c410400e50300900a0501c1d40341c0d64203100141889620050600200340004280914000003103016095070f00020740d04c807850072002401c141e0060348a2000d052a00c040c000100b80e9461107402640c4413201301610300b19040411a01d0070740c01d80000303030030300c000d84003400140e15001c001400442d00c0c0e8955070f687c90f900c1004211a602c1201400380104408100030040403401c800950740c06070140c0c0c242e50420340c59401182c01c0d5100c01e091000040c401c10b000348030025448c103245800c80c2010310300310706502d07000002602030300d52030040c01c0c840c03040054500316 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 690868588 1250 690867338 690867347
    0x1060905070f020c09060a05060d15090902011403010e04080a09080a1101230a030e0f12030f1f0b03091c080105010f0507050d050c0a0b070806040506090421 69
    0x1410448010415464a418010030900320542d401c00140201d2009503400c2c80e0060543c3e0003414018406124280b91004000a9074401c45a502c031040c1c031b80031070341e01034600d000b10780c8001d10b4054800716111030180300060800c8007103480c001c2d41d840c00744014410f1107000110158895070103640243c4e561204041544e00381140d600c0400d079445880100410070000e13203e46645160281c81e00c0c5020071610030302070443d0091603500d04041909002d0800158407940040320700e1b1070780300290f50380e0300c1d80c02009509106004007003600742a400002e00c18825103140e00240d1203544032a640741050009400f1900c1c44000d0f110300040c01e4008804108400418012070305503202e0344106280552030400f010386091024440e0a0220311070000c020349840c001c03802c9a02440d4000058034210423131010a4890b500050b15584c454411582038100040759000f0007070044036251240c0100b0314103142040107840c8003d00d00c0d406166a1800d210000c0c041e0003a9600010580540510b1329202900803039 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 690869838 1250 690868588 690868601
    0xf0711060f030703140106020a120f03090506130c2c04030e120106090b03010c0806270c091f0215220606090b0307060c1502040e07121d190501 63
    0x59981c400414032402e160154480102c101404200c03400d140e90300c5c0e806a0326103041c80e4014044604000449400134490700c1d6000d80c43d0441e06000920640304d490321468203e007212120711142407a20b000040c080d201c030600c801004400b4090402480c04801007c280d01403003000c403060111070022400f00760040c00707201c06104001c0c00c0b0315001250384000b5030117420280301d1004142d1401c0a04801402c040c092030041c8107554a070f000680d00d92000744a0b00400d4050007140c640c2e130302d6401940143e18142024003171041c04000076150740342d2070308100e0103032a47d03071400034604c00fa020289500703600030400d040c070b428220f2078a144c29071b121028000c030001c19000c0001011101c02a420170011039a10220542c1c2c1c000d401000001c0c280c2c0300741036031a00c07940200000300c0d06280c043c100040c0086441c1c000b801ca0f208000d400c0c19698056082850030039510100410710700c190714146041b42e44034462101c06045100720300303014080c000a4580700d41070941005a08416030440c04c2c40000d41011 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 690871088 1250 690869838 690869857
    0xb0307030f170f030903120606130e100506130602010e1c030b030f071523040e130f0f210806190e01082802030c01030e0a06091103010609020f071106 66
    0x980d40c83c85d000d0300d11500d030380c864203c0520f00c803205c0d80416640e00700700c0d0580b0f4540302d195010351a441e00b80a07542d051190018070030200c0c5c2d51101c10100b91500c2d900064002c000d800d203030180513242852006420f407004004100c0c00f540c4400501d020340820b031240703000d01301703180d08000600d2500c683c0824207111030070100c40740324440d04200044a09002038090013240c6c459403039245080d88440b4070b107825a0010080062031a0501092024409481e0002c0e08606c4594001e2102e16640d0390f0003210400c041c0054079030b51a5002d8103801d2000200c4261500783e1003200901c405001070740081c21907000a0300b041c0c054400c000b081100c1c0c1c8051800c1c1405000d60300c145500d1036079500f6101f035a5280701901da62070b07840c04101c2040c1807004401d070440102d40c0200a05082d0201c80d00460040c440248500407901c524082d18000c159540b0505a000c0e0080c10180d4203100e00805250945c0d1582d88500801c81c410801d142c1c240034140c065034041c03903109000701d10031140000040c03007600511201c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 690872338 1250 690871088 690871117
    0x1e020301150608070e150a11150f04020f04022106011101150816080703080f040518090d0215160302070519051b0105120c04170f010b0307030f17 64
    0x1060322608102042e04c02c0c0210798442030406964400d001a6100d50169480040814490ba0542034055920b459084400c00110740c0c2c0d0800d02284c80048071002c1c8c5903082800c41200520003581000b1010300da4002c0d0a482c20351400b00050300c0c52030b164121400100510110740041602a840360840078440121100240300a400b00c080f40d000781d100758800c1480718441d100f84240d0600049298100f01d41510000c3c2203164a1616502911b03803181c01c1d0300745042c804100100300c0d581d44001250a518039031881d00718504e041c28002d480c00f00344c02c600406650014041c0d007421440e0000e100c3d4010014456203506089401c01074010380a107c1009120707000d44845040100305041207541402c9c054011035110804041c00c45218110202d811800598108800303603158ce408440141c200040642880c81c0c50303610070480d44145d80d801c01c2c00020f41c114003410785003044240660b01170000d049014140341d44c50f42c1c0c0c600900b10b60400e4001d00d54007192000c0310781c003198441905c0550600f00b24 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 690873588 1250 690872338 690872381
    0xf0503040b0a05030108010c140304080307091a0c060708062b080313030225050904140105090c190b09100309050a030c02120715110f070b070b131e020301 68
    0x5010f8840c1e003090140d004258a05241015298030035124000c000b904450518656140c98550b030441d03034001000b0b90284040284005100d07140c8088029400f200d6180c2c10380c84604401e555030400d00c001e80010108940c7d4010322003035a0b143c0074980d0340c101a8a141c404200f0f50b40c102c0b040401440100a040702d03101000b0030050f6038003545007020282c401e07401e44080400961000110307001c210384151501c80d03115020f0015040010140b50058010090300101d500000b41e024203642040b540c0300b003290400c1940042d2030a00640410620004d4500380c0c1d4482d09200c0c81403040d00903107405a00c503039500701b420f48280d4043e600c0102020b030441c041d942d02d503046003409031000c60740c01003c83c041d100c04c0c546034291800c08107019080c1d4a000001f02d9004c5980441110032420742d038002c00c02402114860501100100f040d076009000218a135515680c50381000545004010074001610044041c2e0b0350000f00b9110400c42924003280c028907400c0d503180042401000c2d45445840164400c94 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 690874838 1250 690873588 690873607
    0x100e0607061409060405070806040b04020f060d1a03070506091804021903030509090c18150408010e071a04060e010c0f0f030e0910050906240301091b1b0f0503040b 72
    0x29441c2d05c00c1b0b00034011074a03038a60380c03903030716030b580000700c402500d2004490003140041c50000d104448100c0000c1026040c0f90301484641c00f11400404541c148116120030181c3c0d83c24240240c5008250490700b04d0b04200c0c7c00d801240020044c40e00e98810340480d440068210740d600f9501500d10b030308060071509156100e10b03000c8c01940c0021042c81c41040d401000603801c200c2c0d81c0460364600301d05090326a45a0811003844082c5810b00c0941da080c000601022030080001d116214051400b074000780704d40340c079040300d00e0050710400c5588103441c2d904201c00e0144640000d5841c184400c20702c3c0c00070504d00c0c1420001091515880010711540041d6407200515074000280d0f070b00c1d407400702c82c0388141d80c40e490300390311010b400c511030a500a0000000212640781c5528000c141040d01d44c0a4800e6204c01d9240d004140e0090b0404400c0555440001d021204e5a40a00ea00300030300b0304200040442440401e0340e060400a4014032000301071102c0010001e09005942c0100304400c012920340700d540303 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 690876088 1250 690874838 690874843
    0x607080c071205100b060301030f2301020a1d0108012102060910021605040506030a06050a0b040c050d060801020a052d04170606040b090403181d0114100e0607061409 73
    0x4111303508003402d00e803d60f2441d2030701d581202d0403603500c0071641d80c204040355204182202c4052a501144040145417640f00e4000e00080007014095030740e40b0011840c040c040d01013040300d8900d090400000400610103009a41d090080c048400301c03030b8071090421031000515502c076203880c140d0401c20452495034040d40000c0e00c41e10003907842d038007078203590749070b00500080364021140d4950681c460141400070500f69400140c101ca004100452200c0544006c1801e41e0142c0340f40800040c400038000d00c44e01754620543e8003400d042d0000703600c0c1007140e5400410600034a84440c0e41c1c00c50700d180e450844002c8040c600d0340004282c040680303d95940209000246036014a0b1440340501030005013030f854070740705c3d04000103801082c400c440d8442d624100c2c1c00751a0260b000c6881101c903071000c1003080e40c070301140480100083c1d00091660402c800300e0000c03401510124015154424140f4100750440b00c6100202019111070b515180d5a080040207481c075a201c4500b038000c00c1d4240400340001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 690877338 1250 690876088 690876103
    0x20928060509070201140a09020411040b04082401030b13051b100809032209050f06040b03010b0a1509090912020d140d0504030e0910030c0609050607080c071205 71
    0x12114106241d496410580c241c4403c06d000a0802490000107905c07450a0350002c8122400a0400140c0040c10482c000d001e1348190407036028404045001c0008003001c025410000004800344548030b00b03140600e44980b00103010080c1b01210301c03000100d0b1403104440240005411600715110500c5140b10080c81c41c014500d050b004150901d003200c803845c020000c0074081c0c8003803c029441c1810070300551282e900000d4003c40c100c110800f00003000b0501d8000c4602400a04002c500d46040c140200012119103106070b500a03414426501d0781595400d0039079040301c0038190401010402d0300d0007110000c0880c6c01681019203010100420f02c42c1c3ea2515a48000f1290201e6070126012a2309456109044844400c03989041102c072400e420141c000941051084c1015041d008010000580410040700c84140d1003001600810a00140a6240005200ba03040c0b543d90a41001c2c045040f42c4698240500781c910001500000b0140400c0104010141140c45058820b40752070041c3e141ca80 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 690878588 1250 690877338 690877349
    0x6020f0315030c06070809040504030908070605030a23060d021306030302060603070803120703090c09110d0b060a0f031d120715060f0608090c060408152202092806 72
    0x940c0754600d000c0c1024002c45d8031041c1c0003202c0b03608040e1004104030140c1002801102000080f1b00000307006407040007580041d025a031182500c038a41542c0380c03000c44031803480c5480208504510503150a0050a9540e00200306460035442c2201a0020480740c400400c4803000d801c2c0740c00000030600da40859045e01031001281610412691043c0da15030341d0040000d540705900114000c80c6501c1e001e54021445a40300c2c0e4041c0e03070460f540d600b114088030700c03001c03680034640400901c0d044056036602c079081a400088440c1e81c14802c0e0000f00400f000080310103003082c180d850b0f03c520010f084880b0030348400c04840003110b082003040340030901c550300a030304101d4a5240a1078540d80d607045600400090340c40340c5a201119902d4000d045540020107001c183c014040d003001c410654845000074400741ca104d400074140c0a440c18100c103c0004014035000300701644404105080c890a048416506d804565000007521600e40030f4a0f4505480344981e200e446954501041c00ca45801583c2240ca = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 690879838 1250 690878588 690878593
    0x80a020709050604020a14130906180f0903020c0d0501022808070206012417040c081207080433030605010305090c0112020d0902270c0f0f0706020f031503 68
    0x890750401c4c0010b03800703000d1a0001240310104580701002e4994083c00001c20f06c1c121810110713955031414011105944c10124003000f031140e402410741e006002e00c06405004a508002c15491506e0094903011111801403180c2100403454051010940584000d5500c0380303d20032402c0b8450b40802c50050700a07000c10040b6455800082d001c0d0f002056443c102c400d40750b600900609000000b01e4038492906407981408080d84001c5041c804108502c1e1040d4131910f50b02c1d4955041402480ca4007100c0d400102d80d81001f0000c110002e2403280584044402a100c03030b14a1118100010601d152000d10f8600c05030f111600202005030b040d0040800c407002030701c0c204a107450b08044180c4620340c400200c0e000c41d041c80c0e0641c40c460300983c0180002c4842d02e0f0000b030144003940c005503c0360f5250340c01d182c0410000d01c840c100a1090000640c1114001d8401c520f4034402902c82c413298080c6403000d1603003105c0805e10038140301254045a8940440802040d96850301d000a0a9081c0150007600d0107407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 690881088 1250 690879838 690879841
    0x902130606031406090f0705401d04020603070522081c090311030f030d140604050402030c010c020120070e010816030f0609060504051014100302040911040524010e06040b16080a02070905 82
    0x72500115000900c030000303869003186030f540b9003d102c41c65201402c0c0c0d3f420031404020f00d41503400442409680032410440c018089031170a00030310316000c00b051060200d500c0000041032950340010307800c2c0450382e021020500010708038002a00300f10160029510500001444c03000d00c6ca0310b9070000c3c560704220703564032040e80c55010034403040351006c44c5c0080d015801003948861542c041c44901e1b030f100f88140340c4160000080400e07180c50030110003c807141648110410305c501c0c00d08416450140003800c0c0100707080d10072041c5000d41d050741480301800c000b5812000009101c9c0541001d00120f0f0820300910403820b251800310b41d00c036910142a00100d24000104800411081c483e078015151000528282070454081100030508072808950304c41040b40045a9900c40c1e01038980b103164018042d45444032620460341d400c69450b0720320741c1040340311425048160744810541301510059800c1d16101d001014124010000480340030b0301040d004218a095030341c2c002812000d5603459035051241d03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 690882338 1250 690881088 690881099
    0x117040c080618010e120307110703050d1808060721020c031602090f01060e10020118030320030c03040305031f0e010503070b0313060902130606031406090f070540 72
    0x4450301e15072144d4061b0000c101154a0603c160070320004501643c00351504655a652881d00e030600482446c40415221640008204052203030040204990005440e039484d2a0a0060031b0751075003032910311080c4c071900c40421450950303130607640d11004907811659240e41000103040b824200c44000c0b44540302d80700001301792600d902c1140d03040760a903484039a14240c1b40300411803420b210b0844034003150b40c4e6a8000310003003218940704010728042c2e01d0000e100d0080c04040a501c01c41c0c50101190010300f0000d0000280c0c1103002ca0f0780c06609850800d40300e4503480481c0030b141d030641c0381003c01c03000c0d0000c02140505040e030801d07048402c210122103441b42d9a01c903540c202d000458118440714500c203030400c00b052450304204100d074130060810b040c020300c107240302003210754542210000a9480d081d5170543d51039288981d4110300110388089181c503012098003130002c0020400c070104a004141405075516181c2d07104491417021003641043c0d8440e152007260320103421410601140c084400151 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 690883588 1250 690882338 690882343
    0xc06090f081507110f15010305010b01021207030f09240e030d05040b071b0b0d06060e0f0415050402120619150305040c0504020711031002090117040c080618010e 71
    0x41c0754a101c60b114510369554002070b039042c0c55044203000396004000d52150342030000c0c0300303007086c20759071030f60920095045080c00d5084640c00c0500a0541d031012003110504044801951981a03040c5030812010340e040104944501c9113070f012505061f103690200414540d10610442e459070361b9503a10b0444140c10307082503551803150200b0808034404200c20310003030f0481401084228081c590241055a428041c540c014520780d115818018000c6211020766443c0c0c003c3c503005000501c0c2141c003190164001894003200032104a124590301d403048122100c100b04584000d0500900c1151a0b01c03490b842a540c4500c1202d580d442200c0280310b41d04600b00074250b00c0161000c0c2040485018446ca6081c0d009003000b4000b41c0785181c0d4001c0005066446000500040c2e101b540c0d02c101075070114007454900039141d40d45580050062085c080c550341d0100300d04010a108211140d00ea840700c0c101044c0d40d54a58100450f01e001b8034007049880307200d50454a01800030800200310001c14100e03501d8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 690884838 1250 690883588 690883603
    0x4020f0405011811130312030506010201062d090f02042105031c021c1b0e0f041805030a0f090f0e0105060306040e06040b07120b06040515070c06090f08 67
    0x3a480520b10700614054181a4411302c040c1d114062102e03e40488100035198a801d00d5000716040c00c161106802455814003810390081401c0c0020300200382003034903581a072100201c5202c14064100300c503100508114103404000d00340590208081801210100c02a50050060641081c40c50450540700244071500c00162070b001405181403103c5801c96100b080e5890201d001030b0fa40038003441503d541d01d19802100103029810001e084001000110100b8010840c02d00c140590341104100c9d5071203004e10440060003c950000300703881c103020702d2241e000d811503020380988408200715400d02d8000e040b0181006803600c0d040c40c210703a51051545104154081c4002c0301982c840101310324103100001d103811840c001c00c08900003400c2041149010f0741103070142d502006c0c60303080c044400e4000341580140040d00c01d040c8050841480401c529100c2d510406000d450480d02201203500b400c002d40c2d1401c0d40c0060000c0e54160744000040c40510f19000d49840c001e071040300051080400541c11 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 690886088 1250 690884838 690884849
    0xe090c091002070e04140f030c011d0d020d0807020a0c090504140307030507060507050c0a0302070603060816050906010509100302030402011d0d0f022205041202070e0f040c12030804020f040501 85
    0x240c07483c0d5100d41d03c088030305800500446d080c1c4030310203220b02007400500180c80401c200d0000011031030b2401c000b00c00071200b5844404031340d422030b10304401595404181c41a5904103401c10207540d40300c02c0412407400c80d5506010700b0b40d00c0728140c08103503d041c81d00110f02590240141c418804c2e0500b42d22a100d10402c5001404181c08100800000d181038001c640d00c0800750502c02c0c24100c1640c00b0a09241c4003034001ca0041e0000e1500740200751f010b03c62100507103002401030210301050310244006150f140551403080383c1c00b9000481c45d07031244040b200c0088016018031610121014040c0107500706640803400b082c80409490085241c106041940a0009200e00c1a22500e070701c40c01c1c01c92240781c80c140c1c0c002299810724401c0820040024a58440311034001440c0d28181c144141d00b064202421001c41d008020b003004626440c1200b142c202020016440a58555140849011019520a8110b000e504800c0e07000e15400102d8035129500035146400d0080c1c000c0c0c2000100e6400340544d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 690887338 1250 690886088 690886109
    0x905010b040510120c1502060604141611070b1603020705010e100509011106090c0a1a222129011205010917130609050603160e090c09100207 62
    0xc1018910410710702c1d0300c1034052008a14011b071541850100019980611710150344200d0900c8268100751003000008040c0c42c03252a41030a0a40400f18201d410920700400c01c20039803015a4103003801e220200c01020b22032204c99a400240038042c0c0c0240d03e004c801d81c0503004c2c050b00040c90303502a41c02400c1d1100020100c4001c0d00c00454103540941100c410700b07040144005c4825000c0d0f03420040c6a000302e8244000704101c1c00400c2c2000010071081d0015030240035140290741c1c103000c02c10706895080c04003c060540032030703a10303080c14240707a800c6d80016080059051003400d41d0617042040c0709158022000340d4040e0751012040124490034601c1d5130240440c82004001c0d800b444200310805500c10b0001041865080d120034116500410049130420b000141301c1d488030341514100002021503040542c030840c0362000045450100510301c84500c0e03000140e0030340b1a4481c03042008010401030010005082036002c032100c83c1c00401c20140600c050042c04800c1d0350002031400100d4890565 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 690888588 1250 690887338 690887371
    0x60c12030507020a020d0510050907081b13180b010612061509030201081e0a020405270105060306010c080307020c0f0402041215090f110901090c020a020d030e060d0905010b0405 78
    0x90148086e0b10030030036a200d004412990380b0143d480e01070240a282c06030002d2400e603050001460030882c4007154940d12082c18803800304c42d40c90301c000303011002540020001d210005480010224103100200070b040400b120008181c8503082402011001c0c0035000400074592103004404c030661504910b2008116012020001580324401c2c4540c001980981d410b0110740c001d111698640c4103992091480741c0100d014046820100b045a00601da4400ca0703503448460300d401944a84418040e842c010040040050600c1e40910307071200da025807042003030ba520716004034001e40302c400b9000301520800c12900c1c810824a05802524107413501d044450394401d41d01d035207032000ca045c01e0310249140c0d91a030718a00c02154407003070301c11105070080d0144814a00f0703010801c40c9040707058020f418420300c2c00c1e5841024990000300119601c1c1d06617003090005003203080503100b800c000078a066000a0019011400120303079008982d14612900c000e00600d81550b00304803da480858039104410756504 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 690889838 1250 690888588 690888593
    0x317040503060a0b03030c010908071205040b030711190308070917100504050c060a0c031b030c0308060f09010b070303050c39060403030605090a11180f0a060c12030507020a 76
    0x43c001300200000400701d13850440f40000960030740301102c201380d40c0d000000c0313000004e00c002c070155804d0700e42d16407a0141c034113030400c0c0c15035080e40000b622620070401e04c1d00318001006420003400e0709034403188ac5101d0110704140380080c00002d040b00c1800004202d1400010030200600e03000890001010140140c555030052000041034024003c0d00e051254a60b00e200d035843d880e00406c00b0301101d5480344030060316410058030411901079002e000e0382da201c1034940881c0c1d01151942040c0e0385454600001e84078a000510b400100d1003600303510030030b01000081d8014100e00181600c2d880380d1414881c0740e54041d800d81c014040d9500c414890b0004810380c1040d854060074412600200e10799100030f1b55042030803140703070200481c6c044010a03615142030285190801426a0100c4815401d100303840300307280d581d0400e00a0710030f500b000c030070000350720030b416510005807013030b629400b03441c1c11900b5544010042c50b0807540c8000b40c0c0e50340b00b91840f08078030354401d0151510516440d00100012001c56 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 690891088 1250 690889838 690889841
    0x611010b0a0510090e0a020316140f0904091a06100e0f09040507030c0b03010302011407031d0303040504090b0f01050108160f0525050709022704090203060408040317040503060a 78
    0x1d40743c2c2c070401681180100325030540d0f10308140261902840180c0b40e141101d401003c581040c8050400e00c08096aa01c45603445541120031460301e9032241c03178942d114400880c025000800b001401e001513000602d10214045100610a103000c480440c0e511107403071410f96130180c0305d580071500822110b01156060030a005140e03041817040045a808595a031a02e00c0640707001d810407169414000010030942d139002c000761007901024074036580b800705150740c01740c141020303000c1200c0d984007c4a0226042da505005480041c17001800c28004605685403240c034851085031400d04004800d000400c595115103840d61141c04800e80e242c003050020356052700c8009501d09000c040040c00c0141e01800b0303440540d60b40001c01074006070310381c40640c0e140150502000390021020584180008031004441036080201415032403000d460521010303002c140070b400e40b1000a03401d4447c0b201272204200010008000702c90103040c00c4105440c1901c0d005240d8411481200c0d07041c0d01c031030085811300e801d5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 690892338 1250 690891088 690891109
    0xc030905061c09050319020609070510051909120302010915060602190203100912091502031803010f020a090e0f01050906100e1c0b0a050121150f060611010b0a05 71
    0x41c1341100d0400b02c0f15901c4441558020441c000160041018824149010048200582401c90707441c105400d50303540c01071071b07405080c000541e80300760000ca1850003402a407103c4007801030345240c80750740103ca0078080c0c043c00d00d6010444420350168441669000640710702e0050720f0655004d0300c06015a400301e40740034104440c05907458010201c40e150010000e100b0b200ca02d0348200d1200580c000f000310068501d1686a019451166041001c2488542d000c011282c81094101c844501c03070311000d011a004142d50781680270130340d1001030503d070540d4021039100103c82051a10120699441c0c000220130003080c8030300c64001c41c1481c041071071850042602e86200c0e409203049500300a002c00001c041d0126554040c51420355051003a0a11507047c00c0c0b998050010641030045500d00082007000d4074500803281003440058000108220710508508800c0001d1902407095001540c2000700038442840703080e0218840f43d461040d0070b03a041c0146044804020509552540303401e0901260700d11 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 690893588 1250 690892338 690892343
    0x20105090114210718081207031e022a01020d0302030a09020907030c11060f040b0c040801050106090f0e071d0f1e040506030a050622120c030905061c09 67
    0x61050107075241ca0100d0f116684440c80340d0092460402000103000407080a0040c804501e2416003807010300c1c1c000a0f11403822031912042a81ea0f5014201180c01c140010041108018840c01c0700c01443d500080c041140b40000f0300c40c1144041142d42c03105400d00442c510703030240c1c205121341c0003014000e034081d40d0701507142c120114141d8555800140810401c443c4400440d135101c0c110607505a00480000c900140200140290300713041c8081c2c00d544000900043c40800e211000689081022054500400d250b100912441d40c6801300600b100034140941000c06c011514002003480e042040325000c0c042e60703242d000e60140d1400740092105010001c41e60462034014501480d07803902105c0000d6100c0745a4101b030404050010041078800180109100307030300a50750400800d401041154120035003015030f11008041007503100044907054405488610360424051885800c2070541c520b140c420fa890744030140d255003c20009014240c0229441c0342240c900425072001540950212070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 690894838 1250 690893588 690893627
    0x5040305040302060d0f230c162907050a0e102a060f0615050a020a0b130b06010306080a02040e0c0d1211030a08060126010914010f030201050901 64
    0x280c0b03d801091481d031042d442c8500c03960380c42034950344e24005442200e072880b80d004003c4072160440b240503c46d032040605000c42c081030002d5036140e0307108600c09401566921200d945005803070501003401050952400c014030f0314a00e40010001441001111800c10603901e80c00400413070700c400e010a01940018400a020132080a01c10322940d8054450b02030740d5a5102c80b1034208140740a0050301c20544010711802c0c1040010f011203602030013503071904038441ca01b440c2ca80100010803442e02a1b1010041c01d0300c0031400a00c00703601410852038480e10b005504d080d0658448000440031180385200d26003098206641034030051400360006413000341c03c2d0381141c00600380103001503100041c0c10021a00c4401040500400d40e80003d407042403002d200300590708248206201a014100041101c0e0411445a680d0940d44141038000f00c0110382d05c55840041e50785940c05000204803440c102d18840c00e840c07000054205110862500350b03981a07540604190002c0010b558016440d107040b02c054 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 690896088 1250 690894838 690894847
    0x714061e03041a1306060902030408041e0323011404051e07090c0504051201090b0103060504020d060c030605030f070b0f090105270a14030606010509030f0708060609010e160305040305 81
    0x1c46410a03584c1c000c00340614041390703600007031406100b04e5005520580560340140b04110100700c4a00580d4121403420305000100d502c400307040705125800380c000921142c0001350264511a100c0660081803082c10f008000f4049000000c0400f004200d8000b0b01c2d0798092240da070141c0c180414003c0c11032003035000326140070b6150600036003540d07258070401001070000300d0200150b01e0b094029000031000c00c402004000780c940c1703070144004414040070340340c1c42d154004102151503100141d00190342214041006842c0313a5001406440c0c54450540b091042803441640401e000c60a48202c540060009241404500310071405400054101e070500c00d09015405c01c0c0f4000c1440d4000e4074411907404650160840104003d0000542001c8501012013010300f002d0303240010a140c20040c2428241d03141c1c0c00100000c0d00c1d1044001d10040701340100b030000107014a00052050241c00c0403a01c0307040d02d07a01c2c1c03074100650010440e1040c040e840070107010040e803802a0701440d0054084c2c0340440c42c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 690897338 1250 690896088 690896123
    0x307050705040f1d06090105240d0807082701050f070b040f0215130e0610080901020f0c0f0c030109020a09090f02060703051e160b0613050106020714061e0304 70
    0x158130111034000c05500a042044404142803080550140418900d02e25601c50900c2c110505c03a00101058060700c00090780b03c040c014528141d4001c01d41c45a41d455440000b52080e105605810712400b180079511035280e809503029909032040c0002040700c6505009081d01c45003041c00c03015100b51801a2800714200250301c0c0c40004108121641d60995038413141d224400c80600502d0380400e007103c00c44014031480c1da641140c280391658151074041020744903008054028410b42201d0b81ea103960025080510341d2011900321b0485c90a00191504c0f803038001c09260980c3c6110000a51042c0d19003030510000180340d000d074000c43c1c082e07904549000c045501140d116400500b0507408143c0110310507201c58000b45113178a600c001c6401480c10105c00c0f1003807a81c14003641c1001000e81c0c04150002d1030380d48400d00095603d01010301c082c030203135955903000b94680002e40034004000440001503441428240c00700e6094484021503450112071908200d026a0030140040301c4060030314092208 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 690898588 1250 690897338 690897371
    0x801082a1503040b070c030503060409030908060a0c03050c1303080d0905151501090605030a1d03040b0919180c1125050102070b0a05070302120304050606120307050705040f 76
    0x64a450355032554070309060130004040306008011000b0444045035080001c0da001060301d40040c5e0654000c1200081c034a01074592160302c0d0000c051074451841003000c02405a006007544034900d40b000c10040d01ca0079a151810301c2100c40341204000381010400002d40c0c500024510347c040c882d0b000502d0030030b03075568a040c0004000d4044c51020084144154801244480c007010b03442424080c1006182c083d000d482804020000e01d0030303a40e0340c4582230f807007184900010080100304003540d0351113881f44034000154015040840c06900011164840d030440325400c0c5003510340c0c4d60b00390400420180581c00c0904548007404040142c2c108030480305071030400484881d2803820b081c40c0001540c001e003505d56150303550701050440d40104020400e029101003191200e0400b07281180c0d649001d41002e03407401e200325940b04e03143c0304000100f0043c0040400c11902541c01100c0100010242200303061b920302800b040581030350801001004030b441c0c1980811030080a444011460030484441d580 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 690899838 1250 690898588 690898609
    0xf070f0218010b09040606050a080a020306040e0f01060f0e0709030b0a1107230102070c030f26271e041b0e0906060a0f05091807020a0309060801082a 66
    0x1140f01d000c60740002502d4079004a0003d02001e28005050204050b4001c0040101600c00c0c20015800404a009905d840d001400100c0d102011994540403000e005070081c2034602c141c21441d0105440810610341f9100007a015000507600c1c0b0100301d04640340d844007168044c009461240e83c0368841016440d14602070306081c2e000d1a1501405806220821904d079041040070a90364410810040010008103c41301a00c0e00002e15000c1030b2050f00e880d4481d408500712200350050340f004600e00303100680c0001d051922003072408030000010041040c14041a1218482d8005c094060010340c1801180d004144080c0041020511110900c01e6500d4038800d040361720005000c00c6400209400c10040440e084201a03500a1a20401e41401040b86480342464401c0160002d0800c40c0380d60f44188580c144091840e84640d81d04000e20003170354a8107413600c100c011624506000400c10700821506040b50030200260040310715003400c000142142801045000001e90307100740064562a41e4403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 690901088 1250 690899838 690899849
    0x7141c0603080909060a0605040311040e01020c070f06050301030c17010b060c0706020105100b030c0c010e061821040b0c120a0804150e0c060a030e0a1203110f070f021801 75
    0x4603070f601600800e0100d60345000700780314082c0305181801c11400350701508031000c4a0b04500d219046181440004010380501d203030400fa00d60002c2104541c4038008500b00341141c0d01429032100300350362118241c50794002444051b009a0320941e003008904594a84403500520b480c00000c4e04103681000107842c0e41180781c9802d102c0e030110800f409010340910406030490580314101404500c0e2010070006407000404103507440d8808114800c20060940240c01d032058072105803000c0c0c2c40c08064900104844801044070b61095071180003c907140c0403030300302548050058281c03070300b4202030f06000c450b4003040392072409200d108030f040c64004083e000350148161543d070300140750400703003041e503c0b074038072102070242180c43c0501a8982c40300002e030032200b4820075a00d044d11550490810381c028103000e00c1180b07440c025201c8440c10440403492101c2d01d0400d03510300f00700c0c0c9200b078601c00d446405132090002c5148404c1100c02c02040b09003802451817880204605070b002c04800b00c415103010280c5c0310 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 690902338 1250 690901088 690901103
    0x9010914060702070608271908190503040c031e05030301030c0603051e0f0411040c0f030f090b040b0c1908040309050609100305100b040b0d0e010507141c0603 70
    0x40c01807042c0d0500c9000c004100b9481c0010940c10034000347e901540000e5443d040c101d0500a0b4100e81000c10f21001550404c1c8440d071004107102801c020f4002c2e48640b64a581c049840c441507650b5074001c80559011315080321010903820700b50703a9544012040810040f0b198540c1c40542c0300050b004000075400b840c82000a0074446e03113440405400d4680c09000000800031004980c6080a0b80c1c0e1a002e50015402008005949440c280b0001c801c1c0d038221240c0c0c000f418222005007141d004000801034004503602000054035190014080360000e0300c0042c0302d101d501002c00c0201d0600d100c11078010781040c02e132318903040c4026103101e05902d50320074000100b03c18008100c00e0581000c0850b005141c103507403032454a0015070000e100c10603080d88039000c0c59a204003191030200001c5c050380180c00d540c2d100c180d58036101e20b44280d40350410300a202c456810300c4c0303007a50004018080c4d6070241e005c0741c98030614a181e00304504203030313002a0051034044079039840c1100403101602030355005500807440c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 690903588 1250 690902338 690902341
    0x81c06090506060403170906090a03030305070905010e10080c090303040e1503162715090501052b08090d0c0501020d0f050301090f02090d111003060317030901091406 73
    0x180e81080d14001041e0703912a22042c0010804074584064807560074a004400654078100700000a80318041c0441d101c2e000a1007180100400d0303050340c0220b0003503000c4e440e80c8140307503134940044032140f4100c1701250b0010074040351010074034010b800250b044440c4126003030400107500c02192543d0415400009010900001d00c000841a1041d801c0584c500740e01620140003d200780c240003003007500c2049104a4110740d01d20000040343c2200081c201002d0080c0a105802c004101800d003003402401d982034903000000400d45002e1a0180030400d450901580d24030070340e0188140190b0a20040c1c81d68002001003a042d50742d014185650031707104400c2840f165007000c1c00203180014005500050140c60701041c00701c26046025030341102d41101c0003049003001f1000413000385c0100c510064020008000d080100410f031091040403480c256a040c1d544940c8920407010b0340e800d88406018050300d8400028180c151400565010460400110b40410170390303900841c602c6007a041e01040d810000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 690904838 1250 690903588 690903599
    0x20a0209040f142d0a1b050f0409120309230109030806010203072003032b0b09010b0301061b08070f02090601113307020f01050106032304081c06 64
    0x8500e014203d100c10002c1003408484042144400310040754a075016580c90a1182003200402ca850106640100f40c0340701592400d40c44030301920b19010303047c030800d0490029117550038544640e008540d0840e825641c40616820140d000f44590b140555114982e50840036100c250a40135080c03010b40f000001944281c2814010440c00c0064006411900100302080c045614445900907002c1d1401c0c1c0d980c42c0790005000a40b0f0361240b01c1102c03040c80701410305088000400c200c10b401038011810180700041526080002000c002d00840b40c03409018001840040d11890741d44c2c5001c41c0311101100760907103549403403071743d6000100200c0c1c500d61107403403010460500040454000d202800c5c1220b10481707002d0b400742c407200c0c024030b0480d000388e8128032000d184140f0000d2084d0550f582508020b6403c20320002510340c0070410040c8281e40c00d2400020710780c0e00c6031142c0425039801c81102c04141480031322007840703400080c00a44a400040c4080c00c2c080202101c0035a85844a840000d401c52410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 690906088 1250 690904838 690904853
    0x31e1205040503070f0503030d111306020708060601080906070c030516050c040f020307090612090b010803030f0708060f0111012912010504050a122d12050106140a020a0209040f 78
    0x40d0170940ca0105203201c100300360780300007003030700c0303084220000c042a868441d4403480000e0040c40c14113460b030410804001001c0b50003003250000d0b205d01c01c0960b4480d541d40401914030440982c3e070010340e50b0090001408191140c8480820720b4440e00c2c1240c034141402d000c1038400d0301e003035005541e6a003103503455170800c3c0f03024405c1d218406030550040d400c625203044c0140141e80c10788189070902140d2131f480c1ca40040300d03511440040344d1008440c006c2c1d5071240b143ca5a81d0b001110303141d02309481c1e18007040761a0b02401c10148a00b07401850303948000303404001182d1510303c00721030401c590340395074241c0c5d04c100400300f40000f00c02030356505110407a0301c44100503e84002c0c00004600c1d9240100b0300002c0350000c540c103034045d038100602869400321040c00701e0380741c000003143c01c00b420a1300a952044a014500c40d69201c82c0e41d0b550680d001d0300b00b0000c5e6044607000e220746000724100014403140001d0010140c0340c10340f1075005072002a401500030441c8032000300c038200c03031009030940a2030400c541d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 690907338 1250 690906088 690906103
    0xc030605182a1c060903080a0504050c0607020102031911010b0612010e0402120a050a0c150e010f05160501023a0b0f03100c14090a031e1205040503 65
    0x844000d0407610741c050120751204405080c01014022080000000d40c1c4030b02800e080c41506101c0301080c0c03010141132000c010b041a0004a0002e28040007052401c60345000b00742c059034218000d004034500c500100001980300c0001241580010f02c504980380c8180d050344000325856440b08510908041c8440342154000c0080c24824402401030001f170005c8196110306441904040022a84882c000110003519540700300205104a404ca601000382c0441d22461540c0f0950403421155100c039215428800402a1100082c01b0400d56000e19031040601080880103400c28034500904c1510004003e4401081566240c0d00010400140561003071048218240205810058210f203070030a400700d031124007030880043d211100c1445076600c1c994021b83c2c0c2d94008045071152480120882e019000c11210140071506100c00e44800781c109600716001c40c44000c286000c0c0e2407e540d41e1543e401c086c00181c003072081e802002c0e400000d056100d807031020303003440c2c0f110f5442d545054109841e0118 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 690908588 1250 690907338 690907381
    0x110c1c0311070609350f0c070305070306150b030420151908070f030b0a0509071d012f12030c0403050f010207020f0f030a0204230a0c08010e04030c0c030605 69
    0x45c0c0b0081d07039a05001950324401413510071506654599101d020b0700c0900982c10780c0d42c0b160082e0440041040b400017a04d0003100c0c80b41100748203c42c01a050000b269119200c6c54400920800002d000148190314521007509208a41001e41e0300c41030205840781c6100548002ca0400020002602034500c0503074103044013503103019078552074049001814642c0c1d1007450b600b0f054499400418668500c10248084d110140072084c451038040c00040402521201202400c90074442c1b00119501c6080c0d1031a045203805411603440f006d90b604030760001803103109110703079024600c00540380e118258011806802d8600305151118110b081583c201302c460b440c21403650f131041043c0700050311080700310303072854004a5008450380903100c007190410f010480020b51151a15020140e03002400d08801694076011000c3d00150307451a070b18404690400b454007012032160030041106800d000555584244240b804400c000000e43d91401050f0041d08201c0790300b916002040940700502c07422105009 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 690909838 1250 690908588 690908633
    0x51009110a0f0804051f020a031812120e03070305030603060708040f060e010b090a150e060607020904150e030306100f09170703020604080303040204110c1c0311070609 74
    0x1c45480001e00703140700081c400020320120500280038020144101c03011310b2003142035180100d04040e0000000c0d8411401c0d41c000c01d2900014502481141c0580c0c043c070f81d07201c0920360300c00c0c08140040e107440d4900017003030360b1083d01c640303148030076910500280070340c13510940f10281c503810124109420304d03000400034030402500c4010407020400b101c405d5034010f6006003002840500c0301849038090036062810a811480c0c0c8003c3c4440000258001c07901d80d41c07215045100c542d1900b841d0782900c5020303204103600282c14401c007005850300c51042900203100d40c0b5040f510000600e4840140c605071010703868940c00101c108107a40c18450144414440036185c01112009584d401906110b0a4010400c41e81083c00e00d00303a102804118200103190018440c545483d51054116a2540101c408900450500340c0d80d0642c444010305540054403c000a0081c030101d41c29090480d440c0c1c0100e46e001c141e283c1c042680110004002005104c0c0143e01c00b040d4101d49041c40c24103049410f0000c800007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 690911088 1250 690909838 690909847
    0xa181505030f19020604120f050f12040b0d0902090c040806070305041a0a1107050604050c03030c1504020d0c0e0403021b1e13150e0a060605090616050105100911 71
    0x801e40407404aa0042c0c09561141421080b130001c10030354040c0d40c10200e20360301c40603908000d1101c0164040c110502c07445c102d507074101c0054030310785d1250342e18000145036805c144010300040340c590028010110045800243d902ca07260006964202c0680c0c00101c55000000c0501540038103003e0740358411500d09050105051640d1105111800322442e542c0e40c00140b0013044a10306680c01500c111460703180150344420f0182031090300e41e82d041d070341150144107a01019410b420080f055940180d0001c01900799184442c07907005480d070009108a03441407604d01d01c08000760075030b84008041e140e40a42461185011325020f4a0300e0b2203184510008601c2c0594110380f07985046003c2180712000c0480341c4006c107040e0225040600c1c010000c4017880c00d140e02d81c4152400b180c01d400841c0c1e00c08451045603101c01d2020001c41c1c0c001d00a4200081d010000907103941802c0d0000e01d01c4c0d411000b44140e80c07240640707490382103d01c1550544000e400b6450208402c08080c010348035110360584007607140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 690912338 1250 690911088 690911113
    0x1110301061e170402061803030f0903011a03060f04110306130605103005030711011403040c1a07060c050307020111121303120906090201120e060f060a18150503 71
    0x401c40004d00c0203104141c0080c0d070b000c616192000300e564a00000c2d00726a1124254290714290360030211806000b58a80003030b03c3c1303180703d01140c400d01c079100140c0074214548400c800021085401803013501c049800403c2148951020020075101e58006008141c0d03a861518040080e5000549407203042303070031480e040c03228008000a0ba405091058003000b4144520542c8005003103d80001030024017001c41d0040a1000901c1443c1c441d400981c0c0c0d104400003881b0315085203000a44010380702c00d0520303c091220b160f140c0382c00061901c42281d014102160350380c0394815904110b5404d00062000f000388560560240903101410416101103400d080522541c6100141c00400024141e85580c52207400c0c035014031005201304400c560140700307004d1641068809800c2584c0100d0000e00890300d109040b050505c2100d0074001d00101038480394595101d00310403100e000d440d182d404403c4a0000480e64a9401810000394114101107001100c80c40024402045580711074041d0b0800400c0401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 690913588 1250 690912338 690912377
    0x18090c060f2c0a0b0a0e10110a06020c06220201051e030a06080c04060302030a020f0105070c090603020f0108070203030f101e052115150d0b0f0c0a0903080304020301110301061e 78
    0x109807420b41c0c01c1c0030304421f94141100e41e00344078540d4614600503c00d031101441120f40080c41e030140044210340707568580c4140e807196502c181d1400c4054984402203103005610500040070b600240700032041e441502107070b41e5102a0310943e0060681ea40e624410072281c0d005124054074030764215010040c4626640109840341e07038011000344203014000b6005038503030043d003d60f1403054001140501203526000680002c006c82e02060303110b030040d50305050703140d0707c1141e042e4401c0c80d0540c003850a6403988115042d02c2000500740c0c1159011644000c2003014004018499401650b500500e8040c40c0c0800c1c0907803030755411f81102e10300d071425025034002200051314403a6888592142c00c0c055881d510388490040190007020781c403050120300d03c02403004204c02079004080e810b181c5081ca4030f80d64820122032050340010340128041040400118000c4d4014661250014002084c80845a55a420741d03500903000013011581100076600b0400c040e0710008100409402c00c006840c0303121038141c8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 690914838 1250 690913588 690913607
    0x90706080c0f07080408070b07150216060e0a02030303090a030801050f15030c070507030609300f12021201030b0705040e13020d05010c050418090c060f2c0a0b0a 71
    0x30326002070f03e0b10401890408440051031030b482511346903602c1c1c0281100c0d40e40010415289a02080d00b081d03904141c41c401c680c0444200140c0101100481d502c6c54040c100340015141d260164046030300258038280021449058140d010b0800340d0300d10b24020300500010713004540603040c4030560b1000e40d01d80d03140040f001103188601a440750389082c0d000c7c0c154072511400801a0081920001c01c000403a0031480c9924465407900c001c4151548044d64003241e42c2d0130b942034406050001448090117807802ea00078a400d49440c01c05180c1034054801039a01036800c083e0311419200041044c05405c030101e94100b0103514100e40b03098600100156402806070442c1c4102c1e040b841083d04558034280e1481c1c120340d203e0002c0c07207281481c1001424907041072241481c004110803600c411003055100304405142d04c6800c1c1244582040c20841d80a85045114000d002c940d0010454040e0f500c40395800d00a40e40705204405110035091001200c0d480d8000c00d081d840c1441401c1a203a005403290 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 690916088 1250 690914838 690914857
    0x20315100e0f04021c050d03020a08070503060d0204050c0766030203150a06120506150105040803120105010f0516030c02210127030807180b0c06090706080c 69
    0x41d40c01050070511105c00440380d4100600c203118515a010304e050300b54010b00008903050b1100006980c8111013503800b803200700d85075035000c003030b50f43d90340f0040c6800da100c1c6420002403070b103031420031440350350f007884644820900300d64000312a04c8a01d59280080e9403c00350bc01c03040340540b17616001680c4401084801c4040203405100c603c03818900c041c6815007034000703640060484441c046100030070300c00030800b0b030344500340d084c142100860f0700000c0880c03107000a80e05c03a00a016640c0c900620030400042e20a005040060801001642d60000c001810b031032a055401d00748694503000000d824003a08403111410301c00140700508561505801040b0380d15050704000c0110a0300d03100082c40c044603481244550202e051220000840551120021340095017103003410002c41214494550010400100080d42090000310740d10312901d40440d2071522801c1c507000150b00c4440c0e12044741c001020b5003074154001000c000044c00108030700d2008103040d00303118803107040400c200c81031031041c0000e4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 690917338 1250 690916088 690916099
    0x30608100207150b0d060212060102010c020627030721180e040b1b0d140a1a100c06060303030c1803080d110403020301090b011a03011809020607020315100e0f0402 72
    0xd0141c1c4d510398101e40004103a20034021942e881c6200c60300f0300502000c6d183c0303500640c0b0304289200c0d0036000250103030256800301400c85503000354140c0c66080004175460003100340401d0042a00055100c100c0c40c01580342c40080c002c1410003507000038001460030702120031550720000200101981c00b4a00360300140c1224110a555032442c0c108008200800d4014915400000c3d000d1019050343d404075000c404a09001d00301030701c3d002000000e4400080100190801a004030982803500000380341c070344441810075043c078582c5926100111240340e80306a0100317031149580d0303d501d9031001c040000607151a50358103259055490b01001d60140c1d245500eaaa540c07000c40366403160b00314041e28020760b8001c0c001e2040036014030309464841c10030300c41c20310b55049040e8500c454400c00c2e000c0c2d90590b0111765801e040c10030300b041240054030741ca00007a604000200109005038034107004000c20102d864251441c02d00700603001c03d03858520b944c80000280c005806101d914015501c191390410f4040f0b90 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 690918588 1250 690917338 690917351
    0x20907020a0212010e010606020102091026161202121b040f0f0501080c03240d15060321020a0f0611030405010f0b0907120e1c03060810020715 63
    0xa900d4076120110183d03200c0c40c0d1020260f80500d05401c070302c00743c0180900a00c051075650200b41c2c241e000d16114643c0c090080381383c0c9011a03100d000b00c05c0e003c0920404810501544c4400450303511829908500001c6128100c0039880350402c0c80f03d480c041c01c031001140317084070030f4403400b441c0007000d80403102040081200c0d42c4295050030946024045608071a00c8a030b5a071418411054201d126440c0410403070070004542c0320707408003901c1c41607030085080c172401c0c0007294021443d14040d50131158403100d0004c803000850041c4503842c03444a81e0700d400140706411400d1101d03030030b07507030315000b8050f400d071116110300c4243c0c0411101c68080d4029003031031135198180b81200103483e01c00e40c4207030814004002c110a11105400588040c12828010400302034083c003403011f14030046680ca004605c2040c400b0551000541c81445c4c0318060f0b00c2942e490310500d40d00e4120500300c0c1c1d40706000103510303540144011001445110201032141c1d204510700085965200d6183d4000130440042d241d5406 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 690919838 1250 690918588 690918601
    0x6010605160b06130e070f090b0a2108040e073902041103041212020901050316121b080a060608060d17030c03010e070e031f1b0503040b0f0c04030209 66
    0xc13190403e49418840a100850700f4442141e91050680700710701a006038904006442c00042c825000380c400003070401e4034000c1c205204418106e4041d03d400980da14052516400b1a802c14041c2c40500300100702d00d0024102500000c0048075820b28910349505660b02c1031500740c000c03808102c0b1208816448040d40c010a00006005202030301c0b01905500c0d001080104009041c42d44031140441c5442c1c10013402c414045507030403802281d5020340425400c00c00702c0d01c5070740764211044440aa602d0140c0050741702d0f105040685950820b89802c42c0340c0900400282904003120fa45d0103032480200304070f050f00d011002440c0030400341079a805500d58111140a000d2122031542c0c0e013451485100b9600c1c240f0100c119000e0b4400d108880c2002c2c0e200c808103503101d12944661981240043c010451048280c80700c1880519050040d01c3d070340d90342c0c00090603104601104010048641c2c1300d5036120302d010704011070702c80ca0080c108150880304108012020420500791030030740b0f8042e51110000c2c2d8606 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 690921088 1250 690919838 690919849
    0xb1f030b06070c09060e0a0c0801030312020c0a08041d040f29100617040c05040e0109060e060403030605010207060210022b0b01091d16030b0907030e06010605160b06 73
    0x644010f010142c561030003041c01c03201504000100c851103910304410f1340c0d4841e15041200c0c18000240300003036030180104042841039110396508250110010310301010083c1e41d524011034040112801500072504210388601800301e9a040c000202c2084010720345a035890f2180702344480002c1ca035801800443d223107a030711241c900d14007034030868400c0064101000e00c0740a01c2240d2180d007001411420001d11400302140700c0134001c40c3e01200b0418201e0070701003000f0180160401840e2150340c0e86840c10003060941c000d4000c007444000151640b03050500b030040544001c1e0b04610705546c8540410804140d00240300080c41144090050b04e500c0c00c1e1484880c005c0b0301000c0c9400440d40c060208540680301c0c0c2c411004400240c0710444200d991341c0c0706218011441210301166516400064559818048a6a422a813620b400141050400002940350409a500000182d0b5801300030100000800401d40506182d08105060203c4082c90044101d1603040040c1022140800324182d5104c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 690922338 1250 690921088 690921097
    0x504020423240901060315150509040504021c030810050f030a0303020f070b090d02010507080105100e12030a1d18061002070302090c13091109090c130b0d0b1f030b06 73
    0x3090f16a05503550503008024110010b041102c82800da0341c0090064014540d0000200301921068100780851041000030a40180705036002109200d03c0c400310b1501c030441001d4603110b80c9695001e42000c49041c100c04520b504428002e403007440c3c5031001650b0000c1c156204503818503000d81d0f203950342c0c0c01008040c016440c0080c00956004244042150042030305001e10801d40e000308582c0c1c6e12800c00300c07a4042c0a200f0281c000c084030503244039252181820000d15080603105400c81402c0400d400c5c595031060300032900041c40c1003212024405080c00c0c0f01ca21600c11200104c484055050f414030090b005045548111440d4800d8040325000344540d02c01183c0092040030b8500d45503074a058640e20480340c041c80c16140010108a01880d03106049020340d11184d031a0412000030140500d40b000a41030340b003118828006240c4103050f005015010b0098504416240d00c540c0044a0507241243d5200c1d114071684101416020301c0b2408900e0240290318011400042d41c8002c6003d5128 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 690923588 1250 690922338 690922411
    0x1608010320150301051306140f041b030b0307060c0b010b03090c090103030e01021908091915050405120a020108061c0b040b101205060a0203060f03100504020423 71
    0xd9800224400b11080e030083c6040b508183c901d4606091008030f02d008a6602d4029078484101c092000030981c1062aa034021401d006400020000f105001c18090074140c80d00102c0060346480c08900315050600c001c2000744642d0902404811071a50b51441c00c0c8014001c0e02d03a00744011000a402501c1004005500350f00541074003801e503140d0400400c1ca2610f0140c99001d8402c00c1982e11030840800000584030340c100e105c0318100030b2044100504400c20a41c1d0700c142440000f07000c100a003440c1c1c00c03820740340c80c2c03500d03284c0d6964a08414401040394070030080615400c00541d40015236002420540c0c045421100642d04500703070f114992640d01e040c00040d003542c00740420001084011700c60301d8054503482e281b05003450b90301c0c02c00c00312a4054081c001d005400007404a0381c00d65068002d9600207030002c06600300c450418010074504400092007414041d06c1344280800d50401d48a03071800303075040c0c1089440d41c0720fa0b450380e52150080600015180081d60490b80001080c0030b03442d014500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 690924838 1250 690923588 690923599
    0xf050906030411090907080a020609030a0b01171209060306130e070f090b09010812090307033504060c080304060f090c180227010909020a171608010320 67
    0xc00c0d00f4812071444041e0b07007250050300d0080200e440700c0000100c80c0c04503406180100340c1a5035680c00d01004d900500382c42034042c4106e0000d000042c1e4504202070282580e00030040b0029005203010340b400141c5d11003025850700030070188003140c4035102120752100043d5181340030840e030640002c0003080c520301022041d00420b44041001a0340354000011a600007a0610410752240704100741400284030382d401e1a80302c003050010304141c01015040c490002020744441c650b076502c0307038040074490788840807491455080070401d112400303403040c642080407107005040a04000d0080c0c00c5405035040500440004400101048216004200d07400341c00c4e41c090201c0038485c500488100300502480081907481c01a441864a492003030300c2d07030120b8649165840000b20b00290603580c1d0200c0c1004d0412486020200f0112160300003000c4005050751040600811516000c6000302c0c050400e41c1a0280b0000102c4030503449440d05041d00e401c048200504c1e2446c079030b04440c07100ea82e1560364000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 690926088 1250 690924838 690924841
    0x1d010207090f06170606030303010512072c13020a2702070503091e090c0c012022050619111b100305040b070809100204090606020d08040c060f05090603 67
    0x90581c00c4076088410030f014165554003d900300c517448980843d09990540c0c41440108014504451744d075400c100c0d00e101fa00c281c0c6446c0e2808100039861304401d0100301041c01c45100c50040c901040c2a404081c3e10880c004135402c1c3e40c00102095040c1c890100d198001552040041002c00d11503000c03850b803030004565549061625603120b40001c04035074419a45180c00c000c10181c02c0d00700c984c60148c01002080195a80c00b43c030f003125040344100480c0c5641e500d8448121700220700924041140100c07071261600b6801c54402c00390404580c001a02c200290303410072850702c1c1c00080d00d10030704400394044007001c1d000b40c045a148007901600042d6128050b161104101002d908082e2540182c6021b6000b450590054003038400c01d95006080b5200b802c00650001d02c100181c642100d404800c1d20192616044070809a0308207410001002e99261810017a081e0104210641c03507010381020a22440d19448111703520342c09118000c20300c00d54464186000d4800e604844a1110040c01a9100d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 690927338 1250 690926088 690926111
    0x8100807030c05010809120d1a09130b0a020c0c060c0c090118060e090a110f04020711040c030903050d0b150c16051f03020d0b0307030b0906070804031d01020709 71
    0xc082441c0f04407400308600c82d006c10929500422400c8646000041061400c04007448840c0107043e010010840c8500b2803400c01095602c001480780201c60500c2d450180b01790030b04101c006000060700301c4450520400c8080106803010078a4078240720202c6400da20703036070500007031810b2804d2070680d181e112440c1000815542200c400d200760f0700410900c20441c40c2e440b1014102559029180c054017a84207800080000751180d1755218418400341c0452144030404000c40e042e030304140d00c102e812518424190a1a0806228801d0b0029244c030701401110025280608a4468001d040d2402034540c881950700f510f4007100e00c45440480c46019507100b41414001e619810300204d88243c00701904400a00c0e450861a10707810389189121070306a64403080303800c2d4002c0d030102889082c0240c540075001e98665062101340c0045014006201407860400402c608006004003070b1018000044244004a54881051440c405401c141080a20315400050b441d050156108005031410108003115 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 690928588 1250 690927338 690927353
    0xc04090c080a050906060604050904031e0c060b0a0f17210a1805130b0a030f080c19150b060d15080c0102150c03060a03150212090309030d0810080703 66
    0x1140c000c2c08402c01507521050909038444c6002d40310241d00ca403040c00107000da46821480190458824101401420940e46c1d5003010502956608004942c00c40d0145082c00716034000c800a450084031151403450404212610750909400380306049410920000020780c0108001d8980d040301c02e01c4040c1c0501d82c032800d2101c0b507102924034000102c04c100c0c11018003442445600643d40001c06030810030101255080040c0700c0d008250740d004210440000c08541048440c0020f02e004207d0a039841c8907410680e031070004500000702003819520048000305400c004446200080d1200c00703d411145030002070b80700e00580c000409480d14120170440300500103024070044442941c203030b4203d21780329001603841c3c44000c000369440402c00d10005040d1884080110b0388034400078101e4001d2500d907185d0094208403000f80303644a950001c0c1050707c0c0e80d0030004a5601603000fa005614000c40c0300c02107900c07180c49040820511810001051103210310300d0491000d03080c5034080300c0200c1d6a070b042119 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 690929838 1250 690928588 690928591
    0x7060320040f090f0c020d12090212010204170d0c06091112010510050102032703031207090e0112050327041812081329180c0103020a090e0c04090c08 66
    0x50309407400c4d10700005031407140908100c02c44645c0180900c01610081541c40c3c4584038028056590303512090300046c0c3d13804007126209025a40016240c41c00c04900c03600400c0b00d170a006803258000c1014001c0705074040c03203c484031507008030301050040d46840d0809041016441103503101c6d070650111611050154001d03845034000040e00ea102d82d0382d84006a8a80c440c0c02c0d00801a0004421f600071140180307010f082404502604403840c200d41912145034845040c2d607000f00050700b04030204228208401c4642c050030015178800910108c41c2e8a07562b481c86a4040c9030502000c120300c1c02070946080003002d4103081e000c0c00c180080c011500000912109071074048585c0754a14001904a51045c00071074030074107001010544c040c00b9034031a060075207021003000d05000b03101468490140144052a0300644e44296803444544040c04580d09014620340d034541058414480240747d2603018071494100c82c110b0030250360380d407200400c0d06a588510f0304481c01c030034102100c401e0001c0d40410031781d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 690931088 1250 690929838 690929849
    0x90f0902190b0403170c0f0304150f1e0c12090e012306030a020c01020d320105010e0a090501030b0601090e06060904050a290a08010204050307060320040f 68
    0x10080c10710307614458640401140540c8014450034003007400020b400c070a0001e0380c44018181326080c00188460189080101c000450711600041001c01c6081031242c880711038a24142041c1c40311000030b03031001748000455006122103c101c2d0705031150310341c012584a142c140c0c0102d035401d01c2c0d070000e00c800f4042440c180305604040d0910400083e6401c448200a10320301041006002175890300782c2000419007014020003102c0f5803c0115104071034007403004003200b101115011401003030b85d00d030110403801d10f4030584018200503181202419059091241550030034200500507148000209000d2a0250000080d55180c0780020040c891122540b5208050903a585e900c640c2c0c030355280c43c90041081e5100b94001509201c000a0f5181c140c2140394008500035000682c5010042003104a000300b03030404003d14986050861603041a0001c48050680310000f94941454100440e54038419880b4007000c03d5a0741540b40d440000c1c1e80e5074040485071800c00e5503183c80c0c81e03209072080399100c0d2040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 690932338 1250 690931088 690931099
    0xc030f1602131a1f08040203070f0e1009020c0706210f150b12070c0f0818040e03090109030b25030c020d0c1208150d03080610080606071b090f0902 65
    0xc1801c507151541102e8000b00010102c50702c4c0b441c0c02e49058584030390103042207905009072400800e441c0990903807540100309030007851045042000c00b1325442e600f160401d1849a0040140b00c4080d1800513070f240c200d42451400350745968501c40499070b681081c507040b006c0c481c01d0a51000100c010303504040c0340490f020548000003551200d041003148614cc0810b841481a4000654101e01649d80810b005010b00241200d040700341da600c00740c41d481140001c0451b07442012580e114100f510984001c1507402c801107181c0030070074001a108180780c3c800106840140300c00608990411284084041031481124495a400000160180a0403025000144242101c403001e041c424403085013019044007003801d0001c000b040441e5480320080089002c00d200105c401d440d82c4489a41a00c1603000c2e94032504982444000c00c0541c18079130003840e00b0817000d80c0c1407080d1541c0e0b6500700d50640d580082d80b201c000200e02d041c1e400c0018140e203c1c051161070009000d04211003038100101480c0708464 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 690933588 1250 690932338 690932381
    0x1303120804030807030f0626010b09013515190507050f2802101b020613150504030809152701020c0105040303140a020c030f160213 58
    0x60445140c002120054002401c100c0400d0b5950302943c40000321044107000820142d48440451007401140d11002800884810131900c060000f07100b15101590202c407101e2603540b400c00c9040da00484450504ca4541c00b105048403c0444202c840750000884400e449601c0300040610304092406c03034002d00c000000c2c0100c1c0c1100c81c2e6912a240c070504864031164100350140c1c0000b5525005030341c40410701002c113144100814504001e848038007034154000e0800210700305158050f00d044201f0900303210102000d1020a030707004501c09078045489070f0801d002c00b4060511442182240307018801c2c02c0d240400b80028160300540c103d11617982d181c110341003040340b1800b40c0c40e5000c0c1103c0f035104003501c0003001c1c0c40664a031803604100d8608000050b0074140140d42203402c690050b2000c501095507800c0000e03c03c2d2400e040541d120380200c070118203060403031140380c0e128070600185000b05040041c1c21020381844601c610311181d00a44410900b211020000004050040029011006015 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 690934838 1250 690933588 690933623
    0x3009130c020d0c0209011223031e19030c050d060f05011e021e01020c100203060f151606020403080c010c020609010b0307030803100b0c010f06090513020d02151303 72
    0x2485401c441d80c0070303000711441d070b1810180071200d96240404036408c0c20880340d030340c42800805002d1034441c641c00c0301a584d168241041d400f07194407a01c0c2030845018043c00300d00c18159080500942e00030007401e0120300b00400c14011101807050701c00d0003042914100010801d044485210000da03482170300c41c1c00d07407a10301e0860315015003400b081c1240140e025070348120b005401640154001192031001508000d2080105800e01d41400c1c445480c8035070200c100800e91400340241d02103018103440008501d07000c41e00200d01807288510000c02d90b5402065013080040a0f070440d0015500122070640b681000f1441501a050250101006214040200d03206607818807031560b911100030000c1c0780781803440d07456900c960801052003991043d8603c0009402c6c440030020410405180000182248542000d0040f02c0b07841d000036110710b107040e0802169450340705082144580441d14409c1008651000500044481e0420031401c600425850078880d502030030170003a00d11401001882ca400c00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 690936088 1250 690934838 690934847
    0xd06020405010e180a0905011e051b03040302060a0203062b0c09052206021306110d081b071104060b120606191b02030a0305070605093009130c020d 65
    0x2205100500e0034008081102c1582c164031a005441c1320340300119010b007003102d0f0802c9880c0b000c2d5442c4055601c83c0d0401c83c0d0b8240e140b100140c21960b80884bd411410580c03002503030303040700401d043c0c0002e80c004085841651410710901100c2040d40e03008221002c401002c0c4c046401d1104104e60320a01d10030701162881407401118860111080016203071442c614141d41000c1c504034098810b61307401c000607820340ad40030941d2400341030661540c049503020700300c0b010720f01a88040c020007080703040d03014003150855810305070701416041f05074240c840405040074403a190301d603c403c136031142c40c245d000910600d07441e001c0e0403500c90f018420346055980304180486807140e800300c00c1d0004004028039003014094685007109081d40082d0403041d10711640800c0c501915000140c000c41d40204640e4104100c600800344d020108001810340c41d0b1072000c240c1d0300c0031084043c91284034142c040e10f16607602140c1c10340710303a004018000408104c0302d20613140102608600d620050285a04c02070215019 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 690937338 1250 690936088 690936109
    0xf05100e094c2903032502090108010c110c1c1b06020f0d1103030403050f07050102040801050a1d070501050c1f09050f070609030f02010c0f05011a12070306020906090d06020405010e 80
    0x41d0246103011800c1148400310386d80c1000400c1000754007000c0802680f00d1a030f88501a2102e038000081104500360050412001c404080203680c1c03010b0b00c3c2940589500708480990305140402c52203401403450042400c400d00c03045032004042d1010000b510b258001080d51041a801d000e5412150030f5003422030b07645024a660f109150306c204042030000b48100010400c43c003103020240d0030030305c0b25070310070303007a43d01ca40d1003d03c40c1d80d12207080c0301461110340714801a625178410b4556248030320b01c00346612440244aa03034103022002c90303031860221007441203008288011141754100c980d60380c560f00c000c000440080c5c030144114000020040e40000d1320306d080e41c0b025140c8072481c500d569200c60121000700d00880c108801000c0140c00940070861407681c00348944008204e405503244005a002c0762020528450ba200544c040e1600e40701040410651fa0000c0340940e86082c1940400d00910a060341250031003204074450050250303d03070203403041d01c6003661020300c11030355001089640090f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 690938588 1250 690937338 690937421
    0x611010c0207051c140303040204050a0e1005102d0902090105180d0f081809131119030f0c1406040501080a0f05100e094c 54
    0x2aa070622142c51300143c0740356040030300b4031690354800f40c03940c980c0700c4600e40303010302805540080180f204626140c01419440300e0584020800302061445160344d4900411203070228686d0392001c60781c401904650b4602500044200c420002410200442d034084105400c0a5400c040d0b940800c030041603000321116580140d40300c0c4d05200d07101505083c03c02c981d03000c070760788203014030280030002e43d190100702291400766a41c1c545500758003c0015100c0344000245210b00f0f1454100105910810300c90064107070000401444029031002050031051140ea803c2e0b01c041c21080000f041124040d40201501d2082c2c2c403182c2c8150780e4246c2c0f48400700344002080e600c84414032060040b5442030b02c41603070007000f5610104401032803819030f00480380c3c2543d0141080340001e1050000039038140c1c0d1aa0460280002030194540c841030b0b00441d6211001d15220283d50189145002d5a6003c4460f004003030000c400780072141c10521242c001c000032122503484102169519215402d40301c0c82022800 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 690939838 1250 690938588 690938593
    0x3080f060a0302100201022502040c0212041403011503060506030d031b120b04050109061a03100b070302030c0d0302030105040e03070201020607030b01140c0a030212030c070204050c090d0c0611010c02 88
    0x24215030130410450702132184103045650a100c042ca0b01c840480c02d03c4100001c90101c4112804940140300036207810a440100b95440480b035840e0750b80f8031604032000c503241407280c4101c5803041c900190140905614440d03080020200210601c00765a1040340101021010cc4a00c0c042d00030058041d118603144510b9109802da550008550003103400740c9404a10240025a0610820018040b41c9081e080340350364540c0c4400610007109011058804c1d098294091411b6180c180c1c3d25080305003a6008524134400c0c0030a00c03030201402041512036040031941540c00315550b90800030000d420074820188100d0400c1d481842d0580007100301c8141703540603400341425540740c1e01d00b030b00903001e000b001504100c046150349d180040030300c003c1c20980c00c007600a04500d1089003002407800800300c440b50142c5e4000c20030b00c850034002d0011119038580c181c03000306a558503000346400398011504207503040044040b00c2c000f0801c40d40703d05020395005842d034040b11400d1214441c202c2e102240900f0250307 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 690941088 1250 690939838 690939859
    0x903090415031709012c0109090e06040f030c0b0f0618430908010b0102010612060b130e010c08010e09300c0303091209010f03090c0911040303080f06 66
    0x50812000030054a141810561120700118042000400c1085041b0300710032884003640c80d0a6900048041c01844820014000d850f00760002c02c2c1c071500003400c002e14000701c3c460594201030144511554481d0400c02010561401704c4014203807001c1220054800e2401500b05001103440200c2240200d02502846007442c101e41340e00420003440a5880d20250382d1040a0000c2003221580411f10300215030b03810582c2440c00705003e00b510060310661f810759041c15070034400c0806401d036401d441038000d0804102c050742a40824000c0c1020100781c402c050608012400c00c00741500101d096144a40d1245001da03038482c81c00d022180700b80c1d06012940c0040c0c034118400d005240f02501522541d840c0807020010410800c9681da002041c0840341d500013104110310024140401242c56640c41082407a201009000030f00c4c0c1c13805114004107040d5220711540c18032900f405030401070440e0721410040c092031802e5045958001d031000f103001820101c001250f901c80b259459018000c043d001005030f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 690942338 1250 690941088 690941123
    0xc0414040c050412020f0301110c101103040f0c080109060605030d0f0503060d05010209100c02030f0a03120507110109050c130b0901051203130608161106012c090309041503 76
    0x103480f40c04d4040e40d100c2d0070440420b041c3e40c0c0078411710240c00114000d0300d030b842001303d0040d82000e0f0715034440d0301260f14090403c000041c81c1000c89910960108800350301c10b01c18503001014032541c0c1c0005003e0b40ca41080b0748200900c560100c01610002c90890344503051a4204554502030240d2810000c4d4062001c214039041c40004110791910034800541010401c20100d401001c4010a0000082610a101096050902c80c0c6031502003a400608500c0c03405071005810f0000b00360386160345990300c80010300f10303d01c5501d10003422003008000f80320018150519641e11102c07900c82c00d2203041c003ca00e5200c200707442d00c20b014881ca0060165900c1d60b20b402d0812080c0003d03000030706040c1c0000c001c60241640302854500c090009500c685125040903444c220404020148407424064203a2020380c40c0d40e4006a441e0448034420012640003404101d452000030b2a03510003100c0d0000ea00c1440700c20000400039105955080e503082109140c1d07400b0541c05018036210185c01c4020841c20b4408 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 690943588 1250 690942338 690942359
    0x50114130f020915031503060411010e01030b19230a09020c030906041d0a05090303061203040f06030b09060d120302070206090d0f1209060f21050c0414040c0504 71
    0x2401d04211070014200140c1001182c1054040b0900c01110040003040110592206d030481d5420501a0000e2085140c1030f594510b010b40100c80c6941445100c44118000e68865002100000700142c5030710440030940c8506045032246000e20600540605c00c1c65000103401e03031038141ea00c02d00405007045035150441d283d0003544030825582a03408100020099601d400c0020700060621700800d4510308100d100d48402c490001d00300302038850528052007450134001066a0704141708540e80d100c0c46c490551810700d54442d5600030b40003118540740014000d6010391056500710825500a48250303a040c0c10400c0701e0503e00ca00030010010b01425003085403007940071b00b4880d0f00c0603000900e015840c07000100f9583c480803088070907900078880c82003003041a1000181d45220381c10325044050515070098860707800c111240081110b0f03034a000100f0f4125031005072089001642c01c00660a150209580070362007802441d8000340455a4040c1d0350800344104100d0740c034280c0e103203405c180c2414810318 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 690944838 1250 690943588 690943601
    0x120a2a0c11040c0207150305130b06131b020105090c01020307170c0a140c09010302060301090e01090f0309150203041802070302011d06010617040b070c030203040801060806040605011413 82
    0x4030701400e000050042601d03180b103003804000b42d5400900219144c15102e0b06000d00701c1c15900105800c00c814404141da4840150a8241d400b203060619135681e040131a94116000c034951f008241480c500540012040c1d000d003002d800507500038050b60741c3d007030100b9a44402c42040705005910402c01c05c400710390b0703125a000c0c1500514843c2494102913100061500f50310660a4070b444100786003902c201c50041010358441407055843d5441d5614540000703a4074007051250004041d181c25400019110a600c02c4500650003500c4482520460400820345003913130044640043c401c20303100004a00001c2503400b140d11740104030034000317100040400603400140c411000d542d2180d641406481151100381d566201070802009903600d0000e00038280e509002c007403004450311800340004a04000304140d440361090038204186e19103071a08038614841c03903100711065480c1c1500450a030401144c1e0305c0c0140d01503a4148810390725441a10341181400c5040355004180c0d00c1480e128900d181c0081 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 690946088 1250 690944838 690944843
    0xd06050702120a03051005100f1119050c010806060f0304020f061c0b01032904180c081f0b0d120201061e05030f0622020d0602120a2a0c 60
    0x80300090b490141c1c20445411609019000c40e07155410001e44148a125a2000f44005c48404441000c0840080c11036420b8480101c10059030702c5144848041c01c01080b07030200404004d61286502c5410300c241c50300d100d420380700d0028090310302040c550702e000700544240c54002c42d061442c41d00c0d2603082007000255907a4a80cdc2024050152403200b40c039102e490035000300500000b15210000c1d000040c03ca80c0c03910f206803024480040403640d4408910f288081038803040d1000138003460100030a583c1c01d41030901c0188001c07401000401c1d0001d001c640b0021040442d520341036482c410004075025030b4241c40302d15801c1095590b0b078401054580d482e010704950140000100d454680514504c0400c8009040f600c102040204108500341080200e4900f84150064201800d1180d840c100800c646420450a01c0c05400c0400656440c00d940c250110391080e001c541c0c0300705107400031591500c04c40320300024610b000401040000005410300c4482001c2d10012a01030582405072920100160f00703 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 690947338 1250 690946088 690946093
    0x6100b0a021c0807090602030a0525060e030706051005060f1b030412030e0612161403070801031505040206092713120207080d031d0d05090f0f0d06050702 68
    0x118240301a2060301c0e40c2c2d000103160780303d400902c2e040d440942072041c0365104c1011984104400301481c0e0b40481510400805110f0b00503a440410b0004413450b2a100000b400342442c0040300d00781d118000004140c0544104820700050352510703620310003903000f40324580d008441082004480440c11000302410103046140400d41450340c03865500c2c1d900180c100c528000b00c5e00c82c0c460280740d007200d00900d81c010100c9040e0315014440045420105d405865000c0540d40b00d45140d00300307801103c2000300d030080f540040340c8030701d000140203103503000030703c010b507100700f2022114030580c0d400d40941486030343c01804541c40c1911003018461040c00302c160320f203080b1001c601c824030b10000100300940164440d2018000071045400c110004a0000c6018015507104110402004401265145800c81c05080005003c21100c2c0642e43d04c82000580031154060440d184401e41d4100c006803100d0744066070514071080e800b106002500c1680003c5503485600f5101002c0002c030141c1215034419414810b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 690948588 1250 690947338 690947353
    0x905090a0b090a0b15041107050a030e1f02030a03051e010b0307140708090117070c08030615030f04060b06040303120207050f0f0c0102010f0603110d031808010218010206100b0a02 79
    0x214540883c40076130308079400f0000b604042d0654502402900c1080307d0070551a8900500da56403039665504640008040c0034134000140f840c1ea803541e0003e0000301c0c400a00c10855800c541000351660702071305680021030f1400e408240c22101041030003402c00c20400e8440441d0742040400b4403141c000900c8642040181000b0b0814500010054142507104001a60300e4211000000d040680c85101d40d425141c0000c2c100328210b580031600812117500206183d81e2a01c03038001041c004905100000340d40c580020038041200c92500440380306500400c400c1151801e2042045901e1041d80f00140014001040480300d102041d4018148203108204450900c003954942e64200004440d40041d13540000c40406032558084c061a942c81c410380c034007001002d042d561101209040c1c032440b540110054261702007050b008084803807140c07002d00c401da03106907550705005001c1e501503080007950b60590002030341d09500020741e0302d01504007c2143e006180c00c18040080c40d030009100316085104060 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 690949838 1250 690948588 690948593
    0x61503030a031e020d0b04060b0304120809010902120c0109050406060e060d0b0a0b0706060f031205160b1302130608030318030d020f040302030f070305031c0e0313030c0905090a0b090a 81
    0x401405c4011407a00b02241c200e500208010032985154408641650100100000200c031850340070980c42060500f10341940380c82c002c481c0103024446000750440384030074480c0e01103a40000e0190b4100002da0b18040015100d4084c04103862840c81072102007021015200020b191160240010588034500002d4010307114000801d00f08865020940b42400040e44100f4840d440c080c3e040035100740000f40a103140303540e4511010351000000107003000b02c00300da18a003040d500780e44106a1604601d80302980e040050b0988000d44071810104d04c240e2074040b0341c2148005a029420486d0703159009981142d40d480000d28a442c8401c00c10100c3c0d01041140450611341480034001c641980d030203c45e05c4508620502d40b034a0030704a81d4050350b6101010800c00100d002003128055031303408988081802d040035000010300040f01c410320880c000800d109240c03082c440e00d440112402030402484c0c81da6101c640000715207042e507000e942070308075034240d00102e070321982030a0b0088807270011644904901c0c0c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 690951088 1250 690949838 690949841
    0x160b07030b100e06070f08091302190309061b020102030106030f0b0904110117090d0f0e0f0613030c0b09271b04051c0c09020a050304020d03110a0c0602061503030a031e 74
    0x40c000722447e400c0420b02411904100454602c0c0800c0490700310301c2c02a05c44900859500e00701202d50030142c0750361192040108982140803403002880e80f000c2c0c0d8a1103800082d000c0c0d0800d008001c00246444880340081c100c50080754603620b005400036403603840d60307141e52041102c402c05003410300c100880c0f02c00301d00015102051240c00404090035100009990082800b85030b034424100300506c61310301103a0303a80c402c0d0140c1400c050480b0032030350f03800d0000022007010320b1503480079040025030240001c3c1034051600407c07041d0012640545809071440740080328011441e07080c0e41525658000414440700c40e8a01503481040401c6182032a80c1c0c1da000a0a400ea18071212000d00080c060a03c10000b60042903c060108240c080d410315070714040040a500000784064031618100000200740741c00340307180c2482d0b0080b820640302c40846a060403125050f151040314010300c6550001203a8602845200c034000d00000e02440c40d20b6031074035041f005820481020100091429016103015486 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 690952338 1250 690951088 690951113
    0xe0a02190c0605371e1b081e0612120403020f090c03010b0d060e160f030b102001091b06030519050a1d01060f0b0310050105070c0b160b07030b100e0607 67
    0x141207001c00c1c1c0074689000c0d81742c6c1000902c01441403150341c10a04c19202c0c0c4210501d01201c5600001c00103660354480003580000a6880c101054020401d40600d0a02820001c8c81524000d0301c0b0b101790000c0540900c115910200c032002c140303103010720060094000c100d00402c0d0040403050045442501c81415900e07079001500e25541420850000c2040c1d0364020f10818440d07803240c14108102000200801c612002150380c2008116181c400c5404049034104034034280741e1240001c0054440d54900f417600d5004407200314002c45400a0000f455038402e0080c68400e02042d00b01c1da0340055800c07000340260001800001140c0d4985910b011080482850461020940300002c01c00c54035046490812010980049107180001c108004c0003c525100c1c030f40840d82c00f840d00c682e4450702070903c805900340640014030071050010341403600c0e003070300403203000114007d1081e100c054680c03950540490701200034041e008000342d04045d8005000340141e1543e0700e0301412003440d2405d0360750360450302c144 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 690953588 1250 690952338 690952391
    0x90d12140f030105010e04200d020c060108030705070e19020702042022031205031b0403060c1b0b180718050a0c020d090e0a02190c060537 61
    0x400b2004018940c0e010740405c0c41481b05580070002141c001c215031241c0c0071040f0024080707420000b051010703000c10b941102e0303812031148160b072481c1d611501400e4980d48001c0054a141c411102c2c0401d00512003040c0b50300540503140030b40b010380012060100a07400142c0c090740d105603280e10414031002881c401404240004101a035100c0e229402050240240c400c640c4c400030424005100280901103141c0c0943d4070f5081c4580c6999400750001101ca045d86036040441c00041000001c0188907007201d4051100d58a40800032112580c02c4040c01035500740c080e100105200124603412840080164000465010b5691664442c0c038207480070400000c00d01c1550f07a0b1101000340320155407117490aa80c900340301501c1c10700541c40300100260010b020303c02020102601003000c40070b056046070440c80d00841c142d07003860310710300b005400e000480c00c007520305d1030510000400661121011859000403500501003d2100074600c50f00c030f0f034400100ea1402942c484084410000d00c040d01c107200340 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 690954838 1250 690953588 690953617
    0xc0103091a040c0302130c02030306042c0a0606090b090601121113031b0303021005061804030302033106090c12080403120e092d010603060602070506090d1214 70
    0x51561040c01030342120151102c06c02803070500603a03000d80d40801187c0e001041103a0204401c481c0c83d0820700ca07003405006440c66010605d10b006071289011889406890060b2030410030190f5030001c01040c0c64254010641c00322190300011403540c0a8482103002041030a00090718241d0660411000c0d804040a5038042d25009003c000b0032080e202e0b650103080c2c1c2c0b898690003040c1b855901035070b00e15101e0b8006500303640341c0740064a0350304c96684501c01d403071590b03004d9141c60a04cc103000d8002d60040e140e0402480410480704021502c4003000722a40c0701c060741c0c881c0e104c0307001c0e15510002c0044640840d8030452141c030016245c118041004883c50280c41103580d600d207140b400742c3c540c0344c898070408103100c28400102c00903070b58005000ea110b8031002c03481c0006a41050840f0224082c42c26010b0240209070000c5202c1d6810760001c402e550486e000c4450042d06d0b0003c06c0796900800410704c1e03220316a1002c12001945440c2c000288605505040b03c00f080c00c001c1850380c68121254a0601e003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 690956088 1250 690954838 690954863
    0x60c15180106080102090f24070305090f040e0d0f0516050c03061003030503010909140d021e1c200723040e07090506010e0402030a0504110a080c0103091a04 69
    0x3030300a210782e40050200030021490b2205a001241c0c038802140030300c500c5441141d0050740c0600c0640680144000c08100715603507020039250280103a040412402d0191081c04901e42c4a414244120910711102000510b5520400c040440d1010546169282081400d001f080580061444141200c0e07110b14090091b084281c004d042c500b00000b400020300002c180406c0010a800004481c1500c20044010a107080c01d82003401072000800e00080c003600c200301014003280d601240c54402d00c071a041061011000c580386643c0e5601c560006124904000215000300601844946042c100d04a0015030b144013000c0315a802d242d0310303034040070715180300d200800315082c0510b00c040101070049508014114070f05100b640d407a4014000e01500c030b0354920116410740c0c05417180d50003101008000703540e130303141083c0f03d6006030505641c1211000d1440341d004040345800d5071028140c41c4040c006004a05084004602400f0401425100316005490b92490b24200c10a044d2003140035001c0c00088 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 690957338 1250 690956088 690956131
    0xa0f0b010303030c05030f0403030b061908010338040302070b0c0303010303030623100e04021b060604021c0b012c030c03120a03091b0e0708060a03030e060c15 70
    0x151364060039103508101081040003d03c891080c0d400d9001500f510380064010b0b1803d01090305441455200604050500303000d061042e4410f1106060b03d11807040080c03130801003c80c40413056200c1c014142c2290204803003040c241c000b132400d150302c1800b03441103601042c1d4881c5c0c2e42c18158030402c0c8104d001d070400401030046c19050302039000100703607500070514102c4800140c4082c001c0d131040064031445100700d00445081c403c944941149800500c110760740d0703d501e106240445040c00c20038059001e039500246551a1134820785e0343e800c045802143d00000c46403d103400800445000c039040c015140150305004a40d8110950b20074031560740e10086480c03440405282c4045d240c82c180c403a600c144060041c1100074004e0798000015420040345245c400d19006460440b035008041059040740300024581002941060084242c6d0300e030884a9200c0c1c006110440119020140204551b078008003d9810101c005190188001c0e098484602400c0c101d51503000050720701d20b41c0d95441a003030005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 690958588 1250 690957338 690957341
    0xc1101060e070e0d06060509090705010e0f0f09040c0e13060e0a02010f050d020c16030c060903050604110607060504110f010201020c0d030e030c060c1b0609120c0a0f0b01030303 78
    0x50803200d00400203620340a007000701480040f0310700b24003419168000d001003000e07079041030300600001403121006191813010b05688004503c0f03190300040c02141401c2a60804022000d83c0e640050800d01c40003c0190600c0401d40c1c001d00100e507203c100b00000101c5100501c0c04601410340e0010320760942c22903040810a46840381c911501a4205204000040c2c2e040420a80e031210756080850b25104402d01c444020301855a0519241c01741c40c41c41b90b20080054802d17000c2e41d01c20000035030180d440300011206180a8040241207500600114000c1500c0140907044a040140103502d01001a41d82000b0b40c0c0058400701d5880c1e000c4144039441d4a004803803101507070340c00e100850400c54180340681d07480c1c84a5020505240c1c0c0d40d2a407220a403020b00c03c40742d074940c850045440d10305001503592038642c042e55084c0a0801c003200d4840400002050381401000180000c1074502040700c7c010f60241e221800c82c040c40d00c14094018000703034107001c0303000701c19000c0c5041c5c2a0a40c95800d0160 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 690959838 1250 690958588 690958601
    0x1d010f0203090c100918141e04140a0b01080609162d240e01020d080a15050303220f06054504110703080c0903150a0902010e040203060607110a090c1101 67
    0x6129100c15140c100071300c23107080700196000b504240429100003158003900e05001c0e0030308004c1e2803010381c0400481ea5030310000342e090117900d5010844107003503049440003100c0006809500141d205841c80d00145810480c00c08410031002140c0544441d5078140280c82c060301a00000d980400c3c05007200030060304110041c0b00074cc0203001409450101c0d6000130a211b5005200e0721030503948880f1211114041c1100c80090b120144c103c075515103466820541190881510a80c0020a0000442c0408805010348219070264880f241820803110010780c401006403045140301d01200407031250034010007620000c011071003111072445640e18003031100b030740c0a150b41000401c504010010010394842d400651044c1c0c2e003183c00da1507888140009060410510788101c10108070320a2102c440300d903620110308240302341c81d01c4040e5450081400282e000072115154880303014008400030540000c1111a4003400401030300c0b6444d280c00d400d9088800e00c00030200041c803800c158855201d02449202d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 690961088 1250 690959838 690959851
    0x18030114010b0d05090124030605070c1208070327020a0909080909070e03010510061722050a06020a0f1103040b0d1a041d010f0203090c10091814 64
    0x4603075818030680103910312481d0750202c007550f90b54001410384d11003980600903006014103030903403507403080c1c0d80350320694001e000c243c07038a92800c2c010540107402071281c03503101a80100c21003000c2c08496415a84044001c18072400c0c076031a144179004235410242440d01c109201141c1550f214024010300188041ca1b40003140c02c90f191070b20240110fa880801d54102c4401101d080840d0755426008642080c060b02032140c0642c206010b211140075001c41d12000d4031103980e210b46c3c03406601c0300c00030300c1044291580640004480040e035502d5001462a0f040c4034094000c84c0d2007106641d0f20039040f85c1c0007041540001d141c4481c07100e0180c4e4007425a000d01c448660080d401c10307081440100031031040303041201c0082d540300d40720124540100040d41c0100300003002006001c01c100c0801104420500700c48140303519002c1e4035581440340e0b00c2980e0040c0c3d0140010000131b04074506102400c50041909018844c01c000c002a807100e01509080d01647c2005011564024098002da00b02c3da0207444d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 690962338 1250 690961088 690961121
    0xf010218040618020a211b0e0a090507170408030906010b041404091e05010c03050a090b061c0c0609150908211e19020a0b0103030807050f180301 64
    0x3044a80c40c3e2941070001c0203400403005a681004010959a0f0550302403000440300d28103142c29494036a952090301c0060101d0b41c0580c100020031400c8502c4840e03000503d5010039200c8042c8540103080d0b0091b41d0099007800c08681852140141050b002000c4904844500002082203265002884064010030344401060304050910b5003100710b002c03c95615038010382d45e4242e81c0342404074850502100c4043f80f045442c1c0d4417442e0510030701030305088022002080c18900421302050305807040c13141640e080b0625080759200c0408104044200c2e030b840210440ea0340d0321880128032040030a100900b4a5114022510315103451307404c6480d074184904044c040002c408102c001c3c0003250f04044200289590620007444885000d900d004050416101000401e2882e1441580000401d400c02000c5c1c1e102070701e2003c4603000c03a034070140c8100080c0002021001040024042c0004a40144441c01c10505140c561101c1c400a03402680b034141804c0310003c0203404030704081c801e6041d00711042d6103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 690963588 1250 690962338 690962351
    0x40812030f0c0a092c0708060a06030e01090602040e0403091509060e13060906140a0302030c10030b040504290c0f18060315100c021e01030e0f01021804 67
    0x464a5100300104600c0140b0400100000820301c10105080540041c140040d043d424021905020506190b1a044a1404000807880301e5000d143ca00d48a0300c4002c114501c0681000c604030003500703d10008290030740d2900c0720500007071440e0010b400901a003000401d8985440c4c24020a8103110794040302c01c90440b441e0030452694080030200540d54207041c00a100740007980440c044004c00202018654540f0101064a044036000101143d620703c08031700355034040c030080013601c00300c40c407009605600c1740c070351402c49003419907240030815028100010a103c0c0303a008034007910782c104c40450b00b004166020f0700011181c110038290001c48103030509070600d0703c61031280080c8941c0c80c00c0030303402c4808a500d21010070503c07904103502c44050403298507407c107414207060000c03031000300e00d2091540700000d0f26154130030344000c82002c0d0010721640810200e81601184201021a2981055141c44a26118090811101c14a56419400140c1e42c07008903c0c5000501a0f035a40309104e24103064 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 690964838 1250 690963588 690963601
    0x12080c070f081608090a06110d030c05040b13030605090102030412050d020c071e0e091005100803570c0907030e100c050319061a04081203 61
    0x540d00c1007640082288108940e41c00e000c2000d00440c550188264418000881005605005400340800a45924401ea92252400c1d035078030982c12102c5403503a0000d000c444400b407003a0080001d0348071900f443c0c2c4c41c068803811060100e80c0003928035401c0c0c0444540410803c100c6110383c6620400d0f182c003c5045040603034400102ea686440070104004021640c40b107115482e0b81214901a4000202c1304856942c034201e6032540070422030025107455021000605101040e141c6114400c83d4002d00b500c40140d4140303000610019000003044150800049036035035007007000f08820304d050346c40c1c108021071004840d198952a40b0076030030344010360111300c110124107640e242c081c07821240300076440d120060941450002160f4941754006908814070107504d070981d1101e11480350110580d0108420241140d00f96003039040548009541040006c2d05008486414025440c18403004501a90349170745191b041c00b103c400a03c1c1d21400001c0400c2585010002d0b00812700ca0004500c0c250f01d0880c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 690966088 1250 690964838 690964861
    0xd060c0f08160c02040b030d260705040b130306020d15090b0315090c1f0908011107020402070501090203071d0a090807080d0b03160e090a02030c010e1311071208 71
    0x40c02c44018803480c60500d00440d81c0e02c0d004881140000780854014124080c0010400300400c2100a03101030013a805101001c12211100e1146941f171b1511842d25140c10105805076111480646c0300d440581404000079820b4002000c11214079070780410311181900c2801c2c034146032a80805485c500d012149411038401045101d003461702900102c1040d030f00c2d082c1c2e05040010400d001b503401418070250710520a4902420414901107680ea510340710380320241d89007259840d0301d0b49034505170709028400061600f5001054414410790000c03030412a607a000c80c0c540038450b04009883e6440311100308240e4603520220b503101c500c9000c20320910b901d42e216002144560403016106074000109000507a40a0300110b5500001404a5448100725500f2298140080c0610030011056a02041c2010000503140c4c480b43d8000780a0b2000400303060042d20000000104940c201c1082181d80303010501d1803240582c0c41c881000560780c1d5485510341003038528020311285081c04181c0081c0646807414 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 690967338 1250 690966088 690966121
    0xa0b100f1803020411071419080703020f0d030c27050402070c120605060f030c0102060705131a090307300305040503010504050f1b1302090f0d060c0f08 67
    0xc070300708420403092040d1008855805a00069002410103100b401441e08610060035620300504080c05041056680306854200c01c65a07a40b0b40c4407414108404108100020000d441c82801180c40c44040d40580d1130030081c200046002080e0f4800d0908445608500841004540f1098900300d00b249142c44d40b18014090107018003c5901041c50340c10400d10031001c0700074085003254003120510f40d103006030151804950041c000c40b6806051862410000b900c0102c02c00160042c000d0341e9a002021561500060303000d54000101c2c0500203500d904003458031030b00405c200c01055441c3c01d04424180f030900168440240e102c2d00c3c1a04d003019100031704020031004441d60b082c44034103503503040407900fa01035500704a03415440c0006010030441c0004009200c20802426114405a1103940c4007421080e0036445030032000c0ca1800008401455000f00030f030741d20003410f041d007103203a100110794050f200b03103421134841c1e80e110032840b4140c0e041440000b900c01c0928000c20705140c4203241c400c08614 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 690968588 1250 690967338 690967367
    0x308180102030f1201061403041e03020106050a170f0303060a06140f0a0e03010b03120706050a2c01060b0f0912121602090f070806100c0501020a080a0b10 68
    0x1006101181e2092044551101115800c580c039000100900c0100700028401e140208031b450002c940d4600300031054034400c640120b5a845840e0b485000b00300c2d080c5414030102d085558900c80441d040e80c62403010b80144c14141200d0114401402d542813400743c55031a894016401401001403681d601c4500c0d81c107a40040c40c2600c40080310374280c12040c081c102d0044944c09010a8210030207600400c90030141a00318000c4c84500320070300500da1244240ca0415102c100b04014010103e41c480e08450380041d148440003800d1030000c0018000030329403403140e4002c514501c056440082d800d0041c28041c003808441c03289045445a04050309100340070125001d25815a107d0100f01400d001e1185a1098114044e0340d60382d00c0e00f400c901c0120503400882c403441c40740000c11a0401c1c040b81140c440d4019440b03076a00e0b500c0e0b420401c00342d0860000c40d501003114100b07004001039030030300141c84017180356224020b4504120012005a8414130802c900801d540c13007071048400d502000d00055503e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 690969838 1250 690968588 690968617
    0x3020f040213170a230114040302030301061d04020403030206070f020601050d121b050705150702060301050436060c020604200d0c030b010e0705180f13050f09070503070308 76
    0x60030b1071981040c050181c0035100c1e001a410171412501051203a81030644900003c102c030501c116803451003100c040d200940107038814001444154050107649200f12034030703900b80d10781d0300c0c50400080c180e078440d0f001100140c1120003802405508414034071101d04907400900045c3d0304001c0442c100a801c2c000c058180483c91030800c440500500c9041c80110f617511100c0e10f03d440d60305101c0d13030790012840703030600540d13034a024403281301c4940c400d0310749083d80284500d240d640f80c07408100107030200c040e081411240404480f2044003140e503414030750260704101c41c0c3c8400c4603800d11508607101c8101d80b80543d0000700c100030016a02c018640b04520380d03074038400c03058001d450101e0785c01410f0580003087c907501e030b54001c010f000d2a881981d04070b60010a0480c01ca85d100c0504a426020304603043c01c40307101030050030060340782040c0300c0007101070050032400c3c01c035941c0c84418068030b1080e140030b10360700e443e48288141800203104060142805400600c52a455503a86803401d20500c0d20380c40580 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 690971088 1250 690969838 690969869
    0x1406030303040506131e0309030b0108070b041202013b010f0203071b05030a05210a1d0402090904152a14040f03032d05030c031503010c030603020f040213 68
    0x10040f11075100c0b1804007941b610307008418603d0084c054651074001035582030291000055162000240041900d403402006402c0514181e80a41882d02e844002ca0500031810210092000c00c5030b43c105800c042518101581110500120b1a5a0041200504001516104408440d0000101e4001c16404110780980c61003032403154052021a420080d418050910598103100307000a0340468100d40b94004481110303500d8140c4d009202d0a000302000c20480041070702000c2d0307410041001c1400150025150401d507000044201c4805c5404a070b110240c41c000a0682546100d981c40030951030025440c03282da9100000c2a46a03046a80d008100305060007240d145910015100107100500b0012001c42c0caa240c0500000501e5a04905000030702c000110f020445030011341110364141c48892035a144d40f042010181c3c4000c4c010302130031b031140e4681d00064030b003440f03940d2500040c9d90700000c1d91030840c0f04010f400145c51881c28860750051004e15101d480c440d030400c040303170409118041072 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 690972338 1250 690971088 690971093
    0x23060405060c0c030f0321060a03030c03030b091303020d031104120f02061315090b4014040207020307050402091201022205061801050d060504050a140603030304050613 74
    0x3d01c0e054102c402c2c0c05001c1d00d40a101c440304000080d1000c90048158424043c0703544403039440311401164610750241005008101190185080d529098000c1c90041805003248001c5075a03200c00352003201c414840c3e00c50f40b809040e41402000d01e1154680f4013031101103c1c4400980560045014030800c0c1221323044088208880142e0042c800b41c0c1c00342000d5103992840d48020468413641c42030001081070090320911070381c8100c8501041e0341106000f503040800d40f00100001c094a1030742001d484000c0120040c680d100c1c07407044096404001c007003a400c40c0c01c091102e1400905443c41038052070040c880c1c000140e0b004200d10041da0030542d001070b02c41c021040002c1502011542c140d070994400501c96502d03403101c039880300c00c4202080c5255540c695800600c095846400c519900d01049207605a000758403500051a00c0c60440401203245511003000030200c0b4000c0e110421920b944040140444007441c02c1d484d4440c1c800c8000c0c1d401c602d096141c1a4441c40003c002001906121040f2001c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 690973588 1250 690972338 690972343
    0x1080c09070f110a080301050901150f0813240f090f0b0a09080d020703020c1e2206141309120c0314031311030102091810080f0723060405060c 63
    0x703080081804540d0006800d0500304170b580e2003030203003601804d100b9002182700c0761201c0d80022866140c0d41d84465031000d4071801c450b284d1001d05000b454403003030040700c03000c6540100d591047c2c40c601c1c84008600341c11200c098089035000407880c40c10070b04180104003c1038200542c14800f6800c8036030403105a60b0400150024040c0401c0102141804900c0c103000d041d45a000e455601c1c4203408858a521031941000b4003850082e0512201d8446458510840c1c203203825841d442621003001d01c81c54980003079880042d078049030043c03402013214038a100b80c0340c81c040c1d50450307034429032074420446102d035515001c12414a0800070400c2c03024030307081c0008051042140d5070f50b05075041e006e00d0b06c900380359412140c01d4207400303000d031429213042461440340d01c0c0610841c4c07040e4a0080c614a101c1c3c43c00305003041041300040c5004516403903440c3c0091540020721103001c102d817804000cad12405040c40c0381c01160b240708408840c20400a111a190142c0320b120031202940e008842058440e0b141000491 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 690974838 1250 690973588 690973607
    0xc01031509090302030d0501140d020d2103230606030103030809030c07030f0605100b0910050c0a0302012f040b0702190e01051c0507060e21070e01080c09070f 70
    0x4481c0c61400e030006051540c08005481d17107544420040c06542da13035a40e16000490340e0038066501002c9030340108018a498030450090354030640c05030254400b9109200803c042000b8084c010a03154001c2c2480b59100c85040040d07802a502c598501d8103285010590b00d010501005082c0803240b03011440344081001034801c0f00c0700c444103d801d603c0c1c49141050100e401240304840c41810400451125004401c0341c80980d491940400e040003030b400304000a808180c66608144902007140c000030b258144800c40c0d8450194001080500e40c0c407444040c0a035145426121100421900c3c0b400042c0700e40c100c83c00c80b02107901305512a4554000102800641c82400d080b1298042e80040c42003000d180840c103c9804a459840c3c001550b81d4420302070b480031310003c03c5504071040030300c03496005100381d0003108806800d902108080c10959824102c8201c1102400d9000210420001c0d0310112514050002c00001d418190f200e44040795041c64041e12240a003c91480709034041440f407081417 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 690976088 1250 690974838 690974849
    0x8070b040f080d06060e030607020d180902030c030702190b06010f050d2301050a03020a0b07030c080a02030d0b04020903060f040201030231060c0c06110313090209030c0f030c010315 80
    0x459403072003903c4aa40040442e446139102003118060b43d586a80703030105446100b0011303500607124145541800300c402c0c1d5507041c140c0c900100010004212101a4030103544200700750542e2a070740e41000c2001030724020620302c2c0d5513082e104a0b0081c40004040b00003440d004602030800340e110b86e607102c03019107150080c81c6a45041510703020055a80050040e0f01050300200c01c1007141080c2d8846052103c4000103010181d040942402d04000a926000c000e01409000e4603100c441e5110725960045140e120100350001070348003113064410140300384541d0a00d40ca04031011880d0801e00c40101c1e4070b448003340f4501610002800007010340e40283c04580c60741e88040300360708842e0080c0c4411150f1840031420121419440d560105a45005042203061550032100106881d841d11000b03d0f030b001c1c5002ea014440703020031302c024504160340c100840e0180c0031103d401341e00c2c0e1418000341031400d2041280729200d03400c100e4405595031400b143d118592903003842e0104c0d07400c94611500c260010300368840d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 690977338 1250 690976088 690976103
    0x1104030b250215181b0f0a06110115140607030c060e070e01080607200c040203041a0a050403050d0c110714190b03130f0c030b0a0c05030408070b040f 66
    0x880745181c0c049103e0807031015005072403829488060401080740c4003480c401080e6440660045400c0038a942a0001c06034010b02610380044030901180e84410160701030310105e921510102c5245000b8018500e11781030700b000c11145c4034608400c03580040c0d1001e601a000304d100107808401d16206511583c0309a402903c10301240d09ca4111180d0b89041622408400d05070f800000b10f0100f4003c603601e40a5800c030380d290b03600e102403001e480c090f040300e0108402841c80b6140c19503034a40c5450007c0c51007a0301810482d00c85155100d442412001d00600220107546041c08000000c1c0d0450160340051418543c0001d58401146041d116040102030800f4144140c2c03a00040d0151a4001e003428a0300545070b000907600071042803544d0314505d0003103071a90f13002400041c19144904e90000050303030280200d4080032200b510f07039096640054000f070391009005010403003012110300400c815245140350082c41c626058542201d0340c011860300070043c0b201c81c80445d0a00020302034100721035400c45103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 690978588 1250 690977338 690977401
    0x30b040504120306060503090a0b0c040e0415060b120f07030b030105041104180308041203060929060705030909130203100c020c0405010b03180111040303051201091104030b 76
    0x400d142e19001c01d00780b00c8002810300c1400f068192048044e03c0c0208070700750040403031002607901c8201c1481c00511032503030303c0c800340300000300d6802c901d0f007a138012070080d0144c64001c580f01030140c0681b9426002503418450420460080b14a1180c0c025402132080003610f040351a104800c4000d0901c00011aa140d802e2409000910190741d040d0000400c1c1140c0400200c2c44001e40c6c41c0c0703840c4070110064086411000042c0101c1c001920444d05c2800030b140004440d511070302d040c0100c0301c0600c0c2900210903035075000a0700203c0c004801d008c0540481c0e046040041940c8d40a6580c800c3ca0320003070041c03201601050006181c0b00404d000142d009080d94240c258a100341c078008c1030792000010043c4a48804419641082c0c8100342c140c40140317481c50b2a540d5010b5030b8032031500c603030541c0c03548035940c0d01548030801c2011406840614030960700c2d9907071400c0c0c54001c0e0400d10010781046c440340e0b28140550045172020f004036400c59a03c80210f210554542e03003081e01c140c41c4142c0c081030400c0c0902 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 690979838 1250 690978588 690978593
    0x3030a030e2104080c0d080a030c0c06061e050102060c0d021815130906031e030c120e031516110705190302040e060c0f09040b1f020601080604050307080307030b040504 74
    0x74083d0040d40c0c0c40301c0449010000380303c10002032001d4103901500c02901000f511396180d20903000004018007030704102c1140d4041d0341d190740441d00e141d84513a00c1d10710800400e006001c0300c1c48000c0000d213400d10040400303040040000205200300104001e2440e40003503501c0000410002c0380c080c0000c01400b100d602501031070900ca15612940b9800c00d0100d02c0359011540d102944242c42c15079802c00b104200b02007900c1a00380308844245800e5090000100002c000280c01c3d03c02540000880e40c1d50703206181c40f84050600c3c180210684c0c1e0706450181b004c1041070081000c003d080d000d10751034540c0150400b04c07509414200aa00126044500da1600440f200560795011046078420744040020300880c0c4000d42e1100802d40f07040d102c2c0c1a04000c10344020480340c0140001c054000e000240b86218440013614400464034800c2e085c0c1654580d10b19450340500c0014014080c24003c0c1800f85005e50b00c0940364850803900510380080400032640c4244603070702000d85c2a6000c0c0003040181002d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 690981088 1250 690979838 690979903
    0x41e02030f090d110a150212040309060f020a0b34080613022a030d1d060907060212071a041a060a03030e090612160306061403030a030e 60
    0x100c815920b54450300d00c00c1503550b84280c4c20030810090001c00b4108441060b513070580c244201216818803241c083c84002e11004410b024980542d1183e1074000d80ca030720b0a08042c2a060b56901342c0002e64001ca001c51001c00c2003000c1682d48030032103240010203c60600c00c0c220002003800c1d0205003011050a082d546141c10045241c0907031000c43d1007c140705a80e9000c20103902c60352241406114000d84494440a919078514070b0300012001564203013406440100116030f1180320f00850003070701e0341d800403800409100b0310342c020012202070000b641c20064041d640704010b020f0079002400000e1001e05020022042d150a07041055481e601810207041103140030340110320401240c01040040758942c81c08041c65000c583e0315440b10411160280704101403128000c00303540d04010035901c01e106050091102c928164010b8031071300044c40c1581007200072241c1e0380d001840740c0101103401e21156a80041603500300781082c58041200510500100c3c180003201134405044940d4103181c50100b40f16 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 690982338 1250 690981088 690981091
    0x2060705100c2d0c0507090f0b190b160614090a03021b1c060902040203070c11030d1b020d1205070b0606040f050607050718090b180c041e02030f 64
    0x2550356810711015102156a42c41002d60400c1100c1e41158410002c4580224000c02d1031380c0c0100103603845150741742d05000c181c402d000b0544020b2a42d406825000703107803d040006200300799041030076009040c000610032601c00d0740c400b1982c40c038141c0800000c0140d1600401c1418500405411a5092180130b02d50303103592500e0114058011058850a9902c004000300c0a540c0000d00000c45604a2224020304034905007060741c4070368640e410400540c9031800110702600e5103549131019003115090640c80c8686422100b4400e0300003d10b6a00b41c82c0d401400c7d000c0c500113100301c15100306243d1001406032481c40c08000c2c6802d584521901909400001034084180038015150710f0303660ba0400c01c079080c0f02742d001d088010580d0305000d0180741414800b40003242e10840440304115222452144129000140182a603882c0d100b801c080250421500e038100b00381000b07441078100e80c030300016143c5211813072141c00f542d6509040d060181c51041c1c624203107447e4000c215524104890042502c590 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 690983588 1250 690982338 690982361
    0x3201021801020d031a0d140f0c0a090203010302010206060603061311130f0f0306020a051e0403030314070c0212010221060f0910060e0402070501020c07050103150f030f0206070510 79
    0x1441e40c80e040f810b019004849081000c0320311515a03258010401c0041080d06405990500000341c84c40e041c804100100d0001c8400b000c010403040c0c0240c820802d40c0040c6404c042801801440101b006036000951150441030450f0f079070303450356500f50104246400c20b500c2101c1050400443c0c036058110140244400070b00d15404103900c60b01c520a81404032540e00c02d003940310030006030400201700e40354060182c29003035203803461520905040140c403172041400400d04c0300038005030030002c02d81c00d8403030582c14420030b405d040034928020303002610141c15080c010b17000e01c01c20701c900c1e1351024082d8102d810414020219002010503039000348400d600407034946006110b5112003c91307a1034140641d52260030306103003a0108600707012003100d10f03400800b100d503002a024080c003000143d0a001616490650100030007c45203410300040940b815900d41c4045554000c105000c0d05124a041324196030b0802c0e4241c8183d0b000307102085492261840203051405040190152440309400900342d00c071 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 690984838 1250 690983588 690983593
    0x6072001120e0303010b070206071a010e0709150e010203160c14040504081b0106030c060c0b0c310b0f0d0f0b0f090403091a0c060a0207320102180102 66
    0x41c0059144084402c8500c03000c1c62640305100410106034042c00426950313101034006e900303240542e6285051000c80c61499844200b03501c0042c03182d50701e101a1527900c49204d1805000b0f9624000700101d2039242802c0300d0b001c0200b4001e04843d80c0e4020001c9400c5865120030320382c4254082d040c020745031005c500410f108240000c420256615040c042d0600668001c00160300d048880034015100100e0f00030400071039501d90030008042141950030a00621031038984034006030040c82d1200000e0002400d465201400f4003481824030310403511102e414100008a034050381c20a022120740c9007181d80b18005c0114001034200b442c0f04008054800c4422103003050100d159094000ca0982d28040d00c0e0607003040c212203045501c0d14080c006213400a0103810600e641c44c3e2110400c4580071694860304400074000100c40c1c078a05420080240e116907440011401c0c400142c4da8140440003480c1d8104850003185081d0384030014114039604513030030880c002c650b240c003164919010004010140307400350 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 690986088 1250 690984838 690984857
    0x618090213020306090f15100804030e12300d0b15040303050d09060b090f070f020718022505150a1404030f020c0a09050402100f0503070e06072001 65
    0x2900c00340240d138000d00e8000e0103041c641d5140c0b801c0c1c51001d80000e2110941c00000300d0203244070380303078844c80c41005d90450b41c0f68500ca182904014084114403d825030141100e4100d590f2000e50100d40c851455440010070b09401c151031000134445002d5440c0341000110001d0740c23035134142207584140705d4000144c80505010641034500c240c0c60055100241c003240d02003015092071482a80407000e16071041100180c00800c0f44003007502e80b10219003003451105a0300501c080300e40c0104c8800342d2000d141c801800000e0800030803004500081101b50110350300400e100c0d15205000400d4400312444142100d03228001382803ca80e10820004003052036030010012555111550080031480da18002c082d02c402d481e16034040b00c040540304084c02c2140500004209195a44002d20009201c01c0c0c8011820741080d00421480000200440d4244640d107616484180d0b001820340b07600110504000094010910100c0c40d2880342d03200041c0b6601d0707903040d10764007104541c00400f2805000e1303a13200d825 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 690987338 1250 690986088 690986119
    0x19081f050702160521030307080612030703050f0a14120f06090903070f06150902030f0702031215010909061707091503021e032b03020909070c0606180902 68
    0x158280e240d20080711064000003440181401a4025040188003644800b8502000d004a0a42c1c205503030b104001001c0a081c4000ca25009660bd05441d945401a603d0426641e0700a0079501c1500c0b00740180c0300022588004107030149412050210001301c229555503031802c10368000000403641c0d080c0b03107000d07000820b29604044840c5845600c1c840000d5180c001180c564818408013650210340080d150401d241002c00e07031092481c01081500c0700982c490820410301c1c680700d40c0003840c40d01198020f021901808c95a203440c190803020134004000c0c00408e00c00101d4610307800b40c00403488142456400110300d4607281504580c071207043d06403159652034140f08420340354074680001840c62020418000341c07401001c40c1414154094003c8010801040820300380612000c9074940c0110a00a500d040303080110500410f050502d403c6140030200b80c00079a800341c000d00320100b00155280228200900740d030000c00541340701c081001041c0a40383d0071001415500307104038050b040d42c04c1c1002a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 690988588 1250 690987338 690987343
    0x30504030c0201051819050f030604030804021e0603070f020d0c020102030406030e03071202070302031b15070f05060a150e041101032f03010e150d0219081f050702 72
    0x45525a0710006000030036001110107030000c400491440301d61980421080e65003501e45c2c40740596540199088a1500d010003800d500c035200c80a000e0b0700400100000254000b2400b544694100c0e45c103045129086400046084035141054110000100303200000b900490000005d45140e802c4901440304c1000c110740403420141c00a000d41d200340000e005403406608080b200b01415400c0701e0030901607440c1c104981000f800b0900150300100418000d509040c80b2a0b20383c11a81c181c0001d03040402c8012a5a001525035003500340d46002c07498108101380703e03081c9169181c2180407216541480c10300640103000c81a0304442ca003040400020311407200d4291544500d810005060311000100c0c0191b0241002e14140e00d00004c1a9400505003101c485400382e9203510200c0c410340f42e41c1080040201c0c5c0c0c201a14140d44540000580010755540d031a513101c440c2d9050703070032300307022108841d4001c0c82000603004842103008044010b81303440380d503404120481c060200309126035240c2e084240d8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 690989838 1250 690988588 690988591
    0x6030b0a0b0f06030a090503031806090f0712060b0d060b040c0e030712030207050315010501020120071104110a0203221a0c030d1b140f090d0c050402070b040507060305 74
    0x3504a0142e03982c0c040e50346000d00c080c0d039200310366000c00b0a100b0410b6482c02e003160b1080b84d94002d0b01212032002c00d084a810084aa4000a68401050010310501805980712940e1184d00040d0414030980010003079143c110f211400e00148c40c40341d0300219032800c00c02420030303225124001d03443c002000820600c03440c01815404005406401058141041e400b904c0300c00d40003e8040d842440d0001070070391010400810002500c0c160b14405504042c0024207541003002d110802e2060502030351341d6001c070301c000c5030a1641d0050681501190b0b01000c00d002e445003681c2c0c1030f104000820034485054011000303000100d10512540da908816003240105085a0700810351140d800c0030001345540541002484214101801c4a0905510316910400c0d0750b07501c091060404500000c0045207500814111000012035a2407410100095a88100c3d4000c1003c1d041c410006c2040f20801e05c001c08400390007070840584150b41c0d442d0503080c100040c26081e0703170448140c071030304400050042c46486044d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 690991088 1250 690989838 690989861
    0xa0e10050c060f0c071e02120a060b0603101503110c161a03060607060e160810050403020606010f0309021c1704050109271407020d08060a06230a0306030b0a 69
    0x80c00c0c05c0403a02c071441c2e03075000c4401c000340080a050304603015990340000e480c40840341c0801440200401d18101d410303521640b807413900030041802401040000000a60300b81c40c202d00e00c0c24a103400c0514100e003d4052001c1348040c18030f001541640e000008140e4125a03c00140043c04040d500d034010031009403202c401e1503800c01c00344045207151a05400400c4143e00914003c584100d1220040b403d109210401c41050174140200b0089c0740024000700c0804094641e0410a80c07409071406510703035400626090400420014969200f1701944c4019155900545488800e5015078000f4000c5103020f4401d9071629903144d041d840014120040b103043d03c4040c0c2d60754400070310b429410302c0454144601c40c6168076a10340327102c90b18002845807030f05603920f001c40241107040004029040c000303e04003c1c82000003100030072502c1c1d03c65003c1c100c00c5175924030700031001546084404a0340c00040e99219611000042c1007410642d15030410003c0d280100c80c9008503440300c00389070044422444a0313 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 690992338 1250 690991088 690991111
    0x1b0a050a05060c0307080f03010e01061b0b1306051006031d03070f0f0605091507170f0a060e0114010e0109080a02120c060a18050a030b0c0a0e10050c060f 68
    0x1840142040b02c00380144250740d0302181d08000c016aa003411640104000d80e034180c0010004001242c003071900743c0e00401c0141003030542c2c50f4001050107408010890082e10b00711102007c034506203d42c894409620380c22031401c01850501081c10400b001e0320344221000203080c010045160030306000001e040080c0d074401185011103503510700b41709001c3c1a10030713144551900c03c0300c40401c030f4602445111700c2c2604041d02c42c0d1440d90301501c65107003000d010101003100740e404841087c20300d40c10154200d48031000302303407880c3c0e541c001c9940a08801e0300302c0301c031802c0d26400002e448100800d11440050090700c82c0d800301e052110045a21b000b0a21400b00c49510040044016081800c2c5041e038443c0e240c1e00351020f481c0c1050100c0c5c42a4004000c000c0004c0681c80e035580c40d4044e00c0c1c4040040c0004544005032a807958594510400001d03010307000704500054004ac6041c010005640205d070301800424000c1c082d42070203049600007501d156143c0c010040000e05000c8074034015440384906152 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 690993588 1250 690992338 690992359
    0x10050705120f180102010902060c0d0f2325031806170a0507020c030304060909061d041202010f060303050316030c2001060b180a060509030d0e1c051b0a05 68
    0xc524038140083c41c1c040c1075541c0ca1500c403015803107010081602c0c0668600400e0039500c901e0f002000d907840142031100b0821801d0040300c506d0714a259482c01d2500c41004c03a511045080c5190500d229618500302c07403403184d2001c1c0c0c0201038000c08074010ba09110451400b4031556004169000c0582d07210140c40e40e9000300000700e044110350700540c0c2100c024412505080380140109156034400e0b0410004510402c0e805c10902c1c9490140300c0c054494020070202801d40c10315002d030302040c00b52004000302070051000159a10035840403418000913035003030110036035070704025189500689640d4112802c2e080040c075814084e000ea5001070301980c0d0798a48150080050303444454a864200740d50f9500c4100c00101c0545810182c01c000c1e202c0300700801e0510030f46042280084040c0d21060500c002404014020758000c07449048100c05800c0c00c00700240810005104400b180043d5003180c403126581c1d4080c000001900416480030b96014582c90400c2400c22466401d00c4c0700c0c82d40e20103003006 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 690994838 1250 690993588 690993607
    0x12061b0903100e030d110c0f0109050d08220303021c0902092a0c010507021615050304060f14040302010605010e09180102040e04060b1f0806190510050705120f 70
    0x14401091103d190f020380c3c0c1807006040701242612107415062040709008100300b1440c540078000c1c0480000501d000b04455495076903116160a600d006404c1401004000900d40d400c0810b950741098a1244da1310140c8030b2103150240080d08a004500e134490321501c24218001210b05c6044078a54005020203001d542d024505e904c240d811101c1d40c50501802f041200845099402805401d45101300200b130303d1903c100002d00d4229400702e04005842c4044003008034a006071070b5010268590300e4515900d9840b4202a000f8140d5401940c441c1c0c0d1030710000407103000c901161240618030990003440291341d10001180c240072282440c0b40d1001c3d0210104102c46203454012400c1d0103014005030515540b0360740600100800c030360581d1081d4035011801400d03c0c1c910000c83c2d1324035031a14100c19440c81c0707060003803c1c00c8000344540d01800d59110040c00549841c207201700100700c01010800148203481d80180700350000c2d4004c468034458010b10f284c0e114000e074240c403441c114458501e0308148007107 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 690996088 1250 690994838 690994841
    0x1003050a0605091e0c120303100603020a021c020a0c0b1e07020319080703022503081305040f0f0b0303070f150905060a02070506060f060406030c090512061b090310 72
    0x1801c0580c66104e040c41c3c00ca5015400005400018040406803112400d4403003071055000380052080e20b590420010005402d03060300700300d41036483c5e81c40e00507125108664103910300304c01e407039201e95210a820110314120740d000039516483d91082c0c01541103143d84401d1401c090140522080000071780000150001515101030504580010b0407941403003901c610244440c0d03174084042e41c01a00010b40f003401e264041184e80144842011901122100088103401d203681034000100301c990000780101000c2c40c62510b00020b040700910801a513100740c0411001081100c60705601281003448402c1c061a0210988041e590040b600c1c0781c40003036980d00c40d2011076000c0b03019121181e03105a507101090041020074402c0980940c01a0307a002c032820054034140d4020103040c400e481d40c02080e03c0319118801540c0031183e450401148460402200b901c100c143d5070840c4da00030300c05032200c02407510f001610600992140030b94a8a01e07151a20010141c4140c2d0b0b102a010f5004448130310124205 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 690997338 1250 690996088 690996091
    0x501151d09071d0a080717030705061b070614090114090a0b0408130b0a080a052503020c0a0c0f0602030a09031707050d080124020a080a090f18051003050a0605 70
    0x43d6100011420158001440c2d2820360f084000b096000d00401c0c40b80f01c1e01107510b4070412100e50020741c245851559416500d143c000c0a200100c0003900c840804040404d0a440d000f42e4040340078444101c89182051100300700f10348081896080069514202d01c01300c03811405a840c0c200605850840c64491a075642c501400481e14103500f0001826030980150000b0003920080034038a50320b03410020b00810340c6038040e10590f1868508805c0c0a40000c0401074408040070001c1d202c14943c181c000e040d002401404d404c410107014200011041160b00441c10041d54910f0a041441603100c2d503049036a40100c81918000c00ca60460a0002c10124181d4440310002c11032150f24000044e940d40d42801c001111074004158103070014044100c0350003804160425164080c030140114020023980c50850050182529100055064080e8803492004002d410b4900d520550640e9400030a04401c151722140304809103020045007141034141031403000c50f43c008000302700512858407044010b150 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 690998588 1250 690997338 690997367
    0x311040e0402011103030f04210827011401050a0b04270609060303050c0f060c090d0c0503060705030108070618050121060b0a14090306070813060501151d0907 70
    0x4004c0d0fa002c030207420410085206a40f00901080c0d2410a4a45142d10248080404030800c55000f2054501907000100a50103856014440907828031a81a024501810300702d03003025500b014058070f0b60005000d8281c0c100c65054980900e840c2e51520f52650902880c0142518545081c0d50f4455280c0c0c451a42c115043c0d41110014441ea40c03105000210f40d5076a008401107080807a41c200c1400e01840800070814030103020b0001d074604000103a1042c0300303032080c46200d16020300c1c144050044114201001d001d02801f12030060406980261031504244543c0610707100e10b580c0440c1d001e02c03404c0341c0380400342e0343d000d0401a20705160054400c41c01000c0781d24045450f92507040010b010701d0040600030240200c5031941c0d180a95001800d0300c0005540a001003801c1024000744d440002d00158046140d181c006856181d00301e011001041c02c900148c0124185000402d11002202d104402080c064894a8030729246041e0005148007103003100780c3c4480500000f41000b070189006403044071 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 690999838 1250 690998588 690998597
    0xa0f0215130b191a0127120f060c0206090f0a08030f0702031315020706081308091f050306040b0f0108010e060f2d0a12030e1c110a060311040e040201 66
    0x3c00440d140400c450041d60080489084800b600e071940d41c004031403411000c41180c4001d582089036a018503040310f00d20440081d092540c0001d410b001180a03200f0007a135020206100140b06110020741d00d060581d50490395004008a103071150400180e5441600c2e80040b103113046a540c0ea6072610b5046001b00b0440944c0020841c0c0300007100d0403508800940b020013005c50348085e07129402890444590800001d100c40305052000c178900d0714481102c0d2542c0500c07404c4d66850400042031030300d003480c1041c500d40700e0681060f194054201000e0b506c80c40d8180d604014400c02c0030700b0000602058a9050702103110032005028400c0c0841c11150700440191000c891240e49a0126031000b4600c50304019206260100240a4081c89051703104100121001e038015401c020a0a02c120a60000107080c840b91110804403a01c805d0491a268803111074442d22202c102d08120010b2907146813014416100440d01140da98024400c85a4015900b080030303040034144043c9400c4008064002c0e030501 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 691001088 1250 690999838 690999871
    0x50606043014100e0c01021c020106031704090c0305010b070311190b0a06060206011d191e0b120d080c09030708151302010e01030911060a0f0215130b 66
    0x801400d50541e60b41040801002d03c55041c982d1082216100c0d440842580c11100400c0c01030380e40007030781c90218000e0703040d0b08803519400007080c6d00410480d44018249010810499003115541001d0011240401c1040c85541200700044044070001d0050b40c448690511900d80403e202d07091030319807800444125034800140d4070b601d06013500e4009044031080382c0c0c1010043c68090b00c0c090340000701420700007010700d541085c05078815800407210621010765030000150400440c644081f07241c41c1180b1080140b0080c58940c010100244041c1c0c4010505200b0680040d0404102d0500c038000014090101c54a510804548480c0051316100301c902080c0410301c001d0303409220110081034404028558101800e00707403c65120014104940801280b10000150740c10020402010f1000d107800258041c0d03a14162880c1010000320b15002200811f01c044c1e15504011480d0400322a902140d028440044614003102c50856000600c010030b0310802d000507150280c3e86070400c00c1148070088a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 691002338 1250 691001088 691001093
    0xf0e0406030606091a030705030601061101020405270609010315020a0507122f03040b0c19050115050a050310180f060603021017010513060803030115030506060430 72
    0x640b5815003100c407100c3e0760703540780d1812540d112054406174801503000e026618540000281c90313120505c20a030074440921400c044d460821f504680103400e0091203060f4591000701502c1140b0501c800b0107003400c4800011980074509601341604803940803138800d03601c91340c401c00e40002c0c0d04400040c10903c10240b01d80000111800807440701d2860550390004583c85200c1404080080d00849c2d8140c00d05010341105040c2c3c000c811035003030f10343c5401c41a17520b0302a40740992070901010f44ea4020128031078851000c03c00113402c003004c000401c06085c800c00d07443d80108690802c151040640c59031107248200140e9810f5089400780c400c044408641a4002d900ea00c0030582e03105500b1075240380e481d02d040c41140b5001c8a0000f003640e2603c0e09009640c6440000c01e041c0c40180269840b030300e502d80e0403011003902a0001405020018156520795075106554410020366150020109081100051840c01d015080c2e40407218514407109040c00c0494003c1040785108115041c1c9010300c1149401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 691003588 1250 691002338 691002341
    0x3190f0e0a08070209073b030a05160506091e15030c0304150209010f0804081b0606040f09030c290f0601030c180515070c081e010209010f0e04060306 66
    0x100303901480e40c2c95960000d61040084040e0010001414460b602c003a070b660304100104072a18503864100c829402e00e8044080c521000c140c000800da06201d136401c10000c01001141442e180c2003484a0a1102c50b1a0005c1000034050034003195005101040405440038468118142031000500f4075071035012044000c008a5100700c4491180100010500007004604014000c201e101d0300d00850030202c1c1c00000038003100b00d0118500c00c2200120220702031100540c22078501003410a07007594040d108200035500d914048501c5841681b412078202c00307008450090000e0981e01d50381c0c07405e02c6511940e8541c26101c03041412036101d81e10300d000324011b4030075104860160480702c0099a03180707071440005007561401d1014100308285041d1481c5110f1850302c1e0142070781d07012504d95401760001034900c2014000d00101403c3d10050000001e003102020075440d01c840e0300404644105240c0d40111420f03031043c515054000b40000300f401c2e042030320510070801086401400480e14503030780d407a01c50 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 691004838 1250 691003588 691003603
    0x1104120c140f061305090414070e04031409040b0301230c07080f0c0106051903050d0e030303180c0603100608180d080402030c0d03030609060801230402030715020c100503190f0e 78
    0x540c130b004070115a03205c9030820450400108ac01c50b0394910301d03160641e0300038405444030800d640c400c03074003044103800740c0e40c4e50301314054058020f0000c0285c0340c10a0806140781110b4800308441c02484004160480d00800485482640102400380303042c410303400f251800d0b0f016101c02c142c907560311f04010031140d0300d0350360210fa01402028010441030a40c10201d003001580010740c0300380540031107d0342d25514048240c990003180c0509071001102c410005500b0b02154030b00d2241c1c400000002c2040074052020f03008180c410799594240303540c2c0c0c1c2890b520281d800c40800300e000d55005a945400b8944160300d4280d12500c060103940c00b510754807000c5181c650700140d0403008039484280500007070b10780740f084d4001040140c0080c444d051010400d280034588944000110341203000000c0d00390340f010004e9000400c4640e20b40d0078401344502c0003c1d00c40d01c2d076101c818801c1c800903100ea00d1080c03291050b80e010344a030350000c286500c420310071240240403114116000646641446260040510222 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 691006088 1250 691004838 691004843
    0x60607051e0a030f0219060b04150b03010f1d0f0c09220515010909050703200a1202040302180a1506110706020102120a09061104120c140f0613050904 66
    0x80c403080c00645001362401d8030880d85001158002c0124020050030041010005a084600024000a40808034000e45410001420b001008200000d6650001170080d81200c2e0f01400c10344010341c40307800e10140030048980840503c00e0a1300810030300c01105c0b000759001149240410b1420740407002054010b030b41d0079000c0c1c40f456820020800e1409490162030717442000089000200d544040002c4c01200c460300451180903074403000034961a0003a03009d940b50780c4c08103010028100201c0c400000c0769005001c4040003548240c800d82000f50786000b5601940c0d03000300124681d103c03100c240104450002c0000740c404d51150031007030b2041801d1440d00c1c081d1072250745034020403041004ea186060100da000c94116841000844001305280d0b008503000802c01c40040752108190500310041c1046011140c480c440c00100051003403241240c181c0d04a01c40c0015624869458600084011082154a80101000400c0d00061810740c00802819103100100e05820352a00c010030b06900040b1401c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 691007194 1106 691006088 691006093
    0xa03030b060708040b2205060d020c10060609050306100f060c03030e1c0816050307120207050f0a02090c030c190c060f0b040b030a0b060607051e 64
    0x84904250b0403242140e100e070707190f24801009621900c42c41c02800084522061700c180c1451141d007c0324001041d541c1040d070220a024003070f62211413507802c1c501544003084001d4400c4e00c40c0601401c140d90f5441c0b01e16080609141c500301d005011040311506140702006000500000b2906036819881c144155030480c0ca010303400340805502c40340c0039000d0f403da033304c010614140e4411b540505030f40e1200700a46411898681c56402d04000d0b0340010b108000143c0344038000c1c0480000210310a000503d428940d8541034100b4000402d0088590011b00d180f40552620411302508210006481380c510b00305080c003010f0b58881c801030f14400e00c1110740414100380c0140d440010f415005a0b040c099003125003242c074005e00210308403e00c682d1038000210118140010265002903101550440d5034854400304806504403c9080340c00344145420356152000c04c0e9106030841100200 = true := by decide +kernel

theorem cover : BRFrame.Cov 690827338 691007194 := by
  have h0 := BRFrame.cov_init 690827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 690827338 ≤ n) (h2 : n < 691007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
