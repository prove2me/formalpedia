-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3990
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:15:10.640528+00:00
-- url     : https://prove2.me/submissions/1cee2e41-d1f1-4b65-809c-0f80b38f2ebc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 717446043 ≤ n < 717625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 717447293 1250 717446043 717446057
    0x201050f010f090b03011d070f0b0315011209050303011511060f01060e01051201062f030a03050403120501240302031006141c0204030c0b090f090a0e0733 68
    0x80f802d1904104c0c880203005000140018a000303081c030890a106501c5c000301d4106090803c00f441603560628000c1c00c9003528070345503103007c3e40303801011860f640c1c0311410f01074034003581c1d07032000d202e54070003800e180c0d20a0440c2d6072175848100b0b842c07229602c03841c5140060b01c00c00000c0c00c95040030911038090701c13441207440704c2a400e1031415200103900ca108141000011b200f0f01030506003a0f400903009290545070b0f80f802d26030310404a038402c5a101d40c13110445103a40c4104100400000441d40f400c40385103000905500c0c0d0340380880f52101d075003032940246402c20001040e0087c024145c044000411280c52100700342e88003040d020380c0012100d9603002d0095003010171146002d5140600c5006400d05180e01e401c0710701040703028051b20143c40445441d80410140104404455500d01030206072405030f0404084000141c50150490042405506a540800d4110b0740c55008107001c1d9000c001925445500c854044030f090b864010203100201c1c000c440d14031001c299012504480545580b151 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 717448543 1250 717447293 717447299
    0x409020d02120c060d140108030c060f06041b02060603160608060904080403050714010306050a150c060e0a030203031e0f1305031303050a1202030f1c0b09070c030201050f010f 77
    0x40b084601d103548200b0706000e01010039600341d56450040c06201c0c80c0c15000909070f0b00344061054103900580256003a03501c00c03c403e2962a10008000d9406561200d1100c0955902404a0080d250000d50341510700703003a0026110b520380200381c0d680320341002d40842d45101c260601c21481c5074024071950001c508180082001401d00d00d0740194014016030301e1300d1400760b480c1d90301403074059981e10507001078000b80301e20181980d0500422000f404111a054a06070401c1d0664505284102c0031a003481000b90400040080303c1d0000700802c122038003524003a1a103820b0180d2650b01c21940c440840389001c81f25070320302e0390b60050680152421450040c080d07135034803500c855008070314a065456220502500e006d00007680b0310400a103100348050820000140380152020703c980560400350f410610100c072400d01c440c000e541d402e032408000148450001c5080c8001418000d00702134201410604210301c4035003003140d4007111442903008000a990340901034060300d10a008031104090104810 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 717449793 1250 717448543 717448549
    0x3020d1b02010e0d0f0c0617150f0a15050406090b1828030c030b0f0c1806070c06080105030625111f061502010509070b072d060501050409020d02 64
    0x30a01c107005000c2c13100000e01900c0da03000b00700310350314200c032045003a241c00d00c4007503400040c0100c4002c1100c8845d680c1c1c100034000c01214044100c42d103004030208041100a6650102400010300ca003444c3c2c2501041c1e1030b0760091041d40715018001c0411441d41001803244081e40480b5820629008010403084130b038420001141444800055202c4220107440d28110302030580100652250340420401840c5103003040c1103200003880311801032000000c00c48860160002c440e001f00710b06140034052600c0ea00098014001d400000c2d12244810002184071900281c03100e0584030114101d81c02561741d0801742d81c41b1017610641e03034042c01403180003100c180e00078100c600040c4540e0040d1581000e95014106c00c980410301c10344400d50301c07940100020b01d03820640d26642c1c4003d200901880c54040c6a665032401d840c82120102040010144280f00c40c200f100640a00080700700c825402d8203821a800781c4200d0300c81990258503200002545107890b114091480d0f0340a0801d074070656a43c1c00f0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 717451043 1250 717449793 717449807
    0xf082d100b1305060f04030803010806010608151f090308030f060102071a0a081009290a061b050304230a12020d0b06030102040b0d360b060102010f020d020703020d1b0201 75
    0x258085c0d00030240320200020311034030040d602030b140e8000201900c2d8035100700280482d1010741801c100d000c10701c100c45295140c0b040460b442803489402490084010607044802d810550b0000d4000c6a0100c180310450708041c007402e000b40b000760308031740b14161694171402034016070640c0d1510030541088150002802402e00692103001c1c1440012035684e5031041d042558462240458401c10500e0390441c004a40740409800c000c082ea0301410203420804040d00d20f1200d4101ca002031400102c0e80010000100300321000740000402070312500f01041031318a40e00c01c40c0444a40302d061742d900c004c5480c00201c0002d1321015001070501c50701c10701a80f1055070401c0050802074065408100100f110742e0b06e14020501310080850008150b4480d460b90340b604005030300004100746c00c1c25002070915030485010202140c100040511035100c03000141e0061101c204400c2001c0d0000c500b2030070019060340505038440c029002c0d47c201c0c4943c41c0086481a000c01d14002c007000383c61350711801551050326 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 717452293 1250 717451043 717451057
    0x10090c080f010c0504230d112107090f0b03120a0801330c350f0304080307090e0705030411030721060f050114010f0c030f082d100b130506 61
    0x6c4907040440d6040100f075666080c0403080d9002628404010080e0610b00b000c41c0d90000030a031466054140ca80c1e0068070780b4010710404800360f444002032a01090a907020482d400b030000c1c11140d0f48410040300440b80e4000030110802f044001d4000542100740c00c10f003a40c19180305402c212081303002d198500d410502c00b0b10040812842c4032003440040d0280405010032903540c680c2d51041c0f200c50503000d2880042a50220f40c4420502c0084c9000c0c0320107003a280c000744c1c007a1209403a0b58a07a201103c0b415060340c80814041031003001d01851a42110013140220f01500c1803400811944060594400d8640b0070fa002280f24803000d810581072a6081a5019119040c003040c00e0b050028280305a4000703800c08034058a02c01c2075018650382109180740081c40300c0c07c00f8101c0c0351550f200a0030b0b6104400301101070054041c00116074004080f41c1c01c0e00c5040c400c102c48990700c910b400306207050000f203800302d503411801e01d030210300b800f15503085d1105c034000b1558401c8481d09200912907546c00c810 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 717453543 1250 717452293 717452339
    0xd031515030e010c090503010b061306030b060c0706050a03050f040f02280b0a02010b03060112020609010e090a0902090c04080307060e0703081c06051503160210090c080f010c0504 79
    0xd084510030b8420701a030440188241d90b00b51543d07040070201400c640795009220320a10b002c01082c82d40b03542018522003112070f20b0900180110b8004080362192080088409481c080c80d03802003401500800901994269a80d007003102e55070f015451114104103450103440100705811042c0149070860a5080d4000341e0350940710840340c1c00718802200e030040d41040540210106120036003550900c280c06085008500928180d490300c07022080d944110240a4092140020595000e0f40101101c00c0d070707075401401c90030191500e482c0f0700c001031401000032446821210081060810844107a4080c0c4003040081c601d003140c1e0b50381d090700510142c021000d00f4010b01b02c0001c042000d002c0540340520a00fa0700e121054000c1320079500302c41190f0002c602c40e0300030038040f00810b0780307441c15654007402d019400d00308080400410fa14048000b00e90300c40c0182403158120410800c1c40840044903042411144420604041142a1002c581001d00000c0e0103110410440c0c08000c0d038401401002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 717454793 1250 717453543 717453551
    0x303050c1c110d1a090708070503150609210114090d0e030111030f011403030301121104060e011d061008240306010f06020f15010501051e04030b04050d03151503 71
    0xd080000c2e9a90581010f81140c0000c130105041e0810700c114650010041c40c118a0034540792101030700900000e0a9250104188410888503031103103001c40b0030000d402440383c0c400c2080184015100f2589000100305542081c90b400c5e500481ca070b000d50b0091040b60043e1990321b0003060102d0b0325000c09030070b29030f040d0b4071610510003c800400007076018462207801c3c4103036036042070700340d00c00c984d049041c00780a03a10820042282c0220030742160300485e07014400f803040d106000c00140290065402031040781c01c01c1c13000010203d800300720a00304104000240c45641c4d5450307080048144001c0a409c0101d030300740001521000940c141d4800707560b0b22080c101c0066030040c0229143c11000d0300f200ca56103042034024002d103a0100300c00d207641d2004400805079140741d0f601d000713070003203041c03141c030741030100204049880b046200410f154103e55400801c0d140c0743d890034069001c69050b14103681034002d0208154030b440c0b1a000e00d500060070440341c14503003403070101c1c0e030b003120282e0241200070140c3d2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 717456043 1250 717454793 717454807
    0x3070915090612050d0e01050d1a030601080c0a0515070602090324010e0f0402010c14010f0e0312010f360c021b1905040f02070807050601030303050c1c11 68
    0x2452190388054915011081420403051420390720b0114158007100620030300f030b401b04040f0780c1d1090032a000c00d091420f01203603090117440c0c112032820700a980a98540100d00011800490004980d08030040c100c50600720140d50b101400782807050000412122003040110b000030983c2e075001899031840141c01c072802c1c0b0000d401851007000721782c030880301200e50303000041094a030300c0c607082904110329903058401d50038a0f82c000703051030601800c01012010440718a50710442c0a501000c4050340110051164204c0c540b4100d80f03991050703044a90b200d4041d8000320380760714001059426109030b000380780407008808800d0819400380508402400c41c451000c070503090b1070380c0034055070804160000e1400c400e455221094018500c1034090041d10064124010342c8000c001e1082160019a800110141100741d484007902c10a200034240740d40c00511351080010005400e07049030301070380c2c2c02c0213940c03502c0100498a02c100d00d031034401d00c01918002e44420301d03143c0c0030755001403041c402c0f503240040b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 717457293 1250 717456043 717456059
    0x212030103030507020f0f0303090d0311070f080d02071208160f08030f0105040c1b020a030507060f0908150703020a09150c0b0606070b2d010b03011e0503070915 71
    0x8801d8104600180300840c2d82000c50802e0016005174500496003118800c00220102e6500c1c002d08415900c940f4461141c44103050044071301515503500c00b0155007280383c94a02443c0e10020f01c1c41155114420701c207070030b4115840031031000141c600845041022642940306e108403070b00501400c590b100c0341300e81100001003d01c40f003051294803d0040e562a860106680c1555046c143d01aa020b28201035181c00c07030301c0e4001c40c2d01c0807810140218203201d011703d0001c229000c401c0d409c004c00c1d031300c201c0e4000b14101d0f07009608840200f45030b58a51590f0358030359156513124034071100200710301e00710000454540c074029009007918441e6407500d01c0b5111b0350f4400c0d00e61451440080c1c4e4001c20146000141486054813640740c3c05002600c2c4039150848551f503c04120000801d8003152040e1301180c5103400c00c0603c00301c05074203508010188203503110005481c00740c0c420700c00d80c81c0d4514907640d4265405404002a412600b0042c05401403528041100000d00240f8401c900000722900300441c01c15 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 717458543 1250 717457293 717457297
    0xc0907030f090c0810051b0f1606020910050406020a1e0516091104080d0c051c0305150d0b010b03070201060b0d0b12150c13051c030f030b1e010212 65
    0x40d000b03400f200b5041c0d1518100605110203182d030610100d00700070800a9200c044840d4090290313802c001543c0c0e60a0748000d540c0740380940c2d0741110b0b40d5468054442e0900649402512110804448034140c035038015030700b03542c207200300c0c4506005a0020124000400c54070340b6040302c40c1d607140d100e91622142680d80c903410404000481d03c442d2100440500410290b886420f0100c4071103030449140c5030801c2180c0b591407404a1158040000748010101003000c14000104149a0003084580c1401e450300b000c1c0c042d120441c1c100c1c02803180c3c458000418585074160918040d041106040507074200b05504006074001041d04007075640316140083c1c1014040010f180303c030040c40c000030308242c034842003001d0003074030300d40a50840c0d100d076120021010050a002c1d401150102e0342e50355035180c0d402d2075a8a20340990045a10900f004003224101400c03400103042c20b80703e030381c1d840b82c0b00407100f42c1542119013182c011a00903541000c540c0c44080f4024415202400500440d01c0141c0e140c40c0e442c13519 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 717459793 1250 717458543 717458561
    0x20d05010f060816090f110f03190b240f0f130603060819021302070809011e090e0405011b120b04111c09050d02030a18080c0907030f 59
    0x1903035540e0360300d07210450349101c0e40303000d40149000361021550303000c000300b01e000150144450a80c1e40b444030452a600a50001208901070000152102e4909680003495003049811410702c00102840d00c903d190300d03116804079550000c3c2003101c50f203404540031203281132544494042610030030100030705a000d100601848041ca014480c2d4407050106008580c00ca140d004000b49810103c00740920400407030704484a0a14807a5855031f4525400026040035007007522080c21480060101e0030712070054000d00d407004003a200c00c03414640700e0302d0301c0044030652006240000c2c0c002201340b002c1201c020f0f402c0d400038014000414954040c1c02021001035000d969007021070701000c00c1c2441100319004d00c84d80c04108442c1000090611490502d0601c541000d6019180502c4c07002c6d1280d4610358056085583c000c0200c5110000070940a03503654004071032a4041001070b140d0001102d855644002515040c001030188010500140a0310000103050340007890b85891203100c50005620400d004c07 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 717461043 1250 717459793 717459803
    0x18080c01061e0603270b0901020403021503091501080d0f020f011803141309020903010213030606061713020409030903141501080105100614040e010e090c0a030b1909020d 75
    0x6441e2400700c000d030456005444450710520901143c000350f0720000c01900810346c002c0690300c03199681690041c028451900000d5114160703e41d0250492076103805148100070b404d0880380c0f82c442b440341c0002e1250091203a407105074070008032251801d10608000d5141080d600486541c0300200109c1030a660a510750f11908052440d0018103241c0d020b0071325151882094507940c40c1003030380c4c0c40c03107030000805002c0c2c80429900003680800d030351800d43c12036252030209404095265180c0ca08031000c2c0000d4480e00c00050f805200401c040c51905000390b025203030500c40c2d01409055a82800045c0811000c250117001c1c100d41b0002c0030500c0500c2408041d036100000d00b00340704c0b02c648071100e24541030f005981c850389040f040000380c181191542003511080d08100710901c03580103034405240f041d90400541080b2420000581c0760980b00c000740518005401e540007480c0c5e60f41070100340b040700e110280c11541c80f034000c288070030b00c00c8100c80114000484081101d110540100e141d40d9444c0e1000c0360 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 717462293 1250 717461043 717461099
    0x20d09060c050c1c11030a11102a0302040b070b25020c010c0204060803040803130503030307051c060e04050c090a0e030901050c0f06010b0d05090118080c0106 70
    0x400c004240c85022a9000d403818040c0c00c241ea074000c07469445240219900c80c4804403d130210056000e03008600d840601340007220364602903040c0c0240030002d2902000b51920400d0342a144195a500403002000640c02c201800c0120041015005646000112041c15400c000100e8803c81a500030a1514010354008016003819245c00603a01c11041403460000000703130404544550200751040303000024070301000410058000180140180c0d0301c6805688000a0000b405160101c086d201008000c25580d41c01542d44082c5a143d2008950342400117800f0082d125103400b202c40201c02000c6040c4000644c00e460303030f807440b120380c1c0241c83c152815807084d030a10191703142280700c0300d600203804241407011542d40c05100d41d49000700d0081c1410301c030000c5002c1800c858104540d60820f409081110541d5035540c0304400103501c4146403116107400c1200141d110001405030000203065102d9410740c0d1025501d41402c0d41d0440c403603629644d5220b0000217840c9824103100800d2016030b104001c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 717463543 1250 717462293 717462311
    0x12031d10021b0904080703050304150609270803061012020307050403020909120301090903050c07030f0506012709020f180105040606140304020609151c0e06040f081c020d 75
    0x100c4405060701882c0f00c0c007429000c210002d40c4600998041d035525003400c944035100c501d4800101d1180c0304203d5010303450840c00241c0d83d171081e00705491003009440100c885010858500b41c00d203103030307480203094240c0810204010b400c0400180710900104e00d0310003080d011b0082070300240e0344142d070040c000980100307060096190041c0410b801903c000c004200402070302e20946024001441130104081d80c50702e0704424076000b00c0447c0c1c03541c1c07152010b40f40d49688a1408180c1148640002c1e0352510a8000105128440240c2808800003950014075640c101e664480040c0500a108030780003828019420115100c03468005000015504050403540c1400107100403514140d215070300b0001c0406540e0b410703054039806c483d0030940540702296a5401031010520103d904410103010303100001d070020703084036103c0100d030b0040034508003400b100340708120007a41c646082c0c07000791041030b03142c0031a000100100010080002c1001d40e00940080240114049030440003074000255110700d03001c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 717464793 1250 717463543 717463573
    0x61103040b030c040e0c09010f08070c080c010c02011b090b0f120f04051b010504090504060209180604150e131103070801060f0f0f09020309010227030708030412031d1002 75
    0x5c02c3e4441c018a5006042050290000b8642040850500d00380110603010804c400d1040b401c40f80c1c00d641001c0751ba41d07203071011302c41c0c64024812940c0040040d441c08001c0443c003108100c01c07441045183d5203010302c1a0500c8000002a4080e900108042c4c208000c280c00040c107003031100d031291040d00402c00943c540350802c10705040c0754a507489a2081d00741141d0000d40c0e0402e00780e03800d0762085040014140c0d80c0d0300d4447c00a1180017601948000c100c2c0707001030980e42c080242c03445550190780600c4090140301c0715070302d14001401001c8401c0c54450002d69003207503030719440400c1400390300d1012028076030720b0100b41440d829070807112980e51541014081d403107207508150010306010b86105002403400c0f25054400d000b80c013a007180250000f0124854440c25016900e1200c68403000500c070b01003a0b070181e0380441ca98071481c0d019000780c440004070342002205039400c4500c000b2003000040c00c1587c2c03c4500c11401404051100800d4140b01040c2c0c50b041c2809070b0301049038005000d1440c04e0300300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 717466043 1250 717464793 717464819
    0x181b0d0b15010e04052a090402040305061f0308120403031401060504051906020a1b030213140708060102031b0f0d080f1518070c14160806040b01061103040b030c04 72
    0x800d40558202020305c10602406084040f80e2200202d106d500455111544401d500c1808180c6520500215020040c4200401c4690051506032540c42c0c0c0c54640340c4048258050a100c007134181482404140c54001000204991040c4246000030340c040c440d0142010305c00302078102070001340000c90240010304140c003a141500c51140a410002031170013000030b59589030003200400b0120038803804460b14010303401d003a01441d402410b0203030003043d0840b880000c0c5401c00041190402d620040740440f406905098050f01040e40139601d40015a40f8006c42d902521105800c0351080b9406d07200102d030203200244481020740d40d480003504101100e003500344400751120007202c08042c0001c40d207550b40308210410382c01c003810304a00707139540c818291115400458064884126180d0b4110140c00114048200340352801a4141841d06c4280741d507580d00c4103c40045c005030031500180416401031002110522600b41140d141945603410114980c20644c1c54600405010406100740340b00040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 717467293 1250 717466043 717466067
    0x1051c1b1101090b011208070b0702030702010e090402010806190302090411040b010908030702090a1d0114010f180b1507030503060306070516140115170105181b0d0b1501 75
    0xe10080f81c054072003102c144410320134801c0c1c4143d041030080c1001542402d0300d02c1c00d0f8111043c00018501600081d48130b50241e18200c0c001140b05900240318504607440314003554041e5902030aa641d07603800d01448547c2042c0811b00c030020f907803002005a03a4a60080d2040b071003034840b8103010340344e84240016103448845541c1405a0001c06008104000003038404a1360100c0d5811241d40341e00d001070004180d030100004480c0d00c20100344501d030b00c05402c006424022a0312640282ea40c0c3c00c0803000401850041010302c0340800d2070301550310301c0341d00140021000101040c000090100d05c408207a0f1024104501044000c01040800d15081c0a1036a002e14541011468144142d604030540740e4140401030541000303c0a000384040309501512030003000164041c0b0441d260607030001240403026040c403030b035070070000010495403401d16048640d040c24402818a100c101c61010b43e280744601209070821900000030012640071800301c3e00642d40c200210b00030300c5203900014040340142c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 717468543 1250 717467293 717467327
    0x1906020d051305061f0e04030c14060907090902040b030303040f060507030507050702060a0c2301050a1104060c05190b04020f09041e08160b190b01050901051c1b 71
    0xe0081032002c01c4d181d9010102010140e40306034a1240e120480110b0f030050140e90603104108000c154101800580741402840403201840098800551300c50080301e202006810031241000300c20205d4001600741d510081001c0341c0c040c801070110745560012202956061403030f0f0303000d105009081c850103400c9103e620301404130b45858900a0322512914070024007503c000501041e205100d02d8070200f40c1540022248421800b015943d0011124000145255407810022a668294900c20844400d8000300d030343d03003003e10380b41066503203082001c400e9a01e4081e6101820f140241c03000c4240300b05100781034101c55410240140041f4625594485000ba41c0c1d0b00284804914040c802000301c0007012920380c034450b0703c2e1406850314001e0500e0b40707800c004010407010401500c0170b41da41c0b00d0221068030700d14030002500100305482c02c002211303000c43c0003003024049551081000f443c00a005162058000c0b8034526400101e56801c11030045030821002005003460b4003c10b44209540c00c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 717469793 1250 717468543 717468571
    0x201150e01030b0f0910050711010c0801081c090e0702030d0b0402030f011a04120507060f0801030b24030a050c0a270e0c03060f09060106090b0a030e1906020d05 71
    0x90b40e600c0300103d90107000111030788640f000083c0c405004000304168440d4034041441141840303900644010044002041d065003023107180c3c5860381c41001454121550781c0e008003a05c3c031402038a01588e114014811082096020700814030040c4207810900500f4030781c2c01590b0302c801201460048850490070a071090f03004005005065142400c8a4103542004420710884c50f9815010400d41c421070b0311070807032003442c0d003940001d000020590f14200c03500c40e260303040640b1760342000b02c44e698000d000091246050314003040342d11004011602c0300c031810304100c80726000d602000038a010300c0c0d83c0c012121548101e41030380890030074015001c003c00d58a00d00041c9004240a41c6004810b481107061560363b9800c0d00c109260020042c040d49c1420103801c0e15042e0500d586160009001100c003c04184251800019141c1c03060b1051000c4903254500d060400c00701d90303c1103000d0202010400b155101c1c0d410346992603400c110308101c40a1154a00594410019698105450000b81b8110010f100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 717471043 1250 717469793 717469799
    0x1e09031502030f191b03020702090901140c07030c0b0a1b0f1403040f06060b0a020601050102160302011b0b0a02090a050d1703100f090f152304020c0d0201150e01 71
    0x100c04681604220203c001c0d40c0c0c42180e44090310018940c0469003801d45804801c814017043e0554006d064041c003d5802503180d039240c40d082400d94601220400540c080c00c000203200d50f0b0084060300b851840ba1800550051217034507140030810f4141e41c0c0c003c071542c0d00c2c8214981001441082d40c07104100c4e003880c2403181d0107140c01408003441c52030641b02d903903000000a0b040283d0b0406810003250300100c00c128003a00d441e001c843c0ca400203441c2c14058840c4800104003503000040c001048141c0007500c1102c01e05650044a031340300d10303051541e2019030101b0382c2d60000d0b401070750480c41103a0805005884200030f00c00c02880c8001039120501900c1c0d14500c100200300d20070181d42922042107105503032a1116003500c0222000340c2d0080c070080302d07022000702d01b18119400c0080c4c0160011011b02903c1a88023150f000e403441032040c2c08108401c80d00203550700f0b005000c500154500103000600f0f06c030031010480d04004032465a8030040c1d548040c0c584108a1103400c03900a4128142d086c1003a40c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 717472293 1250 717471043 717471061
    0x41e051501021f0b030102160c060c0b0411040209120d02071403060a0b2b02100509210102090301090c080708070b0a031d01020711040608031204060b011e0903150203 73
    0x10140d0f40c241d054201c2c00c0102c5410507141c124030b8280e07102900071961450883d03d03216003207060502c1120320004800300001d8461142d40d038000c482d40c1240a01b0b180f0f4681c0c3d541c100c128844203c40940294003030003240b8440d41c4003400c040664102a0180880c0256003500a04080064002282411030703000300142548000900582c0003481120000c0d445111130002207500f0740c3c440c03103940c01c580701d5000e0702100c20540c11500032440c400d407a0700c4508041c001c002e8549000d4809620340203d1001410007290340505500c0e41c880308100c000600d048509070200e0f0030360344180816207117416229010490661300300300d000010720307224001c0c04001d82402c004e6400703440345030356035402c054840c1d20000d2100b182e01800c07405100840001c640c0c903503c43c0340201904054260140c4614902007001030043c20120885401c1036801250081e5a50340c3c0d91840c0c020030045003014104101d00c112039090341d074501030010301800e2584078140e450b89186804030132980b040f170300750705100d0047c000d200da805 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 717473543 1250 717472293 717472303
    0x1b06050a090623060d060902060c01020a1d011d01030621230604060510330f090e1005061c0e0a02010c330b130b0d0311010b041e05150102 61
    0x3c2003c54a070340e0351001c0b0f821b208014003078151003e540f0280000304400c0d00d0700d0550082c4000544d40c2c0b02e0400900381000004a2440c2d1750f24100e011601071029111404106005408114014100000c40984078550300e00c210020060014008a80300d41d250284856908042c002585c140380c02116403001c8284140c0318440544000c0c92161034501150620000340c4a1201a04400d04207500040e0314030b50780c8061212884141000b2002c001649400e944149a440c1608090361144100c80386044110002d040d001450100d410b403a504010030507550f01001805107840940a004400040480680889603e21840c000c00d0388249103c0c0b0060760009081000b00b40c21051040d40c20595461102c2032500c403184c008840803140b220315071000060f5022500304c5405072100b180e540c01c004010421911240c511551000d880e002c4000041e2240c020800c02d0050000081171014401b8042400d81e07003a140c0010031180c3c4071003c0c82203401036102d0580d000c43d007c540c0404421010001030b40710307 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 717474793 1250 717473543 717473551
    0xc010e0f1c030e04050a050406050603060420010201020d090605060109092003150a09051501050c1b150c100b10090b09030f060907030b160801061b06050a090623 71
    0x11581481081c0d060500a030340f40141e50ba4007800510603450501d018100420080b54200d414903c0c160226481d428000b03030b401e100d96400308050a0021003800e21408071040b004040303046640030090b03116420058004c0a000c58820ae401056074200034002504889042d0404001d00e4909801e02500c2008100d00e40141c80140c50301c25500d48401c41076100604288207015004000354900107000102e40e4011071082d010010845100c4410074011a1a44903038490580c071980922880c1000c0b4000362406043c100004040b010141038000c01c0364550342141d154182c16400c8101c040c0c080383c840340200382504a04507070a00f41400425006058540507003d080503600d030100d181c83d03142d24200308012901014504960b054500710040580c2d821090004a034041401d0000c10305040c030a405200000c00152100c450036802c000d412102007000e200714119500486c151030020401030312603240111501ca80114880300d680c10414203588090340804240e40c2c0c51103078002446080046a504 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 717476043 1250 717474793 717474829
    0x3060e0c040315091a040c05060a0801090507110f0616030b060712030b12030c0d02030c280c06030f060803090f0d060b030d0503180a03050405011116080c010e0f 71
    0x10003400c0c20303c524010010f8200c000d115032412415100b041704402103c0348501e1082000d0030709661507000b4401c1314000d1030b0307884021461480c01441451210f82006500001c00e190144c1800c0b04c40c142c45180c0b1203a403580c401b09422400510a03450340c009080008080b80d400c061000f45842000728103107114442000e03055003011002e50284d58406c0d00700c4c620420000f00442e5016601e00c00c032544076486400d1034070041c0b003030302d0b42d1032181d40c00403003903136040c0b443c46000d0101d0324602034204014a03070018640d0b14035200c0106400004590f005000b02a0185a40002e45060b0f120f01301c41c110341a44d04855603580c4180001000ea0f03517114130f04402111306541d01d4903046040d00d0100040d04409917070b25454003403005002c0c075007540705001c0c6110312010a0319801c0b00300c038040640d840c3d121151000d03000900c104414007055014440174049185001c0c00c6800c4000310300080003c1c0300141c0c01440080c0c020000c0c400c1d5640e48001d56030311482c412200c013004c003c5a100040c0c1025000394500744 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 717477293 1250 717476043 717476063
    0x40813050a0e1f0801020f04050a050d08040b220621151203110303070c020a0b120c09060706060605090a0b120109090309080d0c060f0902011d0f030f0d03060e0c0403 73
    0x80120515a03143c0080c09550001c0d5100e00500443d00c4030368004d4002c041c09901501c0c00000e05180400d460000c0320340004115142a051242043c01984242e210300f01c5d00201034044010012039505590040c040b640c0c41404011203890001a69000d5030b0782c00d081541081e45c410180c040c0d0303c0c6148200c500c601c4042240341071618090361504000a82c03140c99003c04000c1100b030a4002d8609180345100700c1d401a207142d1250701e01f10150082003103054902d2040700c001080d10140034024621440010b003240d0030b10b0383c42d03544d04080d030302590001c100151000c6102c43da1402e11821460203014a803041074100341c8951500c2c026240144500d5814070b031180c42c0031040c1809607103000082c101d0300e0280e65405000b144050003010f40010100d41a514150610800322810b00c104100940e050303444d043c5401c1c000b502c240e0307201c141c5d90b852544820741c440c0e03007402554200a0b090786400041c014080c8410500c9001e82100c3d22980000343d0351030074400300219000c000c0200c1d0141c030343c441c506031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 717478543 1250 717477293 717477331
    0x902030f0702010504050d0819091a131e0f020409050a0512090f1005040b120910020c0c0103090c180f150b030112050705060c01021909050a03060209031203040813050a0e 75
    0x2210100c40b1009da15103403843c010130780c0e0610030400c001d10306040c01007402045540322035540c00e1843c860400054891541c14894801640b081c04450f50003d000307500400d20340c0031a40028040f20300c074a50440d03d99200c13015040410006100c6410111603108815041520f041d011580d9001144c085c3c502c41c1200c464808015805402a05c000c2c0c07400414a6890b203290180851030703020b0540350b80c03075035108500c8840d28038a072900031102400b2050010b0201c0d440f0560041d80681000c01d401c031840780c13003e40003180d00c66040e0742060003494654000315415a103100c1241c100c9229110f04051041544010710043c8501000c69044880d0b81c0b804600340740090030107900b0000542c100c1980460001200e8074080c00c150058800030511003420300301006811419142000c19200d8103400501f400c1d000c1002c200d640e40640401140a070640d00c0500d1a400c40107410351048504407071032030300070440d0149031480d42065005040c06079074644010341414140e408542e8014101d280201114081e9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 717479793 1250 717478543 717478561
    0xd050406020c01090f110409081c09080a05070308150303030402011b021504060206090738210703020c15151002010f0c030203040807020f190902030f0702010504050d08 74
    0x841c0000e042c40002c20400c0c14520344140c2040342042c080d100c0d050407a24a20341441d0a2142000d40d41c0c0c486491454426001602c08000740d010101c0c50000380e13981c0c01140881da502004103580b24407641c07410742d202e407103141c0580301c2d0724042d22250b54400013061016441e2000404c803900036409080c8600f0000100014018462120320000e42082200100101e01c86000004d0030a03201c045d02500c006603034000b51903644590fa40f00d140342d5130030421400c00ea010699400b440c81301d40031001504407803200340b0300660745031300800c6000f0b00d0306070254500040a0705450341e03d820190030314065240c080103031103c596400141c2e0384d800c40c2503000d4010501c0d000800910364910080600402c0f40d1010402d0060300911180084400c024244000105954424800c0b280310717a920407016820b2007015008d00a02c4d903108054950000683c0640c042442d01c540c14080051a8146016076603140594190089107c00790203101507a042409110010f2400326140300038003c82d103050081ca039120158 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 717481043 1250 717479793 717479797
    0x50904110a090f1b11070302060a05041a0408070e07021203060d0605090f0601170a12091205030d0c030207021f051920060903040b0307021e031201050402040b0d05040602 75
    0x89103114500d0708007141150754640d0401c004c800314400800b0400302902e4016144185400825021a000307400e09100514208018114900c29440c1090030aa280c890031840c40700460b0b24841ca120010404000380d1400b040314901070803060411103500e04003000003a5441c0001c3c800340884900100c0051126110789400e0100305030007071000c0c066400c4c0686919241c00c04903e80c1d14090207990001b1509403000e4411682d03440c4443c00034980c41101d900e440c11181c031201e250508010104070f0015500d0202540007141c01d00840146a40d203003601003007800c03250182240c406041c018403001c00940d4886600b4501d0043c032204070150889113801c1101c591082c010030702108024049032140305540032038402c490800300c414800c41d9180030003100d5504ca00494040e10103a0003000180602d01d0000080c40c0c1103c0c02c2d00494401200b401d94840f480280f481071038030391754070100302c610484203d550309900401050390214502810b05c400114544500b5407031320000342d1a1000320301002075070742c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 717482293 1250 717481043 717481049
    0x708040e0c0d091a090d020309060c031207020d030c080f16020c060d0e0f060c1c181220030a050a0903020909150c0307080402040b18042307050904110a 67
    0x304000510030f0f8507010701d40108843c0c0281c1640c501d0b100240c5110400601100d500750560000c0d81004002c50800040d035200340c04004c139602050203082c12000c0d600041d14050030b010b802030a840c100480c8002d0444c1c85000039541005000ea090200346240c4002403604110810700072110b170000c1d03400c20780c501611030001a821410000341d05103006882d900480308070140c24240d076140102c3d03507080b036030703480082c1c0d03a000121204002c146000c01c50618210468603c405000c9560000110082840c0c8843c007010348813020042d4460b0480d07548080c0122547d104401403105040d64022910b6490041414000074000e0010b1080400c074095907050004507401498503010780303002003040c1d4441c004101007010010300c15000c01d012424940a881c40340400d640d030344a46548035000c01001e44103160425400413070b00c0340c1c40c410f48000828407500c078030700605024100c2c5401c3e2410b103180b21204d003520602d68008140610440d500c00220030381142d00704001c000585114800145103044640c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 717483543 1250 717482293 717482317
    0xc0f060703020f0d050324030c01032d0b18090601030311010b030609070e060109140d030314150109050f0307170106150c0b060a0b0a0c230708120708040e0c 69
    0x1540031320ba1103521100941c4520908881561808148550b0311300f491030340c95a0b158150400a18130106502c294450407100c200c121440c207012100d981e0206004405031400d070080d80d100c910300700301824405a540c0d10209031508684071442e043c4280c41e01c411042c00010700304282e516561810101c25000010483c41c01410f540e51424016141551084240b044880c03003a88040083c1c0d003580651406000c403075244009055003500e14040011003000850103c05259a89501c442002021200a8401d1401d66100c030980d061810026140c14080d0380540d10941e4242100746d610b4501084c0c0100f01c40080b0760b08045003c0f0001c50a0142410380c000c0e0351a0030720344140403000f0794815803c1c054980900d24000309a01c2c2c03242030101010890145910741c410030050304e2801481100b0008510b07008000c034191002e03141110500c2c90110071001c02c8541d210600c144000c5078144640510600d03140d003c14640941c0740d42d04c2246000328410b40640041d21030014032480210011180810409 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 717484793 1250 717483543 717483553
    0x110304030e191e05031002090108041118040317090712060e0106080303093a050306010c08360a150908031c0e0c060301050d02011b050a02010f020c0f060703020f 71
    0x2103c96900c1e03000c11441024828400d00c1d20b20b50680a851003142c59508040c1d6a034076855079192261590040642c0841e904565088080c00020100b038811f64000d0303101fa540d40590135111a002d02c501103010700380e2800c2d0307007025030b007005074407014a810031010780e0001010442009180c01103004200c2640718081c0b9000001c20086c0701d10f80841c400c1e15118408400e1400d20700148404030b5810f002c2c05686c0c902105030208111018080c0005d560320000514206c140114240d6845905401410032040403002da001050003d004400800c0706406508000629001c103080006410000d148920081440c081150000c10b40c840e030606405030074940102c0e81d82c1d00b01355540502141152110080b41443e000e858a40541c01058240840c0d0340180510b0459017000c0400c0380c200b1140b00300720b040c000001d20b003240305413044d00003100380350003880900018040da00000d07110b6079107400075104542025110364042d0359407884050205506a030401e481e0403030340c035059152a440e084122060310075 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 717486043 1250 717484793 717484829
    0x31e0c06010608180c0319050c0316080706050702150901230711010816030e0a060f0e070e04150f0f020c0c1918090203071203020d03110304030e19 65
    0x30080300e40c000e6a03904090204ca15030401c2840d120222503040c80d40c9500450215090341c49900340045005d03015000361100d2100c02030001c4d01d05030403440604c0c4100e12005082010710301c180000c02c001d203d58180769160004544c0002d03400c401e4044860020900858884c5280e403140c20b034040861900b2044982a060a00c0500c01d96081000c0c05c80b4007200c02c00c180321030395100d0001d2600461243ca0a80b014a84416083c0c02904000401a44501c00d04a0b40c402149141c081d00f6401454110000340000540050314206000ea1f08045005102c2a040c070001401440001c0d1080d902e0b42000181d2207000f00d00309020305064108401d0031030010ae404100200c02041c40480d15001b01c54201c000082c94014095441c018841d0481d142030280b071b2035099600c1c0d0b41080000510003400d5035665929580c5010003880000070503001030303201c10000030715290188a507800e1008a05091402c501c0e26580003048004030b07003061030091480e00d02d400003800002e0344038405840020301c86540c0c181 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 717487293 1250 717486043 717486047
    0x3091504180902040c03060602060703050901180305030406050601050403021008100b0403080a0806040e07122109170c062508030a0c0e04150b0c1c09080f0d02031e0c060106 76
    0x72620705a1280d07151078407045c440e0b4020300c240c1d0b04035030180d00a060150394000003500240001000325000e55200c0c0030000451950044540341d10380b09807225078480c1030505000c001c80314005c002a06100f400c2000b4000342e0390390a00c2c03d501181501d041021381d074507034465130090040e50f80211a85103002c01c000c420030070042e0103014a0005943d583c0e82640e540c0007040b09440c00c202c0783c40c1c0b403900184000e0290302115146822058020348004c0c2803503429181214402e5010020072001485486092042d42d981840c10303c0581c51840003004101031010010383c0f98801c1e25219204040c070045000c101d82400d880c000b10554002c0343c0710b500ca24000440030080d049045500303000442180fa862072a1400e4070403100c905c044c0d03400500e002ca081403401c4460303a1250444030420301c600c1e529010030031a2003180c229601c41c555030b682080d610300b003490b034070784203d04079007100c41e411507510304078282c1d8000b040da6a00a2800340030304014044042c039507032a06c2544000c40e03035402741c0340010408503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 717488543 1250 717487293 717487301
    0x20a170c0a0c03060e0a2018090c10140327010f0203010f121a0603120409092f0609361b030112150c080f0115020309150418 55
    0x84c0680001c0c0201c0b006000c2c4680ca036a40110000d000784800350b01c552540404411034040b021000c0e24019003c0c10010a018070000d0444120140d03900c0b004000540f4101802200c0c14200d0342c0c2000201041e01c4851050140402402407060411031401506408200b210010480c840900204007044200c5005030195100b4040d58440300d8000000003040306a860144000ca60402521144032041045486035690080d000d00d6042c420190048128580e46004000031b010483c0c0003d00000c1c2c0c0d1a01d210540301c601032221444210f110f01d02180d01c0c1c41ca440741c0e8400b00c01c80d501c640d5100910005960068400300050017800d400c84408040b1007003039080740b40d0704003000d2140260b0750344000d05500c0180c00140c403c07c80d0741c103100400c0010006045000103034420b022250181e02c440580f032003150b0324400d103d07000466034401d105c6124500a00c46e4007514a000c038000705020b03136a001039624413903949540d0040008400b4125040b412005a4020b40000300c00640140145540310010b0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 717489793 1250 717488543 717488549
    0xb1903050c01090506180d1a0402150316030507091d09060105040e0d140d05070804060e07230d060e030a020c0a050a0e040c030203120714010507020a170c0a0c 70
    0x207072080c00c1484810750b00072800706080700c00040c002031030507003000010000709036110708590300180002c0d00300c000542c0c40c000107016141103a404802c580b400b0b00402c519038a01140700c3c81c0380751041040c8040c203a6081c8410011800d00d08012440e519414030889480c0103030745c0a0301c44004248215010348000031103190080810400300d500a03600c40080008468202c02c200050758081021214502c0c05160300f0408a0034520141e4140740d5150008801d40302c0072103041000030703070752401c00081004921500341c01c001c0d040001e01c1c0041c1050b00c941081104018802c03603819038500c0d034407040e80e10f103030301720421642c030040c144a040d00b600d00155070703600641070420150140c80043d90550802d001140d0403207000510440c4154a0140003a901c9100604165031090301058044056141001084001040d12400b1695140b250402a8a0a041001003202a4100030922000c0c80c0d00180c500c0c0781c03d4202d249503648042e0b14121050500c940b11120050b401403940110901407040c01c18422 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 717491043 1250 717489793 717489803
    0x2030a140906012d0503190302100b06030a18021801080d080415050406180c0f05060424120e06011a13060e150d053702030403030b1903 60
    0x56468003080561100c10034000c0b007080c1c1c4d001035081c00307a100044040d20142c180654000800c07a0300c60002ca0f0034249050a24a1381031a00c4508204143d810401e04058002d1980104a01c010304c00c0025400c0c4409451050070307584421860b4512940308007012000c0c2d50040c103007078800700a148400c4010109202e0700c03039940610034010540601448405108a60108100c80306110070380c102d02c020700340684185c5010703544898210340c1d85030f458641400b040c05140d07400744003490521141d481240e03a0704030380e01034001030104000111804e03480c0001d1160800d000220b8810034401211035110041e80c2020507428913100210491000c1101c0341a201102124411440101016121845102444800d4009c419002c00400c1d218468001440e8402440420501107160300300034036800850400101e04d40c4c03a420f03c102031400d04d5122110340d41c81e89481c05a1280003107000c402600c1d4558a51081d50004005001c062195110002205006011060151084a4090700074015020440e0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 717492293 1250 717491043 717491081
    0x203090a09270f0201260403031e060f0911130906091d0c12031c0b0f0102010902010f0e030102040b031510030b0a0303031a060c030d050f01060504140d0602030a 71
    0x40c031210082c0e00043e0802c000b00b4500d04642d00440300c0003a0103120070a9130560f1411a0300f450b0000300c9290040b4003035a400b01d21301600645008108025880c20034240c0e15100080124403a0842c44e802191080b05000902422080e420560f0303224485c0408000f0007205000b0034904072940c007500c1528003401d0204401c1e40400f4035030400d1400003108c3c1519500110000b10b461801002c0d8800a8a440043d0b034204058000c141c0042d401041c08075006a40340c030264445414040e2075512031500910080c045c034906600083c042082041c03282d0308000325a00d003541c03a51800d4045400400882c81c14644d0780c0303480440d042184451000c2d10f40314113105440c5a900d0343c4240900200c41798002c001d8150a03245036410f8000b0b04900764803920315a490b0400c500c0d19070f1160050968500244003a507035074111106144103c801c000c2201e80130051036001401110780c0001618181d4012a00404103170901c41e0008000e00d032807403030003000d1600010400a041007190056507070752400448042d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 717493543 1250 717492293 717492341
    0x1008090706080c0f36330c010608030a20010b06030a0c020f011109030d21020d0e01060b0d060f1a0a1e05070312020a1d010203090a09 59
    0xc400c00c0382070301c0d45004040144203000402c00d002d00100a0300802c3e180b20882ca820041d000054040e4041d21007180f0417404400b01428201221008014208010070700540000e0640049258a98240042c8440c00108000c0c0460b24254007100150480c1400c0307036218801000c0003070107031864003005240a0000d200003011303100c050183e00071b440001402e99080d03690300e403400c1c4010001c200d810021446514540c500040d001c1c86480152403840249568810207881410301c1e107071400300324804104c0040c10707003446000025101240d80c0c2e071170074000d13a81d05003081030007000c0c113503041190241d03501e4800001440040c03d07004008a52a540c070a202c0665504c00c506198411885411303a0300d8142000050181218002800804040d042018884130044110124070f6009400c50010540020303c3c5018540c1040d8580b2800c51601e0055142040c0d80000600003c0545011307081c100e491104072029178005d000380c400408024213564442d540e51000794000d8940e510366840703501d194400c42 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 717494793 1250 717493543 717493547
    0x13083901021e09011205090a05060f04030c0f08040e070e0f01030204030812130803040f1a0601022d010e07030204051605030115120f0509010605011128021008090706 73
    0x680c8402c0c0d20401422003038035049500b81500c0e8000c101c2141080340c0c540402607210141e10480b4000ca01610051001e140e440ca8070310302d403803000703403c1084111003e810800007a600a203203920181e400003043c1850985868161194015900301d0341726200d1010400000d69405006000350748800c0b1916100240d031000150120700c6503000260a40f0300030800301c90140012010710742c206003205014046001c4075210091541c00070303501141c003a0010b170759420500482c0744640c0200300c1203844200e03850404a002030b540d220030501d004800c03e00c91504032660702b00805041c03501c0f20341000a201c4d104800910030380721013050004912852400f40404c11000210b0f082c01301e412151b4451500e5642017403000c0d40d050034030582c00c2080150f0910209007000250050f003c48451032100801c1da8100031001500751803407904041e040182c0301803039100701ea1001500b0614100001e0300c0107496024001480880034902030044d411240a18950000b107920254091107080c2d0403080e5000261200e1741 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 717496043 1250 717494793 717494797
    0x109020f09010309050a051507080109140f15030d020f1b150d020409060b04051c03080a1d16150801050f09060d06060902090a05090603061308390102 66
    0x3444603480c0601c140d4450b075001ea40b0a082540c0103400b21494124556a01d9240c2400c2c3c0f1202c1c0c4141c040344091290b01034110304c069001d040054420b01c801d0100500c520f940b481c2c020501c032641104500443d02c80c805526a4005041c0061705442c0001000b440c003075a2042150180010740c0b0651201100c4002410f0700c1041d541d8004100c106209040286100690000c3e2005540c081d401c0100058500d210701c1403400415032003110503165450b1500304008000c90a070304500c102c0c100d84581c030000b80d00c041d1107648101240c0d800030725044018480400e80f802c0e51410701c8248200c0740175031860700090a81d90201c400e402c90003500e03590b608a080322002402e104554112401c030300240064580503050f03550011010702148201111902d4600540300590b00c464800d66001807000300341e042212000c40905015142040c1e94241080400d0381c4080c014012540c0c8029035003038030b04203c0c610341142c1d81c000300b8010207800c104c1181501100304220b07100882007414041c55030240c40c0c4040c02 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 717497293 1250 717496043 717496057
    0xc0103021b2a010306080d140c06160e01050c21090406031527030302251506060c0b150a0806040308100f23060f0f030108070611060106050904230906010902 69
    0xc0030300107041100c00c06030380ea2100c4d0580b03054614009d00245c3c4121408000483c81001c00007510141c004800310054600e200c1d000c1d595040290030090494061000500b1021003c03905940d1050300364076918001c401d010381c15007a903000c0d003020000414400042c450702c5822010807001c001203000c003800420784280e025540c850002c50300081d480468020b5020b0711981218034480640d41a801c55000107564402404a1701c847c00403400a480040320b1103241d01800325070810414006268503401c1c03401e81d00030070803019201010301c0000d6540f14007440000519020044547c5400c0600d406060b0140c100e901485512480b68005032a400740e004010440d1410643d500c5100f8840c52031141481c025000150003085c10400b8030340003000e81000b441d40d00303000204143c4030750510854500384606507200c0700822200d01440d1580300310100e0b820341182c40c60b080c510790300c14200c0041405003e403501c0c40002c503103064100e8414608020f0505100741c04400a48000341c0c1c031121004101c0c05041 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 717498543 1250 717497293 717497309
    0x110f03010905181002090418050f0709050c070809031507051804020405010c110411030702070305010e07030203031207020109061d0f0f061513060f150306080c0103021b2a010306 78
    0x2c5003102c0913503a139500510303604602400105182459140b1441c541060150807502ca070720404664079020802e004000281684d00d0b01406141000307000031000780078018014218042c00038141210f590b0410441c5c4006204114481852a0005014121350041010440540100024810280740c240300f218203a60058440041880b6540c032180f03162100d00b20120b030001d40d25042000d200031450041c521072007155000b003e480d4150315219003501e05101d4903180035803142030300b0301c016038000c415100981148907400e4600c0c0e407003406c05c0307000d01200030014040c0d5242400001410008101d210f01e2042c0c001c0480d0580c10981c0015a5520a44003200520313400c5800441c05800d80001642403115000b4080d610708030b80c540300384045884a07404152010114441001602c00756490006079a180742030400800c1d260a55a90302c401d40d00400f1810154000f540b00079841d12015410b410a601c681260009151200301c58009000c0d40600340e844200303654540000e40c032902401c02030310404 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 717499793 1250 717498543 717498553
    0x12031309020c0a020406090e010b0306060a1707090903030b010801060c0c093309050f010e010303030b1f0909050c28110f0601030201090509090c1003110f0301090518 73
    0x11000c580001e410410440345980510510b050141ea10790190901414002400042039044403505030300715010015507500036009881042200d5940c410ba02c4111035030f17006003101503401d1103485400c1c0078440c0c0264402d540341105100501d9850350120407804002e8880205c0c9980b5548103440c3e000d811040181f960f018510b0a02000303446402c21009a070148003807240c21900000e10801d10703100041d03261000a0342e5041002565054010b0701d07007248000e8007004c03065041c80f6501c1c00040c0140070242c00c4c9600e440012142d52945075900c0400c50070300c0c0405134007401c0d4400049c4451000d114a1904900780381c00716648505000440d402c186507021900d9004808e05520101c5003000e461032000e016654256a260b00000e20046d2558004840501640c4d8110b1001400d00c0d840382e080030b4050b00010040007004200050b1090059038110741c1c51841c81d000c68800c4014040c0c00702c101c41012004110601040d0214015505941d03000b40144000c0d1b41e2101c1d040c1a003200449625225441 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 717501043 1250 717499793 717499799
    0x120316081e032e151e0309051c2a030806030606101805150a03140c03180f100605150705060c03040c090542060d1401090b120313 57
    0x104060b440e40348140c00f40c00c1000e55690403140e48407041203d9440d01051190141840c1500074042855204415040130084003d060310b40d00d954440081a4541034004030380d28920290040e18540441200440094101504021284210381d001e410840101d2284400300e0490f280200d000307440b1307170400351054140c400c00d200c045803040d81402d41074416020080020500307884e10403550340340d10700c0d03c09502d5035080c0300341e8000c00301c031f01000290000b030701040c007445811008501140e410410312034002090203203410009081c10030b403101140301d034400c246421405601d030741c00c00380031101c04566401100e8200b04032511680f0525000030200c1c0c1190b000201c1c183e8104001c0c54000f401401c2441b01140c0360342c0380c001210382c1550307252a40000303068000500048888140b0240922581c03421040f03890029000c4003000781d1403018854a004a59410458016403081c86184c510a0544880356500c0042400900324900040d0040e81508039041c5207190000032100740030060040d502c59945 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 717502293 1250 717501043 717501091
    0x1008012702040b0301090b0a0603020723010e0a03080601111606050a09031202060a1a09010317121f050901080316030c020301140a05060f0f120316081e03 68
    0x30000210030445a800d0101203014400c0d500030b18060321030440000303581c844910800c000400664418000c141c01045008001555544c801c5004801c0701030401e22140b800700840d01600c0f101841005621901d1805070600d58404d404a01a0f4000c1e2201038510100c0810f413900e03460711000c101e400003641c840c2005413611070340017000f603582146001d44409031a42c0e503102c075028008540a006900010a105180c1c410744150003800201c84c00302c2e8072045182c0045025880c0c1440060481c40c0c480d8065200000080100e03035001241445182541c1b801d0500c1124199a4002c1f9102c2125020340101d0340d400c196000038180e6a5201c019803c11600f140440360f044030109080f810840e44e03503203c6006032000d008072581c1481f00080a8501c3c0f400b0000c444c101c40005280d181b09208400e544003180e01c80074088102030405440e040154254034010510f90f10540c5404030003104001286030600000c171010340f00003062f46614642006a860840c4041d010645042c01601800004078118903 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 717503543 1250 717502293 717502349
    0xc0337201b240301080d0207050105041508040516030503071a0f150609120607030b0114090904081207050304060b0108060a050d0f0b010803180d080f0f07080301090209100801 77
    0x261041400b260a040a009944072940003a880030546602c03e8a02c01d50140c1c051010102415081c604603003000d01e0b0042d0300c4c041f00600c202c8502408585d0001c1030034828148a10004031100402c80500340da0350b442e1080d501d80c07140741f040e00c0381c11480f0000411203400d10a4203000b01c14102c205109612000510841c2950220005621820400c8020643e8850040c142c83c03442d02170015000500c1c0400028080d1107000d022030b4104981c2802014003118018262682c4001c20f071751040c80e998440c81c0440da184650b218403000303015060100140150300100451243e4440c0f9402c0c054030034403400561f181a27080c2c41d601ea00c130b0304a00080c012424481404882d0b980143e844500d02401078880355010300086e04400c1c1c1a4000041c00c00180d80d00040d01c82a00005484030599481c0030380b0b401c3c2c2140100005003403500c0700000c062a00024000503a0b031441c0d00f090304940d03a035039141100741c0290b1003402d000c2d010b24055001b00180300d005000090499000c04603402c0b080d60310b90b042030104 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 717504793 1250 717503543 717503569
    0xc1401020408010f02030109051008030a0509060912012f07060b0105160507052706010309150608101b02100c0302040806040506040204110c0337201b 66
    0x5660900001901d26001d026410b40f01c89610300041e1b0300e5041c440010261207004000c80c03c0307506102d50400c03010800200710741000f0034a182094889003400001200c52282c6035080354444159400310051810650280c01005000181440101040c0c0d1035150303031400f990501202a4414405040402d806400c552030b4541d051500300d140600c292011180701191910580d0590f1100c07405110500701317040030004c103801118203401c5a5111049115048000415603410540c40d8807030b000c01c01500791101503040e403a02d5028001c9903150b2060b541c0e1150200380d2007111904011390b440c100302d850400701410440b81e50142031500c004864110240003c1c0c8540010161700700300c0042d1100d014802280200e04c200003a146a0610b40108825074402d454404d0004030100104191032100100311100701c1810501c0390300800c6041d040510360b804002840f02c041c050080c0c45400158000300302955145900510030806c40038145203943e030b030f5180c01d0501e031400c00d44100c0030513450a18902c08a0f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 717506043 1250 717504793 717504833
    0x706050901050f03040c14150702190312080a0510180b010509030d050d0f0b0a03030e01031103070c051b0109120212190309290c0106091e0e0304060c 66
    0x10f0600282048800e80c0d01c100c0781924901c0802070300307010f1503000f070108800d05203081718040c448107400c4a14921a101d0003070024468409c070341c5105009100d5105000c010b5400c5841c0d2980401c80c1c40c80903100c80310440d901508607140c20002014a043c2d100b4000903100414403040200d0000040d542c010a4220140ea06220091140a1a0350707003c0003050b084d2030403541c1b45911988950202410386180d00152040300e410060450216192900c980381181e80500c3e0191002d142600140c0050903200740c950201e1000008200e10103420500009029200e5401c075031901903280612401d0000760107944c5e0001300c2075181000b90589000340c601c09140010070300700032035440246180c6020034001036034454914000780c0e2010b0580021040e0000c0002c1c3c045000a02109060310782005c031180c40d103005460340843c0740000c50f2025403101014040c0500c0c1000b0f080c0c0325006042224130204400125542804540d0400c1c5001106440865611b502c60007980140c40d950305c0051081241a485 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 717507293 1250 717506043 717506047
    0xf03020c0c04020f040501080a05060d02010f03020909070c030e311d010c09080105040f03120f0e0c03011d0a02060a020307150618020a14030a0605060d141602070605090105 76
    0x400c507a920f100400c240000404103a80d42c0340713820000b5105110081c6040d0740245000308000013a101d032141c2c2620303135a0901e0110071918040034160001e01071301c040103421295030010080304a030010740f00c03032065009403520a141c2640b04200075140c00e5110003180040d0a00414a00070f61185804000490043c0c201146d500d88596a06c100103202522400203a03440d05030058200b0303006403158001d00409002072215140c582c44804900384103050003020041144011201440381382d000c4070b0361200e2070009001c905201016690744a001e101010703c25460040080c1a03c0c0d1011500043e034015140039104e9049140c01f004400d4100c2a9082e003980001c1040c440020300003041324034821540600040c2d010300300001c1060200d10181401800c80c41005928401500050200000c1486040c0340b5601c2d41e0300440440680180d078070054020002140030b141400c071076040f0000741c6501e403030740e09050360f40c01d650100e05a03e070701c1c900409a0008032040c085144640d009081081c01814a40c0c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 717508543 1250 717507293 717507313
    0xd1a070c021e0406081b01050711061c230402060708040305071e1202010c020405042414100b04170102040e010303120b06040b0409020306030111160c0608070f03020c 73
    0x2d4950b94410215074661010020742c801502e0035220301ca000c1c1000000800d05200c2c6040c3d4461900c41200e101d030b0520101141041c20008400242c46010780301501080d140c014802e040c5045040c1c145901210f10b04000350304100c81710980c0341c464070320072042145003a5260341e000c0c0603041e072003040c081d19110001c20020020600030400b007001000303443c80860f1040e88aa07024a2840f007150040c071400d85100300c040c1c0142c1ea04c007c0f00030203d03370101e8002800f516140741c4079015250074205024004003044001ca900d007000d030702c040d5602c41d900c01c4144641e03032030703403540b90248409014401c3c00c42c2007400240f2042245441803128202c2c2e401c001440c20b52185400b00b01e004090303104800040188000310f00441c4c15006001c400c920030f40364641098205200e44929010741d0054000782903000c40050003c0d0707002d4001030181502d50000d150b452008121803a2100340e642825560888800c84c00101c01d441600c0c0c0f58420000350343c6120b181101e81d007084003c3d500440c0d07c00c0b481c1c41640204 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 717509793 1250 717508543 717508549
    0x21010b041e0207020310050f0702161a09040603060e030403151407050304030c0506101d0c04060e0301020d050403080907081b130b12012c0a110126040309050d1a070c02 74
    0x1171800340d95240004103080c81e188074020f14145260014080c082151343c0c2c10007440c2543c040044c4190182242a0307211850344011170010313f1140d10250001d410944000f001c2c0401100a000f070f40d0145007466004400c200000040e1000c6450a01c683e2041c0000129010b100c0d202458000744245400c0b65071405580780d15142010030344484c124500f00e00703000c00c0307482ca800e0fa1a48001908070300b50031051400b4440640781e07020700d1151006004c01407007060010355080d41102c562802e81c003020011821300b8117004046040881e402d480512a02001040b50403002884e801410f86081c007a41d1904101000d02070b9040c01a41d4003250591650b1088800d41e13600c001c021f84d14006c890000800031001c41e0514040147d50142c8903190161141042282d1004500d4407a4140c21400c083e40344903281c1c00403181030b00d0f10f2641181c40718419019890382541c0c00c1005002d10300990701d01c5070344c40e111005c0010308c8041e50402064071402c00242030604002c1d0655a034807003201c2c14201c900404a03004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 717511043 1250 717509793 717509801
    0x18050708060601030f05060a030b2802030103140708030414060c01050a0b030d0903031b080909090a0204140c03130602090d0b1006090609170c21010b041e0207020310 73
    0xc414a00c0c0c1080c0d0402c4460b582c0f61241200105821038180540c1c10b14002045e599100d601014108001010000f210039605510070b500c200040c00701d1b408130120602c840c500940080c081100c010252004501e640f40340064508143d41c6000003841c034261901d14194102a20740d000640c0015091121080c602000e01c20284512420300c0082200300f480700405040c00b00401540742808004581480881c0d44442d00c4100800c5c4d1000c464400a09400c045103c0d00508440d5a407061074031007040100107010880d0b407006442500c0501c00c23815502c001d030fa4051002c58401c1c40d17008080c4001441c2510400310907a045010f460010f00c5d01c1c4040010035151143c0e420140c1f050488079051180c43e0b41c80c0d100c800010a11490034030341e07441c1410340042180c40729116500525a41c854a444811003d002a4400050007018408441202113648a2007106070082c8042c5c2d52902c0b1550000e403e25000707500b0408010110f03816800c6070300e02010001e41007218182d03014401c95690094040f00c0740302d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 717512293 1250 717511043 717511049
    0x6090603060f060504021e0d14070504061412070c0f020301020f070b1510050a02240906060a03020f1002030d0e06090f011401030f02240409060602070513180507 71
    0xc00440c902d001e50518034140c80303c0390701180c082c9204001c40c0a5003082503000540e1842c0d0110503d9443c20f40c644e241000d000f110052640407020b100034000e0080c2c014005208851240d2a41c40c0040010301d6001604c0c050040e10f155403500c030500181c0e5441c41100399a03280c5100e18012039409205401003801c980140000c0c0d450f0036800103604013800705c41c40006500c5490221034607441d1400e90007049181d200005560280280030440c25800c0d40280440031091260b1f0040200038095110201c0d6056802e850350940c44c007401c07000c01d2480c20082402c1c000d40740c000e0b00132441c0039000024004854111f0700c0010450000780240e6250580f60f00418035100c0d5400000d1841c0c2c2404921075003800c407400c0d00305850b03030301d41103803420101c8012281d20304490304504041c18031801800401c0240d19401d000100070300550301107990b090000c00150054414000080009075218130040c0ea40d0703e080d0007220f50090741c60508880940c1a600055000c503849100e000341c000250b61540c2c90312103690 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 717513543 1250 717512293 717512303
    0xc050405010e03010204050d240f09030801090c020c01082a071b0608040b100503030c1b1804140703050d0302091305130f14030d1505060309030f070606090603 70
    0x1010862036034020300703000820104030000c600c6d007403601001421032080d203480200340c800043ca041c1706140c2c2455003504080e40b204024000780002034103510041408070411000708144000104a1380003a204040005801d6001001c2a9254400649101e0002045540803a0750381d25042d00ca400012f00c840c0e0721158100740c00791100c0385c40c90007000403006c10f02c041b5000581108104459a8003405864019802c402d6003207072038441c03145812031480c2681120fa0540700c0081c159511b458001114801501301c030303607817042844907c0108980d00294170410714004810101160100c0d903621009001e1400d10130480b00c64582e03d46d00c240c2401000c1c41c42c02c001ca90301090ba0b00e65810b11294041d1400070030700e01040320f40b90054610f030301d01555400c0541410306010b0f66200b04a584000505010300d400112500ca039903403004a000303407400130a010301c500b0f2964000103941c188441500c5c0201a140d01450901e51403400b1509a900306920648402e500c03030030b001038602458491480618050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 717514793 1250 717513543 717513547
    0x9030706090f09150b0c0c1e040e010515011d090c0a0e190611010b06130f05101e02190606080f1c030b12010c050304051603030e010c05030d0c05 64
    0xc200b00403492055070090700c1542c146a20041000c0340303900080e00750740e034440710307580c4541c0041c5c0e11038680107084140c0c42e00442d42c21079510340d50b07100038400b07022028119020300501e5442d40c2064241c40040d9070b40d100d80091451051111b600419030b45d200000c50090711303804038400e04001a2068005c0e82d4101ea00f00380040d007042d40c84d0f446441904940c4d002e8900d6801140f01c01b0a4403402d418030720840040080710400415054401c1d00098140003008202503210645840c5038420361840f44149010282c45000005560074100704d07480c0580e50f50348503c000c0243c0c9010200c0c00c15001c0c80c49500314020304540080ba204a0f040101c100d82c0a048001101401c0c860b045182c04620300c5c88004980c858042c0c104543c90b860384681c049020b603c2c0100302091898045820000c05402090a0f942844c0740421041e5024000c0d41c400e43c029800c8494014501c500c00c0340443d03107808060000345c040c280901c01d6500510030401e26030700c92021645400c8451000004035064900000000f403c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 717516043 1250 717514793 717514799
    0xc170703080711160b1c050a0e010b010c150e1513031b0f060b030307020a120b06010804050304060e0607150e06010b121308120903030f010909020907140903070609 72
    0x2108030703081d000c2c00305200200008513030300a0540d10800503105020b48202c00042000041c00c0300d03400240c0c41c48052070f0500c541e0030202d6009019107483c20042115601c0c10f0140031141d03105030600100ca0307400c820140340317111404800c04050202c4401c0c8a441e0f2080307610410000f801098250f01c264801e8650548840781480d000313100120365034900700398000030030142011603610008004a2503001e0b01c005510040031012030708500a505002e580010941b500180041b620244440030902c00c03410501195141c400660b41c0c010140d4004d40141d20602003404198094082804801002030032103003000641c1e86c032007056000503407020302c1c0152140c0c0405070b50f00c400c001043c00340c13004a00603420100410850300c016003004103c0da400c0350381612200140091441110002801144003442e1881c010464603a01c2d4410340342c01510518070400000c001d42103110711002d107580103042604603241e41c071040351407029680044240d10820802a20b1a5400b000107400600990300e4020110746 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 717517293 1250 717516043 717516047
    0x2030105060a031505040309080a0b0108010509030a12020309010204050409080909150f012006010f0608070903150207170c100516020d050706060b0d0501080d0c0b070c1707030807 79
    0x9030140075603004002e003030018400078803c004051299908040b00143c0c0b43d40da0300301199240071a5004110500501119505101e56800803070f046e510004024403441c0c03603010003180c0d40c1c410811150001205d11400c1f032180390003500210380100d4614005802c164403040000c0449052a0017110240d0000980000509100410700d03070195140450780b0201191401203002c0e045075002890400c400c1070440000080f480100502c80c05030306048031003541c0c40f401c0c034000b4204140125408a6040703800140143d1090403690240c950001ca1402d0f00c007400c10001004c1d42080900321103507203c82886240040003d40a40340701c011036001840c4091000003400b04441e400342c18801820001c1c55035550b01500020940c5103d40c01d481d0440c0d0b10901030030300d00c0080200d5001114400700c00645400319000580045060322810410b95081e072100304001d5500060a60008080c0c0810100081c038450182070340f44070090045a04942500d542d410318006075000355003c80206208500b402a555 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 717518543 1250 717517293 717517301
    0x1c0626010c080103021c03090e1e1b071101020102071a1905131e0b01060c0b070201090c05040c030f02271e04090204020c06090c0112061406071419020301 68
    0x70364035003800e940030b50454000c100c40e00c00003481c0300c16010340303044110700f010f105181c0380c3e00610018505003803506001c0740d5003c0d03010003075184101c0c2071a0480403410070203e032101900d1041c24448054501f52244d81d4023201d16542040c03442c1555800d01507000411040c60000918010140d00042e407460310190150200421a0982d80158544000c020501c5d02c4030205902c0f0700d400400c00d05402201c401d0310a01c0c0159090018041c1070200d000180c0160001c8034282e2152240781c079584107994010040f404c80b103001c1c0d806803070030207080e604001905045e0f01078200d91400745130104280400b500c1d0141a60702c0a08038812501400d03201c0403c070380c1418814181b9580407120b080c40700850804030404d4019544040d44116504c9262004545c0c1d10f904441c0b81130030f15000d1700c10340d14140c070541b0b80380c0344a1440c035408a5000d8040b40d907200d07010722800c400d444d0100b0b00660445604014480300b508a10780482d40d2002c2542c980f14812020006000c0700781400399441543d81051050501b92 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 717519793 1250 717518543 717518561
    0x405100c090b0906071b0e1504090b240d23030f03010b1317030d0507020d170c070602040f030c05030106060c260307021005010f0305031c062601 64
    0x70a5881c410700484504508a60003030108881032900c0d042c45007800d050412428403100354100200b0000102d02c04194000c40c82040c00c5481e15030301c002c06030144000e541c02490b0042668410390000b424841809000d601107003040800c42c46990020710201d5101340300c2070720a40e081010801400800500c031242a80342c4100c2e8006541800c00d08851031010740410700400680d04404901c030b40b090300214045000400c1c020720911181d00c6840d41c0ca07034a81c0d12081c4a10041d80c10680040d101500000b94840380d0f011036a110807181496030345d41c2c2007011015016500442040020341e000c038149002810161044a480000745441d510303041e06c1940942d4055406a410400308201150300241c940b502c694001084009690f03020110810305224800f0341028018088240000d940d40040c04540ca10440c20b020069a40c845024218950301e621004055510401c5805e074000200082020402c2c0c68890100d1000e48800000340c0304139580e0b11061101901c2c80c040c440702c5070240540054 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 717521043 1250 717519793 717519797
    0x20f040911040501170c09060a030c2601050621010306050f090d02030301090902060d05010807060e0f0a030311070f06020a12030c0c030e1302030c0304050127060903090b030405100c 80
    0x182c946403900203803d80740140c04101600740803070300013000224031808580d4400d40007480c4070380c2c07842010f001900800c1700d4001031002504400c180701c40801c45208201c54845c00c03e02550b09030786001c04124041c1d120b003845e131240040101207964100b0301d00c0d14281c06540b298202140c11b24100c0c1f100580c0b03100c02444d2147d141d11060483d00e40980100c22a81500c04184000c02c0e2804a40041001c0f445904440340300d0a10317050002a50401c046040c03802d880c03092755040002c0c00140708010407401c4801b60744e9032040348020100002030083c80c01c001000c0c0c805050b02c40c159903c45032080002c00f554003500241e040003523800c04210340c19510604088103414204401100716800415504da80c0a0013001d0203030381c00340b102840d524035450308a00700c110b031000d56882c504054807649030341050b20308603442c1d0308001d0b401c0f1003120b01c0031000c000f6070ba00f102c0c0c660042200780c0310342000e03010302d0740143c003030102003900421802251002107214a005030010408260006241c2c0100d07203107600c00c101 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 717522293 1250 717521043 717521047
    0x170c06091605150705150109050106020313051c021e01020105220f0611220b09060a03020313060c030c090e0c040302063106080f01180e0a0501020f040911 68
    0x103103186000204406440c801c0da21140d0b00c181c4106500075600c04c1c000060543e20880324071510b0a800702c0e66003416500313006018441e599a5800c01d0741e070b84c010b402401d10307103000c11002400306003000902103031010031100080e442c4038115004034031079000d8a040403124210606080303205503024050240c000307650900704004d83c1030441442205880200009000202d400c51101c280721b00c03070b04200314111841209603980d04150010010340e0b0300100c001e1403180d001103400900c4d0a404801d5400004028000c503160401c8420118004e40c001807038418446001e03c0541c0120342c032481400d400842c1c03130301c000034600564500a8002c2c14a0383c80046c284c0340301400c116840244406460480c5d506540040c0c0b80c10f80b00c2e620041c00e41e90407910070555200035244a9000358051107a00c00c4440c1c0740c85841d155100c0503080c0501c11001d0141d05044c01c10f2501813203c0034010345c0030300072414444083d104c6503030a9683c1c1c1c9081e82e000d4404900704007004903040c89104101c1c450081c50002003102c242c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 717523543 1250 717522293 717522313
    0x5090c040603020c0c04061451070f031106090c22050702031b01020406142805030105100206060906040513050f060a0b010219060b030109170c0609 65
    0x22000d204500403201019004680240070400c204500500c2c01c5000307005002140c1c50740303885c150b20704140c400e07284102c0e00300139681d10451054280c54032000c5000f0f506c040c0d42c1740c0d00e01401813030710710106a41e9400750425841100807401d41e0142807036034403508240d1151991410b0003415000114800c1c1e480ea0031441c184803e0000024402039014030955001b81320700c20010421101c148100e03c8528440d04290810156640c044011b004039030706030303800c000c000c0140c400d100c6c01c0b0300613401820085914aa088039940e4180000b0b042a402c021008100d800001c0c2c13000c0d000d8815030100200881d0b800b10060002d490503514107102100c1d14401484030b03141450005a0b820805000503008503510b038046601020301501c00001c1b03076041000c541030401851103081d40c1c0c00044811800c40e901c1c260480d1000c0d80b010a8408540428040c0a000302c07100f1384440000785039408040c3e9143d035907084000000303482d45200401c600c101002c21500c1d0000c00c0c190034200700e8024071403001600480c0721300c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 717524793 1250 717523543 717523561
    0x606150e100e01030f141e10060503062b02011209080412211d040b0607031d1207030501050106030204180216063e0f0c010b10080f010509 61
    0x208450101d0b1a00c0c1c026540c1e030000603401080000301c10310001d8103080300b0b14860301c03501d030306640200c0801d41c680c0712551a0303011b415006001035810090342003c88008002d107910550246800c6000204660810031201000c00c00d825080380600c81c0d0411308191a209540e040117240343c0310308c00d264082c00200c004d40e4481920303206078000c8100403840c103100c000c140300b800703080000132840101c03110484100f2440c02600c12030291210051420b890740404040381040c0c02114981d4801620a81c1441c1035a6000d40b88100d02c00d0888500440d03c0c01d0801d00307039079403000304036036002e071100a052487d0030340c00c1450030350380142c100340c06040c0100003c109401d5032500107100e00720001c100603104e95403401450300070650020050101402c1200f1000c8003900320a15040344421180c0020309064201e50181d0184254440d0f400707551014411a089660005c008180c100072078000019425000c800060002500310503c00000d900c920421140c0c04201d01c3d5140941022100d51440380b42150303c0e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 717526043 1250 717524793 717524809
    0xa0c061e18030506071205090109031d0d0506180105221419060605100f0f03270f051509030d02090103150311040b0402160f1e0606150e 60
    0x10001040010001e00500300107410001014640c810142c50701c605102d0001004410084551500c1c58a0500800d43c0124144200c0b002c0c6036058071148001121a454000c00707414010005401404000e2402d0000e181440202d206540e085050180f14882e800201c1c2140c2c2c004000c41c05a0306588011082c49944001c1854a140d000701c550411002c1080098181060360700d03a0907000c00c0c0382c0360341c004220164021105071030007919100880401108102c500310703445912480880e9218034440f030954800e4201105604604c40c465140955407100d0302620f4410800036107101501100360300c00c000040c0001d083c500d46030550780c4524202485055124170405800c0d030107690780021681803a0b40660800c0346e03804020001101e030745a407420005607488103a20040e1195140c00310342882031910b4826900c1206401c2c2c032260500055640c1c010481103c0402a81d60558401c42d210700a00d40a0700c28404510450001c20250702e4504111b4910406030007010130f0100400c1c131000a0307200c4c506 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 717527293 1250 717526043 717526097
    0x905101d010b36010807091803090302011b0f080307351503190c0602120d090602220501030b090108030a1809090308060f01030204030b070c1a090a0c06 67
    0x41c8520703691688503400d11500c1a03e050a04401c4a450000503a00310100c0c0100445c0c041140512144c00b035281010741214460700c0042c0414035071801440954800c4644400c2090203000113003420502c0d80751030401d440310000407602d440000080181c42d42d402504400c503580d480d10368607050404016200d404562110071b4402440c103100c0001d11540c0a041030800305900074003652184503000141d02019001c42030240c81c0300e205034400140d81c1d880058a00003c2a058a403d4141491030480b034000d0a0418402d86400f50284404020720401e88131a4040100003030301e45040300d281c440007400b550012221148607120441c010402c1000c084100c42d807003281441c2c44698805950401c8030f00541c0750b00a04400c41ca492500c0b810141c1000035280500d40c1100c10540c1c105c00700d0b00444c282d11503400003c1150380c4d40000300d01c1345801070822003503151040b45405450100e10003c40c50241c0121000101c0350300403c1e00390700780180c207000d9030040c0c071091a100044d807018074000d641200d0118 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 717528543 1250 717527293 717527329
    0x9010302030d080c040f0311010201140106140903010b09010b03011403030712050703090305120a08010b071a09030d15030618030504051203040302040e061807270905101d010b 77
    0x10300062440c2c5050744c2214040d0400f421003200340d64a1f400e040600003020600c0c0d81c0590718016800610256400485040794443d43d40c0c203200380a40b21004a6070340005000c0340e0150b48030b03c3c551300b550b0340f04141c80303010784001c1003120b403a5850000d501ca02140580841406074104004d00004140c003081140003c0485040c100d90300e01c6980703002c48401030180e00181090080248003101031064400410a51505949065081c1d0325100e801507148214807000f0210800c600c0840b102c2078000c081140c0c40307036000054070300f004200715011042c1d03070030050b064010340595a0709008010052081030423102c010b0410b6001c001c019980513116100741d0207002d00c5080b903400141903e000c00c104403400755a005e0310500015070f02030b00c0c4613540d010a944420882c410403000c3d04442030300240c48002c940c4040d01b1480101c158501c0c507011001e80d00e400f03014080e1110340ba20049081001100c0c00b4500c0c4c210002880041c03078414205a4003600c190040c0703641407820700c0c1103503950801c140c02110160 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 717529793 1250 717528543 717528557
    0xc0f0204051812130807050a030303090302150a15060215010306151d01290a08130609150b0f152803230f0a050709050d08070c0509010302030d 63
    0x112200c028544118009111031044884000c01c45128030041c09031125000e566070441e60310b4036011916040d46011f029040b00e00c2100c01c00c08640300c3c0e08880e12860081c01551007420707104012613021202101c6000c0741076118280b08600c0700d0f04a82150003400f991015102c5102d1482d00541a11410301c0060501521000c00743e030007866046148004122807042000c01104050003c06040030901c03880c0000c90011159650401204200d0300c0100406000c00c3c3c0351015806040c0e40c80200a0481d00e903607407010783c1c2080043c40a1190f0000c040c05804000301c000300d00c0302100c09607401c80022a008450942454000e510307802071142c41e2030364155105849034840a40d40d004405054041a0217003010142c1300320054050707000412180c04811001d1880320f042d0541500850140c0f0503042210841c070000342c541210307038031258220a8919003510225503c01c001020102e0603801070320b1002000606104200d180c400b154000d18003a21010003a61451700081d4840c008549040705000c90703 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 717531043 1250 717529793 717529801
    0x601140102060a0b1c11090a0c051606091e0c0906050f010507061103180d0305060603040f0f120302121008070b03150603151c12110a050105250c0f020405 68
    0x10b07a1440c5610040c945c4003494400031142071901c154065500c601e4050700b01c040102c1c020245900038500e01c2c0c0000e880c6d452400c2c135180c15400030715207901029240c41c0e039070720084400500050014450720060016501070545142005001000540c0c00b56088503c0d1031030400c515150003600c0e921400c03090030441d403503076601e050244c0644030300c00301620205000000c01c103401e20790035002d00c0c1d121145030031188290701400d4250100c1d5429904aa4486002c0c030008001072543c0010b8412075210318000c054800c4580d1300ca4400e106400341040203e0380114943c40460040102c1030380c024040710341c0403007041c600b40c030300d80d29240c040c05100000000000051021000c01466040b68103020f841306aa03490003d030381c4186600c00c90038103031140c911040c402196480b0702e1400f50310709811688000c403000d01a10700307940580458190f582c180c01601c0f42c940110b4028400d0074441e0b1441806030541e031031031031030a40c0d1001000305100300b03004070554030001041c4111a0b076a115a41a2800255034503 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 717532293 1250 717531043 717531049
    0x306130302071802040f06080c04180b03060c250b0406051803160b0606090f09060d0c080c0907020615090c070516030b100302010c0807020402090901170601140102060a0b 75
    0x4550000703c1603400ba00d6480c015296558010411070300d9800d80ea124454071038601301c4202406560203002c0400501052201c507420429000504500749000107044549101007400d0100032208022a0013000c6138120703000000d100200200d21014090105500041d0348440e02d1840c080d202500c0343c2e40e07600c002001c0d41c6094844220390411902240d0716044011000303880c1d41255201241d122000c000424502d081c1902aa000c180000b4100200b856129040c0542000014a483d5000150b50701000110f94507020100c054141d210103070654100007410b200c4040c1c0c0c0506040b0466101d0400c0054070f91205081150103407040b29003401e1a00c0b4141c0b40d5070b407401480c0d4064951700401c01c001501c20000821031041b28443c080c0708a2039900d009400d0100d058600c0040c1c04114200c034448002841d110082c100203100a00c014202510003010840d07440098100071511140040c0780190b940d401c00c022401060700901ca07000c203400c07510000f1f4594401070180300b1400d0301c1d02c0c075506242ea = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 717533543 1250 717532293 717532303
    0x203070e120a0c090506010f0305100b0f03041707050d11120327030a0e04090618080a170412080402220c0e09070203030f040f020a090e011a0306130302 67
    0x500034074610035149000549501e603041c4220480d903441e4000c10002e8030748440d000340b62080c0790584642a6061044a0560207000010300701d840c60303e4459000310f91182c85a01610300381814104179912440c25141c220300711004c040441030600014009070300040c2d0001205030f85a0807601c2d0034480c141000c1c242910782544e0318400b5083e8500481041303540da000b01e0310210a1640708843d0424125007000c00354480c0304400c4d0500014943d0722a0440505040e000000003600c99080051844912200b50810040103401203442e030038001840189503601c01c085110410342c1c14810961420b10755a51348034454400d031188103000070071000605641d506074444c07048ac400818451020f01c03034400d480c0000d1048686000208041d400c9004560404607076881c400d840c1900110318549401c0c03122400608000c100315074141416014134010b888186000008002c01c100200c3c040d0400300e0349500b511402002a8078090b80c91200c45544d590002c0d8481d00910700c444081d40c00d1046080c00c074242 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 717534793 1250 717533543 717533567
    0x80702090c07060c23090628021b060a0c021c391217040e01170d022d0601080a0203011b0c12030b09040b010305010608070602060a020307 61
    0x2100c18410841a00c0124006211052150104110a040011060b5110030820710141c8840c80d4140c000c029041c8518002c1070300810040c40d00d41410081c00c040140c0e42112030043c0440104500d080810340d030100417545003910030340c0703001150b440524007080690048414074820420180640010b5403a40740704c03a150124512528032014695003070105e140313602013822801a00c09054040030305400b950040e00c140541d00e8104080c18034040842d6144d03c0544815502d90307031032071141e0300144841401440104001500f07007009603d0000030301030110700d0000107401504026100e07600c041c1e0210300c5149042420303c1000003000b448000d441044641801540c2030b00c51840045041100010004d00181c4200d009000f60030000380f0314103400d8016142c100214035000c0c00e00e00000c08000042441382034615000500b0007001d00000d840002c2900c1c140c401944420040c0b050000078080c403000741481c00e00800041e4542a0025a1180c2c014851440e60354080041000144110900508 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 717536043 1250 717534793 717534799
    0x8071b0201030617011e0c0206150a12060c030501050a0503030a030c1211071103160b0d021c05060315100e0c0d0914010b09040c0603050711060c09040b0d08030112080702 75
    0x4558030f620113060080c451461030b00300d02e42c1d60401c016511724a90043c0c010640072540036001c15121783e42c0c004080c0001260032030303000c0c0700600003260f100c0800c4009140700f4020600850301e00300560b0b001c0c0c00ca59060300b00f140115161070051120f03031400412240882440e1800056078258000100c0d4810b000c1040210340171f00b042d02000c02540c120000d0580340e8040e107074900f011444003040507034801c0e02d50b17074103840c040010704100b00a07041000034201c1800da00e4009441d090810740581c5070729201001d00316145035070346c040c01040d00b010404c0450020001300c8601c141d0610860400c05801684110700d500f154020020f07495420f200d00b56600b0f1840c2d20401c0c0304034521490881d20a468441c1041c2d519803800700c8003413240ca400a9801c2c015500181c80303031071140c1095812400342400030020700078072005840b4856074000410109100e04240030f04151540d500404000550301d580303102030320410f0030b10304c200085002e42c0126411912400c8100ca20342d829460258442e0140a001a46c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 717537293 1250 717536043 717536069
    0xc14040311130c02101103011a030c07080310060807030c0509120c0d060c110106180902030c03071814250c081317030309060406020a03140a0f06050108071b02010306 73
    0x2881d800284102c00c0e00c030003107170900401c140d40d03220702401d000900c42e480111081e40441e04031344508400079a0032800610078603141078604d0700c1d10b00e40c40c2e10a407546c0c0841c0468040c20040310343c1c0003100580050344c03850148641840d040c0700801e40d010300d520051081154500c41414801c04000762009894081c2a8008043d1107007841ca0080c0031841000c000300b00113625401300243e041c440c090681d030343d1102c039625904643c28004018a101442243c15214001100415603802c119001c0105586440a001d0744401c1d0720200980b600d03400201c101c1d03401d02c018404810b007010202c03410312640054a0070300b010024400c98441540d104054507940c4000350441707040d100190083c040d1a581c0d0b5113001c900c1145020710359244000ca512980a8120380c0110b0001102e0b50020706180c0d145140108925202520030803030004103031111074140303070317585100900038a0500a19000700400d007080440751500c804040e16003124110300a5140091542240c1168003c0d80000c0141c240020310360 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 717538543 1250 717537293 717537311
    0x120806060714030a1e020d03051b03040b040624032a060801050a050d080d0b040f3308033108102f0d06050d050a03030c1404031113 58
    0x5443c2c3d80302110382d8000a45031181c010101c111154038401c1c80300b00d940100b812481da900304070010f0001514000202c0903403803d8820040c20000a10b004038083d281018060a10385000c908940f01d81045104810480d909a0880003213140c1c1d00d021a500150301c4a0240d01c600c2c0f0b0819144074480701d4019010219201040c03407903200c03c00714180c0e00f0aa502020700c0d40c440d82084001c01c2c0c1500d009103203550811201c0340d105403a4106000a401c0544045078000640d1030b1a01138800c511408406100c0e9034002010b0788541c0a205204144d1711040a10064184001c060700ca104a032501c1752403c80a884055015400e600d090034140540701680c84495141e02c2485d4650b29000d40885110b41091860101d5a200c0305181503e294441c011340885210740d854000c40d90805041c581510f07a40c2c03480082e076500c82000001a007440365012b4103880f10b1500c5e0103021180c04d002202d00b044200002d115215110030300700c400f42e0b81c2201c9605403620b128400561400071119400c1c0c48a41404000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 717539793 1250 717538543 717538583
    0x5060312041d010812030703020a0c050607020a0b0c0703051207020f150103020112050919020402090402030a0e06100509040f0222020a030e0a15240f05011b1208060607 74
    0x10520202c840100603000d640e84108095680d0a40500302842c00380800209103454020350041a050003c1e0602d50b1001d0b215458150600c601103518501581000781c1c45d1080001e20b000c03141e44070b02030702c5055082ca001610018420301448203051803070001800810001c6000b04030791200110310030102d450000c02c90400d80c40680e400e11040f404640381c5160040d03451054020300b8890301d2031000600c0d46504072510000002101c010a0341c1296080055011a8966000551207108201d030040380b0810100c045c3d074036016005200b47d482a8a00c0c0040c0400c0c3d48804003142c2054001041111a4030f080c00051a65614000c20307180e00410810365041600351a0058034190505031010804410b03a9400b10361524813108005064944160103901c5a0003140c0c00303042c0e110450200c070b500c40e03a21801040c00130240b5030840725415a411408207e1981d104406030344c03091540e5501580c2003d1580c4401e150b802c9203071024140066203001404035141e40c800d0320421504843e0200c4001d00701010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 717541043 1250 717539793 717539819
    0x120307111b09060103140c0a09080f010b0a05010206040506011806051c030908010b0619090803030c120c09010c060e01020c010c051e03040c03030f0507120e090f010f090506031204 79
    0x807940102c1900000030020f43c064420241030400321101d032a0f1541d504960420183d0000011b5410300c850310202144100d4100b04003c6607000e00d81c0006420b01020b8100040384c540c2c0e038807140c11507024600304000100080352060446030501e5104000341000240741c0090101d40d040690003e1740d2003540c1c40b202e031001c030b4000011402a102c1703d91168407054800d0036524521003840d0402420840c10601c00c203002e07500443e03c2c40314545402e446e500c50360b0280c21075009031240303000c0c2c620206040c00d2172a0020340c1150486200145285080c0400d0006010b0600540b80600310b2952540c401a00b480c0a404441582c0700000003001640c801890240060f001918040c0506091981c88000e018800d0126800380e50451054004540b43d030390b040b15240c038041c0981040003010700101d130001e0598810b850340f03c50341d030300c0d07103a850250b0314140030a0714001081d411458240800410204007800c6c041c40640f1001440030845544110109181840007001155a03600015000841500c0142 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 717542293 1250 717541043 717541093
    0xd0e0109140c0f0301020a09050904020307050409050a06050a1e0b0f0a090f0b0d0209062701150e0a050a0b070804030c031103071e0626070e03010f090512030711 71
    0xd4802c0e403c10502051500300d008002e03014011030608201030140e40703060000141d001d40300400702c41c0041d07107034401300d019502c581204440a600612408007001000e0080582c012810f40040103030441c21a1881c10b404904e50380818406d1384d425540500b0707100c01039030031507150010340030000c01980e410340b544c01042c1e90b0384006206490840e40b4282e52a20007080441c07a90024508100c90710b4581c10803010b001d42d13880e603d080b200c07190310000e1100180c8652500030700802224041c07114060030301507c20f20500410343e104401496003841242d0b00c802074441a00c141d0b502d61502d5108610340b8081600c0381d5000a4001c13804c04100004200070f00703444524440341038040e6010700b6a00e42c94500a41070110345003624540c1e400301841980d105104111081c544109491003400c0c4c0040040301081045c1c0c1d94400081380241c440c0c0b402e007424024040180007424040002d54072686500d9103c20015007840135009000010031540c5100c1c41a40710b06548280035582c1ca42d2092551b4042011401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 717543543 1250 717542293 717542299
    0x7050c010507080a2a0e0d141b12060415060e01091d0d0903061109060315040c0c21140c0f15010e04141204140306010801110d0e0109140c 61
    0x304c0792210505d4081910004646250303100c0091007021503040e2182140460701c584c2200943c0f000402081e4840100114600d00354064621001036048614507014058015401501c12410740a001c40e0000350040d03100b81c100c202d40d044c2001c11500c020240c80346074800041c03a02c2a500104421205501000c10301030014000a1400d1312412507135200e640300760002010403641d020800114a094110032480072009090510348001034000840030740007618165080141030525190a04003031142070038180c241d0400303d00091040c0d80d20b1440110f2001c0d07442422905450040c0d00a000310309000445000103141c0b03407078560b4001410b5580c10710f410081107034420a1824000c400189040303905071014000d202c80e443d555619212102d5105508503c01c51080345c410606c482401d0001d0b201501c0f8404100c030395074544104051414206802051890b45030050b522400e4841108030303540c000021801061101b2502c031042d0041040c080b0140070b41060355065126203401180c0b00c06525011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 717544793 1250 717543543 717543551
    0x30f0106020c0d03051810050306030c01090b0706200c0609120a1e27030209010801020307080f1b0301140907022a0d08040b04180c021507050c010507080a 68
    0xe80c40c100d0341c1c0e4041e54000d68001490600d0326000c24492002400100d8507424403442e031821007000700f6030801c0301005081c000346d00070040c17200d14501803150440d4240c0910340740c1c001c1d40c140f41411441d4800c0940040c0460380d1aa10361881410741240241216241c10605454050301c81c2c10b1511031038226941c801c40d01420008072203006801e41921130600c071960f00c49503212000e086046c1c540600103000750601200650000070000d034001d00d0340030342030414001d507005891031040c0003e844040c0c1004556900510807c0b500f240d02202d86d40e48220f0746000b070704031a10f4020010071201c20017407a1540300e2400100100e03401d80120460b14000c00242c540fa03804c0c5e134840704100d0329042d02c0c4801c03803180950900c10245100101c407d402c18080300502c0c4901da001e6a555a0055603c20307400360501e008049003c001c1070705400b07010840b1a44140081c409004030f508029240e0f81d44c001c1d44c0c01c481c0c4540300401c030564410f0013518400c4d15420000c010314240b8071409840d905040307992201c66820 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 717546043 1250 717544793 717544799
    0x50609031507050c160605070308180706030e0d0302031302060306060d0e01021905030402010f181806052403040b07030e060a0b0a061412040203160f0518011805061311030f01 77
    0x5245d20001c6680f02c2c1e86150030048565400c40f01010041d0200103080384210b076031684020107010200040209440006010381c0032003410742811065043c10090503c14070400031200680c141480c1010790481d20309a0303c1d682c0030300084080c020f542040001b00d1030000c01d440c00040550080001d108441c1d4207000782c50541c0011122803100712402800507130f407100002d5015028510103021550154500180ca5032103028100403100b010035500354a41d05c42808214a0400c032101191500814050940700303560016807445501c00600010003418030440010902c0b8031903403041e01c941c0804820f49905003003102c840800391200180e118455911503000181c0f250040c0c8607900c4a4500300007690400141078040c1c14005070080c000da805014015034845030303080c0c5443d881d0150481c242c03d078011070308080074022000403009072003001d01011001445180403c503402c8420381028031010600e0340d6968081059040c0c0c3e40008455507051099544c08448041c014601c100c503c0070300800d02e82c0e6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 717547293 1250 717546043 717546073
    0x203041a01050616050f030d06031103190308040615090f0b01030506030703061505280909080f091f0e09160e01050c12030117010c0810050609031507050c 68
    0x10a100b09079001c042044080c2d1003101100307140b510103000700207462104080b02d84403411070b840b40d4a680d02c9199240350600c2001030207040600c410000f40c4c0202604c074602200340c1d212200d001009001e2001100001e0308000503070304945440c0401c0d1021100b2180c0d20001c49000c0e1440207050312517a42001c50341c511a510030701c142e43c45201c0060081c40000c2c03a5032141002000480106032100c0508103000c6650f460700c180b034a10401c02164446038031002c0451f00304c0c44240d1900b0618206041841c08004929a84251034001d810306003038a549101140004007040302145400001c0c6d1050b001501c02c983e009808142c0811054a000040365152460951103000c02c28410002c0303120b800049485500c5500940070f01c2240408031049030b00c40231f0903071800c2d40003644612130f07044401c4c41aa4031001c0c03c0c022440e4000c550304140c00c05007849a04202d621125001c2c803409010302180d810915601007220440404000c90b1241c1542010302004141d0b80c0856140e0380b40e4410000c05482d400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 717548543 1250 717547293 717547343
    0x61104230f150a02070302181b09090103080c24101205060f06060d02191e0f1809050c1201050604081506120609100c050a0801090e03040305060a020304 67
    0x11001001c1c0550380b0044010800c40360441c40c071a2046103c4c104c008001a2201c08800540c132210101c004010310384880e4054810001c1d1608103200302081c401c2141684880c0301003810740f5400b5604a0f1103506a1121038075294044010b0071503400300031039503172010607150001e6004c0c0b003541c0c000e4000583c030f40b46908003984120b40b00070116031220b0000713546044142103054001c240144454649100499100b041c6e0300640240c101c540480c1e02200c81040c7c004441c0b1469100000d1070b442800c00700b180103050f6480100581c414089070584d11104840d0700c0e0380c404003a0442c0c40c0100000e00f80107051102d10381005180710b011084050002c40d1500e040c80a64044545000061048810000003803c601c40302402d1703190400c083c0c005002c1545402d01c03940b403182c0e001200070642543c0070701000c8269201c1856500c00d1102c100619001c081d445060641901d248040100d03081a020b0a01865449503600282080c05131206101030002d090b001540110f00070244218443d00f00030398403141c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 717549793 1250 717548543 717548569
    0x50a08030a0f270e07020a030210050406090c1e0e040218040c0807261203160c0b04030e0102011103070903030c3212040501050301090b0307230a09090308011206110423 74
    0x540d0082d08200030400f0380b4bc010740c2d031040c4586008100580642c1d41c00c01010303817541255958039141d11010100c2c20711004150010008044440080d003441d8002c07500300717041e51150421800c0701c100000c082c41003142d60310009000210480b00c04d160740e610f50340115900700000b20249030382e9128403461980c00003010310b030040c0344196040c0b41d034841c88460000002049090024013528a001002103201e0720f0011348984c2c001d4954003030404005000a0842d04c0100e142d170140c05043c010b01201c1540404500300750703541424645050034150a000392000710101e00e03c064440c4034815000c0c0340340510b2080000520250850760035a61500c3c14150a0103180a428001041800100031842e00e9030002c04100c20007809448050392100003c60000030301d00080408000310b4140c0e96505d007000400c5030024a00c001d42001104429940101005010b115003c1d1b0b41c0842480340041c00b442d6400524480380803818940c2c0c440c0e840c81c0c120007050350341803110480700980305803803414104055080e2134 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 717551043 1250 717549793 717549797
    0x2091f0b0406081602100c030912032a050c0a0302010603020109120b060907030b0a09060f0f05280e04050a02120d08071407151401050a08030a0f270e07020a03 70
    0xca1391042d6982e0b41050710803850a04500c40c202c88040b191803948603000d6149800d580108407000181440348020b10840c4c440380415203041c840d005405003a600b4100117190b01d0400208210495000b101d45008581803540c0034000c91100c0c0c0e04146d0150702c0041128401e0329000340080c0c1c0c0301a103800c0455900f8001e4082118240080c0080c5440c1e860b0f50391081e031500300001e5003106000400e0042042d41c00810016545440a010f142d402c401844001c03c040300540c0800c604010101d81c80c581840348941c2c12200c0315a9015900d003103403100390081c050089030f03203140d49080d090550f680c4031000300c280c1c06802c0384503554000d00350100b08105030032055181c4221944030b2602c122010449811403410100f420720884001961894402003490500c00c404039101d40a0080d5403018241039000d9480b40000843c1004244c5012043d42c00c1c441090800c03044050990600781c0303900f101800000b450303011164100301c1d81d4410101c61000d450360b0070094000b65660701811703a0b4840d440000980 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 717552293 1250 717551043 717551057
    0x609040b0103170f070c14060c0307020d021c03030c170601021c030e030d0f06060e090c0f090d0b04050c030d05120a11032409040201051606060302091f0b0406 70
    0x400310b00300121003d40e01d1008070f050b518088074000c0c45515500200d0b01100c0125465104003c00042550081094041194068901180e5071081c82d40d03841209802130003042c0c00241c410665890304c0041000440841c811490103040c0e24004008021005803640850900625070412a40c154200c1c1c2c4119410307002007030a242d45d96030091031404214140d030101502d8508004401405102500340d2000b003260115003120710404a405685542d080766082101c011282d06240d0340f44062643c200e40c5e07000c8a0740c0e030360400d200030040c10322402c0860b40d00205009880301c104000e00400c24802c4d401103043d5864840e19204141c1c6030f09800d07060381e0004e80c00348401c505161180c10501c0c1c00107410100002c0000d107020000885400840302c11800100c440e064001080c031110a0400c00701c81201c0b0320901d490a5030001c2d000b0b004803110100ea0b064644660010130529a0142028580051500c00396203002240c0c60411850081180c0c6000011400042c203408464181c900350380c1c0c00d803103480e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 717553543 1250 717552293 717552299
    0xc05011514060315121b03030c120c010b06070c050103240b0f070f03090e09120403140a0609080d0b0301020309060604091e0803070807050901020703110a0b040b120609040b01 77
    0x120b583c0d04058604414140949007088460360341000c0350000e41c0303007240a010a480030101010103105e40c480711300e00030b8000300710f400c40103540410072441d410545034800b901c8016044080d030040c1062840c40c0d0b08620001040030502051202c41012900240d07030601040306015071107040c061451016415058802c0428002d001c510b2000c1c055a00c0d55112883c24803829489404d046c4038120800d03404140d5071141800800c4403a04010b40c0580140c004103540c011703000040c001845648005880014500005144010103006452005401c2174091000f0b24490402c5007a1741e00c0520944d421504c1e1000c4100641411f0007031300d00c2080c0b0103001e040a0780d110070510000d442044401c50350304820010710010b510340c0c02060b0901ba40200f001c6910b0780340980001d031212201810f0901484002e22503540c890380d0006544054a5004070000591120740300031030341800071604140c0f25030802040100e0a9140500580018030780c88105104541385d0350180301d040d010a0b24080d29030b41c0104018 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 717554793 1250 717553543 717553549
    0xd0e0321011a0c0d0f05360a08060103020118180e0d02070303120b03120c010902030601050a29090409060b0a320315041a1f180603120c05011514 64
    0xd1001e404007420081d1a001f80760300305501030345248045c440455050320f0003c2c0b4180e00c50104000300d501c2a6060300c221410074140650702c820512000b8100110280d0413480d60400020000081036030850000ca0b01c4600d0841c00040c1114000800307140c8201408491124800218001181c6e05621001070030484520710394041e2900741c51698140c0714500408004128070300003010a4100d030800001c11485a03c10141044810b0b40424800d901b282c43c140814420b1050715a1130703004030402d401e004110400303581030a02460004a5001c0c1c5005004014001290045850900f08540c0b442101c0c1e250b0281080060100f01007c0034a40142110480d010880300b90003105140101101c02d81014a42c4568000030b045400711241d10a441e41c0c01e000d085544102508080703c51001c00072880c1d400c196440440c00b500c5040e241074050700104040307038200d9001c1d0000e1500b00c42130b0346501d1031042000d403c03c54482422200d640c40c0144208419448280d03c41c20760341000107480c0d0882c048810 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 717556043 1250 717554793 717554807
    0x30f090105250c17070311060309070503120702130c020601050d0c0e07030f0e120307180807080f060108010207080d05040602120a0c030f0b060d0e0321011a0c0d 71
    0x41e80c0c011801491068003941c0001c207440442622901180f550b044c2807100074101340750348540715800c81d802064240001468881c248210040c1546c180d03031250fa4000c442031501119911039601400707048014041d00c8940070090000300e000b078840d040700e40303800d0240364111032101c041440144c002da0014020382c64104103598be041d0080c00d00301e543c41c3e00c800c2401c01d1f20409031100e801013a40c1d0300c52520310742018005c041c80030340040b01a0800071280c059204a5120040c50b071410000604c0c070140c40e03100c4003800b42c0c000e054100110707444642c461450958818000c04000494440c11000040705141402180c41940d0300c400700c2703818100c02c10303102c00c042d05018000b11880c1d5001d2121080707100c0b9108600380701e64140e80000c28007039824500502121065400c0d0100b581c101801c0702ca964440310308451403a04850f1002503414a840b020074114011500305c0543c482034001c07010500c021500a40341030710b21038008000b40380010b000c100d885104d502248a56a089075100030f80c050f00640c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 717557293 1250 717556043 717556057
    0x41514070e3a0f0503030f1012030c0b0a0f050c0702040509061504050a0f0f1a030114060f0a080a0b040203010b0a06080f10090603030206040611030f040602220602150702030f090105 80
    0x91040643c0d4015555542980c00841c0d01070301003c00001004401e040140510000b80660440c4410451041e01c0080c404455041c2c00b501c155035040105a502005a02a1410302c0880d0b034100504d052450300700807a40d001c0001684120300701004078503800c7c4007007041400351010587c0c456429954a050101a01c030040646440301e43e0307140c0058046120f4001c000a142c122400041c05807007a880545200c1c0018882e5401ba0789070661460080c15038050301c6803c074008480c990079420003140006d030a142c06810918950142c440b1100400c017070078030014000c0b1304c03c400074091140080d00b804142c5505101d50000503101c1804a15502c2c1201181900b011840358100c44490700c650068058071569070003180140e000404000c10f00001d4451030354200012801e052450400d070700016480344010780007a00c0d05500050030191100c1e190000b00207821100b244807541650351402948420100d03103d014000981e000045040344040103c41070700e45546402402d00f40580011119508204 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 717558543 1250 717557293 717557303
    0x31e0603031903140705091329041808040f05040504030813030c12020a060f0903090510020307150b120f030d0b0105040e04080c0f1203041514070e3a 66
    0x62411211084000c8005210300401c0d2542603451420205200d507400d0300300108d039501c5180000c0403a6129a8050304003580304480403001075504440d0008004041c0007801000b85400c86030b00e5030030842d0240160040b6031451008000c0165582d05100569004850050000c1c0c4030400081600007602d14007122a806480c251490b1b00199440e1503640035440940030150307120030000c40c10007205004030f000d0b0241c07141c0140001c00303003070342c2c003401d007400a01600303208500705d100d03a0480c01e2080045d621501d81001064401882d14038240c1d00034042018014081c0c485540c2d044503400c1d00150882d5484c112800071451b00312942a010010060803280c581006402c10000425402c1d01c0d83ca00e0281d4090199a40d8814461002514007840f00d020003080b6040020b0b82c00c40e05109005407684107030480440001040c20214000c000c1540000840e5000c0b112020700403c16840441400554402d844160260352104201500b0b01c4d82c420032410003441503006004403c0400c180503496901c61 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 717559793 1250 717558543 717558551
    0x9090302161428090b120f0c040e1c030b010f020c010c02100e09090610051903061505220c0e0616020316080a02011b1505040804080703030203031e0603031903 70
    0x554a103911940c00e039001049445d111122020a8580301c8070040d0300b04480c00041c605152000001c030384071175961246070b108035600c1c2c82c40c4000307880030b02640100e0f80490069207500f010040c006001061044602c500140b468118404158000250b4180414050711800100605642080900d0141c0c1051804001b0030300e118070155283c03d140030307000300349490103003005c2d141420708d602400e541036002920946a5903d0600f0f159000308011060380c1d000207010512840c40c42c405414503026502c4650081c031407000a00d6010180035680600c00e141103418041511211800c64003c5450619117034001d6041140707120b1280d881180c00f00080c4058299002d001c402c4540034180905580005810742180381081c0856078400008594226803860303c001801080d01c403103409074036040061154559400106043c41000005d580c001c1164404540c0b1072500d0340f034020b40303941055603110507039050505110070301c202100c1702d1441550302030021410034020103050415100b95501c01c3d418036a43d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 717561043 1250 717559793 717559849
    0x5070c12030e030711040b060306061909051f0305070206100b03190912080606070c060f11060702030a020c030a0b04201003050103140109030806061b07090903021614 73
    0x100f031015055485c080c03080d000c002500c0c1e0041c0303c10384800c0204544110020000c128040d642c1005580f03000c40c0d038145031503090502220554191030180c00a40c6d000211045209409500f0007030600c150300703980e0341400151100c800c180c0c0c0e074000640700e014660017003c0b4180104061440035551020301c00c2004d40d00640d10303d0100007190329103030050718882d810b4554100445e42281c0c50940040041c1c07000361800701161a244c080f0f20250251034100203105500d126210b11806070616000e05460941c0c010342403101c00a59640d00c0350042c1005405082e00303407415450b0124070b450256400010140306991250790385070b2040703e5180d1100461001e03000307c4007140c81c2e41154301030480702034800217025419802c0146c0000020760b6042c1481e8144056900020362280341c8a03003104050720a03c2c0c80310583c00201a07001e82c00f503821000303442041d0002400c00d20301c2c0c200c0c0010034080d07000d450004080640040c2459458000d0529680081c080d42c101c0341442801c031500014081d245000e43c040d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 717562293 1250 717561043 717561071
    0x305010f0519060e19021b01020910170612011410050418050318030f1b130504051b040e1c0810080d1407050a0605010501030e150c091c080408070905070c1203 70
    0x1f0300c078080c6106a940400e00c1d00c2c036414048192030700b144503801c00e0b40400355000d03000010000b0081c07005018801c095a8000020f0003500302d0002d0302e201c04459200b602c0d00c0300a6450300c0c8018440d452089080807000c2501d4260000070741d1140c0d8110001d9484d00448055144030340340400141500f52140210310b415440d07041c0001020075094107402c203001020582041084502101709014151134501448005400050f00020750346040031080490007144002030300038403500c0e0100c40c0c517009003100040341152007040d41d1220303d040c0c1c803030b1009034544001518080445002d0400113902c0351155020442c010b400c1c00b030b803547d02d820380c0346e00d0320b0607907905e00b400d00c0d0641c02d0495009807142d0040c030903980c250184452645003000140036140f11001c02d80003403d0003800034001c1810014000c50305d81c6600782ca280d050040000d204032900158546192240d1151080140318000da03103020603540d04a009681c080c0714917a55060304155a51580e1000d40c00071200001030680d980030801801f4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 717563543 1250 717562293 717562327
    0xa030b2707030b0f07140711040b04020d0b1003090f11030304090e1c1e0e040b0402120a2912070317040f0b0c15040c0305010f0519060e1902 62
    0x540f2410b2840b29a05000011403030404001d0310003000d0003030800000c80309031a21000c0d505500e0700128001291040e4001017001807540406194002d400000c00c4414002c0343c4c0c0080c100d20708240c846580350050124120b040700c024500040541d601880c842012034001426403958040003801c0d2850f2643c1e030b440c05c0003240c2c007113420f54020b80c100500d0000c1682c02c01b03000425030f256138200020300c0036425101c0c0c0c2e000c140015441c424070015040b403410130380340c0303601c86130038140301034011950b0b000020a40d5407000400c0b601103110500b403421071034410f07031003207175040000b5210404050010007540c20406c06403900c421401d200d202c1c90100001056003d0304030030b24680c4508903665220305010f0b521406d400c45400903002071100700f12a46490302c00092a03000d140d05d41c4020685a156441d00c5017000d440da0b84040c10640c00c1c80000c1000084641c800d074089c100d001c100003c5100b2400e51030060711200d10a8a0500501400040155590320081c0d000c40b01005c2e0300514008540094040803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 717564793 1250 717563543 717563549
    0x50301020702150304032c09070e030d18050a030318120f0303180c0f08120711010f1b1506080c030616050c0106030f0b0c03310203100b0f0a030b2707 66
    0x481c01c01082d0041808c150f20410b41100c0c09140524111100d840425a036012002c07a4000300001201902e8a0342006603228002c0d180007030103606e019599050081203124801401d150040302550002103142d00b81d000b184055a000c400f6008403409a14154000c0007600c48201c254214050050002002044010301a0250940c042d4005060440861501c101062032110304c0008120182c0441c2680281802d000000d00e040024002800801c59458450b02c101d0384440841c11504810003c80e0b00b00700010030b114610402c02650380750b0400d80d480516009050705504400041100c1603900080e1000c0000380381031203031801911304100c42c00c42c0c1d5554810756070441d080a100041000e820f140d1500429001c0380c0e1811030904c0c0400c5203038240300c040e20544c441400140210880c002108040810b9002070950300d000c82900b5424000d08810124a031003542402d2a80311180f810344200b0050700c0d0400c000f4541e039990090003c8803150400100e0f10422400000058060b20404c069005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 717566043 1250 717564793 717564857
    0x15101d1306021209101107060b0a03080c0706020c060f0a0c03050c16031109061f02150906100503012c1c0f08070804030804031808010c020a050705030102070215030403 74
    0x81d0314000540034140300e503c5d0038108419082c95081e05102504d43d094641c0150440782c00140d00c2c1c00b02000403d0340302180e10081c01c40d14003048100c02d4400200c0c1c100102c0d46590283d9070780ae050101000f10354410400c40c10f022090a01410030300b180708000d0f44249a2190914a181100841d5414604810b400c0d412400107030742c00090040010342740d003000d0020302c142e6582c18a0300340f410000d001d130410b2005c0c90400303003030000c040a0401e10802100241d030140490030042824060095500d6040c01c450b040302110015100290074201441200601405071051030814643c00c078803410411a034090f0000584200a02c401204c550003000d610550403e031543c0d1400184100060701c0110300419043c01d0150881c00c002c082500452801d500c0340d80f502d828410300355140050b90b144052a0050384440d0b281a400f07180f042e40000f070220030740c0c1c051070403501c0c4256203800701402d070320407407100075081078000c900010101e03040e50203103401c80e00c2030070003502060020800c9403481d001e000750a92 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 717567293 1250 717566043 717566077
    0x6020d06030c050603100614190f020c0307060e010c020d080a02030307090f0b0a0f020a0f120216120206091f05070b1501080705090411030915101d130602 68
    0x1040101000b001e0b030050009455490030b5160a00c0b191303000424030700c01c2c2c40500c40006045aa0454404101c079046803462030300b48504003210100a00e42000301d4920009031048203a001018a400613402d401c855003a541c1c0c40485000270011542151070f210100d070400d49003c9102d0000e0451005410744408070343c0250f8591510440041440d0030503440700c3d07203040c0040303410301c0355003030410031642e81000302c1c2403c0100700c00c1c0403012031804584600c003405049800380c0f0102006440d50040d1824000c950031111071824550500c030104002d0701c40c807030480c900f00d520100142007403000b4042e91003004100505036034921411960100c070030300c1ca61000a1000585900300300b4a0012150004049510561038441d4040080c1085102074030107409d10a02051625050b50b0350b8110407030b804482254036449043c404100f5960313840e01006003540000c05d100040030340141d0401241121100d8079800000760481c03001c60f0a038603003d490600301850041825020a031503000400070000ca01d100c0701c03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 717568543 1250 717567293 717567299
    0x50306390f0d0b01050c151510030f0f0605221104150f2a081303030e03010c020a17130f03080a030e0c220906050915010e060604061b06020d06 63
    0x70455640780d01050505c102803140120600d400541c1006a0112070340c444000c1c2c8030f00d8610066107c080242680c0310f00929076501c42141c0c1600308071000444684248485075001070360f2019035010740103640d0070410250018211220b84400c1c24007500b0f0310b00b070005d2407050242e129034036a44950024111680c0d0b8044202041d40c1c4240d1094034070f140351070304012810900c00780140002c4034043c980184500090407206000040703044648054402906580250b80d81c07a01625000860507286d1082d40b07400140c0d0100b40c0007007013841210350301c121401c3d40c8403440b44030b401c444e4000250018080d070103218041503c00e28680110302442c01000304a03115441804004c080d0350f1000b0f00c03c100c40e0040003003c0080e0f21a1341545c119000b0703000026805c02e00d9810101c0c000c0c400c0c20302c0034041900305814040d400c40e0120f0704e104102c503401c07802c032020703030320b461004240a805071055038000303400300400c200c201d1103091800f00030031a1850794001240c484d101d450690300310000709040740d59950700c10 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 717569793 1250 717568543 717568567
    0x20403051e0105040305040e07090b0a03150e100b0d060f0b09031b0108010b0d0e121216080c0a030e121804111b12130906050306390f 59
    0x1040204110341c000d00080c90955402001c034001d603c10052584040b0780170030f1619000b000301c0c2d40608500400b0341d0300d801c84414014080c1241c075a202c1480c030301c1340101054416180c45414409e203501014500e0f02c929250640b030181c0d201501c4580c08a81d1094045101e000601c5080000c244544900303440d0780510b020141080c0e45200c0c03031120462081030018140c0d81208516044446041216031120410041440038040280c402d80c241d02540405003419039160010300041c40c2504400d2403142d03202d200c40303841c03041e0a9022502082c1544009220041d00600034005810729140209803c0390703540d241850401c03030707802030700d40401c020075400701c0c019a203882000718510448040c80007248814031000f42c0c3c403504c03441020300f60000e102214000004c00c20300000500c44000303a41e543c0102d20550707601120340c1c0a0907000c00c0c04c00000164034600050700d24015041ca440c00c151034155070389030000f0f51207041c0c81241c0c10340d600c01c582c0040008a4000d011050b00410220b80c0e906150200d07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 717571043 1250 717569793 717569833
    0x30303060e130b060112020705010609090606050603070206010506071e050607030b01020a0209191103070513060e011e1e05030906010e0705190302090a060302091e0f0603060d050102040305 83
    0x4140b042109402000e0220f5110310420340c02102c2801d14601c1130481c0300da00e001910854902070310179820001e001036080030a03031283c0c00d8107000300c008108040d110010080e1030710054410380300503484100140200d180150090501134410400c21a0512096071210807001030030b48151a00c1d0047d200b0061815010b01480c00c82e14402d00c054000c200032a4001a400540605640d10000707000700c08070200110f0340c0c00b00c42c042c200c06520a13243c0c60a010f00a2031a404001440b002618403000051210301820050010300016116800002214641c4008000b105403c60082001d20310b1410100c016040700d0144c00003955840e181d0344e181c04081a4a0078030180d200c01c5080c00c034603040010441d40001515041500400500b003030b44541841100680074141010b5449114070400040d030540540c01010b4041381035548c0300c000c480d074412000790051040e80b45a00000d0302001c000903840d240000b180d0000005050a60a170403549549007241c01c03c4c1c004664a60007280039054a07040310031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 717572293 1250 717571043 717571051
    0x61803030f021603030b1c0803191103040204020904141009051006050a082805071b0c14010c17070b090d090603091a0411100c05060103022404030303060e 68
    0x5801c2d442c0215000d403840c074400f031000010b030815030354006951182d500c403143e1600b42003420030200105146410154909d602c280c440700e40c48900d803000c0b90b1804555014000420400d99060b50139640c460b002d000c065484040503e5016680d042c4047e8009441200f40b0300500c010900e45c0c0312242800d4144080303a00240c209022580c0c001d00800a841d40310044905c0c0d94541d151031255030700d40d20100e0304c40599001c100010031a809200c64021f01150b8400307807090703480e542c030010800c0a880c1c03100215a4203903005410340b60840c00500c19444201d4820318581018544401d0744d40650301c400e031901d4103007071045e00001e500288450902c00c81460b030039001490300c000303440c250b01082e101524200b400d12854007810740740d00300d82060261240d100d42000320f10707200440061400345001c8400d42e2a010016200300100c030450010907200718401035100781d0080041200d6400d41d020410000e511503010503002c460100050346c0c40a115028000030b62003a00e001c61700d5410030020803000d140040c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 717573543 1250 717572293 717572321
    0x18071706061b03040f0b030402100c02061903020a09060e031e070b190e1c110117040c06021605131107080c03040503010506040b030c0d0203030f18090702070b032206180303 76
    0x200608c4056550001040a00b40141c18000f840c0c1d80e2034804122140103003000f001c40304690080404070160560014005071255076103941344141c40c2d241c00c4c0d5503a4440c1d00b00ea80c00d503201c80324074106450400c0512900d81801d40486018580d140001c030010b074046c07246031044842a10307038000c00903003110b100e01000c0821210341d12102d10309502200a42410800584030f00c0100c40291070070790040390341d014030360038010742c03811b02d0301e8141026140d515a41c42200018421001680981410300c4080030580da0000d040449070085020900003030a00e4445440c2080004c10900000468040040072450080006580c84510340810142161030090460b401542403140101c3c603030360080707801c40c0d0365201155000640c802c14000b0074614060000e0b00c20103503200140b800c0c00a200d400140c40403017400c440c10511540c0d888000c0303840c0e01092081c03002e40d4009201082d290f02c094541504108001c608103506001182c1385d250958100c139440186164030b5020507800c1c550f01d030040810150782c0c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 717574793 1250 717573543 717573547
    0x41128080f060a090305211503011803030b190e0103050c0a03080904020a020a02040f020408060903070807020d0f120302030a0b01020c0a050f01030204091a18071706061b03040f0b 79
    0x3581c54141c40d2140100074144056030b80d401c1c041050b000e07000350b0f1142c0314481142c207904d4912219000621100b0744100301d2410b291442c007040751405014030800c0759400c081004510310580d90903030142500c0f884281d401800125402c2440c0344103881440202440c00e0394045551460402c9802d200c3c81f00101409076032440c0007070000c1040d610031507084503000e40700140e5502240741c04a040c03400c001070080d4010300301290104102c0c0545c02803c2552000c105a50f681c0d10341c003800698900c1030340c1008025100030702c0600090f240c04030b4000107203401020b02460541c226541c3c0d0b401100140c0221003c17039404000c1c410095901d10410006400c213000a1420340209000204000705610850344194013035103054815910039010f84004180c0c4440520071131065180900601100d0305030f6a00a1a8080d00c5800500721030541c50301030000f540f40d10386a48440c0300300b010070030310080683da00442d00304045001c0c105580741901a500001c0d015640f56418950b0050780034510f58480d291806003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 717576043 1250 717574793 717574813
    0x120807020a0f080f0c010f0c12020702211029030a1a07050d060801020d1103011a03041103060a060819030801090b030f1b0f10051204112808 62
    0x40d01d440141034210a083e0740300d11005403805910b100d441c0d40300f1040d5013014528491003001d03822084410456407100350115032081e110504030300a81c18040e600c003140d00d06d01e4642c4c88003090501003c900b85000d4401c48200d4084c040c2c00c1d92900c0c0a02d10098514038107012840d10a07007a40301d0790b220114003510fa1f5064580b03034030040c1c201c190252003c0c2c0f458070b000305a00074058003c036140b10120703060034403443e940ca41c0800e000350001044d0032a21404c04030009100c20901c4101d90584200b204e0003181410b6510744000c1540006004444072840c0c1e41d071001c02c0343d030200015071140c003c24101242e01c50070b00368282c0c14034203627420b42c400f1440040340c40302c00a500520034605440c0340040020b0103042c0b4034002407070a40307440b504804d40e01640407501c03100f0015400324503542e0f50545241d01c040b0700c41010310898017003008084001403030a114000b00440d88541e5a50081d000d403940c000000700010010301095100a0032035a4200030110084442d480c2c881311400400c1d104001d0841100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 717577293 1250 717576043 717576053
    0x1050f180402040515150d1401180903020a23011d0703020d052e06050609010c02102d021b090c030415060e0403180305031c0612120807020a 62
    0x6000340009200355140c0d0009400c1404403160b5030440c0170010903030f0800b0500414410701170307801440d5581c41c0d6420540300c02e900507800c0210a0482c1e90207401c140c13034900c149800030000e1500c40c00440860080389002008105205848000c00704808894290700d1195207006085400265001c004c42c00120150150030001051503012a50155401c1003520302c3c81c038045050010340d001c5001c82001010303106940340c2075910440c00d0294107810400005031200100030007070081540f2140013465580c0107200504101c1c45c2045c038034800381070111041c090078011075468620344010f4081110940480419682c0c1000401d803600c203a41d0145200c0610328002c280b1800c002800d1007050400000800c0c00c21407050f45030502190081c408101c41616604034204d018425a0254009070168619840744403201d041c00048a50100c000c604e4100036041c3c0d402420164407501c000b2036581d200006540c4500602c0c00303540c500c07810300c00c00302c0750310341c0c0010f0800d640c064000c43c1150b000c2440c50300000c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 717578543 1250 717577293 717577339
    0xc020f1219050d0c0f08010609082113090203071214181609050f010506191413120b090a150207022106091e0a0204020f07120801050f 59
    0x102860400381c0c0e81c007200e07000341c0707040c8680d9507001215480c04102c2c02d001680890241c03a0f02c046903680c00b069981e03c480484107203520340100c5669030020302040d87c0314282c4081c9900c815000040803400c0117044080010f50030741a600141a40780c0000411070366a03482640d1401200e800c080421400103580d12010100c3e000a1481c202500b00c50707408a402e680c10010304002d000500306003031825896583d00c0300640419544003c1e222260340c000702e4580b44c020260f60303000c0c580360000c082507034001004490001c0300051b14070072213600f0400e800c4946460400d0704040c01e1200c802015640071840c2c41d00d24124002c100f03d009410100c0210002617070a004105260348040d40541c42d04000d00000382540785256032040300117203481411411600103d105446404900c0c2540c02031402110300f1a01070000c07100c010150b030804031481d4010315040c0e0103024a401c822407001d0031312101d60307200b0146a9000e01000b0100300c0550040180d454070341c01d407401c000010f80b800c104100c40800383c00625 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 717579793 1250 717578543 717578557
    0x40b041b18050604141009060b090906010c150c051801020102040b0703030c03060b0a020d0806060c120c070e0c0403330f090206030a0c0e09160c0c180c020f12 70
    0x141d115400324000c2d41c0c46030050150610306514000d201d042c0000003c400b441148a0303d1042c90401d0000101c010450040c1e502b400310142155200c1d6840d0401192901c1c00702004480340d02604220405241c818415201d4150701c41c0c07121a03481d00c0c1003000c034862490108034903045a00401060100480d41c1096074071166041c00c01240c0e001c120481030b40900080d4000c00e400c1480400c101400d00e030f00140840408445480b202d0407900c864060010310f2180c000000795552000d40c0328012150050001c10041710250b0541706190b031a0444082c1409050719507800c0508042400c0c000c0c40200710348c5241d4440c2505542c17507180300c0f0020380c2007003100e001c4807480c8041c0da4a0b00c40ca0310080341d410001810764005c0076140e5900d0000f0004005118007500f4000040407120501020f0400109007030141c0e051070030041c80f41d45015400c036620601080216030040c812000001c0091460201e9405082020b00114901e40403004c028a00180b582c0380c18031a50100300f4102d0404042c0c000c0300d00e1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 717581043 1250 717579793 717579839
    0xe07061d030312182b080c040b0f090301230a0905071413050106031e050603030301031e0b090a030311090901031b050a170715080606130806040b041b 66
    0x25035104e841c450104200081203130310b00d02030503449014080320100068010030b40800088016132075039404444a40c0220b0307504400354810002441403414000181c940300755014242d519049440001c2030075035061a02e04220051241540c80d4507008042c8040e5102c40c10303010410818031280c0b07400d5900c103e03910400000d00c1050031000e14035141c0b800c1c18400200503400a0000d5699240000c005100c02c0040e00200e032513035203614851400302d001c0c450054400400035425070742141c0b41d0341440301c606c0440e40e6440d804040d800c000616000800c5200d01d8017000075040803461030030003a05541c4400f081c1c00650104010b510300e565954018941500c0e04511071818403400741e0760010721004607030001c0703a20148480b40043c6024051014641d00b15807001524100c654624201c1d09603008101008007007600b01000844604001001e0305050920004800d075451707a5502d5141040001c0d1000e4685004100c100024005100ca8440c911080103040c0c0707001c01c0c07400f2954610440142c1e11420 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 717582293 1250 717581043 717581077
    0x61203030a050c0d0510050a080706140f041a031608040201020a140f03040807180902090118020403080f0304120f0e04090515070f1d011b02130e07061d0303 69
    0xb55044101c04e032035843d6883c076030030402810500100d1005400313510440b4850b220791038002c40c06107800715a01d001c0700e005440341c4511700340c0032480c100c10b508000440004000300b80800101c0d40901c3c00c8404460644182c241c0c1d80381862003001c0780c0c4042c1d501e40b44051090500074040140d0340000c0038044590801080f201e0000340700e0b42070f0309140003440190424030003c18041503484c0e022852004403400041d04800c01001181030b00151101281e000c1e6101d005500108091b824121504000354042d0400600e4140c4965805806800c2115911042040442040304008005101030701250160030400b999001d101c0d4000c0030100034903144d41c00b5607210313240b034001c00000700305416008440301403c6079185014440106290b00c100c1e4000c0001d0312201c0000d40765000064403040400c0c06942c0c90120640d1090611401d00190340100c0c3c00c01c0b03000400c0c81090100b4417400d01d40e640542e0180c003d103490030800034a4282c5000d540d80f80480031884541c0903907000400ca503032a01400c10031741 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 717583543 1250 717582293 717582301
    0x1812120b0609040e011415120a121b05070308030103020f150a1b0b090f06011505091005090d11040b09090a030f091e0603060b03160311040518040308061203030a05 72
    0x51701424440210038a542c5012041c882c03800300090525034000300595900380450a0150344903a02c261004000c0c142141403002521070030700c180c1c0c0c02450b10302140184040541c5541c1c0e0103181c010b10340e00994100030044014401c42ca012035020700c0d00d6104941c860182c1c0c5130401042c42d00d00c1841c1110080c0b01921070011826400d01000c0703126a50400700d142082e00d00098407036115480402e03550010700070301c800420301d1104200c100380d01d8105583c03110305103140c400a00c48031003100350450b400c0c424144800c500c10303903c800d200500d19115150310329210052000344000c0d00c200c800118480c40040d010050309007000034a04071803e40514001e502911091010340346007000343c0208410070308903242e040d885101050001c0489540d6581048160360f9098171040c0d0380402d5500f07500041d40c03c1881c0342c45034801d41141d075002d0311043c4241d00e02640d40000480074070a0075450412802c442c2c1c204030a0540051106034080c0c015600c900d45001040d1140d0b8a074131000740804c0b03101d55078002203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 717584793 1250 717583543 717583571
    0x9090213030c03060e0105160903030819020a0e0102160503190f0507090209090115080406090309080d030b03010606080714072303220602031c1812120b060904 70
    0x200c0150380040c1c0c4295641d0300da0811802510b14080082c41542c02c000c0403602d00035030410707000c1038064559900401d0703504540d03003140c030000f025011203500714144007201c090802c40e100600b072508680d00c4850403142c1e800c0019080c441c0c4400c45109404011030100f016403400b04100c0c111030362001c002d83c003140ca00d1400300f00e074170340d00940a42144103030394000c02c6030311082c3d004101c1b030070048802828581e40d0b00c00341912010740f00003000010b250341001c0b800050582d0441055a0711030f00740070b440e441c0c0381e0000d18a4006c6005102000a4032100e10f44803908007841440040e00039850b10002d1850203040142c4400c1c0040e51800303000c100011801c0a0080781740d6480b2018004003907403500103901146a42e6a07801c442004040f40b603151401c0c8564815641d029012134880d40c01450806c42d40d02e40341d00101e03c0054102c91029102ca10300e070308000351000d158070414130460080c5041140160003c055000660414015500d09002d120b40c65940c101503c5038180200c5001c1803400d245020 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 717586043 1250 717584793 717584827
    0xb0a050306040929010806070c080a0c120f0810080703200603040f110a0302030607030b040b1906090e0c0403111c051f05040b01170304080708070501030e0d090902 72
    0x2400501d80044112541d04c546804010110003c008010850742c850495540340c14040c2c3d440f00215002541ca0301c001420007024240900150400c5190324095482c2c01e440001441c0000d00002c0314909041c2c98250400d030340176001050040c003010658188103071190b4071211346c0800b034040580340103440080003003d48100303840301e001380c0700548034105031030111a4a00c20410413610120484090342d00c07420300800050890390020000c0c800e540366600150024030300304d00c00c1c541283c0c9407600d812058680e10604105110030820102d44c491800400a041e1030301e541014000d44003030f1051140b0b081c4075009030340070359400035205401400407500041c025200440c150301c0030011031200500f44000440c070070300400d2500b0302035100f04050b0740078042180c4003203c3c002d0202814000520040e19202c0b0000d80011904040320714241c0ca84100524001c220340c0a020294010f41c414000c6507070500038002025204d000800d281800020080d0200d1002e010310b400d400c0d0b02007090304001e6940c1031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 717587293 1250 717586043 717586061
    0xd0203161e120207051201020c06010b0c01140112060e07080a021003020d0f061404020a05041a0f03180d1718121c0513050d0302160b07110d02070b0a05030604 70
    0x40400001a4542c06515520a840b80c03920400b0340d040b50a80040044c021104001541d0028100d903a007481651510b03a04010800e80d425907985007184003a160b07020a40d4060a10814560382c0d40d00746107040e409072030546600300f1321360300840e03401c207c200341c00581a440c255040340e20445043e2a00c0d4124004c2c0200c2256040040c10320b040701c00d4500c116030080c0151001c1000c00c800d014080707006d1106902c100320f04ca6000440c20001000040d2a08440d4401000410012440d00030075119000207900181c1e034604804241c1038864009000c1000200b81040c02030038100030b246030000c01c84507940f03001429401200b44140b652a2400020321009100350b610788500d03071300e503042d4125411214100780f824080b01450100401c000300c60013140c3c0c4548941c040c005045503400000c08074080d421060310f040300020b03d510040c0005035184482e070310520340b5a40700740b00f10341d4441c07540c0e06d010784000420b020b641140b1410b0000840e0402102c51002441c20002d5030f036103071000420014141c0709 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 717588543 1250 717587293 717587303
    0x6030c0303270b0307180b04030303181209080606040917220b181507020118030215030f070c03120b0310091a070e0306070c031101050115020d0203161e 67
    0xb120100e0010382800c00345004580542d1100c0c0c02131511035000c01400e0130750141c000034440a03c41000000e1080e0429240d840d04810403c0441c0a036940d4150011035824142000c00c0d0004014000c2c0d5100700210ba520a204031000e0010000f9610760503407000b000c2c0b508911030400022043c0c04000300301d41c90340e800c141201c01c0120301c030380e0303100d40054541080b82c078800c406500303641e8050649001c0300c4c2140013242c0811700b107142518139401903030400002c43c800e1044160406001006d65948a00d8418400d04044020f96030302c0c100040068400c0010500024012000d8000c0042644030709558000c2c5090b6000244121802000030b140c0110542104100341c20110111304110061a1150030a60044905035554440a1080d01d40e40070740c0707800c0341d0150300500010320000c0c810000b03074030018081d007011a44200e010030040d0a580090300b0035800f00e000c0031030700c240140c1d0401641410001d00d00c00717141408482c0031190000c4448a8020b00081c00c00d0001e003078041007001004103c25401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 717589793 1250 717588543 717588617
    0x609040e0f0c01110114010e0711030703090906060c03080f0606040b1c0615120c0e0409030f090605090d020f030115120203060a0204031509050f030c150a06030c0303 73
    0x2180c845035541141c6042c07607000801c1c00c0f1440d05122814022042c0910400d030303184507140e0922840e501500740051403030040040c0d0303540c1c100329a201440144004c80c06a652441c0d050f041c104d8400a855050380500200503001c8056000700c2d0380080c1d10343e000303c00850340501c90744480002035158045c9810000210000103401c410f20f238100030031108191480c10050140a81d40e00c0368114100602800001207800c041084400c05025800422100d0075811b00344107c0c0c0300040450b00b00d41c0015022404158601c40000741030390000d0a580c01480146403803885d003680381c030105081c242080b6009026614031100702005d540d00f90000096040360084602020b03641d600d030300301507000d0424141c0c0a801040c001c03422549181c001c460549411111144810007a4514800100800b1800b59882d0244207140e441411091005084824002000700310384a0042124010b000700540b01c021811b01d0b10808000050302c0c110601d0459400d070401c0343d481c0c5607054201820910440c0b901c1c0c2e45a050f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 717591043 1250 717589793 717589813
    0x3122b0608012f04030b041e0b130c150203040b0309070b0c5b02130f150c02061e03190c092d09020307020109020321090609040e 57
    0x103000750300000c0c00820300e00243d4126007200701c12a02d104501015001c1400c0070005030100d4110004542016469011440003100a88556501c2a0306803001481041c6c01040e00061007074841e00c2030b0103840c0c0300641d01d4028162a001942c0c0e442030388200300e01c4600c04400140180000d02c0820000c200082001b5034540380300503016210b0314141c2a4044646401702203030701400803114081600e20070004001c0100d40201000719401001007041d00c40610045840c081d00e08030790001d84a001c0d0000039072214941411140300d003240080d000780e102c2000030f07605d440301b8507406a180d404241e01543d03d641c0c5c40c898401c84001e40c1c03281104030442c0074030002c14407507181a60114004494503010003002691414082210050f03440d00c14a180000d0172441c15103480781100001c68004400c40311100850f53f60001001030760401c41d42400540d669450300001e5040502104801442d68071642d00c1d002001e14020300503000e00b5800c503002da1000700b900401e035216580070405130103668040f10720040d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 717592293 1250 717591043 717591071
    0x10f02070302060c030403091a1b07061103070b07181a03060405130507030303020a030e0109050601080c0d0309180204080a1b1208120406090f1103122b060801 70
    0x3205080880041c4100710015040b6002c010640f80943d42c9a940c1c003d00710b1815038007040030626428129801c003000c216034904a02c000756450f4800d41c508000d4100b280c82c105020780740705458091100940c00412004001131508c410a0b0381c00190360820340b0003107076100ba800c0c010341400d400c0500395810442690256102c6000654800c40040790140a2958ac8400b81e00f41e00c800d82c0700080c1564403400d014000240690003500b07000801e40780c00103005512480980c01c3d07494410b015203058200d40018000010240044071103210103031100d40c0ca04003107a900620102c2d480c4540943c03d2640e44003500300d0b40c125011580103242d46001c46680c1e0410b03092a20403003010a01e50110071320741d1200050301d45502160840240d40220000381007070b50842d5282e002c00381c01801216407a558000407000034542c40d800301651402040020850000030081c14500074204400d02c601038001e204040c40d00c2501c28103a02c80c103844804d0342c0543c9001d1007484000d09429001400c0d20b50030082c03c014220 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 717593543 1250 717592293 717592297
    0xd03060308120a0612052107050c040905031323010e09040b040c05090a0507021c0c0b06120102030408070b100f0302060702210c01170105010c0206030c09031209031b06031602030c010f02 82
    0x43d0b82507c81c000c501c5200076250a20a85a000745190881803003414140307020303401110440c0c09101900c3c03600500b4450604d6500158224422107007100004008543c411a240d4210643c00c1c244400f08041400c0000c02c140c030003c100030b0000d28400c0c0000c040116204410000701009803801c8400d040c2402c6401c0640001c8400c9401441162503001991840d442440b40c41c961644840d100208107444441c0107160040c881c941050f805011114441404d10086118501a41d07030343c1c0c1c0340c1480b0b01c2e0002c440800540740f0131134540c0100042c0300c0d0300c0e002d00349403089950444d19903940d031340f0920105240d4004290119440c80e02c1740d03280140400007140400101e90240d0b14900b403100e10310040c20b2049000e015050000d288501e114005041c0b1030b00035030304100143d288a04020744840040d1401090b12a889010000031400c92440d003002c0222640c108904501500c041d200c601c041140741c0801070000d54020b680c514444101e030300034002c5070036180045000344440c40305100d80802039 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 717594793 1250 717593543 717593563
    0x703090203031201152f07052107060509030714010e030706090501090f080d08070c0602070f0c08010203090d080703020d15030209011a0d021803100e0d03060308120a061205 76
    0x2040800140310003203100e000ca035100005880001c030102d40c0e080d004103104101e07402040d606c9100c0d0007000320b16550340011482c0c3d403454038150049100700405801d410600700380c4c403000034400248442040c50b0390101d00d500985045180d1030b0b0b085030300382004940018480744000d8060041e20300109502d80e02c8851081074640030b899140c0015074605028100005d144202c00c0340b5080b4140440d1414813408003a60400301925010429030f609858210883e40240030803914041944e80c054200700c0106c1c01c1c03000420050000b10b081d4501942c00940700d203c2814008100070301440002c0c0303494040d41c151803aa9038400e008000b103840d080400320a0b209240800d91042c540c81c0c0001500700d02d6422400b400c0c1410298807820095502101d0001e1b4124140054215008c81d52010458030200729032440c108509a001c105910500070742410320103207040040406007041c1003800490942e10407540c40c0070312003002c04825550000b1103001040141c008071030100c1500080004d1103c005401c01d00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 717596043 1250 717594793 717594809
    0x51c050a051b180f03030c030913060803180604080f1b0f03070b0c011b02100f110f030a06080303040308100e0f070c15060f080705060307090e0703090203031201 71
    0x29646404031400c45101d03000008800a000801281c08075032411404003183c00d90140c40244040651000039045402165800200c0d5002184001480c075143c80718150b00f48120138100480e50401840035200d2240c0c00c407081c00b020f00703481c1982854840d80200c90040400328180d540b0080450905511580c484296041000c2c01c1c421161080c07500313003030400c90540d005004040d464a032411506080c1c02c0740031801c0e003d561702d4005c0c0e80f0503260085507206010707641c0c0c040c2121001c101c5044080312034002d8102062841c01803010b070507244010807113607041103075040e1a4695484d502d1004c0a03003820340000006010100a10003007640051105001d0710711900b84441c140d84515419000710307003c81e0b404001000d94804100c0f41030043d41d08103c2c0318090b500001e01c05680e001d120081e118140e0042c01440b50f415801c002c0c0c601c052142101500084401610f142003010009108608500403220368130064004070320030034001d900c602403496001d0152030712524000c400007040b900922030302c0c0d6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 717597293 1250 717596043 717596051
    0x901090f1701140f010312030f05040f05160b0a0309020604090603050c33030c13031101110606100e0a0305010c080a0c050901020a0605070215090303180d1d01051c050a 74
    0x143c20200d02c50003803040c21445031281140e807071500c400d2000034400c1c550000f030580c0c0c1c400c0340d014074030750303000703007031149000d8001990003c40510b405803401c1c403281e80403024051850007c0c0001b01000d400c89400d02414503002c15607032024000200301e481503030304c02a03070103151540000400c500481c018651007411611905100001d40611100140d00040d105030091103456011031301401101560700021a041018108907820020440584454100340e07585020a040440e43e5030f80300a4040694a0a10250500e82005c202103110100010104800d00c01c0c1800848820b48900c8607901c019600708009200360104604085c100110640e85c908103981014451513251b0700440031079004910682c000c0002c40002c2d00c609009101c0034000a00b18000c4190701c5001600e41a0313002d00403488040515a2400c0c200d07800148108000c0c490350154100d01354a65072207402420440c0e549030408041c2212140c40d01c01291240700c1d002c0b01c0200c00c6141c0c0c11240c506509035101c14031541601000304 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 717598543 1250 717597293 717597311
    0x30507350117060f191a1318080a03090b07030507021606051215030a03030213050d1703091e0a03030f02090607020f0d0b040b0f010f1a0901090f1701 66
    0x1548028012040b96950b5101a003c00c18824013a51110740c08050011007061749404901c005042d2006c5408581c40e41c00d04c10b662108a1400e10742d100411122080c0400c4011b001c0d000700f4802035003240000d44501c2c07002c50300e015540d000382c0011079619840000400c0c4d918012201400400c1d0681d4250010302c201810404c23021060030380041601d07425110203040c808030507422035480000601c540c500c11b0b51381c241e400983c0c40c100240d6498038802d03100544c403000310003440d064400455000034031a248884002010074010908001442000d40f06c030b0795295500003d403440c0c0b00c080c8084480307441c0342180380d9512450206428540506c642e40074001e0030624000f40003a400780c6041554014070400540300140307401c1403002400d6101600e00303446400e0311317210480760840031507080d942e0a0003c001c100201401811481c05041d10150741c050483c2080208243c4102c90b1521100011001445c5c0380d15a004426050040004c0c9100d10881500c95070b5001d04840d442c609841a50308040d451 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 717599793 1250 717598543 717598559
    0x427030801120308160e03160504050a06030201090501110a0f11041b0807050c0a0b0a06150c11012708030d0b01021902220e0102040509090a0308070305073501 70
    0x360780740b141c050351036800700c1e01d681d110502e5400c0e801c1e60340300a1010441042015440034402c031072080811a0064140505c2e040612094031001407a0450486c5003000500050ba001058981a2a020318001d148405500c0c4200e20b003800040b4003418000841d803118017000b049a8401aa410081d2428800742c03002840181c60000f840d200b82000c0341c450340000d8282031040c0003405041004200302c80140841c1d40f10008541010750302d803d105038450301c003840010b881008010050b031082c03038180204141500c45c3c1d520403260a900e1810004c194200c3c0b50760600c84480c00401d11701da180c00f04409a40c031544c80d81e80c1d9000300400809a4280307807582c070482d80040340340360711280c480710800c40201c4030742c0c00c20010f818040610711101e10500074074103001c545803040d001c1100d00c40b03000685d00c1e8100001c10503094001416400154092540500001d9104841c00d03005a92070402149549800c41d06840c5186051030f89070908081c01c0c0c0c102ca5910114140c03850240666030601c03910b90b219445 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 717601043 1250 717599793 717599819
    0xa0c20010e06090307030809040204030c0b0c0d0c0510150510030c11070e01031203020f041d01151b020307080d030902120d020604150219110d0302190e0427030801 72
    0x30461340340c0c00c81c12042001c01e03c03006c01464917000041c401403030a501e95079110300e846081d8215403200d610120b045aa260400c000300c07405040c16003010040c080144d03481c1551074000203441500d150316010b08280c103c070310384070300009840010714941030024440c0c1c005000706403c0001d05c3c009208288074058208010031650180c1d221485815aa6130030740e00c0792120500c20312096410103908000d4051003403c3c0c840076001070031884a65a00c034402d141594282c0901c180c001d00c008c007854224006607181c120b41d05a40b0344c007164840760502074242c00064240081a0b01c43c8401d030040109010b25650315522070710909200301d810441407180550116a6498150343c8400541d108030045004070382003220102c0104034511002d4a42040d01920000e0000841d5200000c5840042404000304003808201070180365868210b04094008206402c60064000d0b65003c0c46843c007401032103034a6980014140c07040003490b00700c140326000441d04a035205a8004e0b80054825400860910741c0001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 717602293 1250 717601043 717601057
    0x409140a0b060d090507090c0c060c050301141e041d060907060f18050604030b070e01020c031009080405150304030f080c12130b04080309010c030b0d080a0c20010e06 73
    0x4414204402008490010110f1040a40360342c0310751b10780085c01200038000c0d440410070315981c030347d5400440e25041c03056030764403100141846828401400034000038002114000012100200b4060414841803480c15400480075002801e000b0300300082c030307060721141c504610036404564481d500d8154580e1181030034001c00000446800070070850340c0c81303035039203a040062104001c0c0409590b00300152042d4029881202c5070145c000803c01c0e41a003080d28506040c0081c00070b000b41908400029441d07461031295460010307039605550051000c4441514041c060260a06160420303250800c080c03508215401c50024640c50708450401e44200d00044c06628801c1c242400c00c50070b44142e101e05000100340c50b40c14406861130401041c2140b0700750f80210702406600366a410042d840d036003501e901c80040802d041c1802c110b1445070721507061886c01581c00c5802551100084c1a0850f82d088480001410900106011107400c12650318030844184090b00d9410500c40100240300172406041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 717603543 1250 717602293 717602299
    0xe010f05030c031929160e180c090405010308040e0c040e040609020d0602180a0b161e020d0501020a0e01090305030a080912070c0e0c07050303011802040b0409140a0b 73
    0xb64054401080071030354201c0c00384501c1060b8140c100c1c40d410141185e01180c2c2c1107809030b0680302401178010b2550708007034001072280ba0140c103000b203074030200c0e14441c10b0411503510229410300042d80c1180740300541782c20b030702c00a0062019517500c0c20020b0041d0050b000e0501c0b00051840030400c0c0000b4038044038220303946101044030668650306c6040040c10420700581c1c01105030342d0781100040d014401003105044008843c4802c0d046641803104c080302540180410260801014000341c0554001c20000c0b507002980b0444103604580c01c400c2c60010a000942010700404170b02e040003410340283c02159115552072038481a240300449180f4254403004e00103803c200f0900c0b01d41c600c2048001da100c05503008881d00c018000b90080351540c4001c10583d0b440c2002e68090000300d072003480040e040b280c0c0c480c5c460f01b0b064913521210b4481c8410b11801c1e03080b412200070380300481b1158040d980200143c0c0c1d007603030300c40703580b0713242d4802501300ca1029040d0100e04100080d030441180c415001d90ba9409 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 717604793 1250 717603543 717603553
    0x3040f0e09120a050f071b090204050d060e0115060c0303050c040f09091a2d0621070b0703050408101104060e010c0b07030603022b08070f05070e010f05030c03 70
    0x140b0380451541c0712000e003d0400208200301c241c80c00c4d8910040800c644128036941100c24107241041c2c00c9280790b0029011280104020415a528031410310405a0071420000302c1200f405202030050031141c801c46c404c0da20702d440000702207402401c0140a41c1c0682c4040c0200d03603440d2040c0030b440c031860017040c03a2805410020320410006a0100718203900c104141000301d02d03882040340d820f180440c1c42091190400b03000354101c2004a58000382c03010148414034140c1860000200c038260740a0020b002065240c8040c4010101001010020040420559511002401d000f00729074403d0084803024802d841100c110800544101110900020015420141001d00490b008200307204080d04208900f408107010998100210780200e41a4400098484c9184140814481034580041c841d0504440382e00820707640c191010300c060740c0280c0941d40d13440d945c617069507001c003410400b6000b4071542134082110404510554143d40007601040300b0036954004060f41d944010158130303016046 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 717606043 1250 717604793 717604813
    0x181203060614032703040819080d020a17071d06030906070e01020705031606020706230319020712090f0b0405040203041e031d04090b060907091703040f0e09 69
    0x40c440243d0341210341194094000c100c004062071081c01c005580b0300d0b02e504001000c004448042081c0410404414031100100400c0d40311018980a5030000d00b500f40d80004100c07030500d200b6900f8942800559000741403d04010400408041a502c032050340f1007444580070003d4940541640d2081070811300500b65a60340b1402214010340c11584c0d175041d442003034804961a50203000c03400200b042c07000c00c11411072400748000c1c42d14503070350f0010051181c11032250220908640180050600a400007581c075184c440120503999050f8001c030000520100b81d010411a2a0621040a07806550741e1070103291541c0842d10510110303c1082409841040100f11310f081940144d40c0c868020341c2014517104104004140460210f18114001201522505128681c1110000402c00147c0d0200880e07401c9503500400084050040c0c0c1c810050100060303a414480c040d008040c0807820103c0e807181801110041d035070341181c00b590550b080f41c210b0203c1c201d0040281240f142810a0042180f000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 717607293 1250 717606043 717606077
    0x507120b0f070c0210110c060721030b0a0e040206040b16051203150f030c1f031803122a05070506060d050d050a09030c0b07020112140a0b040f1812030606 68
    0x38418103121b0b4a405401041c503615501c6c0c00c0588000e03401954000505104181c03000741e00c4507120a200249441c040c0078162030341310091082d081c0c1d6514054040310f5201c0d03000180c5c01307010b1b40e4080703489814002100204103080d00e5103252041d21560484c1c6080c00c1d500105060ba010407a240300300b011549420301c0d00c515128014040019014090b5042148014003080452a40e43c3c0c00d1440d12040c0075210618551622400820000312291215003517002d540040004c403004d000c045040b0384904502c0c1070340309100744101c035900c9400036a015846c80228040c0c109d07007040e1002d40301805840300086041c204184940c4580d64008080c0800a645c4074041e2aa90444c4251008020a010000c00003c86005243c406000c000118507201c108a100045c0000c061810b8519240d0402d900ba1070000d0415903c1c2d90064601d8802054100541d00858014162140c1d411007840c200707007652240340d130b10f1903401e80014000c3d014110920b10060081d07080d503816200f40000070710000802503803c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 717608543 1250 717607293 717607307
    0x1614091510030e0307290105030d031109040603050c011701050a03061d0303091c11070608060d0203100f0e0601082e09140d020106050105160507120b0f070c0210 71
    0x5003038100020011003c420461840c5c00103503040310641200521620b0318400c030004803201066070040440d484d0f0512000c40c0c0c030b0740c481c003006905140d265480034a5549030481580c0141034060410490780e503483c01c00580c0c07003c03403c0f4001d0225911240484907185289174460588130040c1a0b046101c1c40d65480070010b0018602c0b070001c0642c9401194080c20060000b10701070f284260041001447d040304114040d00b40d00400c2040c040203589a122203000480d0910842e0070a003007182466981c6000700b400d07004500d10003035250040c110040d2f1011900c2d405807001d054079a404004000754011113a607030310390a01030410260320042404001440300d044e0010401408030000b5600c040c407410130000e9503035103082101e4003000b1100d5640c500307604002034003010035148000c0c0a1a460b140c0003922510403803031404090b205884044d001d01a0420020b0000c12442401c900c0d0142c05003401100d24006a80c81a0400e1182c004034061038440d52200602030b0b0000c20719071407600001003c0da040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 717609793 1250 717608543 717608569
    0x92111010e031b0f0901171c02061b040b13140a0b0d050408090603090c101818140702030307090909110f040f050903121605031f0816140915 62
    0x48800c1e590303040b04e140c81e0280000c3c02071a03081ca511400809440c582c1c3c6c1400e417500d840455800145468156450b030002c1c0090700150103102c901c1c0341084202840d401031260b034008086010001450000a00340c940100e800c0f203116101468603d5802000c110b0305035218801c040c801c00f0140098060010503500c942c1e00300c0e1140d07450300d00d00540c407004280d080d08111044450768015044a00d11802d2110780c0300a08103541c0b4194029021200c10f8030702d115083e000700d0306024080d02410f00e040300d00e0b900241111480000a88052425603070081d80c0b0381c0100e41910021310407010006182d00c07540241c4203000c0d80f1605031448086007600740002c0030a01a00c080c0d0003500c03040304504085031445014040e2002c4001740d9500d95980c5143c103d10362000d0502603000081c41440000035510000b9290040308001032107483c1040071002110020540d0081c1115000b100f0030340442042000c507000c202d03101d607009075203034240e120f0400c86d014100710740480481180c0c84000700d075071400d03084c22005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 717611043 1250 717609793 717609799
    0x71701060503072304110412060e010f0b10050c07060503070512010b090a0b0301050a121a01080a021e09041502040308040e06040b09040807080307092111010e031b 72
    0x556a51100040d1030504960311110f000302440c048100e03113800126640c0c00c400020b94041c02001d205981708000ea02c00c920403400ca8a080c0c0210400304419600710401500c4500024031440345c46411324001082c2e2444400c2c0b040710288200c4250038040c0b4203540400201c02c2c05010114074040060704c00b50b000034603a0007005802c1140c0640520244907041c064000c8841d100e81710011202400414034aa03001805c0c0c0c04014401000140d0700d40e075202056130401d4112850200749860901c01409120000c101d00f405500000b040c070b6980002c40130007550003202c801c3c46004880b01e55960130030f01090019040f1204030002008111005558001c03141c1090340189013903500c2e00c4500b42e076001500176060100b09001800342f14a464018408503490494612420713050503665400c0c1c9118001d0b000b09850004070001d15210300481d0854000d2a8032a000c040b402130803913a4118140c40e210044075204034601c4041c603654031075800c60091503405002800c45010380680d00303040761040780321158 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 717612293 1250 717611043 717611051
    0x30605060105091008061306030222110301080604060c0e01020d080c0f0c0109150608060114060405060d1b1404050925050c1b0904080d110a110f0f071701 68
    0x181501d41d20b10344ea0f4010740980e11070a807030911104102c13860b40c241404c854000d08000051000d640e5400651308070388031400009010001c1c40b0420700290040100030800d008000c00001034030100480c40d10700c118440c110402170404400070a80740c8440c4078450700c0c01a407241c5c10b5224040d000b0303511150040c07200d2032440d04084000d003060f030056110490108080e5144c4c12003000308480304646590000e864201070080034104082913a450030305100e80300382c684204113681407640f50002141c000c3d1802030482c3c3c3d590500100314201500da0450075201c101d0318410008607241c45032034404101c02001c1c80f020b140618201c1081048600580010114540080303601d207100703105c0e05a03015080064491030b481d4420000340a091450b2035503150b00e4640135100c405096554104565031150b40702c002c00c0e8031403422324811402041121a811031003c4001500c03900180c01c20b80c0012170441ca581210901c04405403060348034000d510040109500c940c40910520861100100b68035698200020b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 717613543 1250 717612293 717612307
    0x3060e060108251d03212503050301170c03070b0a110f0d17010506030103031b17040f06030603020904060507140712110a020d02090603191203061e030605060105 71
    0x211007250000f207944041400985158041c41c0700a0b40045111022030281c2902440310300062030b0043e070004500d480d0341d0005a40d1400c065400c13000e108102065a11440c1c16005c2d1902170201d038000c0c040d00422a000b142031482441000505d2148072802034064a0803500c1c011604607190084816001405140070151045c2081007040c104c8420ba1580184070095001c4000b40c005035503800240788000c5018014071050312440704903411241e01d032030300354403403042c031528034442c2001ca9070000c0801d040c140f051180c1860150242050714401d06250301d1541c1c1e5200160100d640510000390495900710000d804142280d020303661222003420302410030248d01c40002040e42c0001401c440b1201d510b842c0102717081d0710000c1d10483e880d010004120782c8260340c0010780c02420804009100d0102040081d640d51001d018050315094159a0702c0803492652a004840d4603140c80c015000a192000020702c42411102c210280001103007002c045a00316190300000d04070003048a41413040806c448 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 717614793 1250 717613543 717613591
    0x70306020f091c0c091a0306240105030f1f1e0302031b030a06020c03210a0b04050103020310091106180306060a030c1202010519080402040b0a050604140d050d02061603060e060108 79
    0x4079128030062405e40364031707403da220120000b010270200d050400c441801041041e045801c540c64114241d030311176003910103000c0c10040303102031150420880c5c0701c0f021038600080701d00501000103036031007101580d00c6d500160380c0030180c07240101c1c8420b44c950b21004071900400c0040d80140355010801c8150b03850040c0f115021550a55500c40c107400d20302883d000c00c218100d19100300c5180c1d0000b00c070184465455a000a40d0300e12100450b90066666048070030b082112980000002c07540213080b560b103c03025906a44103810960030348500071702509001501c64544015884140ca80c81f5202d180311605000800d0007403082c100d4200d042c80810008420741300d034040f04a01002c20541c2d01c1180d1403401c0d02c1400b00b030310761846040d070040442090a00480d076400b4103903402c0c3d0741e80e50407804850501c04000b440080c1810780c00f40150299107840208154081101031042c142036030038980c1031308c2444003142214030368031400b60507421241c041030056201d01205904910341c4151082ea403c410101 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 717616043 1250 717614793 717614803
    0x1b1403030405030318030310030b06012007050316050939090301290d05012003040b15130e0c0405010e10050102030c03120603070306020f091c0c091a03 67
    0x3080e030342d50340013008100e811380e590340c95120319101d80805141035050000009080d0080e6020041611030391400060041c1d110f00c80816041041421005035807a9039600c0c180c617005180192400703401a141498500b501d02c1c2206c030125800030b80b105559542c0c840300c820041814082050281d807002c40a0303104424070b2200581d0114600d14000c2e90303411903500b01400c60b01c044aa10400d94408032010900000083c601d148009060300e14961400c0b45180c0030340100108a01038400083c14100c41d0000202c0501840c4114460042d6000c140c503502850b45540004400d51079001401001c014441403242c4c1207074684928550441d01c8032003051000800382d500c00d8110914100049040050740320212110340004e0a0078009145455030384160039440b0b00c1000d0502d40340b9016000811000d03242000180021074005000319123407051054030114070b0b4016034403e4800c0d8985105596903c03003071054203160030f511a0142940c0742c500031840026049401d0010b003240219240170020381c4003405 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 717617293 1250 717616043 717616051
    0x1d010e07110a080f090a090c09050910031e060c08041122090f02030105060f06030103060b0a03052401051807080a0216030537081f061110020a1b140303 67
    0x2a503103485c1c0ba449018800c0d1009140d2100b5450303810808070494268004100c0d4041d14401e4a50420940d074180705000210441d40c0020010b41548282c0e1454402102c40c4c0f4580c20f2003482c00f880651703410041110200d200382c4000c0c18482040c007100c1c0451a155015100344241e00044130f002c0d010b2114074008603001c240c0291901108448000114502841100c0d402a811100c01c80c07100c4282002c600c007408140801045244d803868800400d907152447d41c80156071040488021851651407290680c1984914804030781483c4000710301441c10a24604c6c04090361089913416980707200c02150050000f43c0010070a40d030030009000e4641d000041c0034200c034005d4a0f02595003000070b207020b066110241864033100480340d0044040445010704000004581c0340810058451504070214500750070881c1000503000d050009a9503005100300d1404d011500035215251651021103040e84200c605510004245501d076003203d00000205038075450042c000c000b070f100003170b0b03401a18582c4161 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 717618543 1250 717617293 717617317
    0x3170c070308091b010c140d090f090c0c03180e010f0303020f1207020d1b17010c080402030705120c030d09050312120f06040b13061d010e07110a08 65
    0x354003014181c010514030b820030a520b0042007900000d00f41507240480c0315120b54104203e00c08481c0c1409100340e82d04000d080d5a00c20341c5c2c4070285881c0090902c011610030342d07501c00d052600c002000251441007000c2c600440c0c0722100182010350701240e0301d80c00044010b031003003648140031455112109030310703002e0102803001d50401821401c01030b1502a41886101942d4482d501c0000f00d82c0da408190b0b4040344d4181c1d20000721042900e001d5a0490224a20006030030709820001881811800d16045842c070740c4008101003400103504503800041200d0180d05944841420849820000401c421100b0304800b0703070340401d040c440020304107803084582170002608a003060166240c240304044001c209200801d142581d8a848080c0d030000082040042c2d450110005003140c6980e000490001c400601c040e109464484030303e001021640036081c20030010001285030103e50f8280036040e203d200b03074090b07881e9480090031981c0400e440c42c00c1c501e81c059600d11000252504010b0030910001d1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 717619793 1250 717618543 717618547
    0x9010507020709060b04260102030405010f230114060405040f02030402120619050c09031903080a06030809041a0a081f1e0f0b030708010203042003031603170c 70
    0x6032030000d00d85810350300300c210450315014003080300052440480d012607203464581c10300300c103558050300c180d9030502e40001d5255000100300000c0050640c4007d840b042c0c6004104614240c6811080c000d5950480031804c5101001c010300c02ca000c41080c055440d10001d2250f0f143c151520003060540e140e01d000010100e402109100031803030010800602d10b800d00000340454580b444201403440107075a000152599514082042081403204036005010050100c510186850203c0d16840e11101001c0c0e00103810407020882009081c0a02310889810080c0141058400340c2000014201e102d21041340d204021602030a40c1c9450303190200412503031019106240403094001440403801450207149072a11280883d031181480b22403894807100305c4c000a0320104064650004e2183c20541030389449880000141110150011846144120b40c0b065240491201d200685401040d420351716410a20503030403400403140d94100c105001e440c01e04044490906440300700c0e102921800050600 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 717621043 1250 717619793 717619801
    0x415060e1212570a080a11060f070905150706061502010f0c08010e060315010f1412032d070b010e0f161211040e0615030705070821090105 61
    0x58044403c91500441140d0001d071443c80f505074a1900c828140c03007400342c003030329400c80421040111000f02507214402c2c66690510541c0a0072010320b009000545128000000317076510b00c0b0710040e501424007516401511802c2504010380300c46551711122070f414040c405000401c0075801000000c0551062981d0620702c940c000074207590b00181307000c041a0500407030030f800c168005922411030f48003407207084982c1c894a00281c1001c20b00d480c041100c202610022505c24101810300d0101c40151085542c0100b03c44244050b40981c2c1c0c0b0038003c7c5410038440d0b800b10418240742c0ea1010540c0b40402400c43c40c00c14a60000740c0c0110000f40d03a070140004c01480510500d070382640e00b144151518803c14a0171340c94a212030f4100540b00301c03c210302e035000d801c0c01c02a1501303c1e00c49a14900d4002d5104c0c0d8030781d07039101d4154000302c0300e05120300050b0046c0c3d1445031034401200c1c041d00a0b0345d603103407401c0310585690030340e03a02075a0344000e018242031100c0009504c05903494000c0c0c100300004030300d6080c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 717622293 1250 717621043 717621097
    0xa240608191b062c0d0b0c07140d0314010807030809060c010906060f171e2a0f12030f0a051c0c030e120712020f0a0b060415060e1212 59
    0x300d0501e0401c2942504d007591902c660700c080d2205607080d03100c400c601d660398400106020b18005c401c1c00031700049201c21103030080000030406211030015682c0410144840301e49115290b0001e1150020300d42242c0820310104001c0c0004242c0c02d0005010b031403516070980c1449084400500d070540314255145404d0180d040000458001852a03070100380d54404030b00c4907591100408400c81090440000381c115a6403400d000700c502030640c0c8810704101c80080d400142007843c031040311070300c00c0fa009a840728162800c440000107050080000b91704100114401e0402984412044818030105019240800c0c9514503146941c3e0894580031442518054014080e2005192a100280c101c0d00400e00e0103a8034400b55240c81d60001c541030300d40400540141c0c104002c1d00c2403004680034100001c400c7c800b44a0b8002d000e49401d950401404a80003805a004a400d0003040700117950303400c900b40b5031701c0c0c4000420b4110b9114400d88041d0301c0300000000083d4401c0314840c1c44000c0d0040d440610030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 717623543 1250 717622293 717622337
    0x9010603120c020609010c05010b040f2007030f0f0e04020d020a0f05090f0409081207020304180506090f040318060914030303010e04031b02030a240608191b06 70
    0xd061810540b000d001542d0004156005458009040100c03017145101804003d421071125181c026104001045105001201401201402c8445510001d194203206a50300d0210b90005070180d48004540040300001c84040c0b003203240e1101000405810305000c1d83e142e20041c180c1010481c2d00584c2c0e18003c5801518401400c00c000d000e02406001038489038444000c000100002250000b03080c01c59850900c482e80500908200d041c5001010881d110750008010410345040c12180600b1a0b4540307080c8068810441c1da01f90445202c20116036100b649803a0700d03800922a090031010b0348160942d201e0318203a1a80328000098240c3c000f000728000244446c52a1070095010398519810104071481140b400ba0001b0100401e903000a20003603d10980d50107030640c000c0949021055600380700c41c038480a01c808041d032200200703800102e200c0c40d105003001c803140880648003074402c11105006d03920745000180ea80c00e0300e900140f05c0400c6447c00d894068103040c1c5414000c0140c41c0120800e80d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 717624793 1250 717623543 717623573
    0x613020f090403140a050d020703030606080f040c0e0a0f090321023109141e0906040204271a1e06041e020a08090d0c020105070b04021809010603 64
    0x41c54051040c003012070343c40380455034100300c8403000642d5910340d04001c40f090b10070310114022051003c00c2d07181c00c0541c141c00990440f803040c3c2d2540c0183d250b282d01c00c805400151402030040724000407c00c05620304080a07648030058003400070f08034100004200076a6151402103002858000201900c0800446601e0410361040350071070800c040e005901c1c01d8110141030304a071440f2641d000c9040d0100c00f102000103482c80e450b00b4403071840c070520000b2100d4806d4a00c00c80000aa40f0611690850880301a1041000340000c0c0107584894003808001c050143c00c80034051a0780d40c06648000390b0b0f91200303030054450b01e0544c04050850416190781c1c0f1002c1c211a66508005006061034144440b0080d04020111000a00c00c118101b251204200d000c1c0c480d54110300100f404c0c0f0386a600481c0d1207100310300d40000e581440c50302d00422250710407110b50003404518244803400c04100340c021a00e510601c042e28041c0c2c680c20003803409100b85c1048621501c0c0380e456070028010400d0405061040c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 717625899 1106 717624793 717624799
    0x52103121006111c090b07200105032e093803071a09090f04060606032007062d050c0414090a0e0613020f 47
    0x903100c000ca4207002000d0103040001007080c029003242d80ca40d00b00310050400240d6169803400b041a01c048840d0410070741880120700021650003e02e6018000d218040f406010001c03841308965450844504200301030050001e07454886071141d4400307082405040f40c200e0f108942d8801c50120f5848071143c5428803100340d2000c15852440016107440813401c00d107012a42c019103001440106440307402d540103102c200101481c2c885552030080d4140e0745c00d0f01e000080c0c0005000254203540748907001400c2818841004180d1080070020f1070b09040921603450100031100300c03410740410200450400007070450800503264011070304401440c080809074807513001f400c0e0007014111265a0b00603d07040105e1a80c003050710544040704c01c42c048400e900f6440380203004058802401d90301980f0385a0302a0701e00f041040c00345511801d91521b03800c0d96401c96004003c240c07105440c0c0240 = true := by decide +kernel

theorem cover : BRFrame.Cov 717446043 717625899 := by
  have h0 := BRFrame.cov_init 717446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 717446043 ≤ n) (h2 : n < 717625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
