-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2090
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:37:56.488886+00:00
-- url     : https://prove2.me/submissions/c040907a-2e9b-4c71-b659-d0ab3f0c032b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 375719424 ≤ n < 375899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 375720674 1250 375719424 375719437
    0x50a0c0305010b04030c0b07080f040e0402130b09160908120304140c090a050a0605060f03060a0906080a0303020f04090219080708102916021504051807090f0308 71
    0x703040600002e2903072412410f5900340da41040d4518000351406240c00715030307840900101d8104209020030013a4030300403c090002030240b03010f05162450b0602c100f081c51040c50300c07402c20311031a14240d81e6094544461180d40b100002d071095081c3c046900003500c14050b0742d4044503061007000c8111b81122501c0c2c0165006601c119550003c0c0409160fa41d42c079000d142c5421038221071940c00103000d030380f5180c1107590440001c0100080454690000c100c40b030b4403030703030003815610000000d11084c2d003031030b40c040c10090030050f00800030541041ca00945550365030102a04040e00443e41040b203020a20854004110080b0212344e17070b0410301c0e01c0121074441c010424012411031740000741030038042e1540b14403036005a00010305041c00c0c044040c001c560400550300b0f6550043c4842c0034036451400060500030981e030150a00c100701d40c030420a4140f050134072098081c1c400d0100700000d4036514030b160844500303103000c8002070b40c034032170100d802c03154550241c4c98034447d514000052222900081c240f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 375721924 1250 375720674 375720677
    0x105040c200d0216060e101106010b040e0603010606051b07050a031202060a0e070303260a060f2403021b06070507061803020705040e0c04020d02030f07080403020303011e09050a0c 79
    0x113070990050b05009018070610507840801c010303400d8440704c5e15111184804c52074880c24000c80903a50001d80901d0940309801802450303000040502c8a16403519100b030f0720000882c0240501130420200400e14003d0040280a1029080192000c0e00c1c061002002030840a40300f000c0442e500c1c10b00040445081c4841d10160144c5804205030700442d001d110180010003000342b05040c5181d07002c4401103a441030442015140c00300d281200301c0c0200000c0d01481d1920404070380d0074103000d020800000b03680d0100c060103040040400303e49070481e0296402c20300600300103071680028060440116008107080034180a07003c208524a80c0040140c05614014101000300c503e074100d20b0741c400f0001c81c9010340941c0c442081000306240a400c500760700b0903240c0a8601070b54161000c40d00f030342c12890607490425001300402c40382c0c000c0c10a01683c4203416180511141c101518069264401800741c28100080700c07040078042c04030000d00704002c004012b002c00071480d11200050080c01c90054000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 375723174 1250 375721924 375721933
    0x5150405060307210602040312120b0406290702032406040506062209060914061012020304030516081e0c1506030c030d0f14040e0105040c200d02 64
    0x391a814005450004e4a01204400d03100d908011140442c210b03414500b00c849031b80810001c800201d0202000550241c07035103451148045840301d0006403009290418001c2e813a04d241003201411901c1000c0c8050401f407507a6040d071940c01d662401034411031002940501c00d280e0381c12800902000c4005010320340702e4900749152110707000c00042d12429122598030010a000c0c40002400c0721600035401e0b140150ba8041d071503501d40300030080e5600e941c84800e419075903800a14030081800440d960050f02220104400d0300703018000303008203516002c1e00551540c0032000404050003141155862500c6884010441c000340c50803900e15071182c1520310700a00c1811510131008020780581d0109034100004c1c2c00c0c0c442005a0044503094018003c961610811f030700f10526840a208460240010f41d40e040c02c0c81c8007061000d00100700c4140c2d0812046000c1004002c040c08c050723800c5047d20000c88000c44e0140c445802182c82140c601141985070781c0c1c13081c4a0200fa0700010343c2c0800d444d107079029603 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 375724424 1250 375723174 375723181
    0x519060b0307080a0b0a270c02030909010e0c0708130305120c0c0f090a091109010b0c280b070201020706050916060302030402030601060318080a0201020a030e01091a130605150405 79
    0x40003070351650f18035a1b820a0386440c050140307071080880b540f004198000c1400c1010000e005042c1a140c1030034001015810024854046090141c401400f404030700d116a1568140800c80034400e11030214080c1254a0210b45442e00c9503000400f00021074102e4101c42c9070400c0e0800e08030b11a8000341001d001171080b0700fa0003140d803c0111030980f401800a000107200d0f62075205030405019400800c888104040441181d1a84d07503100c41c5020b001d0300d4504d25180e0f400c564400d460500d00780784944600f01020140310780400e0b104245d55259a02c6001d110b450307100c12005078003a004290000780458100020481214030008a444100d03150400188102d03507101c5040d000c0b84001c3c2e030041d4164000c0801803001e14001d820420442001055034045490581c80702200390308812417800050f50005102941c2d2035141c003584640c64800c000030441c8030019a038440c0c58803580030341e0500390000701002070405c5800d0803d203800642c00680030701843c540841a1060b44542ca02001e00c51440e21012 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 375725674 1250 375724424 375724441
    0xa080a0b0a020d02040306020f0309150f16121a0910030332070b04020f0f060a120e07030b100e0405070603050417040329070f030519060b030708 64
    0x980059a400840c1000d154803004281000303507104022420f00c0540810000001a2903480248003c01c44000c42c2034903403d1030703030505042c042d085544c491009a180240300761361990181050304240c1c80200d000c5600d08001090707800c0c9030400d18004c20a450120707101070b866004c800c800d0032107c080340d08041d0b0f5900c00d014400b0400190102074002900703140c64a000b400100400c00e040d0415009070600105a043c40142035402940200d500e40394000a20046050841c501201c152044a071b010600214001140241c0101e580c42410800b4119154413009001c0c1d10a00490548100307543c2055186c0c1000104642e05a640380f03000d01c02050002000d500c1a005c480c010796100000d08101442d0100440107841e025009031a00c40217a160442411501d034000c0004500c40c105440408d840007206250140d05010050201c14600040181041e84964175050742103c6060000307082e05d810030905028a00c00108425551528a002c41c0c904803050245108449075610860319a03950040c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 375726924 1250 375725674 375725683
    0x30204060605072f0d0812101401030513060203060a0f1215062103020102250308070e030c3717030901050a120f1505150405030a0201080702100e03090a08 68
    0x680e20100003100510a480d181000e17130100b4003802000000e09002500d16502c0b80ca0703400f5980410744d9444454104200031001110700c4900c0c0e02400d04020a103010740c003070b144044841c88002c103102e6000000801aa0754a0a54000b4084ca0a12052455203420310003601f101c6000c2c0070744001c0130042c04843c2c080903d00600080d980d41a14444118201001c020010306146600302c095540a208004091000741040380c019203c108000c00c94039810b0501802107000503002400700b0444d10f4000080391000602050b454809460341c0c84900042c02c005031030001d0201542d100c41e075940c00c0c2441c000940a440d41d041e00c00100c52590001440e1900c29504c1c842d4188960105d0824086a047e241c043c04100d8181d80d071082000c1002042010302e0001c859490080c2c07203001c1180c800502c407600303029410300d4000c90740d540c0c100d01c0c2c10300300701c0081c0d0f071103481c160000d0400c000c003070001d010319100f03101c03100c038180d40e00a050043c854080c124a85a4021080082c040c0403e11000211541c2c00075 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 375728174 1250 375726924 375726983
    0x30305090c0a05181008061f06051201030209060a03051c1b03090312031e0603060b12070e0406020c0a0321050c0904090203011130040201120902030703020406060507 73
    0x24541401480c4d0b2221000307080c2c00041c5110135010f041040041c10542c1032069500c1a1700011081038908040810150102081d4001104010040c003405407210031052420741505d030101d85141c45982d8090000340319a00302d41000301103000c0c0d480e001d0074030a61110510359a40854550884159980400c0415200102da002d400203c070f00b0002c101041c0641c05006140d4003d14010400890340e00c0d54108002c021036040d54204d58440c1d0030070504c0500d11800c80d0350072044070205071082261640310382c0e0304070501135600d0702515003001ca410001164111040800b602d0250303807010303801c4d0601401600410384171401000c01051485440348542c49140e1060042292090a140c041420b0000410711803108903019942c8940f0846080c207044090500ca0741e080c0d08090311001101d99262800901618110704036840000303100060b03801c22400d100e044d07801c0400144180045c00020303e04026580040c1d0818135100000c10381300e50100040a4080c02000300310f03050740e210240b1100001490 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 375729424 1250 375728174 375728179
    0xb0a030e010b101403040215040e09010f0615050f0729011a070f11031209040e0a0201020a0b130b040b061f02120c0304030c080715031a040b1903030305090c0a05 71
    0x1594000c1380d034404d41c0065501300b40050005402450191900c44081d441500300d25500d8603034070100052240b00340030f14950154810b03003c0c00070603d40a8840b85005440021074140440412103940711584101941e030f0150b0001c00b011401c3c68205215260468110040c00083c80780303074000b02d81020100c0080c54082078420a140c5020f00d251200003924514031022101c2c0c1802417030000640e0340800c04402503088000750f103a50307a040e60007007104030345503a642c050654200d03880746070140c0c0e00415800300d1240c10207841e1081e651058617400c0f170744d02c043c600240542d00300b0041c00103000700c41423868811101580c05810300e0003034a0000d81c007844800c0c0250b0050344410a60310010b85104c0141400750500000c503400c2c03c0e203a582c0e1041c00f40d180c1d008900c40703902407082088056400d80200d1111a540c2c00c040141800719020700700e6401c5280003080c001c03a00c50300c00510a0f1529114004002024000701c40540d0316440c009024090599005c00c0500c110281c216030b6103803142c8454100c8100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 375730674 1250 375729424 375729437
    0x513050c0d0b01030902090f071b0f030e01140c030d1116020609060702040f0e0d08091b0d05030a0c291314120a120c050702040b0a0b0a030e010b10 65
    0x40c0510300c00a010b0704007000e4101900d50b15000010703144d207030b81030340100100b041c1100149010a4014031059100075642080341442c245079010520200c44081d0598052138642d4a015288005032041d1301c145088103840d100010b224202e4800c08009010383c400c0042041c480c440c1200c040300c00c02d000f6203503a041c40c0086c0340150f00041ca00380300106030402002c0c000f030342040f030550001000c8940c0c404003082e045031550718490004d0b00178060848541d03042c0c04d00e164a81082c3c6242a51001819001e15000360010100d201d550703102c2100e4080390364004100d0341e03150011080104200491807040f00d1100d80c0051140343d1481030800600982c501611490140d9910031502c261003007105000e50b88007007100c80c4d4404407541400524881203008170502d0f0f03180d081800c000c000020150360007128a181080c440c0c6101e52050440e140341d03030101c03804100070002c0000652041000d50002030300c60b90000d03030141e2042c0c03d0341151242044000081010742444010f005004007200791481c001641c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 375731924 1250 375730674 375730687
    0x30302100507300204080304030b0c16031115090312011415031e0103080309060603010506090112150f0c0306090c0e0108090c041802030d021b15130f0513050c 70
    0x3c000c1c440380c00700040b010100781020b0780007004049070f000c0d400182d060b4200003410310a108a0b858155000010b0000c13681c0340200700140b2100f10511a50018100300603840242c1c0600801c000340c0c000f5521560546400f401e196110590300c3c0e0100740c0c1030014444580c00064201d150141240030001c000c1d042d44e0740c160340b54584152540c0014241000c514004c00113042d001d080210080c040d51081121590300c0c00c080525500d00040140218030030380c1400100249502c803421030b01d0440b90310808200202030186011030040c2404424000c855282262034000e0030101c1d00000e03402030301a00d040003032588911008055030701c10140368000c118045081d82d115441180120340c4150303030100755010f201109001a0655030010301002c44a80059241070540c94244211183c00b403560008181035000a044401008603100545200c0c0c1e654180c04503206681c00d0031900d62015551402281648442c031640320404180591800b9800340301e00030703090113620700c6032034020780c03507110050300742070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 375733174 1250 375731924 375731957
    0x1051c051b0307080a060501051509150a03020d0504061d01150b03130804060206040218070c02090c090406080f0f030418021c0504210903020607120207080303090106030302100507 79
    0x2581c01c1800c0d0144142080058600c00501c22019a144075080202d00c9514007401c2001d4802141c81c820b0207131504020504440d501c01078400d0500040d048815203039009250b040d4001e000f0600680c502c1402c00c01008200105540300000d00c1c0c000195402c46207080388600d070308882110800280025038400c051010603001c6028552082a40b4020703001490b51b0b43e52494540c11a5008d43c001da0700007800e01c0118505081d4210b91140c018034084007502e880d9900600c84041100041d00a1260101148198401600701c07003946102900511245c3d5940d03000a5445000c1c8140310f0190040703d4400144e608041b0444045404140f4008540100521755100951008041034801c620382803605903204030310b01486101c0d50084021200320341c00c3c4840920b44018201424041080c2c034042400160707528030030f0301c07a829000f0845003422050058103902d8050f094200d110144000700c20000181c2054000c04142c0e4420745c01c0d1540030a4a10028043c0c8000340c456030b001c039040500e0040d000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 375734424 1250 375733174 375733213
    0x80105091b0d0503041a18060705101d010606110f0f1506010309060507080402030c0108010807030f05162303010c0824060c010b011d090417090303030f01051c05 71
    0x5002d042920b141036500d51650946d4807120a0324489035a004c00d40100d101e18404000000c1c2c0c405540041c03801006603503064a4116034504440030907680c60b95100d82511240c5c00702d2070b448258008200094850b030016180010035828101c81d0720504d008080603c00101d0002341d50440c2c00001c0c80306907131410300d01038003c2d80140018101541d4049000c041040c1c2d001e45406908240c03542c20b1581814014103091a01404a0a060000d03130001006284000030f03040044036003080f121521301c000da01c0c02504100c0b150111042a000326403012400003c1740319450603140b11a00c40d540e0a841040501d0300383c8209214071000724032260300140859000106846000c010100d1110042ca140800a0301c550400c1200030303a1a9521444031358030356080f100d954541400c3c14100c200310700d40500050310500f0002c1005107592150450265207840c02e10588e614514010705503603d0340f03002000603000210034400c503032048020744c3c03513010000042c1c1c00c86400035820202070855031800f05894500d5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 375735674 1250 375734424 375734449
    0x60604020f030f1e040b060f010201090b0a09050102040305030c01140a05060d0305160b0708061207050d02011b06050c0910050c1b0a030b01080f0705010918110909040c080105091b 79
    0x104110f803001383c0d0700085510600c1c0d200c0c910a040c4602642820824092000020b25019044da80340002c03074404a80050203c42d4010b41501011842109618000e40a0700682d40001c1a505c00820031111401c419004220742c0f55540d2880301040d030302c601c940401d5400545000780c03c8100c0803901c4c40800d10070401002c000e441240d514500c4061540e4102d100c01044034000b0004103200c082c05518540182072124601190000300195418040021590180d00c1c2001f03051100000c07090550480f25000d048041d03404c007008100310315000740070188540c00003810780e100d20382110200c85100d0040055980c039145500c0100550505402d08203401042100c060b9842100c4600c0000018170704100a0b01034070503040038010001c1c40d5541d07a8a0042c064101505009594000384001d0808c0318400c1a8460000c0020070b40080c819582e001a1180c02941c6801070321600400c010b1010740001641242e00c6a0000c100c1c5a444030100c50321914501020480e202141407440b41501c0c0c0061142c20 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 375736924 1250 375735674 375735691
    0x20031204230303030f010509060420210c0d060b0403030e0906060c12070b0a111c02041a070201092304021c051006020609030403030c03110106150201020c060604020f030f 75
    0x3440300001c00040d146800c1100c0072030150520b28010701460502544007034004406031070502c240d09200707025488803101e6030310140600a001c17921006070022031014800c460000e00702c001c00c0741020580080954410020905002d00380b40002400300000011a400c481e05540d4040391540d04804101c1160b030054aa1940240148000615000c0c10300c400d100c8904e070030140c0b40c0d55210b01c0c13520312009100101492071261418003808004a0280e0485849110180c003c0c12000a1148940000c0c01a60008661900c83d0400710038403076482c200400400f4000d803a410485541d6410225008441212000010b44080c002e43c4040c107094014000b406064080c40e42c00c0c0c000301d0380301000c4500407141e003144840326805c10000290180507860300540c209028500d041d0650310003514003112010010208030f0b055940034100c080c00e6000c0ca029101e0398034219200188900024003035000380c0d42983d1240203213004a6801e20303080c821141a0001c5003121030440e91850140c1e401c00100074003102 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 375738174 1250 375736924 375736979
    0x40b1c0902060f04050a0e01050102060f07090305122110090b010201060e28180f060e0d020d031a0307090504020303040f0324290d0503030420031204 66
    0x40050782c0da080501180140c01d00c0441d12a8942810001d4010099005610035417458005001e140d0340458101c2d409040342c15200d10350f4a81450032914008554000380807805510204100000004010540d40d00ba4122407008001000d0b02034021180568001c2002d00b11907004004034a02d41c2c2003001400f030140000500c141d0303a0314008091140440348100044604442c10003900d03154025550641c1801c5000c00c0f2941c401130741c082d100c10100401801d20698211603100b0800c00e50400320035244081c050f5480018810780103543e8043d441c0704040802c1c1041490f0329208070a60800c10203400040042012602d0500084001c00b0050300917038050208007c041250000c0301d415000862107400c840001c0403030148041d134104042810001c8803410000c3c0034850010070602c0c83e9801d41e00c01b10140350317005d408000030210b582890004155020100400c0280b100f4581305003003141c0742903c01d201231510941015180c454241d00d075580303540c1c18402408412030301c5842001a500c0c0d918080c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 375739424 1250 375738174 375738191
    0x180108090114090a020102070f080d03050c04170a03020609010b0f060f040b03010605090f0402030f041211010c02030301091503020607031218050a1101080613050a0b040c091406040b1c 81
    0xb16030a94125010105540440300ca0021542c0c108500f10003800e54000c001c1e1110b05080e032a0362104d1410840504044d00c0da40450704460701002202e00800803240004200e081050000c1d4031410a541d00741e000d0701424001508841044c09003554120000306072a4100240c1e40400c43c1e10742103021100003a100030300c80450080c048500031400b91186403141c94882c20700700d00301b01c41158044003280c0a107006006000300007010b901519001944920b0004413500044022140c0040c0c3c01c0101c8545d600340305c10000b00f00d8022006506840310030100f80580700103082c40701c4406007140f05c002d4001c802041208040b9200c4d884030004071403a140e011400310245000745848500088040d1150b400c04103402d4100007805100c68050282030a00b07103018030b40640065100d490000c05480d4058440001403d44a103d5002155801006004100441d080da030000e203a008103010780040740c41c0c2c140c2c02003003602c1c02c0d906640c2142d15070500c8034503000f40b0151007003101000000c0d0044051721001031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 375740674 1250 375739424 375739451
    0x1140a0b1b0f0a060c0e010804060c230705010506030102040b1b070f1508060a0f140312040306020301030317040c0302041802040903120b010309080409180c0905060f061801080901 79
    0x484800c035504800800f440001c9080410445205030400340038807481000381c400e42d0740c1015410740d000781c101c03030005448481180141e48142d01e0b480003005020503000b000d5412903c3c0005010303d00d010f500208802d6a03014289800c034030403030050602c00b250074418081303942e07002c1403180c120704600f0313068a81c001c2d07884000700c00040198110181d030802c60115504812f600100f0b9a51151003101c8072640e8602c1e04003910100ba003980100c21200c2c00071002014591810400800d64484072190340e69201c0d9641402c8001350030a000c00c80010f10200008414602c401c00c1c410300440e0400c0314040742614503400c01000380811003035a018800c200702d1003030146e80d540c4510501140a5150326944021111400013260301e4001d0703250626203806901d801140c108015070b001c2e41c4038103400203141581580015015002030700004d2106540b0500444c0000050300aa4001c2c03000341c90900d9a01461020000d540c002e028200c0140c00c4d0841c91800c0390740c802c11002c2d80102003500001001c00344550b4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 375741924 1250 375740674 375740683
    0xe1b03032b021912090b010603052e0305070b1e07030c021e04050709060206010b0f13120605010b0306030d0f050c01140411041416090b0d0f0501140a0b1b 68
    0x40140c0f001404001d4481c0d01600804550040c1d00344590800402d84640d550324450381040c001c0b4003c240d601c00000e41d904050003c0d0300140036022851105010702c00015130b000302410b0008542c80c2c001c0701c03030005070188508203581640e1042c41080c0c04c020381380d508031226a040f4500070b600b0445032541c600056100c000184400504072060303020100da060f420303c02500c8004d03107980200310a881c010441c60794085141c9043d03440c4c40c00025a204403600400c801c50081c51294242c2d0b00b80520000390700d117101d021448149102e20014820741ea40d4407444095400b080340d255030160800308210703a42510540e01c601c2402001d0511a0801c4040e40e09942125120009041844120400c1c401070040e00b240d505005c001c1164148031000381c060a0035991072003c0c2c4119181504e400140f800e1501456102025160070f84800b9114210307101e403200074202d0004004421441c060021030000c240d0b00012b803441401401c0d4a01031898002d035000320360f1180011641c04401a03081c3d1050355800e10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 375743174 1250 375741924 375741937
    0x30501110c12160611030901050708070203220f0f030501110403030c0b1308030a02120603010c050a14120a060e1005010e010e040603020d060e0d0c0c05010c0201031d010e1b03032b02 80
    0x407821922447d2200619084031000307400c000501c078920040082da20741c00011104000c2e180c0b003025082000c0050b501702c1d41c0240d900302c8804544014408103000079004840002c99000c0e500900002c5102031000102d0304c65400082e001444410b80c12000c200c80c100c0450708800890410440c483d601e0b11941c030180c0040d20b80028607074000404404103440c8034401c0390000350840080142c850b542202500910803924502c05000c04401c114405405500030f54800126200b401c100e20320742500400d005048900840c0e0000071580e0108038610351210045050741c0d0103850360101031f042d8800541d0780100d0800150740c0240c071510b02000507225480a8044540300700d07404220090040880350500f106007240340c0401c801d814040c0c0100d105410bc030300417100d080c00c1404420b503242c00100d02800c0c0100c00c41c106403e031802c40402d20394055200c40065100041581c21440c0b901c41380039210a4040a05941984203000f48000105a030003007080e080d078142d003d80038818140404d0816030b044903 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 375744424 1250 375743174 375743201
    0x415050c060c040f08010b090f13051903080702060712180614060f190306051801150302190311040c0302130305070e0604020f0a030e25030501110c121606 68
    0x40f5003001040144800500608031a8009000041c003e802085410400601c459115590b20000c5104001803c0021001e213401200b81c98039040518101c0041c4c0c0e0715000201d000034003540004006610101e80d05001c1d5149989610545080700100e5001e443c81003000038940300490644400203c007441901ca480403400311343d031010324001040003034182540444bd030040341c03e44c000f411310543d00c00d135100c2a66070106000440c0e484070018100303010b0500c0c1c01c9207159071829003e001203076940c0c000101200d100701d80040449105070320f606801149484018103c1d01081c120442601c0c1a802184244440f80b400500f081c50b40041300c00100000d50098942d07030001103007030010400132806154041b4054405600d012107080b01710300307103229150800b8101680c0d40c1801c0d0740e0395030500c07000104003003480302e90603111800c420030990f090131840225070340e62130044080b9000c400b00003581d21468000e406080308517080c89041c001944020360941c43d0400c40b081800c000303800c920a160320300d01c0d034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 375745674 1250 375744424 375744427
    0x60e0d02031c080a060e33040603050313050102030c19050f01020310090b0d02010804110a0306020c01020405090f0403020c190b030c030103030e0909030301060c080c0a0605071b080415050c060c 85
    0xb0180138100c8806400410107175071144204010b00e0f0803481244c2003070b242011000040c0c031f801186100400407601140c0d5000d0705050b00002071100020240464016a4400f00451544c1d00f0041e60b41b0320900320366985a03048036298100034002c1d00c40a0651901075000d07070b0700c01f895415017507089034006c03075291601201d1040144502075040c492840e0050069071440006486030300080c0590800901c02000300f8112404010551166682a0000c43c1e00100c29500e441d10414468083d401c44d0060718011070103180003c20302a191034500340245d4040e0058500120310001340080c6010f00380c0c1c18801d480d0aa00000303038906001000703605c205404108141c81e03504600d4003c0011a42c54080352003468020180905483c002c011241180c4050408501c0400b0a16103030307456024032071041d202409100c0b841810706c100d641180e40f10f00d09503500d94480301d0514101410700c5d00481c0b006801014144820305c00c0618112501402e1415030411038144014144841d2a000003221071480c0001c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 375746924 1250 375745674 375745681
    0xf0c09030a0f05030309191a070c0c080c030c06070206040902030c0f0706140703090b01050f1201020705012a080606031503011a04110406020a0f0201030902101106070801060e0d02031c08 82
    0xa000000340c0d2022820440750302201520b988d004044100150101b01038104003050b101406005082010b036840024030030220750307483c8031507120441c0b590090b000780201c110031090f40c030b0040100d8030010b074010135503410076052030940c10094000800f10080900c0404c1680000c1842d4805408a6841440041000c0f1811041000703840805048182030504041458000520303da0b02d0324107540c02560020819032200e00002c41c001c1600002d0348665100041c88401e1000640050601401c010511030311001c5d00c440c003000c0c525511144400050b00b1313a002c540700d450120000c41d0800301c9404204c64030600c3c10300003401c560348100e80c001306e40e83d03c484035034180c2090300900345486000007045090514000c0043e4882a68090040000100106070411603020707500c80001503801a100b0320001845280c040c0615290240c07403d6188036100001d0790381c074482d400d054141d444a580b10521a00c3e2a000e0000700c540c06c900890707060154a880e004500306642e241454200b43d07070394260741801c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 375748174 1250 375746924 375746941
    0x1170a1d0606030c0d020d03080402030c0d05070f0f05060d020d021903090303140907060e030a050303010f1a04030f030804170a0e010e0d05060105010807030b0a060e010e0301050f0c09030a0f050303 87
    0x900c80c0c41018051000b41c1c0c440c1000d03a03612640310f6161f41d01401c00000a030340780e10002e403c0070018080f141d40b05c10035141900a00c1000120301081c0d0312121003c3d85001d8680900c64429012445844c0d8019030420220749010459005020842010800503080c80340365000b2000d1191a1141d15000994a5042c5014942d05000d660024645040c00d441c3e00d0402058080e00c0b40d8143c0100e034140000d180d0104401c9d241040f1400e440c40c2c005041c1c9403603503190b8100500c0c29220780300e01d40070f2210607407a90381c2c9400e400003102c0480750301c010500d488a10560342542c5400000f00b041d030f045014060b00303403041062440207103001c1c0f50710340da414001c03038075500058030019402d103555001d02294008000000c81c0096030605580090810641e96526084210040d01c00c11105a40103002620b0003d80b944d003204803c440c5003001d1301c64612843c80003081c0350890300f00f1282e02c10340701c43e07072000300300b01603071420050001002c003505464424201d80c5450004114039981100d066200000b00014030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 375749424 1250 375748174 375748183
    0x801020703030b101701150e040f141f0e06060909040b10092c030c011505040e0309030a060209010c170d050c0f09010f09083901170a1d060603 63
    0x802c0c14203110102050340e017221010306105009820580c0740b1225045d01c1507000e8050031106d044010814003559030b864001c803000c0d016102d240f61041e500e83e40441c90194104210611901300e940084481d14a8a1071400c14020003800464114404011241031511140410741c401d03400f40c3c1074482681407071180c0a002c4241079004001242c074140040310900c054001c1000da801c54912400b5150b60034407541c500390310544460380025844c1c0392054180080c0d0004a008a072011034080109882e183d091503124810706032540d6054000c083d44600007a002d81c0a00400030041c5052602460550390f40e80c1c14045040501c0728421010550341c0810400c2d004190748a40b4003244032b4141103c411040049003c0c0b4030040c1c0c10b00a4944c450310780e0502ca80d42c0c030310091640d0300440303190480a40408005100c1c80000c20590360b0b60714902030b603064040b00641c20040060b510b050503440045426007141c0703006425181c43ea034850708803403021480c100880f4800000040584502c0c10284205440c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 375750674 1250 375749424 375749449
    0xb0601360f050d0215031017150a050106020a1410062d0b0711060702040203180c04060f0501080a0f02130e280905100c0c060506061204080d060801020703030b 70
    0x1600403d0000e00181c84460482c80005099103549440e41c13916035441551705915080701e003692800042d00150814001501c001d00c00c4842c171044c0d01034550031003100c25180300740105009079104413180000249400e0711421a000440c007a0307402100e510541c0c030155101903100c000c41102001a00843c4064103d9201c898185920f9031141340d840c1000142c05401503c4019000303059000d51403185458807401c039030040398020000c5550345480001c07103014081a0310900114414000b10a15600300b52050318140c0303000ca844500c04601e0300004503003644000307280407200ca0325400d000d6060341c07542c0081c000b0380c110b01d06911b0459003442c00071640d4046c02007990080420203414032807031002c8041304d60740c498080302003c070780000a414543d282c032035001d02d200503840c07800c40d0f160301240d030110343c90070141d22841c801d2249442e43e00030004140142d0f2400000c06074100c02180020740b2440082c013480360608804600c01e40d0303034591282240c10091080e070110303880d800c0d9100c2d5031601c280084c2d07a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 375751924 1250 375750674 375750679
    0x1b031d07030b1306090803070c15090c05040b030118030509012d03020c010e0a0b060a050102030c1e150f010f0905070e01110304050405040f050c09040b0601360f05 72
    0x1055186841d05030120074040c01c0c040140000c0c40703030031044c090140c011400d107940000c51140d0f40e0503c404010504071488000341d414800403010507403105089d0061418440e000000c0d01d00003030030203041000901c500011554550760b20344259844515507c40799100901940302d19481da406040050920030508550b82c0d005d4841c040000514005611006a144881d00e40142c99243e443c17a03240c01409818034242c0c09200741c4521808000303511700309511036a820340340081d0070365451005907540c1c06114104903894020810f108882484c5a8040c100030800e030080b00c51900c41c621800840b48004d840c403025a04030080148010070104034040c004114404d0f08011a25010800801a054005806041081341690180e141c07004000f0790300075040c000d00c101701078100b03441d080003003500342c9408464900600c001ca24030b030318050005503c6075420200260050703070394100450713035000034103544110508196285102c0c28140c801c0120044000701c2522102030802d40e070ba03500214254017092 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 375753174 1250 375751924 375751933
    0x140708010807030b130831050603010b0903120c0a031e050306040c140a050702030706050304081615020f180f060f09040209040912080a060b04120203011b031d 70
    0x841c0900c000b601108407a0407075000c1440b5182c20b0003420181a5594018200300e80100d660300f22101900400d0120f20507440306c5041041e0012207451110000e44207007640b040090004101140419000b804803e034002c1c20b80f144919142c0800c00690000c8144a52551154405c2c40400d50801a1104140d511101c503500040101000030140c0c40001c1519000b942c840c2c0d0000f922a0140403448849000d8052494840300c980728002c0c6103811024042c0d20074825004000b07491802801124040c0c2c0d004458207181103800f178085404900517800c112000c8040c0440c240d003801c0c0c248090b107001c01000401c2980c03010704040c00410707154940005441000184010461591000c1c1190203642e11500d40c20344619103400010000d0049401803500b0a080ca0710240c108005110120800079980c0c0300c1004ca900c0c1c9c1d003240750440300d447c01080c410500c100820700c40c40b2000c0032400205440140045148520b081c071b40c0b818a009030740d5003004170f600c48416488030b810071130f1150142c44a110050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 375754424 1250 375753174 375753179
    0x110c0105041511040f05100c05060106050c060f060a061808030f0408010b030609031b0f060703020403050d0905060403021216180b060705070e1009140f07020c090a230a14070801 78
    0x400c081c0c074003071045502c11a1f1030300311150542c0c09445014540f64000c026a001780da510322010b08543d002c00000d055502910001807000001c03000d4040c01408040e101d004480c0c14000150341d4243d4404502980440d0b500c400030712100200020010700c611100c030161901c0c80c2c1000c040c2501c051942d1a0310981044003000078a800000c06d0314441707441d210749040100d01076070341c003420068410848003003400b0311010402031030380580040046078440e000b1a80d1010507030f102150349074078500915038480d20801040007d46041c0c4920003110400609a5081d0303590188c42410704681039000c4280b03004004403040c0d510040d445965070b002c030140c070304a1401800d0769031641c5918990051401c4000458080741c004020461018090b00c8442010040380b50b10180f100d0382c070442240da0720303040070401c0c00040074180f001c00d040f0f003030050182142c0f5041d2911422172010308808e00e5003051485001228400545961403064080c0040c1200010196043c8100740c1e44d852008180505101c00720004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 375755674 1250 375754424 375754439
    0x3091f0c02011209020a080d0e09070c0609060e030c0a03020f0703021f0509030d031a0a0602060415020f040905040b0c070804120f0b0106180905070909110c010504151104 75
    0x64030046509183c582941100c41c1c00c900000c0031504000380d00200000300105000c1e5001824461454980d19080c0221aaa008000c400c03c41200c01c1d20000307107284016000038845070800c200061040a01081800e820b056043c6140c01a12030006075070300c42445501410740500140005440d00c1c1c0c007500f0f070f503030954000c500e244107442c0f00d1510441203034120703016407403041040e103c2200004090302c40405d030409004019018000000080030050343c0014030314501501c0c80c8048604a0300030f09065900c40e21440803242c50140301440040d001c00c00c0d001c000c10b03564001e0028200600c030005141c241410807100c011801440c1c4004400c0803c80040400c61032800d503405c403010100c0c14001041c40e032400c082c84004d0040020480080500040b407201d421244950420038032800031880d403a43c0e1314400b0144c801c240e03814400b1404103a000c1c000c554213508500c25110701c8600003440c04d62000045801c60320112001e0750f5885101445280310f540e603019146030420700c0021203040c942013020 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 375756924 1250 375755674 375755687
    0x70e07020a20060a050d02130e011d06090406050a06080d11010e060112020d1e080705060a0902131119110d1805130e06040507051201061d04022103091f 67
    0x650051120203d018406d541290301140c001e04000b0042002c9960f4900b442c1880b0300d828012650b106e401085203e10000c0008015480780c20020018005a2241e0702c1d928000c1c10054858a41039846020100d4904800c01440681d1991131b525907a000c4582d45485084500174108140103400c04001000704030743c81d6266000444d011501e8561a41c00351030f0019502620b00138514102410114004c1031100701005060018052400d581c2243e0352118000100c0b0303000c4100039404004040c0201581c1605c0d40080d0b003520712040e40e986003100354a4203162000c500c9414800092010380d00c110202c0c4140148180454076050582901c0d08903070207a80115030704e0027541c0c001d80c0c00d0174420070007052030340000c031011090b08255616420300d410121741b62200c1e4041c142c00f40684003410041c08505225441c00c403565940305048648954841017075104003d4800c1c0d902c4042005500742040d001812079113a0072500380196921020b19081c02132210103841c12110000c00404c2616005401c801d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 375758174 1250 375756924 375756937
    0x304142a03061b0f04080604030e0f1c0809151201090b060a0c06020306060706020c0d02120c060105090402030f0d0e010206070305073f0b09061207060809070e07020a2006 75
    0xf20282e0700c6201c00d03080c421503400b0b0f560155420703100d048180814180c114950494010081e146034880c2c001003c14411042c040c3e011240543c0c008112080208075814050080954000c0030401340c64031400302181d031a0040405c01aa00c2619801082038041c64400e150195000340c0c2e445080c078070342c0c11000e0098030b8107110140c1041d0b0000006109580c3e44070895840036030001c811503da44480e0f004941c2d41c1e6001c0380050262046590b6452511350540a40b9410803480c0000d0202c1e070308101c1440282940a08100c0e014480d030803010b403000c0000e1098409508265440d5928084100002850280003503d503a041c50b03c0d0a0900c68004c1d4070a10781940943c4058128500c030440590380404285905611030280d4492285500c0350895034124150001046030240300707031f448140070050480c0640c0c1111030765a06c058010040f440c01211055400b801c071400361f5042a68889545070a814212108030058002099010130460380b034818100f05100140c0c2c68103107000340e0000c10500d12038030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 375759424 1250 375758174 375758221
    0x61902030907050919151208071a1305100902011d0121020c060c0408250306022b0b0a0b0f040f090501080d030203070e01050304142a0306 61
    0x501d1180100820300003880054a60310942c80c19010002c05401a039040400f0203060801c0c1c441c00c3c080b917110003019034040100c0b41c1d80f032a030b441c0d441c484035030320803a81101c400d40603130002e41403004a010010702c5421100440b10802c8014500f440c00c000344c840048c44224070f0942c05c000582da205040440100011051003a0740303140800607904070443e51240c20b22142810801e090071350441d000b41c410320440c20110b941544030381e0600c401070301860081200c5d0f680310030380b201004031320600d015001c0180c0401e00d9401076126125001664406034130824010051481c0316200400b540000c5a40c2c0c108020400c09484040700040e5412920f01c500200303424007040301e508001881044400038060420380c0c20b0b055580341646805440c003480b5550660117001f400c8101c0d58000e000b20381c801c40e0f00d581c41100c40c202c840c0040d1040c0d0800340090b2000d42c80e0500045100c14100310085041204400c1d100c4001e001082c126009503074620100d00903040310041c00102d00f180042100588100c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 375760674 1250 375759424 375759427
    0x1c0f050405040b0d151b020703021e060c01061d01120b07050c010209030a1208100b03010b0a110607020a02150406081504090b1302130c08070c11100806040509061902 73
    0x405001482d5400d00c40c0c03000d0102626080802001707001907101040d5000f411818546000201b0010781e1108014400a0b4012200044001b544150001d5a14041c60300410326410405086012401c6488a42000f0300385c0d01c0607034009d080602211790301801002080044801804203545007070014502912603c20b00c00c01090403030744e2142c20b4054400c01c810160448007080d140c1d08100c40707042c0f0001550004039403c00c0114851000a030018025035107a504528030310303440c1507041145640704200355010806e800440303840c0200709001c007a000303d090341d00030030140d0f1082c01000b4200c03032100307070003c90408108010020150050b80d0300754081b240c041c1110044140d200460007400031800c0041003035503c542048204080081c5131072aa43c000e40b507d0100781030401c1584100c6407019815808148040700203441640324202c0703031a0161044000c00d181c0c0200d84042103001d014903c43d400800d40351810840320381420b1044903402020f00300100018103120b032034250a2448424440e880540 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 375761924 1250 375760674 375760691
    0x6060905060d03180b070606091406010215040309170c01030b100905041d0a05060a0b0a05010c0b100b0d09050f01051e090705031b030c150405010c05010b0a081c0f05040504 76
    0x201d080b2010003000901145d5540b00210328042c00100306601500007100d2400c50000308503c0c0501d5810b10810041e0010003a0b42c40003030740b50000701c0004004a007044003045002c07600c02c207444111903070b510241d40100b6402c9400000941619458030589001d40c0410040c4103400d0b03400300400741101d900b170341d000030580241e000900010003183c0343c014540c4a0700f1140001c00600050107840340ca012041000781ea240b010400109a03050b124040c0014017243c00540407507001980c0513080f00000190801c296510210301e1143d030400700075807410076554281a014040280182e00c80c1801e280001c1040f45420f02c4410514074620003548640d00c0c0100008042642c10000342024103001003c48207000c103009400080354801840d914080d01030b5081516483c2401d540b0b440642100640c0c0c1820507080900454503c0e14084041c2c84564032410f600d074482c2c5034000381002405490000e8111449060043e4070b4140100c22242c1c00c100c401d122608016500405940030f4807002c48003c2001c05 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 375763174 1250 375761924 375761957
    0x510020a03110414011706100f0507060504050d1202030903180312030906040606050609010c0b0c090d0b07080c0f030a0f09080d1409030f03040f17120406060905060d03 74
    0x1840c502c0d0803540b401c0000380818241820a901c3c0c400b508241e8070b0b6a402c442c081e43c0c1004807442030b9451900107101640d108400c0c0d008402d1000c00760500d150007400e100381502d840007a141305603019aa1608042d1800719600d038013414544410b20340b104190b145060005c1c0860343d92148044001509110034070b96481d90b58140102d00351220305da4542c9489044c80300d4103076154201683d088487c98035041c000203040c2041026107180a105854410080c10542c603210040d4500a006036002d282c1000b440200da0307036410300e040302180107002c1c45078285010b10029100c007074064100110f070582400802282a61001142c3e800380215001041c1441c0441d00c1c1c0c000f070000c0070001813071141c010550720030100044e0f00100c004100760550481c261074024080d61a40315824a80c482824200005400301d40120394101c81e2034840c002e1001d40b051940c2c4e5040c05a003145001c04504610f050502041c42841d0103020080c1c040e000f403c12003824403000140002e0700030707a03004017800004808070901d00b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 375764424 1250 375763174 375763181
    0x15060f0a120b06130614041113030305071a2202060f0a081e0106020c01030209030a0b09030c07091512051002031e0115081b0705030703080604180510020a03 69
    0x401050707412100c0c80c4400e107026500c101086030a81c2c080d0944410803e03c08106019070012030740034105c0c41044007512804e02c0f02034502804d0303666a149003007022070180103030400810004c40c040d940703084c0c44400a1400c041308151401c4000710100d01c0d4810300c01d4410103007071003046281d0007002284841d100d910201c0c40a000c0c064056058000104020000c103400c414103d01c5003c2070b0708440c00145126011081c1118280107500040c0c0c0030f130301c1503a800d50080e401444000b01c01011984440d01c6940c4000304044120740d00111a04007146035189000c0821450015203111401808641c1004c1005101c0400a21034444080c1140782d140c400c0c424240110600751900d403505669910380342d00c004070500100e410440c2d070044000f00000e140c110000001040d40c4555a5034126512903508000701132020311044416024104104800104104000c040244c4281c0340c40c107491501c84c0800c4100e92194046110413184055440002000807030310958180910310016115820144218020f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 375765674 1250 375764424 375764429
    0xe0903030c0717070c152a0312020d0c11070810051e1816501f08070302130b0f030114061c1e090b01060f0215060f0a 52
    0x407407800068640500000c004880e0a645180151041c1404440c00c12203d00403080c000100800444c0711403008080c2e50541204200d00928020100d84160a004e100705ea1120007803c0b141e9698330000403030703103411183c192800701082002d000c007146400e18994a5885c0300f001c60412540e04d50014007071102c2225000c5403808a60142c07941c0e4500105029103160b00c1000010700342c46408001c0c544540913940c09000c1d80d02030744c001c00c0a040c40220280c008541e43d110340c4244098000e004c00c0c2420140c02304501c040300d01813004592503408083c41340440c2050950b950320360600408040ea80d411490450300103086260050740c9980c02110500842865084542403480c00180361b4500d2408101441c103999003040e400404001081c2045014803581ca03001c007459154122803011070880e60b100c01c03c0c00c1d041a07031404aa101c000702520032980e00130412514803001c0f800500402c0c1e4040a070b00101055400184007121550b1100110f045000b0700903446040340010320205611a01c419600 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 375766924 1250 375765674 375765713
    0x3030610030222091107030921170702130504030e0f0609041a040518060703020a030f05180f0d0912051002070c0611060105090711070503190201090e0903030c07 71
    0x26070034143c0301040d0300c4100030310910032018207280d801014003e00740c0c2110401d40c0d158540079110342ca40b00000c0d4511810701034034000407030003801020114211200101e0a045451261959441148108800c801d082e2191100040c80e000801000980141035055010811110120860056800100e461080c4460290402d0610300c081350f140c0624030010b50a40021201405207035030341c039a110310940044442008540c440400701d1103140c0258010a6200321070300d0003280135580000e500081d40e0080d04d03525100403d0103261074200310203000721442c49100c040540b1014015102c01400105240039070070b074211100103c1350800504226200b00d22914203420b41d2944800d040c4201001118032480002c00e0142900c0e007120400801c03602d0580d0700081a041154585840464144042203228a0580b181d10b1010540d50380400000c0c50203900c1d100300406160491000500f441041e5020a02010610701030240c40e20000c010744c0d5222003011511912100d00c1d040c41010310001121202 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 375768174 1250 375766924 375766957
    0x50903070906181103040206040e040816080415030e060106030f1509150909030206040b150904081e1e2d0409060b0304120f09080105010801050702060711030306100302 74
    0x5010410030b800105643d5404008021814908510485510046400a500c11020002440361100c5003044542082c0501d606038206509400c0c865111000310405581c0100042030402c20b0961000440c45401d000e481c00740b00410168102c0c1e0f030390b0710040c02108103141c2c03a03124038850b0f01a5a0f000511052000d2142c1c0c144c0b0b6900c06800009120402005d4000c680940000c00c0c0c02102c2d000742c241c100e40c90f60041c05590b032180c40c1e00701e00a01c060805500100c020b0102a8150788498103280a14055030407160740300a9010312900c00c036602c0b081985ca030407003030041e0403000c0040c10801e04203608000429560b0301824400c1c914018403119140440408a0a2812120349034806032056070046c0301d0400c210354a600110f50940812600180b0b201d000807500030000d40704059208003501d81e810007801e20394598503140d003516000d0f00701f03902581d5110100040780d64100b0500f9005030a608007468000402425540c80e40b000929a9000323003000303806420003d12950441d10103181144960 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 375769424 1250 375768174 375768179
    0x12a11010f0c020106080303070c06020d0905060f0a06060e0315090c0a0306060305060a09020607060b010905040c031b0503062b060603030206040501050c0306210c0406030507060216031101050903070906 89
    0x54001c010802d02c400c01076103001c101003403d40f400011a40520525242c88581e14103603078401001c0e41c019002c100c4030b035132030b04900000940304015440c010003001e4a01000c614040d80c1d080d088840c664000300402c8200c4034000d040c1d0310041703101106008401701e064510346e02c0c90f11183c9800c044020b5690080315030b420000138064941d0105064910440c16142151980800e240581d0407407075010354072031030070094200000c00300d50005007052418180480360550b01c000160440c2c40001c00f0001103500c032150f1003240c114442450000c01d26a0418505605188010402d08485031300c58000710401d15400380c810780d4201c88212000b5504c000c0a0040549a107002516220f080d5030413191582003c011408540e640c00c150382c07180f040501854050800f0002000303541da00b807645600b260007246070010850b252402107401646c080e100800b9514540310f402071521020100c4025160001401880050203110a000340380e01c0900c0c100c1e4480c03400000290401c14981e0000090030b1a04100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 375770674 1250 375769424 375769451
    0x1315030b041406090a0501050a0b1f09050306010f080f030c1e01270b060d050d0302090d020a0b03042f0d05100c1e110c010f090803030c1b012a1101 65
    0x34812148598008c4c015900d500030f442060740d24150445502500480180c14210403520f108042035140e803511000c05603030350010909007a0f080e0064070300303080303040340500600750200b1844402c11b0142c0011841d120580401310f4131141c40c0380c1d0701d1901024507418420350440942000c400c50604801d0402c011824680f0200310a81151003210303070000c41c00c002095480c0450040340c8a82c1c20001034100790701038010403002903000004050340005024101c1e00941c07181840e5801400683d500c05950703040ad0b0070080107400a00c003003184900e400710001c66906200e08240710182000b03030390580c500300841c43d0890030411035880440d90303645000800303860b0f90391040c0f0040102c106450504011080d21104403017000386840c2550044c0d20031454031090354403075010021000280c0c82d18245068071103080c5400c660003640d490310f03080c1020800e1280c44a40f22003203032800200500802041072800703800050b66464501002d100d420180030f40300c019008000c5481c100c002107000f0849400240c85 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 375771924 1250 375770674 375770683
    0x20a03080a050702060408032a04050f1c021e0405070905010e0102030f34030c0209070903121d0301020a110c240903030405040c05091315030b04140609 67
    0x254000350394900412921801440b450f401841c80c0d502600c1151303280d8032101030640c009050440b40710314460010070700d43c02c0503402400c0810200360082c2c0d11450001084025440002010705c518004070041c1905040b511000d6080383d8190f80507070007030b1050100d400740d440c0000324060704142001c040207007140d8004070b1042920000d803500c3e859880d80c180126500d020b148100040c4000802c100b4184d0350184090070360010310b0840d0021035103554041200e00d50b003511401c8000c503164800034070851406210709980f089291611200321490358860b03041c40800d1818a5040c045256105004822600440b40a03907038050005d40d510041c02c04020305610450b8510324540c028030482011903d052a01c0b030216a400381401d004400d005a000c910a50100c031016038144020803001910b41c5460040411401d040e8460688030403c10040c80b0542e401034807030f414800d117083d032810601e80542104009484e00500507060a076200e20f40558044824180d40f0441c0c4038440420094200025 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 375773174 1250 375771924 375771943
    0x40207170904051503101d0706050c010605030c0607080c010b09180f03090603040b07170708070210090c0b0702061c061707080c0616350304021305060a03080a02 71
    0x100c0403c9241c0d00e4800d0500301daa0880c03035180c0d1541140103a540208581d070405500600c00d510341c00754103c0f40c0b050880c07814000d917000d14045180801e21041c950020702c144001440290050100a801d4000280880c800c1c8070b00100103510208050003140b40035885005117400142648110381010001c0c00d92002d40400d0032402440365820b6040021400310685841c580301604880c29034580e42c0c0d69160203003000b0400307010401e0a040da030040d80c18001b400703401100291164405420885002421300405101c40000b0604041c41c040000c0d4400103540d0460b1121550b1985a15491001805d144103c800c080491895485070700c070000b40d143c3c0710304111101d0350750350492a1013070301100b41c8035125440341100b10307080031641d11540e040c440010000542c1d0500404142c0305680e490300300581d5000c415025100c820180c40d01c41645a120081c8a03100d00e545e49401c6252590000f03101c141c12640140c215901d0300d01140058a50954030000765074030040894444501180c025904c0c8070b0079 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 375774424 1250 375773174 375773179
    0x6080601020a1241070206030c0c120d020a0f0f1e0302040503150a06061110021b150603060703060810090302161d010f0b0313021f09080d02060f070c020402071709 72
    0x59559403d14076655003203490176680541100d0941d07941070044c03040798000b010345035000d014417050342c04100086c100034259000e04020050b00d450a41800801c405d9550201505010b0044010341556420140810442d2104514001c6c88003845204a000e40076540c4140d400d03204030940c50308610032818081f0b100300d101200421600c2c0d640c00080b2054003501040306280d80080700c04241d54000364005082860790015000c1c1000d10014809181100004000d404070f6038507801e01249280920641c0d8003c1104d00d0280718031030601c1c5203e03440701034010310080382c01e07969014181018001d0040d40182141e44078111401c1c0d5440c00185441901c031040054060f8080002003402800214000d06a40000314240d0a5a854040645240402500c00e9a1000d451000002011907142131100416003030f135192a2494903014078146031a42d2000c2d610290340202007040b050481d0ba0b0340c103e0784250185031081100402d800403c00920030010040c2c035001003045854880040c1c4c000070204035905 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 375775674 1250 375774424 375774527
    0x80c0f04111b0127110105130b0a0908030c2503020d05030a1b0b0a05040f080d0603050f0c010804170f040b04050f010c080a0c02030c121606080601020a12 68
    0x1001010b030492000c680c4c103840f40c80051a0301c804a00c10151481c000e840c1810914640000140c0c0280f001c041e039445280120b400080200035079a20144070700040c05c1407030046003445c840c1180f0544a1803082c05140640b500304103c400114040c40c030740f034021360700540a201910a94200310f80c40350b000500b014040b52444000d100704151010040803ea0380290f103462198481d1036001018240240c410744500c24500c0e070002c08502c00d24018034149120a174002422451481d001d0f050980f0240e2003241e5401945e80c1407400d1b60080180d6074800c0c3d10100d030000e1105150700d80310040c01610200000c00401040c0400c1c1502004010803e81b10200c8000c55501c910bc00112107000300900001c003040c0702407003484041e0340102406080244010281c60418921101140440802c1d84c0484901c1d0702405140c00d110803001200c00103842c091800d050185400c10020b5603030300680000070264004100742516092140c070b8109a009484210a010360400c1105080030014034807035014810107 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 375776924 1250 375775674 375775691
    0x90308161214040b090f0a060b0303220501021002190f18030609151b05030c04030506102d0b0304020105160308100603020406120f0b131b09080c0f04111b01 69
    0x2d00085400d400d00c1c1ca8001415487c103130b0b0751810040c1003c190056018401880081e40c51120548881c07008001001d001607943c0c80c000c00280f40c04d9a81c440015214810000e01d194852040c0e0340407030390b04440c213000d040c8408107401252410a004201038000800b00408000c200c1d0a804c08030b646070103810b200d1034228004131070b10101d405000941002002a84880210a0140c00030b15804480e0140113400c0640c0d030348074603081180481e48500e0504001e02709010724101805690f5901e01e0000c250303200c450841e103548500d842a0300032005036120110009085a20130801c980e00c01e500704100c0030300385c1c0c12880c0160111300c09855003100041c9000d404207050780301e032003a101102c0c05681c480082102c1101e40e18014004481714802d516144c0b5003081d51916207076444c2d114840440c00018085840aa000c1c80e18010016054100f06140b01304202c16400010091020802128103042203d90030740000c0041400040c48803c07a0000708a9040303c0040001d81000401c5c144020b00c903280 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 375778174 1250 375776924 375776941
    0x1060b03090a111507031e050c070b0d0915090320190c0b031003050d030504030e12211b0d21060509040c0513090308161214040b 57
    0x400c41e2020760907445a803100c004521008686081c4034805415620320243c041004080c3d0740c03004105401003440c5400c00c003440681c403400c03406c6a038020701c0d000341840381301411540c03281410b00c0b60500680000c00c1040b240c490300d13400110000e6101c0d0511008002c44030420b4084c11030340c1010b502140c0059243d00f0701d19103461000382d403111490080d002c03440300c4900107a008501604160390300100c0103000318098181c240214007480612121034030b8185035181c45890203200300c03246410113084c1030030b120000e0740054180407030800803150103c0200c2100002842c2604135603001510701d0003141034064035010709001301603403030110700110b68036940f00e04955900c5100103049000600c3c1600464400511040308844005030348501090309035840d40013802070802901c042d0f6400e148020200103038942210003110b650b60a4a0602c451f41c0551000b4140d190001d10050725240038030b0a40074000c3c8640d482540820980100b0080c0c1400d030580c0c1c4007050070845040b540a10410013080085 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 375779424 1250 375778174 375778177
    0x3030f0c0c0b06060d0e030307020114010801090804060e060c01150906080615010809160f09050f07090515040b0d02030901060812070303020904060e0f090d030c050706090201091e0801060b 83
    0xd64000300881075540742c1c401804015070080c6140890a40c0e01c2454a286010500c008d5000741ea180d800810101d0341c0814200e2241d0060b480101d4580c546803019000030020300503a012640719003081d00e89100c0020110f06180300e107014141c031035442c00b01511600700c581160300c02504c3c242d803010800c003921500f170310703079600b030259501c004084440503000e0f4990300c100d8441d54040e20070000d845c032240b050140c1c1004070034a03410600ca002604c0c80c0a10142c8001c1c86480ea122203294105015420140c0c000b601c4500d860150074055003072707108800350307c3d40101304650080c02c02070119030391064500d1a0600a4100361549000c41d401d1813000a10044005a21941000c41660b81ca2410311a50780c01e0b0000d500000e21300f504941c8030f400009008120301e84a0f8420030510b07000c14042d00d41004c18900340b07041540410140340c9444104070707000d640402541e0352568400000034480c100c600040e0303480120780d4041014030322000c4e0042d44011072186a4401c841b4240001c1c03000e15101c00703013800035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 375780674 1250 375779424 375779447
    0x3040506010e0705180d0f050f0105161e1107081203040c0801140a0e070e04051501050a29161b080303150609040605030d05070b01080a0f120311040303030f0c 70
    0x41550848201c81760749400c80c8000082d0344104890b680302c899540d0f80c0c50170100641d040c1441655154104060300d0003140c1120480c0c055460120201c82e110f4840800c4bc07401d409200301000041304518291602c1008031340c0103032020030221990080751208141143c1d0041302d04950b081002c0800103400c00381401101e015814060310488581c4c0d6451101c00209410342c81d0300c415216068000480769400116540610f0045010301234100509034280c1603140103030701c4640100c008281c2006601942102804400d002840482c1d11001c00c5138421002e00800406122149114030f2810802c007040030000d030009018070341c11040981c8c5107201c3d9100d00080b01c00c907500742c02e5109010454640b40d0300602d0015002007001861949540c0840d15000c01c16101c08046900000e0600610005c250218010003029009280d054040c0d030300c00442a00c0b160009001b05210000e0781070460083d00417003030107000644010345566481c01c0040180c205400d41c0c17904245045070715441c0318030a28601d1360 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 375781924 1250 375780674 375780697
    0x31303110106380304080403021e031009050703050601080c01170105011407050f07140319050a020405060d150204150c0210050a020a0609050d08010e0403020d030b060c0303040506010e0705 83
    0x140500914044503a50440280c40364000d4006038103d43c024400e10107940520300440720b0f25150f905503c140a1070040e2143d040c0100d0100104840c03581c0e0b0002841c0c10729101b860004030f001449480c040c0e29101080d04001c1840c06204000304413080300140d045a0450242d0710702003121041d405400c003200702801001d000501164407424503440400080103080d2250341143c1404031036001240c01c04841d0741000800c1400d90003410300d145820007440ca000b60204038a61001800c42e03031450303501c3c110500c00034000ca131540009110f03680c9034020074800300d410040300408040701070a103500a502ca40283c040f070000c24458503d88074890b118400c3c41c00d0703024107104000d450411060350280c001240c6801144900146280011258028421160f22500c02032100c00400080a0321180058001e000b004000c1d4080001082d40058585000c20710313820001398010f0b003100892018030a007a003426051100005120030440300007901812a8401c1c4005010b07612503010459071032281940001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 375783174 1250 375781924 375781949
    0x20c01050711060304170a03090c0510120504061107030302030402090f010e0f04060b040c0504050f010201020307090e0c04121401050f090a030813121206060903021509030a08031303110106 83
    0x3250f0401500964105000350100300700640392511100440d4846010400043d49600440c0200300c1711400c401c01600040b59040d94038482c03000700405490349048800141e03078641000c03c1c14442150302c1200d50f028454a2030b0b6540c040c0d170078050041d5106071012400f8180d0329000494542e40070181d54143d03a080905400d032030301c03a002103103150309018209039441940d44007030107240c0d42c40d48107c095031407003621000d486030729100801c4003164070007411505690042041010300e907440030085c42940c00ea80d40141043d01c0300d11070591103002d81d8205060406070480d41c0005c0c4a0f1071142c0301446900c042c0207126543d40c250940c1128003090341d88141a40c448030700c03500000c0c024000c0036881107140b00c0b50740f040001501ca04281840d000700103008120540c003142e124215500405010b418242000203146242da400f00f4003111510722140da10303510109015215590034002c1ca00c05c40e802080e142e44a0400d0361060f40c0f100c0f1300307980481c082005560048a0103a040c083d0b98100c840042d90038 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 375784424 1250 375783174 375783203
    0x17030711010c0312051306060f050f06070503040e0a0905010509070b0a0e150f121b090409080714100b0f0307030f03020a08120a05070314010302041d07030f0201020c010507 76
    0x654200c0902d10040b070500c036101c003200311460141c0c41994454900d01150410118041c00c0a204a4010740c1241c00c001001140a200301e4440301d0b0340c1c41c41044242d034150345c0c0d07504504082d0b0850145400c50048900c181050244d80c1c01d01d60850f20300d03580071744001c100c60b45072880c0c42c0e5640c001611030004105020b000b007080160007030481400380036001d0306000d41003c05101d2000075602041c540d058170800800c141c007100f004031201c00d602060180440d020902521110140380c010051003622a60315020503804002c40d010a036038050740d01540c0c103102ea0a10180403601c0b880044594103505260080004580c6015440c5c10103088010b405041c0745070464032260040841c4d50b4099041d407040880e00380000d44c000b0010a2a0320003049421500d082c0559a1810340f10080e01d01c0c401c050502103c60040000c0120160441c0e5048034005070306554641c2d8030100321903142100c996401459030002c00d00040c1320752060800c0c0300741c0c02c0d2a0024401401034401d0b0040c140c0241c08a0341e4070801 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 375785674 1250 375784424 375784427
    0xf01020d08060a0b07050609210403020915060a09240c020904050f1213060f2010060b03090105180303010b0702040f0603030e0f060a0f0c080f04030803011703071101 73
    0x1072680140024081c0c03880c0c9030f1109141c000301e9210400c101d07550341c0003108004e51700c80c003400391424144a03010319409124403032030581c5d6180124000a4480c129150110b2030b00c1c840c1700e61340c045003c0c02902c40c0b51100c52045c000f6006415600c01c40c541e10880202c0c207200c8140001d05114500d020383c440c521140700540900038088802001111107102d0021821076800080207520301c0c0e500e019500b01e6441c0400003103c414400381f544040203002000801a031441d4010354030715400c0440c400c0e01145a070200310b00c05d142c074001040d281c504038070b041e50108100d0300e0382e4000c51041100700024011620340f5010403121080d446030341d6100e900188014403d050a03580100b201c20f0000340b0104402e0b051215039411134130103900413004210000a03000d444d060130380380c0e2a0040c0d0102d4035a410f0045005e070160281c8282c140160802414840000c20030a841c03054490800d107000e600303034499407070b4640a001d0340c0c000e000d501c1cbc99030041c61480c155141c0000071152000e80c00f4000b0071041048000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 375786924 1250 375785674 375785687
    0x80c10030c02121c02040e0405010b100f0c060b0a080307050609061303080a02070c0906081902130b01051b01020309060c1305090c07050d0e0f010503010e01050603040f06020a090302010e0f01020d 86
    0x14540b0f10706004c40d22800c80c0c928006880a4148001c43c45600e0405203011800c4410448009001c7c524801142c05002c2e000140c07580c03101180d04201c0103580d12454010000c000d070504099000e1460000401d00440000290485c98499000ca0b03c054807080541540d54400b144c411072650806017811000034410340303050347c1116040d103015003822420303680c810184441f43c000300121640c40004002800c410440500b81c03510410f40d100d8900c1c0c0e41e40119215440f0b06021041c210b8480c00114804e03441101122805800b80c80d1482d600540204c580d8045d500554611000c0d20407500403483c0740070508220f403d0411340084410010385014148441d84800900054a00c0c03400e02442000c550140404c58410340c903590f0f840c1e010600ca400700640082e448500c0750401c08180014070443d04c4603c105415140c04450300c40d00c940c0d4611f441d0745601c0c0380d10402003120703001007445680290840300b18400d4900c00d0f02c0ba140891080420700210542442c005801680502e000040060003900c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 375788174 1250 375786924 375786937
    0xf0501031e0501060e0108070c03080c0f0403140328081b0c030c01060602100204030f0609080918010303090b070b06040c05040803040f170c0901030602031f080c10030c0212 76
    0x2424818400c0c0500d9907402ca5200f64031180c08121000700d180c00941c7d10240c4268804500d083c000c000c00d2907510028218400201401241d2900146440c14420f0800075140110380c004518221686032040280e01c80e0028502010314a170000300300d445090503098001c000e40c0c0d80d0703600c241c0d490783da41c48a54040c140082130360009272003c2040d8506071034284010000509960004580240751590082ca0303d81c0060364136070f25a1041c801400040c007d88105043e00d80c004001040c241d225041c500d10034400c90110b164001001c500c0c0d0300c40306850108031812a4080d8980000c4a5502e6a59401512800000401c4944001c000800c0c91510707a11039011030840380340481c205034032240414070350382c8107030401e4038203010b1030104201c2d10460b4902c2d100000c9801002c0e003e0785040c04040b450000c01800001c0c01c55401000081c1c0e03005807008901d800341d08040528001e59540e021560f102c0c0801c60401d4060b016195204200754020b00030310f1503503086a030003000c000b084240407010640040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 375789424 1250 375788174 375788201
    0x1012090f080703030203090c040b0d06021e040e1806060a0306090c0306020301061d0f010f0c061803050903010f0b0f01050d0f050702010507020d03060e0402061b151005010201060f050103 82
    0x90003000800e000d40d0242001500c00d031001a568141071640c04c2ca003010940d8502c1c4141d080078840d05080e111041c070340d44200c4e809400503840d54800e00820b00a580781c407800c16000c83c030101d40000c00e0301c0c81d000750500070f91b01c285030540e130840c13500340040d102d4408680705034111003141810400295240d10003a80c20f8090089030075410b803243e07214016070b070081c0d105100040c107101e074104880d001c0550507a0045d008031051102890480c0000e003240078000c00160610141a051405010503500504582c2c10701d08006120032125290140c4250800f000c0a40a58a030040c03000c1c2101c000e118200ca084001002ca078004000d0701c00464059001c60004000c03540c07030342c54003004d625090041034014282d42d00003027024a07148100178542039803140c6200402d0704180041205459100c102c035041501907413182d95428022903a0310700358015001c0365110344900540b1902400c500c90307100f809034415a090071240f070366500049080e40c80600036400080a08401045158040c1e40032807043e0408 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 375790674 1250 375789424 375789443
    0xa080d2a0e0a08060c1611091009180f080306060d1e0b06030438010305010606020c062803090209100306060902040506030105040e0106080a0c09050c1911030d1811101209 75
    0x10800302300240c0301079441c0a00c0500c603a4050008076480c2c0280099511032080c800900407581c0c69408500c0351501c4054200b10001001c5410f94480000310359800480580c14402c0380a4003400b40c41d507240030600c01004501c3c08000b0304017850030000300e03030140d030300100380c40c0550b6a0012500c84c0e0030030075280a81c981c2400400455603440d860251070082d1300510000a1091030028064100f14a11005911070036080004076003600c444000010140c222194003542c032003055100750300500310420080c1d070001030b550400501c201441110400e5a00c1907505108065407600f20308148c0c000d80c01003e510000c148014440c0d03060507072101e10350030300c1c01c000400c1240d03071135440c03d080031004841034410b00d2145c401840146060300482e0b030001104024140344c29007210306204480983c6040304100400820300d064900420000d5a5104980c50010001a2040295a100c440e074448045905071013481d080d400714505031039559501010b6031501c8103408582e1107135800030031580c20115450305c4d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 375791924 1250 375790674 375790703
    0x105102d170102070c05030a080307080411061b0c03010e031206040b0a0b07060e070f1203020109080408100b0a030b060904050106090c030b010206090a080d2a0e0a08060c16 76
    0x2400303041c60160803400000140e0702e000d24205074002050780d4100074000d43c040e17064080050300c0c000c00c41c1c0e84056180707000805500c40f4500556800c9a51040981c094004914800349070720130450851003240560031642898650000e040c280c65110030049040d40050000c2c80c0c02d0f504003101e43c0d40c801c0008000265950031400001d00b400069004140301c9140810b10008014040c880c280f1442541d1000f040d46615140c200c0711403a489004015071403070280200c5003058000d40121250540c0490720316251500c603a0810340e1140c1c040362aa6525040c0044400c4a040c8030b0709030004d070703604801c2450042e40c1e4141402407000340a001250190340c0c0b201c00103541d05181c03052031020803d6640c00f003800201c000009140c03100240c07150034680c00004104000510035030895211090030707400415031440204c9000312810956200b4040c202050802d075100652105520b0610f080403641c09038043e44590043d50b503080201d5000c0c200c4ca5081001400107200e10010b01207076845080540b000c0103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 375793174 1250 375791924 375791939
    0x90801090305030f07030b060307030216120305072d0f050c011103070909051e0a0e120d060e010b16020a0503031c0c11120901020106030f03050a020105102d 69
    0x490242041d000100080103001c900c1c4060301000d904200e542c98103200050881340055460310002e8120802c2c5680001d40c0c0100810140180c3d20080e04800c07d003000700d84114014010346002c440c20300000340303240b643c450440003176019003a00003017171741e401d21042102420903240c9404099100d0240802806071070b41018007401429200e0b038414445a45070b09107031402520003006c9402c841e00a90500007044001c0c070201c07025040a914a104050142e10382e5001100201500001840a1f0080c41d1607581c013281c0d540000c000044002d44100b1140380d035540002d0404030280120014003000b0015440003041005030850f401f40010013801d072899a640000f1729540c1b10034080311144520a02080c0c00004c43e00c102d144200660030700024003031191000544944150303000d050405004900c08a407039200b54040000786501419402c031540090034003400541001c15014015820500080d81104600f804d0700e08503240c00070000c204410b84110318610071640e400d41c01800007980c40000700003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 375794424 1250 375793174 375793181
    0x702030d0306060e04020c0a0f061b0306080c010e100f02031c050603010605060901050702121e0a0606150807050309102306180606070606050312190906120c090801 72
    0x20030198500041040c41d1034005080c4118202c01305210318418001410714042c00f0901d615444c4d840403015920650514001000b0702c03088807070800c5050408403407640c240d01039000301c0546c1c2024003200c03200403c0d9401194062107554145400c1826040f03402403050044800006590060041e2401c10310200c00e0405070704081c130150b10310a52241c082c85110308080c40f4080c0501815035541e0702d0300b10001e0005c0d040b4480e00000038001c0409201c4004001014007415452a6452034000b10100d66060040d80c1c55810003010360700e00349441c1000070349098441c6644101c92003900e420081c0e560301ca40507100343e0030040414406004144c4042815440ca1040d22550441c06840f0802d4991085441e50f55080040c000350080d040c1d8042e44c1960f40c281340404d94480701c111400b030340d18492450200c0181c0301075071000b5014481c40c0e80420030f564051000d082a204201021030300341550741c030200c0c0c6c03460711445024081040e07950400c241e076040782c004650405003801e110b60070315a070ba101c06084 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 375795674 1250 375794424 375794443
    0x240702061c36030203180f06070605060109090618050c130e18030c031911030d0902090a0b010c061802150d0509030315010e010903080705071514071205070203 70
    0x50603001030300704022210001c030490302c0b8101c0d03a025541003582e401950b688540903010600c19119044c164582da610002440312110241807240c03181400d181c404007522081c1c803454003045680001064807034135032081c9000c88020003070714603074410103000081c01000050098a44480204a032083e00e0307520312801c100400324074200c00903900c0c29030a0b440702c44816500c0d07203034160010403400200003400010b0340c1003180c1024000d40c21150010b41900c03244090000350f01c01e030102142a00075806c5e982e0081500900035500c40e002d0f5519015908200c4071240721103408100c00b00c2030700c40400c0c2258401300f10451606058001034800e500002d501400c42e60f10b84080401c0050010303d092201d002e01c0790408205002503080d41441c140b042202c421040209040007041c0a100c5c00580c401c600b4036008581007802e0303a0f6183c0f21424041e48036003e0340580761088080002490810380f01303110070341c0f80300040c0d0343c0d0728107007405540c50f514241141c0401c9020008148107107000340ea01407243d03822 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 375796924 1250 375795674 375795701
    0xb09010905032a03151506120108060105100507031b020402041214160305060141030c01180e060d1406041106040b0a08130501020a030b240702061c 65
    0x1604160443c840714460414800301c0c025040003040520300c09410501c03a030001b902a00265444a003000410b20070700a00007040755102e00300000003421440440c2d0581600c006640d1618044011001030301c4502c1040c1d00100040c1d000700c801801c0c0b580e48d0f903812921034070042001d0f180c16a6901c1c42038802605440c00c0d2800012003136100088501045000071003036094001c40822841d45d12425181c1c9170500ca030404100c2d00c4003807403801c4650022480c0300e19008401c0180b80300c82041c041070880c10410b0b041c5000740b1984140c503a0701d6002d5004030500441c80703074003000c401b41010190314040c40e0180415402040e54524480081d07107469030040c9004201c001400903240070b040c02e03401030944100710b41c090a03080105202072120f01088401c05001d90801030840d40700d01c0c002103001021160050300b036500c08501038607020742c16007007a0340b103480c00c8031200070040349041690510405009031841e102d4040000100608100c0064840d80201d82804035001300d4015010007920301d049a4600b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 375798174 1250 375796924 375796963
    0x709150306090e120703050304050c09010b0a180503030f070302010b061206090a0c14070201020a0c23041503122d030606020c0d02041a0d06060602071e0b0901090503 73
    0x801a0614881c00d1103c802c18001022001c0d5144880b0b90b0a100d4a0005000c005c1c0000018040c0881006403504501019001000da90707981c04415001d40c2003000000300040d54030540508070216400c11030241d60b00100a10314000d54200c0303c00b015440f07131b14100e0a43d500d0b000c0c1d08200c2d0b6540c5000d003825a40c1c0d220042854030300b800400500040081c09a00c2551900c5080c550340c1d503001660946014401c0c0041da681c031224001030303191400d84000203100710305e8260003081421070b01c03a21003411100f190707518440440410800050300c28000e03503c441242c2c1c0395010004a11380034038041d0303454204d051545500c81c4031041700258880c40380940e40c2101404000000440c0d1500c1000c000f840940701601c00d01c200c3c103002500307560008a001e889980c403078000d1907044000d100b10b50410080101074914440440c94170a0242031030f8421880540203000e030006190f0001c0303804c0101e070020105501101070030509042182d400083c005410410302c04404140c0b51020080400e03030040d00361441 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 375799424 1250 375798174 375798179
    0x1101030e150604090b01240c0b06060310051e0307050f180a110309011b090605090405040503191d0102030a0807081306020d0506150f091e030304060804050c01020105010e0f0709150306 81
    0x65840610300010f1f901081000785802001c200020720180d0400340456506c0d5490f290079410310020034064025952125180c1000070400c101c0d06d0001055807800c4e0107aa448980c0d0741c003000180e04035015107a030000b5001c16003c080500c01000c80c1e6001c0c203c2e400000306100307503440101591300300b2142e84280361b41d11928030689c10b640103406041b4648070700d040b030036140c28050b004101d4003030041c800e402607440e0000f1408200c0c00380191500951441f90440b000402c0510080c9440182a04011005005240c222103544080100c88201c1c3d8907441e501c7d02c0361100d442c00ca91034107009060b184280403030314010000030782074001841500403c6101107130b01d0600404000510024400390698050100401c01c104800b40c0c0c242c030071741c0500b10f91084502d00910360709032600c1c4a0590306c1e80e050100140202e0344c1c0b500070368040e019502640c00c0719603d07a403617001642295028050100700c00002c8002450803e00c07003841940c40481c61915110045c1e0301c0c100b00000101481059000c00c0e00c46c03506 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 375800674 1250 375799424 375799469
    0xf050414060a0507090504020703030e16030c0f060818070e010902070b090c0a14041416080108030901051e07060603050102041401020705280f030305071101030e150604090b01 77
    0x42e070010168801040746042c0f4441c09003803140c86202d05401590041000018107010b684002106144071043c5c9568482120303085444c02101d010484190103003000104a0140001c0300c8825141240c42d0490117484043c5404680701036032122101500c50941c001c100c0307410013007905000700083d102c096124070503032408a42042c4010081103540d0303c9030010074080e5403184002c1084440b00c2200c200000e44550104000d400070880d05401420103006005680814500c500c0d0101c00542c0e40d8803460762201e0000751a031107455041c40c0040c406200d0b08400302da69500c0e03825400c1003848210320b00490340d5240b1090320b400b940152001c1e5030124041140e01250401e582440400740f0180540c02c1c1841c0000d600884412003406a03100005107410080a006903032030080c004807101c02120550301e180041590f8000b55048514070050341d041c910f154042d0180600e01e20208000c2c0280e045842948010b0003070082401d9841364031180b2400106903240b1805001e0405101965030b038450100c50f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 375801924 1250 375800674 375800683
    0x315020a0f0206190c12020f12010b0f030105090709080d0c020102061506070809010e0a14040b0607050a0204050601210b090c040609090e03040f060c0b15010917010f050414 76
    0x8840554000ca0f082000d140410f0b0b030498018900385134000360420541c00d08490301c03152480400c0d1101c0c0b0000300d03009140e0581c400340c40121220750b110002a0389540409104ac0182e086000c90101c061005000c90b15100f4034039a4031071550f107401803500c2ea5800d40189410f52845803030303003c00e00806044003903581c1804410f40c005281018503013040c01c200081207240c42207200140180c4800314564465138802c824849401130001c25844000342c480c03003c5e01e035084034454007503c00c03442c0c02c007605002c2c1841c030181d50310b25400030040e207480d0a1903000c1c400070b0100141414100540d01510b4140d0303e0780c079201c02c040d02d1b404d0880007801c481210180022a4009000580000401c1c441001041e0340102d218065402d590400f0030040c0404510300e145010f035400c003007640c07440014017041613a8040c100294443c0900d01924031a15503116606010581e07a00e80703400611076000c103000030300c0d0700b07207003c00d8841c078540002030f842440f010520200c070000d541c02c0b581180006c0c604c00c4040c40420 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 375803174 1250 375801924 375801947
    0x620190905030c0d0c0f0e070201051b0a08150402030a140109090809100507051e0d0903050d0302220f030212070e040f020d1b1a0301050a06180315020a 67
    0xd188411509080020b0340d10f01218122521074a03181d5050f000f0030001e4403140000b011910640398840742c866040d03400042c002c0301c5e08001517203440000740401c440d03100c1c07003202007030190030581c035081c02c01d1007c4959002c01031440038040b10340741ca110f80e6900c1d2440198411107041100140444002d03096200e9100103130f100b030f01464204400c1d40701280c0c0c40d4044459844c021240100c00040c850820f5655011345900644036000750256100c0c1820344201c8000d03844090740c15100c107400c0320241603c40c04031a0101800702da00c480381000c40c860180e40200320104801c0c02108070307014809040c2c80320b07003a250232650070410484e00410071414901c8410842844e01d40c050700394642011904849443e0003070014080e4140c2e0074a04080d51540b0420441482d003040c1ca24450103101d1690040e600c049200303400c450f400d4199854200003680e801c0d40e05a800007881703280c1091405a0817548103070701c0c1001c03602c0f1403181d010020000780d2240c2c1080e04200e02d075001503140d201740e030b00140c1045241d4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 375804424 1250 375803174 375803177
    0xb10020d140414091b0d060303030501120308010b0d091502070b130b070302070213050a0e0606010201110405190e090a020a050d02010c0201120e0111091906050d09062019 75
    0x10300043c02050b03005a19a06070207070641e40f001300390356440c0d110304014240400d20965000c0c000340c020945112030300400143d82c005e440c1072245036618400820f140302c41c46006000a040d000043c0a015421002044070521040c40802e80c1540c03034a403190310320a150b00138902d055000480d40100903204c20242d92001110b14850f060031680d407205c0300c285000420700d004141d8005045011036035000d048402d410111001001645050311140c40100700e4060562030b1440b403013002900d590720500510341180c8060ba211420140b1300824010b0800550004044ca0801034202003059247c5400072803240322031000904ca07410035801400000d4500360000c2d40103014603065080943d82040080101e0755080c40c0c822100e9110390003040c0202030106901090f0b50a01c41032404402d510406041440b8080303481030741020f00196940c0c20a400c610030280415802c0c000d0b03000740407440c1d0042c41100e000d15000308003180d042e01031903101c0c9074100b8020500d1601081b0300642c400c0c09400b164145019 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 375805674 1250 375804424 375804427
    0x3110402070c1a041d0f06040203060a030212071d07092405070606030b0a09021318141203010e0106110105220c0b030a0b01021506061c0b10020d14 65
    0x494484003030b01030300c9010750540402a4541c030000c014810f011030700103250300c0e8907032120740342c480321143e6020205032012808032407403401081c550b15243c401c0303a008540080070141207600d184c0c00d00c0700304802d0f500c101055005007800060304d02d0319104007001519003010140082d15140c10007414000352504140ca40043c412038180b144401846554071810150401607159440c03031900d940a0f055581000307244544030700520406881c5a0020003041e80700b102c0e5241e480c0125604401280c88640c0d03151b29500390a141c10020a2103000c200703404801074410388901005086410305280d0003070744900d401c03a85140041003050752103a00c09501650301e00c000d10441c03d0141a020a2903000d2001b00c940c01400340d001010003841d403d4003001000c03c510713a2903c03417800b00c842100800c0310781005409400740c540003400031441c003c610f07031040707100618440c01c0440c054031151319010100e0102031540d60719450f00509640b4440d4103a2006e489900a102101c1000c0b8002c01981045c201c6140300e110 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 375806924 1250 375805674 375805687
    0x905010507030509030c10020f01270305030403170f010f09021e03060f090f06040e0d02061303030902120d0201060803090a0b0c03040f061806081905060f1903110402 73
    0x2031120440e8019605460050745445024002a05105100e81e02a501c014106020400300381c02054041c6440741c460700821001c0e401548851fa040460100711300590a001603107800680928003540d0401d000b86070604180800210707800803040280e0b0304402501e0175070010003501160090000c0940719010b806e40c03d007840074038110f81140c2d6005900c1c060501c04000507101d5180d4038195046940d00030300f58015400e01040e02603940e4016a085800f8034204030491041007000580c147e4042c000b035005100f5565400b80300704603400c4004c0120308050f120b242c5000566a004024240d984111020340100c20380d0b00700c041d084078140c0e401a48242c0062144882d180e0b00c0e400302404070b078419448544d6034000c0c100c0d00e5065105680240000300031b45000440d40d1a40027041c801c0f1000c218001c2006e50f0344501d0140c40300ba10450300b031036040310109070304141c81c0b00c150006904514058400802646494001260300c0707a074100d07010510103c107400300207100c070200b0050861a02628114034064 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 375808174 1250 375806924 375806927
    0x161a0a0207170910031d07060503091605090a020906120705030f06030115050d02060d1b02010e01060308030114030c03011803120501050604030209100e042004110417030c010f0501080d090501 84
    0x81c24a24030b205041d40c6109000350810752010760030030101003c4c103850807e0b0700d03004040d000360015103607002644607010000400c0321601e0384220036550700500210083c0d441c081070f0070180d0f02440c961078011000340195040c20303405021841c002c40c2151922500d0b487c000c48414400f940051845200ba8103010811464030390812110f0103407070058402600c10f6100e030008c5681403069010810440b882c00f5134140c00c040200b05801c8000415034028400070680003100d509842a074000035015902c02c01c010860b02103034043c4441541380c042e09031800200070300006400c603500c0c440c1c04038403d001c40300341c40105540420524414034009208000c9035040c523000c19070074051800001c0c040c003103501c003041c1001c0780310752035200406600404c03008900c0e01c0d1528851505501c40c1c8a0044010075150880c0391519010b1400c0d80c1d000880301604003481d001207007805158000300034005000c10450741c80d4403102030240d052582e240c49004201c0d54940103410f46032600c80d1800c0c10801115020034031103613 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 375809424 1250 375808174 375808189
    0x109030209060f010c0c080d0801090903020c0402090d0b0c04090b060f04031101050c060c1c0e060a1d01090c14060a02100c09120302010510120305161a0a02071709 72
    0x1482c01e6500784602022900181d40b07034648108050440505100005080880012000041c21280d030340c84405136660001e00e41514454100280560010301c074000aa0801e503000c2c0180b100c006100e40c040c6000c5496038040030400b0345881e540848005020b115120680c0921078003000280da55a10b05192016105194051408000c00d48440104581c0c00340c0e110790300fa80c101d003002402f50307140b600304805d2034603040d480501c0300620b146e020364010a865440e0b2041c00103121142e00504180d03599000b40d0001040c040c0c07040c0000d00d00c00c080106000c6401d1107403100161003450b04403440c0f42051800c00c1d209040c02403540c400c072010000300181550120300042c182c2c10307109000c0760600c00e0701d800345d8000096402964410414110711020b0503415000300c0d004910380002d906409484600030340c44402c07a4100940420010854000042c4500714540c0307004e80246512504115603e07441d9800c0d400517242480565008140c01051040c1c0014205c0350702d2031008020700d00021100814100d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 375810674 1250 375809424 375809431
    0xa060b0403080f0a140a030902182e0906060306080c060403020303160c0902030a050a1a150d0e061915060c081b06160905090103020102070b1b07030309030b060109030209 75
    0x3c804003c00d00d200e4060003a0300701c400c1d1521205019488075a80c50000b8000c00c40000305070300ca070000003c0203500e10070f460f410501513400c90700d1922406c500e1800d80c5000000e168082c84444400f81d100180c04075480c403a540140006070303008554140703840e2038549441c2e43c2d00040352280700d08020410042e83c00000702c0310f0b014a411810301d04864203042400c0650126440411103c1c00041000300f2110241d000901c680e1400804100f0030707408402c2c640c1c072504201c00c02c580141d038611041d01548035110140581803102c200128419510804560510360240c62208c040c0c0412103201c3c5264895024042200c6103100c4044111450448010100f034103011000e01015000664400b1a20340030442219600081007200d6090410003403090013301c2d202e0110000038070660006c03c00b490040300070f90490360160700401900713040003441c07280381d03002c030f0402a010354a00304000b401180a1050b44015802926010b0b0450319500348020901c800500c06410080d00710010300041c1d0750041034640 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 375811924 1250 375810674 375810697
    0xc2c070e09040515070504051e060a110106080106170f0c0907140706050c13050301050c0304020907110a060614030138040509060103110126130b0f0a060b040308 71
    0x10541c0721814a2070404a002c3c0a030400c81074031800304680f486d0410014400c498041d1110070100c1c007980508585500880071740c585c000001c00008a820388145031042c00d8003030500000070710320b580d40609070841c3c0070b0360302c5103819021a44c0c6003504400c0c24000b0749103e2004a0240a181c4903240003e0b4103030300b005009a080c01034062041e00c07404400300c1524901e50f4011010041810000700002c3c868004001d402d000f50a0014081006d0a040c0201402450329242c07460554650b6400c01c02000e100074902010414626080401e00030100b04070071034503001c0c04000a1140c188a101040e010080d85202d0180c0e05049071056080d190b0b105090b041c48048000c002d1003520313112416102c0104540c1141d21505010030b00c04002d8011807200d040300e03c0b404072800380f18400e00043d515418803c4201001900140c0801804247d45071303443d610100111003070154003226690f81c0b0001d603040d10140f07500d81441080000c030321110310400025101c0c4032815030420340307541d55910603482200c01001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 375813174 1250 375811924 375811939
    0x31b07060e1b040e03040302060706020c031c0c030b09090316060b0a18060909020d111309060203060a062f01022a0606060f0a050901020a0c2c070e 65
    0x42802034075840002040142001d807040280c841101200d4400c0c070344081440360f403a0400004100e88000200e504403940680010308061007500c8143c020740154010404a0008014005e40070220000020340780c0381c02c9500182c0142151002421130b01c54440c0140142c00c0c050500c020710800005032400004003c1ca01c808042441c9084000740111688407508071b17104d08400308516440144100203000c41540401c88142d0303c01d080c409664400b0300203034004150b00c50b0784020800900103886500e002401c0300c902a40c1240c1405c007290800f4800780c41081e400300c24000c6529000d403d0200070001c82c500f00f02510f449110850400340304d040c2161a5099003403920007004029015250124907618500421000c2002582c0f4100c42d10140100b582c0100307800140240380c00390a40382d10f48a0044d000d428400000c405446a51083c000e803815841500c15202c001807000740305001030b10200301d48441e005144c1e01d40a00d101c05c9580003071010700c1e42800b0440c41e5a0b1000d00004590412500070703 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 375814424 1250 375813174 375813187
    0x11a030c04141908101a0d081605070e040b090604050316020102070b04121b180b0f04050c0415080c2a03030f060f030c13270c080c06031b 61
    0x43d40e00e07090744041403156000140010341000d002c55024170420740070300f003031103401104819100c00050000319a40d00224544000d004681c07034001911145030203105403030844010381c480034a0692640c4c0314250411b90b050800c01003140da1901c2540203c120b0700200281d0405030350f656180c2c01a103490714200c0040701d00e19400d5a2007000f22400400410b104039583d00d4a880c03690b41c004c0000c000c1910400c207840a9030002a140b040e03031030101c031114a0321a5030102558262405003446100b800d03403140003e241e500181c1d951384a624011712441981c90341e130301e280c8004010314080c200d0b0a20148100142007010302c0100350125404505000203001c001c044c24208641101600c9000803860310001c801c01c030681c141640401c0c011441200d85500c2d1110800c00c1690350801406170540240c00429003408003030140d00b0060b4500c0040e1302c410902400d104200c0e078503036040d1005560304010b604c4100807840c1d0a01803803842c000140c48044c510f01e0036130211644039140c840406040c03600080c2d070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 375815674 1250 375814424 375814429
    0x28090e0a02091c020a15090504050c0c010f0f050105030c1f270306050f04150b03010b27010909021e040b0607200103200c071d011a030c0414 62
    0x440d503070b030701008000303a01241101400840001010104902a00401a000c00c900c00300c0c032112045100150307200400c141c10308043c04080c0c0805001c506048505000c5020f5005d428000e20068101c00f40300050610100380d0310405481c4107030302c0380740640c2080c11004401e8550252407020301045951040000950b00c408071000148040d080310112001d40008541250303081d440d500302d9015180c284010b440d1000c0c4140c101c0015103005101e080702400c0400c480764503400c00142c030040107000089004400c000702c5e40d02c900c5000184907503c1148024080e02404281c15405800b040000f081921525030110b92100500c1c41040b0f8041d8040000c00b000c2d1b65a03402c52a4483c502038000c0740c03079110f103151150000701141040c0441c0c90440b00e04149a5101e031003108010200314a0800421032080c801184ca540503101d091403602403020040340910301e1004400084410512000c00d40d890702c03c010700c11a100b8590176001d0702c030401c20f106603a4000810340382902d1000036400c500c201042700 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 375816924 1250 375815674 375815677
    0x141e0a030803010b071407060509040c140a0210180f030804060b06040f1d0411040b180c0a0f090501082202090901020c010f181707080c010228090e0a02 67
    0x401041d41c180080080b80c503010000c09040f0103403148081c44c5100c0707105d46916403144200d000351000079100344000007091406400a400030072460900e071811048071481100030f80d121640c4400507074026103250303480d00c109128203c4003811440d4141c2c0340701c08a60720b0520884603c9000350170010000b011a051040ca54080c600054002304031a68880c3c2c0d85d290340b0a410918407031001288102403e032818404c0c050642c0344110b600c040440d03002c18405080000034001c0310a91500950f4124a0b00780e6502d003003100c40c2c001d10701c442c01d0036111210064010240e000c0301400070704210b468542004070340d030082c0d901d07034201c400d000170800a002c00030030b0414002410b99001c0c0d4003511003024015405019402003905400103802440544a04901d0b803040c0d40c014604625401408019a0041344607040b5400100403000c407141d150200c1d03a100c02d20141c002000000103130750b0015540c09141103811204480380c00c070348038500c0400d400381806001071005100e00d050796942c032400104160798560 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 375818174 1250 375816924 375816929
    0x12051b0c070807060215150f040e0a06050c28050a08130609030c0c09060803070803060d050d0806090615120a0b04060303020312090105010f27180b01141e0a 69
    0x2c0844440b80d40d24000255140c10401c1d25200446d515008140413003081c1c0050110100040c00e1144031448280501c40206410022020703e401211551000074805003c0e0f9400b40b40503101e01a00d4541c181d0503241101310740c00742c03040c445500c10135480b0b816800509503001c10032941001a0240e5808082c0300e41b4000c3d0000090505160017151410180c010290200181c010310b00c2110040e140d6681030116100c0d0300070108550310501107003000440e404019a40198080d003900901c1e0015900c480c41c229002c0040004110780d00d003045140e00f00b45800350340c8100704490301200b03220303401120340b0107120ba001c40022038148580010351841881d0820240901d000e8400c110403075490900a40341e80100c00c3c0c9000c0841118081203500d481402054140d4251200c090302081c030703044139980d0b000c07010201300e11181c00040845580c030480d4446c145000c14001c0340c1c0e00c00710741103140104c510201604280108076010360005d8060301ca60000703400301c03241480044140100400011406101039 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 375819424 1250 375818174 375818189
    0x319020d112b11010305010f12050a080412030806060313060c0225090b030c010f05180a030809040b0a060e06070f060606052d0d020d0e07140112051b0c07 68
    0x100d08501c2d04001d0080d0703091440e020f140040500b510420044080d141c0a22400801d0802c65206016142009808a0085210700c1c01c0352054003059440c3c07811600035a0100340341620040c100024150030040e01340e0f005d84100c0da11807840c40e0241d11a500410045006000c890750781d103004003014001c0001d0b51344402c440b54841c44000c4214050880101140100308401c0d0600a59600740d0030005000500000142c4902c161030700140000c03520350300600145640240843e0040000d5110b403c1c094010b1402a4040c1d030b6034291384ca0510042d034210800d810f0082c0014481080714903071028000502100881d03681e0f60702c10a43c1020454000b5100d0050411440c00e600000d01503006401071110700d107210035078039252030722001c00c2c0240e0521b00c00414502034100000071070135419a0080000f4034202c01c001078001c0e00c03003441764540361031f0f608100341041038104000300660300b00070284071341c2031200350501241c503240700900c102c3c0c50000c0c40c19010441c0846c132010b80c24800d1081501905e01c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 375820674 1250 375819424 375819469
    0x40f0b07031209050c040e060609220f030801230901090e1015060906050a121104090f05061504060c120507021c0b010b0306010c020f12031303020319020d11 69
    0x3031303061044e12080706515540c421803401c01c44100c20b407000f044040c81518000d250701d4030381d40c40c3c07180c0780d04030707000e18501036240706542d503840000942084000442900a640c0d0300c2d46581000341059104c0d9811403640e802c03103450361610500385da880391110705444c03820602184403001d00904502c0d200d2900444a01503007490a03240003100401410002c607845175039806440d40e61b900065840f8822001c3d1f100004200e002c20755040e011703e400c5010480607070300307a2600d0301d9624000c41003100c15400c0000d001c5a215814010706152075405040c07400d5401031b04a15080c68890003800724000420000d00c2107034081d0502482034055025200c0c0b07a500030303042262059146140c003c003400360540484208803003000124540700b46101b40da11620040e150950145955020400b11012500c5566840365400c406032680c20400d02c090710a070310750843d40003500c605500c101170415120a001c600821624803501c00540d0314150000c1420307401c0a80141c10301c00a03404500390310060070382c1c83e00103035030b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 375821924 1250 375820674 375820691
    0x1104060b1605010605040203070807030506130507110c0604060903020108041a040c0e090307030c23120c1905060106110309060a05091819020f0405040e01060f0902040f0b070312 78
    0x24a00d24000072600c254001c11400e80c50b5010003040317020541c0d11500141c02d82002900c52406a44070980000d070050820a035641d9035104036003540c40450304c0c940096081682803120704020005c4101854040341c403a401c007404c00074000c20300c4980d444003904100d8075201140c14000780340f01103400048003407100c1101e46010305020182d21a548510500511604002401c86a01006460900754103540301b100b120280d48076800890a031200750450213048035511080385070200040ea980b190500c107200e40f1a14448015810110058003089c1480c2e400555140090340210301e05054a801d42049010444080c20161641c00740080f2660031030700025011842c260031201820365018220391101144419404003001c00c3e4003551103500b9000313848041c003450001030300503050400707038040841d0400d9621000201030b61700c502c0188120781d646034018880c0c0700d19041c840c406850015005d6140c07600c1c0c440d1182c2d0100701c0c1e01c102d4030101004a0300d0b00815204403910000810480000c1c800c0aa = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 375823174 1250 375821924 375821947
    0x18031203020a080718030b06040b091807080609030f070503160b01090609020c07150c0609080403060516020a12030b04091a130f230a0303060f051c1104060b 69
    0x18402c9050300c2c0490311a400240c0150b03c58044120f0710803504210200c01ca1075903588a042d50005401903512544070080742c280f030303200da5911604c2100314601c442455140745000c5030405415401c0342030703590020b20810000c00d4002003191040b61580365080d07510305060500c1821800740261000c648041c21124005002100c0d4115050b124560420802d0765038500303e0004900c1100c0c1c1030b42c9903400c025820000710400740004202c1501605195040c0010f030f603a500c1c110f481d10101116440f83c042400d000740500c0c1c4c4107144e0b10800d90035502e003a0600458010307581e013405040040104010040580c40f0f01e1080c3c11204640201820a00c0300c500c0c6890064280c00090312101003801c40440001c075022010000604000d8111109038020065911004845c9032410f07184002c14802480c007104080081000d50009800f030342e00000c0302c5003000c2104460329000e611041c8281071070b504640341c002e209114068170640c40150024007100f0140801c01921055022840d1804c0100310701e014131 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 375824424 1250 375823174 375823177
    0x30b091522020c01050703090308060f0109080a080c010b060901021b06190c030e0108060a050d0c03020307080a030e0a030b06040e100203090d080105090103110d0f080d0f140609071803120302 84
    0x5800400070711046d135a07072a089088905c10b40d0042d000890703e0002c1800d40c00c22005210101d0018074002d019561117019803450b201c02c08030212490798000075260000002807180308080182110890318010b81040002d695140e00882150f600300d01c0d80301e4a070f2581c1c882007100c0d140d08410000411449100c00003403d054240d00050b408143c80d209400250f42c030500c00e0a118102c01008014420705100602c08034180882084409441003034000c0b0140e5420040c0710002c1c000c50340241011441445c004100a5144c010180110304e000401d06c00504451001c0d13601c882c0540300000e240e071030040401d00d40501d8a201e41440c9100000b804503408010a03040603444c050b84413003c0031391703a90050115110003448081c102c2c8041200003403462501070707070321030700d03a070140d0181c0d000c81045031507414056200c0031400d4455039440241c064100d0450081258000000c145525945400000705003003120040ca20783c1088070310700b200458034808445080155400408000d241d00030b01002400a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 375825674 1250 375824424 375824437
    0x1d03010f06180510090e0f0703080301050a1502030708030705130b0d0c11120906040e070315150c11031501080114280b040b0603090c090106030b09152202 68
    0x140401c012041c482c49945010b4503014409001c0d080801038030303060b105001440e101010302c80a01034508421403c04003002608080c40c001e00403559654940001c0000c0c044507131b480444101c18a40e01104d03029004020380d420300b90401000c6590b6034036140c00315094413855089542c41c0d159400003140301031559000d0910304500f55230401c19102c2400d0240e03510085501044455030044201c1100d0a45110190603100c0010f00014207240e01c07120f03131030112001104d030703100000d03036a0b0a508040303030388142264000c24104003082942100e03220700808076042e154002d0450461181ca03880320351010070103e801e40c8400d02e809503081d615048914042d040c4030390100440d01c00c50740070450100c0003800e00d02d4030307501540201c580490b44c0e14500c0701612841018a9015544000c50546600c440004500ca40031200c00b5116003003660301041407800e81a040041058a0420380c0c42d411388a000340300d50001d4aa80880100c1900301d00099a04220916a2004210505401100c0703070079a03000380a1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 375826924 1250 375825674 375825689
    0xc0c15090516050904110423061003020301080c12160b130e09071a040e01030f12020115051504080a0b07080610090306021b0318010314090d1d03010f06 67
    0x90401500245100d011400d0041a0f40131024001080004100307600c241c1d8900006000844c1c42c0b0001c004200e4a40b8010004441200700c12003001414a04030786114440e40f40c9017008c41c10b40d414110351640d01d140150109000e82c44500c9201040700d01044041c04128000456808040e00c40b03403d468070f50443c807841e00005402e48004100d05042c108028494505500100350651900380507420303401501305602c880301c07803c01c00440c1d0b0b1609454a18069806070550b000d5004452038880724040039500c81c0811a413509070a13004c41002c015038070044600441342c3c405c0c10452408103004074480e41d0300c0740040340b1030300001008101f02c2106042c450241c0740c43d14107144d038582041c480884082d80c19100061684942800003481d41c0d4054250703014105582d46d81089400b800c5491a0701007480071000340b058031010021503034540150314039140c46124003901414a42e14440e80c0e00c1001e81907400380041b40c03009503c00030710140315810002c0020028000d0150358200c1c007001384038a025464 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 375828174 1250 375826924 375826933
    0x70303060806091f09050d0c03090e0f0906070f140d1107060e0d1b061a0307060302250c050411120411150304030c140a0b090705090105010908030702040c0c150905 72
    0x4444c0c1a49104d0894541d13003000141980302c041c10380c06c40e290100d841045061200603800400c2c01d062140740c086c405c40c4000c03012205802c10101c103071301c0c100b0010004030801028000c181002e03039111440c000380700705003820f103600e40e5540070340c050107444150341c85c40e030101c800324070310003400303510f403c03820100c0880c10907210442040641122074524849201d0501d145102100001420390f07401003000f2054452455241d01041001904000543e0f00000020790007140644103080c031036034006014804a0b803038040d460596134625203030b08000d00c91180700340e81d551521001d403d1184100c0d416050104091109840c05241c01403071040345500f45030240c4c445181e0381301e0001c00a01243d0085405448103615800c1c5a40d0f080700c4581305800f4200c01d4008d034000400058210110a030140d00312002410a41d82094103004a120050b800705040000c441d50405c400d09000c411210aa901510081703140c0c02103942c203031480004000002c20640742600f51108403034540c0d00519400788600140c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 375829424 1250 375828174 375828223
    0x1030204210309060c0b0103110f03030a030e061515070606052701061b0f11040c030e0c06030c03010303050906040506040308071101110709180b0403170f0f01060507030306080609 79
    0x44a05c440c901c82c00400380802840144003140c208000385001c40001061195541e00d040d0210b41180c1160082202198840c415050124800e000315a440040400689446503d01c00014011200304440752038060b00014131105001041d04940e002d000f000d000f12a440050100742c94104a000d04248a11011b0030000b04600340310b0303503503280005e04811401020180303a4a4602d20078001d9001154442049445101a0b0721940a5003031103202640300014403665400300f1609150380c0e000154800d003030800801140b0049403050740d0550790540ba10075200c05611300414083d201d250020350b40040089800010040071400412a1030701c10301082c50070b48602001500c800700030030403404060f0083c0c8003c2c081e07026140d200c2001000e03040301c000c1301040300743c840209044090f50107600098040c0c240c16404801500d90f2600019907824028261a001000940852060141b44100100010603c0c2814820340142026181010a48115040100030142c2c6e42036080e55404280c2030180d100c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 375830674 1250 375829424 375829427
    0xa031406160207060f050931050f07021e0c090f040302010e0708070512030403060e030c06011502030a08040515010e0106090801110711150a08010302211b0103020421030906 76
    0x143d000c454060302c0780402c500000b407081c0c07103e03040605090341140040305149600f240c015600d0310506a40034a4200b590034a03141c1e003080e500010309070305007001c050043c040303600e0380040e03491403110100c0100e0340314254034000b03103050131003807103507558030034030f9141071010085005588a0143c0c1c4031740c008000c072201090000b5205c140320b22580c00d050300a0380e401c01c000d080c081d13500301e103118a084c10b40745001e86035a1610111014011035070303100d500100310410f00703440802c103070742c0908800200b0b41a4a0304e0000025034038841c0d5040101013184490208040007020806144910508001c1c41b41c1980c40d6190360300099024030814000484155000030b5004040c821005e45011b80d55045141040d40e469000c0500c000c03250894109000080d542040c41c9104003604081c0300b01d9850404652550040191100e491090341000e450342d2031213080c030070500041036008488454410f0700102d03203890050f4000c0c00346510003400741c00c1840c1204409a031080401d65020b209403201007003551a901b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 375831924 1250 375830674 375830683
    0x10e150913170d060906050307060503240d060e10150605040e070c120507261608090a030c2c071407021c0308180a030309020a0314061602 61
    0x9981c0484240301481c40c0200d56940e411007490040e64107001d00d80340301c2071078100440d00d03960703c101c4110343e070b40d0014000307407a00b4826039000b00701600e8490700390704180005d20f50404040b80c1314a0f0390f40c0c5a8040ba40c203925406030300102e03190401020000c0e00c1c0e900100c00e0b240e0075118902c0d90301c60301d040c05031150365010944c44004d031446580d0b200c3c00d2504103e816031040a0203031800c0113100003050900d0000e80b41440c2400c4941c3c06940d6940c598005185c4002191043e09695443c03a21811041a000907100151524800d0407403000c82c001441d1b080000d0148039000e2126040380003802c012060241c10010881210100c504a070702421145503440401072030704029040408070705e804140210f101e050f00c02805408031040b18903082141d070005942c040c51443c21006100c01080300e41c2450b4110051303552181c02000500142441805081d8683c3d5007420020306250342d40e00c041e410354556600a902440c1c0c020040c907003d144020300180e5a00d0300700c5851000c051340202e0702036514401714 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 375833174 1250 375831924 375831931
    0x2202101805031c081e181606120902010c0206030a0905100b01081f050402040f0810141f0906080604021c05120f0721110c030c0405100905010e1509 65
    0x390240400700000b40450328004060f003002e0943d917901e05940303085590b119916014070507080c01c40b680c41100208080c01c10034180040c5401182c0e541301000324681042088d001a82c1103040003425011038401a0790703041e64068041d4001e4004070030040701c0c4a203a44400120790049048922400813040100199042c48102500007500380d00801c00004480d4554082c01c005144025000e5480e200404c04a0b0490b5010307101c200c50010082058940620912811800e03c0806002c012030701700048000d0200a4050020741d042c03090814408042041b031080a407042a505001d66582c03a580c0c0303503944105450591180d0720304803445d5521803800c80720004440c2e020020700342c0c544894030301851703e82100d1820300003801c042140d10001015002c24800510001c8000e1a074050b003203030010015641e14910680d154810b03000102550f400041c1c005110b038007105e01003015503da060340c3c1d0340e400140d4040c0d10620300b40300010807460803071019507100b60410420421022408000c2009500d0242c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 375834424 1250 375833174 375833203
    0x203041403032701050d0212011403030307140d0e010204120c0b0309190609050a0c030309061404090f0621021801061d0109080703050606150909220210180503 70
    0x101d1840512207206050480143c0c0504000303060502100c40c10b4140d03481094402148840b440061010654011030340c040c8500580c000c2d8194600703084050440b42041e6580f0303a86d80404541e040d4031031100d4000f40380700c0c01c1d40c80096464694441d40507080060700c3c801141c0035540c204002c540b410200e02628031440001008104030000c01e0214985401141ca05440080c0c845010b05c000c9032082090749011842241420f00c1c3d50302e982001041a03805411040420014030605044020018203442c1a100360b0340000030902609514130004141d5a4400c00d01305c824505440303042c1d0307840001120b40e1402641d6000b00e01c0b80c060b00303e041c460424000e020100781c0c40301000f00d011612842410256006042021003140c55003000c61400308182e2040b2907640c07040c820048141003070000e84418055940c1e08070304003a030305000030f4001c00c8000c12440190b1040c01208088048120210400340d801030314601c440c20f41e0203001007903d1a035604002c910f00040f00002000d0078001040105000c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 375835674 1250 375834424 375834457
    0x3051207030b180603012714010b03030d1d2505180106050304060b061305010311030f0c070c0b0a032901021002090d081206120a03020607110f0d020304140303 70
    0x3e1412245605015164680540d6079010700800440c10a84c00a404480598070100030015407415040e00321078040340b41c0159042c02030014084c1c400109a4140340b000140c0800c02a2030364042c42d180180342e05407000301c1e20418994050000f4000c210314500400c0036035122416403036506201e00712040a80710701d0244003039070040181ca8400c10155400a204120100311882001300080c00c07070b00010700d00001c0b202d014000304469a00341c45406260310480c8100343c10f61900745800348103980002c100072440b490004034141002058030500300a40304c6280d103030741c9810f03a1400c010002c1100b61400e00715046540c100401100c00004041a400c40503402417034501480450003019400c03034849680c10150004d0b05400081c1d404001d00020031149001700c9071440c14504000c030781c2000b0180888503030030040211000c241c2c040750b1107502000a003028840d0000703240c0500d140960756800c4e40040d009002001c0c602580c0032000f841200c40c50720840860210440416440344503001040c11400390 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 375836924 1250 375835674 375835699
    0x9030a03050f0913020904060504060305030901052a060103021215010501120e030d02120130080c0a05060901060906081902180703230403120506031903051207030b 72
    0x4164020905540b1020825040c0b0240101048001c5040700d5031164068011811004a04042c424180203002c11a0180009891911401e0f1280305001c00c460410070001415070401c00b01d6000012004195840c0006280100b410144c40d10000c2c04101d07c2002e10000c0703400081d50000718400002c0815500c200c00303900c1c01d401582d40195554210080ea91180306001d0348007800e001070300011244100259a8601c518240074140780c058011302c00c851a1040e141e61000c00000360340c1310024000040d948024030764203110300e490040c504400010b21400b8a640204003000c02e465010713501c044028021540c6458007c82907407000c1c0220519980001d80903004407860007040c151850000d010300f224050070f4039081d5901001102c40e43d004c2521925503190342c00078218003284044041400031a0381c1400d960050242c44420594020640c4410200da241d542c20304c034074114400342140b201a643c1d06490080c0c000d400c50603d4807042c034210400600114000d0040c24020307140185585540340 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 375838174 1250 375836924 375836927
    0x2401121d01020a170106020a030c0b100504050109020d11030106021f090b07090f05011e030510090507120e0a050309130b0d060e1c1b0602090907030603120509030a03 73
    0x5040151030644400020000d4000c020a100401d11400b942e91030750420001e58a92600d03088069002c42c0455001c682c103030700441d0b8000c11906c1002e034003080c0c40c400303510b56040c442c41c01c04d000d40001d03621a141200009002010f5401045a00c5000f2800d0101510301c0b96540c8144c0801d2007084050f800540801107103c071070711045802c88051040004030180c031034540d003074400821200c01011402c444002d00980108102c2c0800800c003d181103050706210701c4c003030300e614512010004249034840010519103400e007801180903141e035103820040e520b81541c000300503590002441420f6441d140741000790510109400001d031750000c0096150400304014040c400d4080328140d01210f60b6903400c0c07505681c44154200c40d11340a0744011911161440005090481c0e010202a1503901e1034014201e6681050316400f10305010240081d0456060038508040c1c8030b83c100842e031107100f507810410050b4143e4450350540e4041c400070828403880c10303c16607513072041001e4507a06501400c41100040d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 375839424 1250 375838174 375838181
    0x9020f120d11011803020601050a090903120e01020741060103140a0b010608010f091407050d062c0717040206070c05030307060504051606050906092205240112 70
    0x1c00b404000007030304031000207650000728080801100182c00450040009280c410380d0000900309600040281741c1e0f180d503018140558561044070155100c400840f8410400c4d41a07071816504121021440301d401d040440720700c07101d18480c0700d090041d5280816144040ca40d09c4118200d43c00050502c0c2c2d0964030781c8145580d01030000749692040b00d40c2880082c102ca01c4282c02040c01e40c680e0401c07541018191224030b140e40d0441c13204031b46000c90380003081c5403464580ea04145c4c907040540d501d881e203035840d0b805440190044203000c201100c0205940311480d680c40e041501c50450000291030b056401c9032050150b0442c0c0d90403081d0030300440c0141c90540014500702d44a407049001c0a60b0f00d2010078215004100103030385490f80d8908201c1480018410046546540201c11001500b4a071001c1e000e4024500202c3c010500800d04c50b15944498101c20301d407400200002c241441e50f03a0b0244054102201c54080000f50031391360780440302810841002034003058641071069224200003a008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 375840674 1250 375839424 375839447
    0x7061a030115271506111207050c0f040e0d0804021c08040e1512060411010e010f2a23060601140306010201060302130204050901050901030c0e181009020f120d 70
    0x10144e5888125514102c4140f52100030074540c0c40d01000300d058007040c50300b00012940445007420b820000c2c0400954003240d403031010031040760540003400364480801c004000c0700d0001046171203840c0c8480d000310303040b00c05644124403c0303400118000c140500031040d050829002001200180001c2c0a0307000500512075002d40700e0000c01940000c2e5200041d000c14610b255494180c00c50300501c0240306060f20b000000c907400f0300340101031030040c900091180c0c00000e070705000c0144a42c1880030000705080c881d01c440315007240d019005290340c28164000251400d41556082c8101e0304800e600401150441c442c403416120007d216007001c000b2400c0e41e200400c403904555a9400220043e40c03510b1508910000c0c1070070058071503003003001780542458185c102034402c41c011001040000c2e58480701c20141c4020916056480d180c4882494000c0c1005d010400a40a02a03040603100e044c0d0380000c0e622070003244c0d090300c048210703802d205003103c961803500ba054101050300307220240242d0002c0320 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 375841924 1250 375840674 375840749
    0x2a0a03022d010501090b01030e010c0203090d030215070906090f0501021b01050d05040c14150702101103040b0a03180213050c0f070b040209070810120807061a030115 73
    0x825144405101c0e003112826048500c1171645d0340c000001c1540d15201b1300b646541288000c01802c140a603000e50340c0c1c0035004081d80300d80c0719409400200340c400e000040c0b08624501c1076880605004101070400c809501030f0310005040403500003a81760052801c80102c17481038000e45149013050f00401000c150314a20181448020803180d01c4000750740c46000c0c8124091210f444245c1d003080980654800c144079400d100308002002d00101710203070340450341714039812035100285042080c0c054501c85010380045405000111340010942c90352401407110030629501001011700f845078070001c1c04001c00c001303908091240f4810320b10314510f500042e08a1003005d81581480d842158461640e4820b201c00c44203200345406000450074a003095a0b0808054144603400c2e00c0e0401c007101ca114081c2c8500f2844c010300d45030743c8050203c00e00c100d83c08140c00c52130500c240380f0b0708200d124000703d007403481e1b601a41c601003042c4516101c6200200544d8042e1100c0142c96034621a00302584070303210503441 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 375843174 1250 375841924 375841993
    0x501081e01033305150a0e0109090c05100f030b04060b0d110412050a0b1e15040b090705091018030803090f010c0f08072a030c082a0a0302 61
    0x1001100c02c0e040c03204140f000748000b04403450840307074207040d202c0d0181c0080e005540844050024049005145041d121004e40019403d002d6061501710441c0503802107401c540305503402281c566000614001c0c2c00100d0b02c06000020014060100311042442620040402446809108801d82c1c210380e002a42500c926030815031034206000e00350040110132111a40240090707002c1010555540354003007501c030780388080010f44692602d61080014660440183c10010007545070380d640d8041074041c00007910920f400c1c035005001070440d80c85400030713a03c07035400c8040300d0364041e02c034031102006142850003d03d0303000d1443ea148044c640000d07002500c103002c1d0b03140416006500b44259a440c804541d0b8070081e540040101504e444000f404a07001c1010b5030300d010107031188454140d111040350302a01900c0501c10f08044501904813500104181e0001460304171200b2181ca05e040010400c0100200c4411080c8001c8c2c1d844503015030080258001e8814242c40032104410051224100300200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 375844424 1250 375843174 375843233
    0x303050a061505070b0c0405030d110304080303041401050a091e11130c090906060e12010f050c0301170316020409050f011127011d0105130806010501081e0103 70
    0x500b4080c45400c542000602d010940105000b50340102c0b030382011018004074501400d140120383c4800e04e0200d0903081c4459900311000c140c0f010000c80b0001e01e61b41d010380380c40c0c0c00c284c40c000021107141ca400c24050743c03c20001c101c034001d10b4400d000f80d603030b4070240f40d588502322001200070b50094000b0a545419141c0b251440b0b6856010030503982d02c4000b1000205030054060103010010700f600141441460b00c0018041c46410021305102140107c48169041c1c520164035400360480440f803034600c0d8207001c00d00c41e0700d180341c4024505a03040d145508400340c14210b0f5082c2c0e00d00914507908042e900711260003000d401d06034440c44c01d80d80100182c940a540415a140c00d480c1d1404140c84007aa0004000a82e03500c0300113840301020340d20f0000000c42c40c0520008040d204a81d00c420491008502c21032040da00680c01c03950102d5011000090b4240d0b00d45a0940380c00d001d105041c003042c000f0b00000c004509c204041c140007002c3d5140410540d00b5511074000500b800d002d0b02c0c401c0c0180c00d852 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 375845674 1250 375844424 375844439
    0xc0108060d150506030118080d020304060e01020723030913020d0b0d2604030f03030b030f01090b0f070806091617011203140c0c0d0804120b150d020d0303050a06 71
    0xb44080002c03070407404100c03400c0503c1414211122104a9140c0d52241c59140b00000e01e4042103035038415a52501507183d4845003004001001e045120505179807000035080c5c100b1220304100c058900d0807020035a94180000d0704a13403203105600c03400c0c0c1c0c002c240c210441c1c2c500c0e00c039501408101c030320520000380417020240031419040b096601562030321040c1c0185d001c5550803882c015444100001c03181e0609103035948240e080ea03080c0000034103043d210740703e10341103440c200700312100031100200900008a603410840c1031640103645054600301d41d480065841c600514681e40103000107000b20085a03a503c4166844522206031130b020030202001000e126501c110406001e8141415a04d40c02651460f0240587d4a140c04d100f00c7e1103018046941595000300d09008641c00586211490110a01d4a201d06110300d030002030f60781c00d5000203102130004084501d4401d002c04104101080750070410031102d80c1c10300710000d602003c00000400020300c02d402164011804d42c0c0d0124030207440d15034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 375846924 1250 375845674 375845693
    0x106210f17031609141e0a120605090307080403020105070609060f1d010e0c100504090e010c1b0b01030807030c0506010315230117150c0a030614030c0108060d 70
    0x9075a40040d41c040140102c4508140c0c04a45501d16410a03440c0c0c60b142440d100891400d680e0514400d00c0300c40510340798015800c40c40b0701c140701c0c020150a100c0d5103540e6440101405c007042500c21a00c0c00001510350640002160701940d004001c250030180783d503004581c9980419000c41d03410752500c41040002e525405540c6001e0549400414072100f01040c400340c8586018840005a0400d8107101980f13202045101080206448410003d241042c0603241b034403681c0e01c20080a49000d070340ec08040c2040d44894042052070399807816440142040142c003421200c00079000105040040000881000041000d14407a0420b04850555a22264100380b402d03071050301d10820780d0b0b0810b8400941440342040204500782c07186c424194481010030400d6050045010300d0714400f48101c03144074204080d00020060403440d10740b070f15040c9810800c2da00100c01d4800070a0500c80040345807641a016010703450740203401005000800710046684e9900540500e4100d02d900e4035043c00704009c0607 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 375848174 1250 375846924 375846953
    0x50f06090304090c170a020a03021614010510150f0e030d0804150e0a02040906020f03012c160c03110304030501051e0609040303020a05130e070207080106210f 70
    0x910744aa01c3c00140000b03440509100c3d904000030120700b031402200f030710341054010094250058a904c8024401d90082c45000190880c6560068813441001100054480e013264030031b000f4001900ea1201c04424111039004058000a040c4030655030a07100307180448410070649050120060500702282c10203800c4164003000808900030007050210100d401c0101c0045000200403401c0c41581c0c1540300e10308080024030a51312511401c01f44905034040d1a130400700412a5540c0307503034541c1d2000f020b54080c41083c00c107920440b107041c03d0344140308032240310b50000c8040c1c0c2417000064030201e9083c00844401c03001d1000f40da024060381d610800240c0040c610031000000c503800d04035284641c001d204002402419030a804000c00c903107038400040c0d080340c0c1c54140541c0f20200d902d020740c1c1c14041d00b800403d000112020000d41031a036001424010500b40d004d9807082501d40320028266070a41c01040c00c0d01d610b02040c841404416499468114007411501c804524903545041c203007440c50 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 375849424 1250 375848174 375848191
    0x5030a03050f1506090a051203030f070f0e1908030a0f0e030a12081515030420010e0f01051b0706120213030f11040501080d12150909050f06 62
    0x810400126a014894941c0265400030b5403000c601d4000b641c1014001e002c0c000b240240d50114400d48581c403840b840902070000200582c44550b0030340d00345a501d41046a4a03290303184007034082494075000340c040c3d00f090403032a92400400380c0058213010481c070100c0c1101c0314040c02001c0004900c54140050010362000b0350b580e0a248020790002094404201d0f24640f01e07400021100000031031400142c0030103d040d050800f0b140c0d0760701c211154148205202c19401160720704a501c50706d003019008600c01c07841030041c1c90380303030001c000d000e116905500b0465001c5500324501c61014034041c482030340b2a42c814509145071240b0354582045d001c41c6900c81103c56072100c4803d000c0640c102e0880c1e100595084c0341103043c044071311144280042c00381720250440340040201d4080c0300c038100704070058402c05070042c812960341301c56461f60b440b80980c50070b0009495408513405a10a0301400c10703c1ea41c0aa00b0340302141c2800391600c01004081d40840310780c403840440800b80f85040c44900d1060018 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 375850674 1250 375849424 375849427
    0x509040f062d06080c0c0123010611100b03030702030a05060103030f020303071b020d1220071202040b0a150801080709111b12070b06031504030f0302030403031104030503 75
    0x140a8035512882c0005080385925500400b0301d1580200c1e1081c060490314507140400d603030345511341e17404c82921400804c4a40f550802c0040c00704803001254156181c2603031243d82d240d6a980b000210340703d00c0f0769186900302360011207c0490005403500221401100101074a14104080d80081c1c90702e4031129040f11140c01c8500108185a0840203120501001c0c0c00907519501d01250010644d040101800308a20030308039114084d074441261514017558000c8090355152882c1901529401d5400c0b040011541c0140301d9144444011403610116281c001c200040c07246168200005070501007000d0345c0241c240600001c0d98080304440710840da500b42c6800e0380c00c0d4108400c50342440010341050721045c0c100220f400e0401c0304642200d55036000042e11445903404103031401d00746032180c50904000f030004a0b66906001d8040000c50040034114200c1d207501c1410402011080d10890300640030802141c940403001c1e02030740056900c1417281c600001d6072610740040c00312a4015401c241c41d00d520 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 375851924 1250 375850674 375850679
    0x90f050405010e030f03070804030c0f0303020c102d090c060f03270f050f061f1502030a1b020a03030c050f0c030705060708190302091e090a09030509040f06 69
    0x1c3c420186402040000303540343c01c01104004c0072a120242c4400c0130024440c00240a0602c41c100b5504656400004160f5800080c01d00a01031b42100c00500e61074060700d101e085407411280301d00802d1221007401103003001c10a00c05004480c101111100d6182d80300c16900000034200c8140b400500403988509c940c0c0e410100c001802c0381d01c075181c0c42c581d20300b02031644200b9195213203030703e8000c65014214001e40e56441c6400c60034480c0603020f050062250500340b1110781103290584d070038540032524200386150740301c0050300300d01c0c11120302c400903800070415060304070311406100318078034140780610640004c2c5038080b41c00a88241d1007500000c0d40c000d112002c10005020881690710182c00424541c0e01d40000030b078a030200391007240d1281a0010f00d0604110090040c1c0d2064480c40135424443c490b45040070703020f9400740024034819420305440c154880b80e0400701541c030f2040a00f8030a070036510102c9610051003c500181c080c00014021030f20155241d0040219005441c100810042d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 375853174 1250 375851924 375851933
    0x1060e0a060806180f07031211011401060e180702010b01030b0f0a05130f140105030706050a120c0504080303180d03020a0e0d060b0303070c0311040b0112090507090f0504 75
    0x101501040c1120700782071040103440800541c0c0c9800800c480726030300140201c80c071042e20f0412909641c0c40780c0e026005000051051a6600c081410b1064a4803c0780702c46103240c00d4201d950515521220444500051040d24403d81c440721001101412428000400f0410b800e03424608980c10710050391070f2150940d05590500500e0a2414251807544039010401c2c0029020b10701405080d001d110540e03481505442c280d0000510056070324020440c4004115090480800900440303010384268a00058014450822144505c00980e2441c030011510061200940032480358001085003d1002117001442440118015000071114201484800001c0750030b00c11016694000c1c11b2051111221090700f01c1140203075500201c0340c041d0405554070f0000000d0070321702c03100d6400d8817010a1280401910044100c00d6a0040c0d0341c01d4001500402000305840b10f0014803400602070b07410740740d0041010f8200501991150003514442511101c50030708881d400196080010340b150240700501 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 375854424 1250 375853174 375853199
    0xe061527060c0a020f04020f07260909040321020406020a11030d0507020d080c060c210105060a080915100608011406040314070305060c0403120809101d0f0106 70
    0x501516030310b04160381d102c00c80f030300d82c035541c00003038040c070304001c90100c003651140e0480702c0c004203030264a0b488820600b00140807a2001c07503021713060080d04500c0380b4220031010075030316101001400e50b40a03a5556804480c5a11048428036540b0310040b142c5c0300000890000c1c00240195500900c1101c003541010344043c409002544d020b41c010f0800f1079050340d80308084490098040d66100c2502c680d9151014451090400300f1a0b18050030062202020000c001010051001c0140401c0c0c030103002c203624002c1c6001e10803154091010000c454885018615640c0d00006007403d0380e00024228a15981100d0210782800c540c0034030b20b03004d20105400400c8140903044101000c4c0144503001c0215015200d1800054180303107075601480310036401048514003441e409002e4030850700b00340c0160074041e0041e0200b01c4a03441d5114500c44a9841014464030600c480002044e105600f400004000c03c2c1c40442d40400c850301d4004001082020010014001855800060000e1070094031481a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 375855674 1250 375854424 375854497
    0x6091e110a210206090306090114100b030a0b0402071704090c1d012709020702130b130f0e07080706031803050a03020f0409090b0103060615090e0615 66
    0x150000728042c0100c8421021055040c0c00307081d0003481144031400040e1080c000c804a0360740c58031542d404c100e00064190170800101c21171510980b02900ca020f03e182654000b4010756440b00818400111300c1c0308a600202d0003210040d0006140c1502a2100d00c5000800b41300d281e019000046d08002020035403007030328180d010741e2a2a040070014a80840602064081c505040099101048030710300000715500d101078942a0300050019034684021003c2c0d00a050140d1141000c2e1030804201c0080d8001d68001240c0145010f81032051500d100e00100344600c12012681c0d900e001541140b0820400781004c0e010000c0144800ca00d840c80080030707140109003031100a4034030594900042d41100581d11055618200541c468a10106401175801070340e002046083c1800003100c02d200003400000c1c10303a40034040601100f42c6a4600e120340781c8800500740c00184440c0c4041000d00003a410081d00254002e1500c0e40440c59004c46441503003244401c0641e1003203d403814030850b54800d200400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 375856924 1250 375855674 375855679
    0x16060212070e0a03020319210305060f0a031104091e030206090d030b060406211107060e0105070c06020f120c030921031602010905010c02030703030b040605060304080706091e11 78
    0x1070890139640032a0b20350064502008102c0c051600010411a82c07510000c0324004102c1d5286842080d18801400351405443c0c070f0f17020b800d40c04103840140c10061f00a138180c0ba000183d99101c4004102400001e09000400b651a014020030002400403255042200580030394010862400d042c59141e0a142903001101d0625150200e006156100c1c10285d0341118000e0904400040e65140c00190045d0703108011140706c2d10f070071480b004805100e40580100f902402d020452100f0b80c048080c02ca400541e82003000c1002800070400041041c1c0090040d14030281003e81050b01895504d8209003003980c0c00c1c12884408010082a554100b02d800c1d2a080c04054030710450100600e250000d200260803114640c0d10440028030341da0007500712484071980103000b08220100300800a403242c0002801700d0000f402e0420301c00d4185000d00403031040d11401480f85141d0340b51a9203410050380048000c44084d501c1e83c18240100e50714086c01c030240650083c02c4c1c0c90104061070440413180d8501e1a051 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 375858174 1250 375856924 375856939
    0xb0702011506500309150901021e030a0e0c0102070902181009031403190e030f0a120906050c030d05040201091a040315050403080103140307060920030a0b070516060212070e 76
    0x40104000221540d86c0302600c03a5a41c815111070301400c0c0640b041070501c54220149047c8040340c280150700551003480c0f00c0104014444060700c20076260605442043c0c0183d20171402440504080d60041c0055100c030b01e03032880c407c0440804107002d14607040e55800803d1540e00100309101004040a44076034548025500d8002d4000070b101400503031826080800c0000d64041c0202d44081092f01c0310481248103c1764201078501c1e0000c40c0e42400d515600000d0b0021800160440c0940c05070b800100008000e14182007000d24550300400008100380d0401020804c002425503c0c50fa6610300e05003040801542c4600b1400d000d61000b00c140700b940703001c074a0318003080042640016114156a40424041c0c0e25140002da614a54020068040c002d02d142001e0441081401581c0080d00c0022350308803103214a8000400d900c520301040b026045200010000306520b1060b40100340c0c506003075101e990440e002c1e45030b040403a0000460307040c200c0481c1c000c1c4005a500800740899180040390000c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 375859424 1250 375858174 375858181
    0x3070305070b041109040b07030b0d0201051611130905072304050a1b020601030b150d0803070504030602040b070506010f0807120203030c16030b07020115065003 71
    0x2451441009005000a842c0300301050800044076040d144149004112096074141810072652502c01540e15402291030107400d45002e06103060381042c680c1e0141c44050404000905086952180c1c1000701c038801d480d81c03401d807138a650740c0456440b0400790001c00100400076162561600340c8613040506824000301400e018514070341d200c5100070303009a80200741926050071a03800751100746006190b09241c007100010301ca500103603c504036800388500325000d8131001b0b20040403e901242e0150052204050200440c0545e0700554000d20300d1724005180c15500d8071607008070f0300582c10000d080403000502c07000307112040200d10701418007001000000f40c0f800d182c10f9030301e500c1803203200d03681640d00b00d03000c0640d54240b00762589141030009690202e400300001700100400e901041720311408a10120b08994414841c0f80c0f00201c401540030a5a0308150f4140e03480f48180c0d00440100200c1d04c8454266a40e04120141c0b9111050358881c40d8065545031414a881100303c0031411030050080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 375860674 1250 375859424 375859427
    0x20f1203071718040b01021c0509030c120a290703061d09030a0f050417010e1b010e0d050f01090302010b0406060c02060304020f0105070f0b16020102031b0d20070201020d02030703 79
    0x800c1c41c1a00031a4001034418803a40148c0c100021245072500102d0030100e501c00c01034201005101280d000c400303644440007000c04000382410321154000c03081e0303c02c100324400035150117036100307015a4003030070800c0d040304580011460802c02c840e02800a81c880d0010030504140744030300c52000c0320302d038040e800034603100c4201d84c0c2da40640211001001400021904694081c0c0c00b1540548880c660841c4040c01c1071154901034180441410024807078603184c14104122a04449202c0703030140d440c2c8139100b00355820400d00800d186801d42d070303130700560540c0031800000344600c402552083e0004544000e0403420001200c00f141d101c0c0c1e00307110f80369016000603a10306d0100c1c0d0b4404e40c101c800d480001001e01c0101c666004040000f000c080e41110300344280103480369210300c6400304d0150782d01e424940c02001c82c00e0340010b4038214403580100c100710107802009800340c00e40403038640d000a00c414014040480020005401252039000051440150b5906001010325102107000075468110319940 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 375861924 1250 375860674 375860707
    0xa1a01170a080d0609051303020d0f0507021e040e060702060105010c02150307050f0a021609021206131e2003040b0a0207020604150503151c0609020f12030717 70
    0x100400c00b100001e5100021402544400040d0007004070030421840e011800c001d034041c91410136009813254640c10b010b1070b44a03440c20f661144040e990642407040710343c00d101d940081031000300000300360031195480d030741c4503031090081a40c0c620380201824284050040d0800b05d040e0030141c1040054000350002d0f80701c20600c2040700c410403450039a640e807081003c0b94a03020b00980c040100c04001803002400d82e002032425107054030440c80d40c84041d6200159822840b5038984491140c1030040004e8940c94000518040c00030700741000b0407802080c4050003440e0010400c0c80d0b80d0030343d40e82010200380c403e4a1040c03001c54000030180c0e06d1402c040c0c0b5003038801c2c6001401c1c1c02100390000780590031500c440c0c1c2610001c0240040600b0310130004503014019410440300782d0034808028022103100d10b07001c4074250803094542d40440c0d0150040c0c0310080a030141d40d800f66003003203400144043e2030702c9a800810144003044069a103c4000d4602a402c4515440c441520309800b44006e003180c152080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 375863174 1250 375861924 375861943
    0xa0c08010b1204060908030c0c0106060e1c05070f260a030507170d0c051b0a030815010903081b0f030304020f1012050a0e120f040e090f0a1a0117 64
    0x301c20b0081d0388030714225014000c1a44002c0c10001e005c0b082c0205400c100001d02403505802c0005e005440d114103007260501c2d04411350355440010f4000b2007094030041d100d82035005004030151130040ea10742000380b07809445d507400804444180b50f4180204900c0b03009201e0422a000b02500c210741c41c60300d00510b64050206d0203803d0010f5003c00d4081900d0010032155500200802403104014020f000362007600452030640580d48040c080041a0901103454081140d01d5201d00059803142c0200280c020301005945050209603000400414445e5015045030150b05903000c1c2c00d0140b05135018244400030001c080d40e41d20504c217200059850405c0300400800948908400d01501c00c0e0860302c03442081c3d00e0015440c030303007018840c1d039200917001044070303c041c1c0c2c3c1113034200606d08540c21094030500c40c40b5002e4590071310051110342005c1c7d103003540101c00e0350f0480314106841881e4506062400e00100ca0302c81e11020b03004280d112049490f401098017030500070050804450081d00c0d1802c05 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 375864424 1250 375863174 375863197
    0x5030c0d0b180411090c09010207090f02131202010f09030b0703020313060507030b0306060604031505070507021512011406070f1e0510150b0412080906070b0a0c08010b 74
    0x1001d4801d0340c0c1e1100c404a00c03482c0b041c0104100182030a0610720b103075200e150421409499400005000040103008a480041040e0700910109140601c140000d11449083c110f100343c080015401d60080d042c8024042c0c840085100c600240b144005040308c560302100006120041e0700800100f000d1450311a40101941005684ca642e080e0300c07582c41e50804417000385882d03d0319081c000241e81c564882a407500c0203038215500c80c1c03039200400c101400341d840f009091120201040800702800e822058004030503080003030401006074005005014401c5101c008400041281e0a0080703191202900403c0310341c00703100c0c041d200c3c0d00101c0d400788514000034080d03000e140160b404201c8040b000c0303880e44165101204039103200703207400e40c1ca480c0707510784000d5420b0602035424403500394001c4c45400c07170701d5500c00680303030920709404280101110b220644c0c600ea024045d040c41a00c481000f0006070340f00302d0104806103032140050703089441c900c540c44104a040b0f401400705441207811140b2030101c5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 375865674 1250 375864424 375864431
    0x506060f07030e22050708060d0303111204120f0e0a0e10090e01020c061501090e04031103040603050702010e12180d0501020d140a050f07030c1211040602010c05030c0d 74
    0x341003c1e01e50342201c0003440d030007400c100c0350109510424040c2041d0f0081c46001400540c803241002c4501e101c05131500c0398020a030104a6000034000c1d0b00581c144d0108452190610075503441d2180103440445042d500c2c004c290344001d0030203502c500251b00070b88050901c45401c40c1c0c29408505000d00c140902042d01c0e96150200780404140c180e044010314070b600f020701020010141da94084d40044101d52018864540400d0011194144001d000070b81a036038026014a44210003d04070005882602031007a051424030082c1c10030b0005002a0906403808220360505c00c1c0000e0854100c583c0c1d1882d103400a611828060405004490b0241ca0721590741007903204540000e8501c0000d0080103000e50300c0026a0455440300b40c00c40c0401c3c28050f0828080d0760ba80c280f400099410454411040f01400f50008181030b009a0001081051074602245080c2210010b041201e030311702c00400c40ca24000c5401c21240350f0902464003440078502c2d20074110b00700001c0b43d0249002d414001100c0c03a80303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 375866924 1250 375865674 375865687
    0x80f0a080a0519020c01090906150503130f050c15180f010e040609060306050603031305060a03020c0f061611100c1b03030509010506090c0a0c02040e0304060519030506060f 76
    0x2c240180c580707200c156040362a082001d00d20207075031540c0b20b20025010031840c050005070701c1d04034030a040440e85055100080303030509100895041d1700051034040405d89030600c16001c2103000311050401403013200104402c040c0d540410010410355203000c0c245501c03c0042d03040100748181c04240401040d40c914445e6140c44006840c03605a14040a811910f85100014000201d0f00400112401110100300d01c0c1c13114828143c8900c200805082e40c4070500e00c023001581070100040c50b42c18083d180c01402c0111750a1840c4c102120001001a20383c800014410413001c550340742c0d04900064280810341520140c1250348803040260702400301ea5039030440c3c0c2403641c0a01c140d480141c240010700c0c45039401d58500640200015a1940b10a41c0780400180340740c2030000c00203003d81c101c00b5510303081c4640450101c0e04a031030742e0012a0050b0310b41c1240385505000700050005004a07440d02500da030440c500f900b80e170410342030b8240b0801d42011706018064840100312140e126440e058a0358612 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 375868174 1250 375866924 375866927
    0x17070203160b0a050702070605040e0606070c060e011d010e0f040e030a0c0507050405060609130e06010909020f040c09180e06100e091204290304050d09080f0a080a 72
    0x560385607480d4558241541500b000b4162120512848200d04200083e4031540340c220380e5242c0d64092100401c200b008141f0008245801c115404440140f4075850301c03030540d4440c0d00c0703010302d86d02c40400700c0d4200c10250b865680005500600c4900041e2094129004500080035080c88490b114068441091101c02940b03880d0010007d9a0080007103996503440180014904480100165141d000d86000401d5500c1e29019150003020000d0101d0b0829080c4d0b0200300e46640424000d071000c0e6a0703840c1406001409002c0c040c020480032030300094102460042c000c034005c103681c405100e1071600c00d420507942c1c1c00c48842800c0d15915500404100781d100040001800086007442a52144001b00a101842120603038160f0303403000f0000080740c862120715070740c460850080c108184401d210503c1076411665145003400600d01c948040c1411083ca10314541c0c1c0242d405a410b60814054040019003109010000b8140b0320010803002d6041142c20b40c844003d40303401841604000381160aa9 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 375869424 1250 375868174 375868177
    0x901020a0501090c0303080c0307050f0d0b0d050717010902150a11070b040312030c0210020c0c04021c0b030a050606040b040e031c0608030a09050616080d06081203040317070203 78
    0x903070080c02042449281c2c10f0103c100010740c4002c03400600014000751100800d20300b542d000d100540c403a641040000d1402d541c1c990401030500d81010b5543c18104840d81d030300c000c1c4035400f50081c009801300908058000a15000200c65078010fa170510f4050300058844e100421103c003050141c0a894452142d001ca42e244543c00c182c400b640b184100c0410140f42e048010012a885001c0c110f04c120300b04907054041d5041c1240e40740140e040012260280700c0d2640003000c80080001c2074030605543c03100084d0481c2c11410903040529a0401c001050190902c582c03c5062012002840c94040d10395803156140c60060041d4010f40d11200015460b888030342081500001034400c0c6d80d110703c440a0192011212907141d0b0f1126421702c400012402c00c01300c00c41d4810764581e030b00c4014190510382800701c56401000c61001e68494070f0070440100f00484090b20400020540c0030400c50300e8064001d1401e4100203100c07003001802c02c240300019800071800703204d424001d1501310190359440000e9095 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 375870674 1250 375869424 375869443
    0x182d0908030108060712060815060415060e13051b130306061502010b0a060c020405100b1603030b09070801031211060a0f0e03120f0a06030609150c08090c06090102 72
    0x1108040004500740102155451140525564106c3ca54510100c43d4065078410f00c07800d031031134001d500205415498150403992000015001113618600010324003401005644548001141311542801529020300000c00603400c030003040c805814020b4030724031b113000f00345030f00142d49200040b94002c0e41800c2c06944021034024000300003040c0e6403d00d00089408184100c80154607001c400c03000c1d854801c0700074041d5215961240c0c000b0700e855003404000c00018184c10b481c1c50341d498000403e10540802400c505039400c0200f52020f4840c90090f042d101c01e1040c40e841040c0c05402c00c00c41c15840903100e0b0449030080605041d88100c07040075110895080c0000c0c40c075000700001c2061340d19290300040c003410490b0204000036884208032940b6405001e0f80030200300c0c200307008203207090100d00d032a6402c040217440000e6007e07600c1e5242c404507000e18400300c1c0c40c42070307070f20032031080200b41c2c800c42c01d072043c2e2400c10761080d00d4681c019640b0b5200c07001e44180304100209445102e82d10070041c0351038 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 375871924 1250 375870674 375870683
    0x7060e0922030f08060a1809020a030f0c15050c060403031a040606180605120609061219031704020a050105030a0902150702030c010518090403051909182d09 69
    0x1c0000003030400904240098040a0216040b080805c03c2403c14007414012102c64503814032810403c41e26050207401482401d0742d201045000104c04111324080c2031030703864030427039200300180d00e0064034600044d22221030702e00b4000c0500007034801d010041403640e0304c15854500040c401a01c080303880c50300c0707424107912500b261410a020403002d8110415904054004038640040e65035a1021210751064500007910099a0008121641041c44155403c040002c000345140e000c00620180b0b4109524403040099903010045014550490784600388180c4004c603021aa01e41074010030022221441038034104200040001c240e00c410398419212140d00601091203031a040309500c5194203d020300380d1007401009070001c403a41c054411645140745550b00003961041000030003110540007002030f4103001003004400d020050180100c0d600c409503440d0006041d09003410203007000e6101c80e00740121494185c481e082c03000580c60740f0b01846d040c4942c40c0c210072076420380c1902802464034000d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 375873174 1250 375871924 375871981
    0xe061903140c030708010911040e0f030a031506030b010c030f0509120f070504090c1a0405040c03020703080c0c030f1309020c0f060f040f0b04030309020a090b0108060307060e09 78
    0x2500001c0104181241140803070407100515144e400c0642201c0d058140146581e8200c03007096190b06103070b00407200c0d61010b0401e46042c40303040c207856400d591040c1c100e0b2001a99944420604c0d0440c140d1001c041d000304d24081040803000d0f40081c1c8850301c001301c0601404850300014045a10840848500c010047d010884450b02c40207065620750b1900d02e501004d000f082c0c004102802c09202e41480340d50085120346600f4504446420007442c02c03035103000104010080440d032078446000300c12481219030307801603456085090040503210040d0030b5040800d4200716181d01050000155400c00120714185681c4d117581b030072203540c0030415030303c004103443c00421200a10200030a6003d1070001c0030003a605e0b0740d40d8100c01c1062000c811a0028140e42c080d03141c00001c250200e8242e540103100f4200000d0800c029000201c594045a21000d05680c07106d00158455900c01c1d20180c0001080c2e0040c041e082c10701c20054025405501c00a0141290340b00251500c2c1400000040388210100200c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 375874424 1250 375873174 375873203
    0x20d050c041517120712030f02042705060303090f0d1704170f03120c090d120f02010b030309040506011b08031b090a09110d020c0a0311070e061903 65
    0x1500d015058480c600b00b1410f41c05032441e07800d40225010940500d2921218540000e03030b900c0044554001d407a003410140d0724410841201380c0c40c03004201400031107026026105020802d07411381c2000c5035651304070300e04010a201c0d0544001080d030315011002c0b1030400702c0c440e00300c010400354208410054400218004c4074000d004004000f0410307141d8150300c112420440c805c80e01d035075081c0c0c8100b000c80c640c010403446178080a5900d2003600400840020382c646580880080c0d00401040c030155038480d440300c0b058a105400a0242141d050180000e102c2c0550b071400007a12406011201809141c6130000190280c5c814246d01d041e8200032079504e200e070003ca0421804a0b0803c0f515044503840c42d84c80c0d4403228a8200964580c010002e001c420702c0d40c1041d01960181000034a81368099200340a00c02802c0541d0005e410070001d4003004000c003a0031414018460007007582d501e00c090b00001403d04c002c0d904002402d80c000c9013901c2c0c40c90310103035000c896940b101e0300b070340082e04542850b4080c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 375875674 1250 375874424 375874451
    0x2d090a05040302191205031005030109110103050105100e0f030c1e1e1012110403050303040605010b070818130c0305090c150901110102070f0302031309110304020d050c04 75
    0xd180035600035804c4541c0e00c40801c2101000c080010405484460a01c80d240c04e042c0c8210001c40c1d01100c17040306000380d1035071040828251003161000301c80442400041300350030350780f6110340c80c010101140e2402241030650001390200e01c580c4c0342c0c50301416604107010101d403030070446050715000180030070b62400700c91002089041c01d804400d40c0704100c1d0711445441030080007031401402d00020201d82241c0b10079a025202441d001680520681e2144403c00c00390262001a00045000314051586c2e0b15207840c0c000c0460b0170503004070300400d0042c81030b03001203116002900c003070785510300705181018500c40028818101d500c2c01c145c1c0e5207044c0030040090f1507068000500482000040360704511080c41088480560303e00c1c180842c1005104a40f9250310506011814081c1800014907000c515216182e10302040c2c10103a016a10020300584e0f00800030b00c841c1c0092100300720401011401c6050381d0068400900044d00c1424800304400a12005200070b007525030004004016244601d1103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 375876924 1250 375875674 375875681
    0x180a0e0103050f07062703050d020a0605060d0f0f0305120c0d0b04110a030908070b0901051015020303060d0204020903070e1506130b0c070806010612060b092d090a 72
    0x8039035038025071092050280d8001806410350307042d0303251600c02907542c00440d913090600c074030106c00160203c07000001282d004d1110440e4410150f01810001001d0308000c8291500601524021000350450f000860510104840720760b50029041242c40000d0134100c0d494010424004405101103003030014070b065210040803061003140c0240000c00c00002003108a40780400c1202050104001c182c410f60310030b0744401c5c80140300b00d41030350404019807602514807504550f58140c1d1ba40d182c0074014084c500e00800030003441c0c02000855200c0803408000c4d280e0002900040c05080c4a0ba8694119030340d0380c05540b04004043c0071100e640f5a1110f050030826025140c2c21503a102d41c040300c0304e05041c100c048908089000400e0b00c541407520003c80b245612030a424000c60041500101d03107a40240401c4c1e000f000355649801081c075150100c40c04461240e440007400885c02c010124060b11849241c50100c0300000d02c07040643d0700e8445140160381590f070942da102001e00f04014001140381d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 375878174 1250 375876924 375876929
    0x9050112110105070c15090b0c03030f09033a1b1d0307031115070f0c050a03121107120305030f0a020a0c0807050a0f050c10180b180a0e01 61
    0x142086521481c0200640301481a144090002c480e28001071040075100313000704041502614042950b03d580d010103284a8205c0003205185401c00402d001c213120303400c2c5c6d550744c104190b0360240d40303000c0307051001425040e01c481300e01c041c61200903100382c40c29846240700d01c400c40529000348076220070a9004c44542c400d10a5002c042048480c0d02e09903001454955000094007400401596041d40c030360f05442085103100941c01543c0000e0100d04a520f10007070310b4401d07c22003c43c0f90b01d6049182c00d1100303848503085140121034420f410004110081758046124030039007004009140006092420030506400c00c014010240c00b5140070594000000d6205d0051140005182c2d115648960b0030b903c1a240c4410015419244241c0402c082e14000d0401078803501c00c42c0d01c0d502c40c5945e900880405220207556640202142c0d0300c0e0388c2001034151004225a24121040c000c15103280a00606603008008800a02246051140050001d24100040d000348200c229541d1040070075500302c2e090 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 375879424 1250 375878174 375878183
    0x6020a0b04021c050d0f050405030d03050402040b0a08060a061a07020d030c021002030c0f15060105130f0e0a0b0a0312050d020409021b210403030e06070c080f0d0207030210031509050112 82
    0x20781d11140d00078891f5007034406443c801406880c0d20030000b01f084015000c01f90040c4d130f00943e10001c040302039440303c6284004201c03003000b030400351400024010460380c01d41c0c4080b03241c2e441c59451000d10b6480004a07054207a0485d15410741c5c0c4010b0800b02c611000954000b13400800c1c142c6c07090a1a40c0000140141c1900c144c101d5030303148042e6100d9a160403040c041c20318030070f40840103e203031503029001600084440d245019049643c49100410441c80b5600c181ca0f2058841e091015840c1c45001e4488640c4040c0c0b15030199600e556100141108409840c0003082408100401c051000703404450003061050300c15034582039902d5005810a4094000c180c241c0701d10611b0594065084054101d80950240c4450800c0d2454400f507410b003105600709640540d00b00300e00c80000e0345041300d0001401c8100020582e400c090600c01c1d14240200d00104155405800c0c20401691204d01e0040115114a00441c07071742a184619403040b112604110403180c1054000300b643c007a248419000c4600a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 375880674 1250 375879424 375879437
    0x5011a190f0303140c01020a03021201050d02090a051e100602061b090d08070b1303030506220b040b18090d0e1e031603060207120201050106020a0b04021c050d 70
    0x580c0382009003540c15214050088070100c0080011034021108510b100a20080982c42e1041e00040e190032030707003c0400305000c05c1d400319110104911258500380035143c15507078114626819000243c15003c014100d258043c0ca03600010301804428465401c1c9000448600000342070003811001c0d10b8040c0d0207208010300c11381c000980f5059929045014803419000c206240c00c02c1e0b0000c3c8060b040e0700074401c2c0d40d8140c080142400240001e003003030344500050700b0a240e0411580c9401015070b140a0600c034810700d000002e1a40c11210602d4001c100c80404000040d10505040800d0181242c0803081d588500303c012070320074a0647c42401e86c8204031203000d03a04110b00d80d01c426030304509507041c16500245d4074940114483d04d0003c0810b01710358001c08a86508981c0d00a052106009401c102c0e0f21a40100c0c00c00d0402c80050345d241c6045040b80000d000e80e41c1000c100030361b100c100200c06411039031298080b4096403100c03100050a003201d442c8814441c107160030030039035808441e8440f200041c81e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 375881924 1250 375880674 375880699
    0x60e150306060d030c05030f07150b0a0503030d0203060a08060708011a12190f05011806090902090c0304060e030a27210507090207031107060309080d1805011a 70
    0x100440d40c03a1182c100200b150729014000e440484032040d881c08119a141b00800200a801d1640b00182c450a03102e652410003070400c02ca80001550480c003881c80c0580241e480034080c035070300801900c4820100da20010780b02d698440024104039244c0d801008140502c03001d10529540c030402c00c9060f01c40302c480304c0c107071885001400725492084080314000e0907004004a01240095042e001c109900e0100104000c204000900c048036000ea100b04200741400024400080541c02408018020000308107c40382240d008212042d00003052444000c1001001504000082e40300c1402c0c08030b42400c480d1284080e16020b0688005051420082d85100d4400311410015800700c1054400341c0d00040007a405410785000130151031b010847d418000e417040424508210320240c8035041c0a40c0c0e41c600142070741d803103281c1000b01c01c0d04003604150030000c2d84800b141a000032500380c42e00481d800680c2e480004000010030b1800a001009035091402a020f164540101c07920403050448444274000c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 375883174 1250 375881924 375881929
    0x405151305100e03100e0705010207031e03020307060f0203060f091303050901021e070509070906020d0c080909072a052808040806150f0d060c030f060e15 68
    0x60140d008031000080c440074040c80c00c24088000c24010a0300341a582d03035160000003400e004980314810700442c2c0d0b552401c403c030442080b8002c010030382070006c0c04003d82585ca0710303015140d0800707034404455241488001003610800c116101c240d00301c41d0030426500c1c4038000001a5200750750152042c0b4a08241c4138103841c1c414290360041d1402c0001c10002d0748260380948868110f18a8039042d0b0282400d16030040c190210340d202e00507401800b0b403600c0303410700c0100311143c41c01800000030826040c405000c803640000e500864042130303003440303c04549145003c6d40c01d4070803480c00395005160401440881130700008680f60300004002c18840402e0b510700b6800c500c0c4140c51001c0e0559001d03010044015004002000072098000c000d031640e0516600c7c0d00f401e40e8010f60109040e03038458010001201c0116034105245001100e041680502c03590019100c0030441c8006004030341e480000c05580c1c0c0c00707a8056420900a4201070211566402680840741400c503060070b4030300010b040c4401d252 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 375884424 1250 375883174 375883177
    0x1e0b0c060601081b031b130308030f1807210602041203090b0a05041a0403020d0b0a06080106120605090c030105070e01180b0301030f0c051e01020c0f03030a030c0e04020a0302040515 80
    0x91135903a03a03a0540c2e41e07000000c402204041d000c0400d28104001c0701c01c034200c0207240032000e18050200c6903540d05090100d0300007000c00500b00350007030405548518805201141443c2282c0e0f45403072104a410b0b0030300c1c02c044040110345009060350b1000a0005e40703881841c10107070061740651904105140e4501c143c202074440e100300701000a900b004240007035140070716a001050102c0c400765084c11740b13903800b1a580c4810b981c1d09035440d10f041020481e80500c2d600940000d080e0540082c400d00c0c1c42d00309001e0036201c400d80020942500c8000094501504001101030540d0080080c4540d0602c510007410200103c46403900140b0300e2600303602800c503140315103411603400c0200c951642c1c1c0796844c1d0411032071150004980300102c1800010351507884940010034507200301554414a0851070000e80740c80908481d8a0240311030301d406007000d039008000c0d81d003e80e00e9400c0100c0e045814080c00c8410714000c5032825030051000c02c2c0320035483d0380350740600140c600540c3c43d000d0a0310240240b0700c45 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 375885674 1250 375884424 375884461
    0x14010906122703050702090a0b010203030606030403121e060605180402070305070503040b0d050a0e0c1c05030f03040b01300201050d020d050a241e0b0c06060108 71
    0x3103500d20031404800d21080e031110000110001c12031103448095002c0b4140158008015000514046040c1d01540b4050b09001e401c00c00d1071030300700510101031001035200e00000b001d551043c000800050107042c0581c280c0190314841d580c0402449400f01420320160f400d040200c10310300d2400c1400700b070172070081e0200e641e4110301070400c4105043d00d008000203584802d100b207040020074004c84002590800140000d4a5407002007910342900ea1042400c5603c010703d80400282006070a414200000c1030a6070060000d8503030900b101064490381c0d00400125000500e0341c0310018170b1212001050b800317036000380e104c0d8a242c41d040e6a0b400c012216010300c0c1c41c030100300252030107400c221040c0d940d00b00c0f0081071060622a0a2010449407002282c01c02d50000ca103c5442d141002220340301882524a8940c9090040c440c100c2465220392502c801409114060114000012a0020701c04546030091103218811a906e09000781c0ea961039020580d1141d020500c207501003101402c54070b450451 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 375886924 1250 375885674 375885677
    0x5070203090f0d030908031206010f090303050d0506060f0f030f0f07021f2702150f04051309060e07150f1d2107061d03070e0c0f070b0114010906 64
    0x40030b001000304500c40050314000c406000043c40001100007050018012003c50076035120402d19150f8000342c81440510003480c1005801c501c1800000c0d0040e05030703140c000c2d0490300016180d4482e808211284a10700940c441154040340920001c0c03003c0000b180b0404440c484c0d08001e4481484c0c0b500742800031345202c000358100c203180c3c00700348620010001e040388500c0030100f00e1200e0040003142c01103848004a042c10142c202c034205500704041410600903003c0341c1c5d0343c64160b00c8400004940600e0240764481c1058004072007040751140c0007041c480307401048c2040015082103901c0e0384c130f641d80d20444851800800e12105414003944420240805030b4403032000704200c029600da00820a85011940840c00c198800b00182d41c00c1c41400c0303046914002400442e040010140030404c10350000702481010410304e100507200458520110782d1200a410120307118071b03943c10481e0042c2d03004902508000b294007414025404202381c122036180b0340306a0b419101600444d8582182d008160 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 375888174 1250 375886924 375886939
    0x201030e01060302010206011e09060b0a11210702030c031902130603030f0c0f0b0703051905090307020f031905100507020a0f120e090a0c0306050613090903090b0c0a060507020309 79
    0x30700682c100c0c41c0e803007055204422448035520362b409842140c000b030300a443d410381d0100351030003016000814203048120503801001c0d44000d1440e4a24542c405800043c0020302c0451050110341b820080004034400080545c0d05411104605100b40c0740341640591060245518048400d01240300f4a016241c05540d180350000701401c05890381e02c404d0404480d040c41100720385020074840d1004501038807440c2c0c2c000c1000d04000c80a42070716803102d1043c1e509140307880e0501115240000031684039560544a42c00c41d844a0000a401c001c09546003950400402000e0b808009000c01c6020040400c50410032103610380100c1240e8425000ca002031000004590220105040c9200b906030b8110500d03101c0588407070b407804a640b511042d24030b49091525200c8502503981c041c05800e000d088107860f91420080b1362210501316504038850754107040e50b104101014184100d11400c040c100790030b03c040c2d0f2042060391003030780d030100709405036a01443e001c00319034618408412900015030042550 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 375889424 1250 375888174 375888179
    0x1b050a030203060a09090f03091a030a05090f0a06060f0e130609172205060708030408090d020604031b170c12010b0d03080403090801110301090c0903021c0201030e0106030201020601 80
    0x5500030b5002420055104030100000a001020781c014500a284a0380710060585003510300501800803a401c41c5849071110b21003510b0740041813050701e51006041001041746c4c0c680000c20344c208070030741072444e007680a410004808d104403a009101121441c50405038204da6690918a1800e000d41e040c510843c8080c0012002c81c2c49500031541860046d070794400030040030700f6107152980c0b0102c03d0a00c1c04102d070421f907800d1158005200020f0005541561802941e60f4a040040c030000380020548030b00450811882d4807004100d549007503010b130000d03503a203460f8100445801d25094600644000319840440c140e2149108003203407040000042c114503410600b04000141d030100280302942d84c40f1003400711a55410b540200e503d0198503080503d01306410b00034140e00260b00174143c41ea050510b0b0010300c820010481c0c1c11503c91000001e84c03441d45a00032a05101103a102030362142c94100004426905450390f00a881c0c400d032010011801401c000600f80e407140d11000e80540c000c01f004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 375890674 1250 375889424 375889427
    0x2306070311070528053106330903051c020118060b01081e01050f031e030c010e1606050a1e120e03120403110a1509061b050a 55
    0x41d00c0c624449000b9542c400b62100086940f044205800359070a4101c0080c5030719800b82a103444020f81783c25500300d081001841da000c04070384400307602801c45082d83c940d1600650841d510101c05880c110155490b0200050f294490300c031030346081180c410400720300509405014454030400c40364000d020388028800d40c50402d4030100146d40348419952500310805022103026420701c0054440d8900060090350358000401c0060020000b41d0034207a080c00c00050880d00c00484d0b81107800c105c42600701c0040f0070001c03d061040080c4404100d204000040c0460040130000e4500369100800802051210b12803469561420107004c20300e1000951040c80b01c10703c98002000d240c122401d01d060503948501c0cdd4107030b104549141500c00901d102c0380068013500540601000440414019420100f2003440c0070080a4041d000030103000d0b42e51450050202d00b07001c05500b480d040143e2000340701c0100c1c50390028010246045900c0d6103042032407000302074100c00506100f0001c0d1703912030034400400740 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 375891924 1250 375890674 375890687
    0xf04020d06080a1b050618060d0f02070b0601110d12020306040209030307060b010806010305040b0a0905250f09060821040302060304030e0f040506030c01050d02040302041523060703 80
    0x100c400310180c44003000b0a10010070803c0003d11442100580070405082c51100003a490304c0e001140704000800c0ba0340c8070303400d260120b10744182048031010b60320030401280200800900d40b20000440c0040b8064043c007400c1d0780e43c548106801c0e00d0301860384150080c0151134000c002401000304640c2001c601480100764060350380140081c0c8014a1b114001000074956048003004584040e1a0404a501e03560702c0021284c008800382000e208504040e038840e44e003138038003c043c1e00040b81e03917421040034000f0410990400c803803108070722400d85401000110b117034400d502480c0488140b0300400a00d64a45114440445900f100600180307485c0d07110055502551000b0940010000c2c4004000759a9040c01035002d1482915544040c03108207040c090170840b2002c40e14452883c020800c001c07501e000c00c0448203400c0034038103107a0f18201030250100901641c1c1000c2d402904e001107103040310030364210040550f42203e460410100d00c0e400c1030048103ea0041c4550400750601101002030f01521 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 375893174 1250 375891924 375891937
    0x3070609021903080a1404050d02040b030a080d060305010605060a021c09030501050a0203010612090302120a11070b07021e1005090409241401051516060603060b0913020f0402 77
    0x385910404440c01050a211810a401c11350303241000041c480569a00075403071480300184106190309252030240082d18080ba1034101a0059460784004d2800755400d00c0312080403070b4051560b58031906406c0102000b80101c0c0011200b41d860040041140e180510076030741444003540c010406c0b101c060360911420500703d0440824401c0140000c0700041080c00780a11030f003030f841c9005880e90b2602100034100b001981c80503290031714205100c000300e0b034040382102d42c250b50101d00558136010a8401c45602c24030030680040340c01910804103582d00c0490052090728002c88415007801840760001c0c843e07680302c3c4102c039400b09075003101500f1039000e01c000d4004690003c00c0061051581e0b16600c00343c02604075004a03005211300303107000c0420544150407008003030380303d6440382c0d6040201145920760b8180312044000c5020410502c0d01d00aa04284255a4041014410544c0e01d281a401070101d102c00709105011300c40019513095401071000110a400400d00003241140d14244002507000d103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 375894424 1250 375893174 375893179
    0xd02070b0301140d0c090e03070204051614030603070519091112010501030f090b040c03050f0a08091302040f0806040218150d2901080105010b040e0a0c031b11010b01030e0307060902 80
    0x185c00100780000c2e1180010313400001014603a5a801d130f10400003140d500408014207082c48048100040b94051440f000031000f001c0d00d030381d40b5120180003900d0200b4603841954080d460b0303010914540c2000403004100c440c47c0703c1c00e00c090581984054424041da01411901000010040100e980f10740c100100c1841c00c2e42001600c0162900c90010349841114203440104140d84200200481082803030540d10003400a80007000039940c030880103200c0c0165a51145624500c801c810554a03411903000b00300c900b5003c0e510543c2d460f1586d4507824121402c2e4440c18902c50860b24031011140b20030b1140060140102002441c5010040001c2d41070300283d50130b02d00b4a0300c50742c0c0380300c40c0c100032003046210070700d1004103600d030203002802d441c2c0507042170016007070a00040200b0141c05030016003016038050007044056107460308600078240159100260020710b0114550b00350018441c910000154000b40200f50001005406981d114400c803000703544104840808114540e11000c40180300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 375895674 1250 375894424 375894443
    0x503040c03140105060906060f1218070303020706030e0a1e030c020405270102160f050a0c090204150201050903030601120e06070512070809030a0f030209040e0d02070b0301140d 78
    0x30380d00e4034150841c50b40e00300c00450f90740f4404d00210f03280c40c51205034084405c032801850f004d00440004114025044001c0901102c000031a40b0700a440350007080c03124100080316500345c2d590a0007036450b03000d440340d070010030b00d4803c4565041c00c001c82d48801564011210007139100340320040d03004000f42c00074241c003040424201000103a4030750099030b010342900d4494650520310038021840592960075580701a1f8410006000c08484a8141c02c03004e0b43c10540855000741d1a0409a04041031036100a101010442c000b113a0740005070301038800d0b0350220b040c0e0244680848000d80c201c0f0419100d000b250303841800050240c3d071180e44010b84a808074580803407a44580d000c1c1c986400d00981d07105011038404640110b54040c50110701da0f0080441c41c0c11101c038144110000e40703034800c1340450800c001c0e10b0a4101c5d122070103a0125100790380060010030940d04807881d03031a15800f070010540018000d40d8000107035841110181c0c0d05950100c00040054007070300c020054249000281101d0301c602 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 375896924 1250 375895674 375895679
    0x12171311131103010801060605070c0611030c07120b0901141503100609020304061b08041104140907060807230702010e090f0f01120302150a0605031f0c02010902100503040c 76
    0x560740600411500d008220540729410628083e09447c21a0484010050203210328404207001d07074691070444019051050004801120382821445900c0120b0003078420107234006045100711000310707020390103036561038030646428a00318287c440640030014201e8040c0c010a141360700364482d0800c0410014101c900001144041e00252034040d0b109004441e404810042401031302d0040c4010080060302507541030005100141c1406070140000e0102e08200031302e00055242c0f540300260b1011125440000ca00d0001d00d075540c5d0348503134000c0d10009421030001c070f80e4003402482081d001038a045030041d4104541d034480f20b29900040400c4e410400c000120916945400840d603000d1500c07440c1c6100a481c2011084070344010607071200042c0310b202012007011981c00308044864040b01903000100f0307110740308200e002d0206038001940c140504d0303e07210043e81d42e4409031204800e01d86000e02002d040a4026400c881e2400c0780030703422500000c464008580320b1401181c0c01881a1700c400784142c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 375898174 1250 375896924 375896959
    0x901031a190905060a24030902091617071704170301080d23090609030c062709060a1203110601030f031710090b1c12171311 55
    0x300195020740c1500399650003401600c0003401030b40d03845a016181003441e60318151900b03141c591500425418000e0046058120324401e401810803a90000c000303400509103000e000301c03500000c0900c0004105005001d0312100302801c4918441c111588428001d00d00c042c1c005030061400a1040381c9040010449480814070000514007800e664002402c0002c0103202c0a010720368404038580140a40c21205001d40b003222045418004040c0c030407a0b158044140841d24040c0342d040d46a50140d804202c0c017103403c00b00e044244001218100d22000c0c45507542c05d010450b101544e40c40d8100e800848203000c00c52200c0c0000048911901d4400c41c0307041000002400e0075000e07001110f02107628840101416401405900600785071406440681000b0842c05039105d45071040c20601515201c2500b00782e59030b00462422080003c0da9140c5604c91403514a0b04031080c4c501d80400b1038215011505141020107269104224200070014860802d840d81214808144286039215207104260080d15 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 375899280 1106 375898174 375898189
    0x90a05161215030b070917031905160b0105010f02010209090105190305190605011205030f090d320d090510050f0c030c06060f01050901031a 62
    0x80c164500c20700050320b80e140c002e2541e0b4052050001c1030143c4a101207118200e076503140c540c850b0b10b407144100b2a003104010240154810b00c10f00041e415020245c0c9480b050034100241024514407080601c02d1980320200c9144c021000100a0365803c00c261002c0e0309140d000960800f1001e401103142c1e2041413050510030340c0d250410524004000a803400659040416280c10b44207498143d14400700c04003080f1581751410b0b000089520ba4507001c0300d0784a0b03014000c1c0d031a04001102115142d0460094903501000f6031080314005144070340f201213002990849140140390281c0300000190120071240410340100c01d042d90310325404401d88041d80c40888010041e040c8082c0101c54901524107040000440000d04542d206000070141002140301d00c2220201d940314014040c0103404100824089402401800102e6029400c9000c40301e86211600403650403040024801 = true := by decide +kernel

theorem cover : BRFrame.Cov 375719424 375899280 := by
  have h0 := BRFrame.cov_init 375719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 375719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 375719424 ≤ n) (h2 : n < 375899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
