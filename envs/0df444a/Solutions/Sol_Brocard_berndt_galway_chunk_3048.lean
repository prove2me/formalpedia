-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3048
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:30:34.369964+00:00
-- url     : https://prove2.me/submissions/b58dd1e4-f6b1-42c5-945e-c4a115e9c32c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 548021582 ≤ n < 548201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 548022832 1250 548021582 548021599
    0x20711030d02120c010e01150602121207050d0e060a09110a120201051809070306060f0f0f0c0201090b030f071d030706080c0c0f0c03240a110708070b1806060f 70
    0x128013103405410044094200e5510f0300c5003d0015050394103c46081e14020b800b21039070b0905a0001c000a8450840d211424070380240200344103500c03501c000c0100f22405540858903c80c0641e407036041c0202038030403d0701c0541c0c5817041c10070010180140755180c2d104682c41d050051910111810361021710200030704001002410800c10b66982d040b03142c05020203440000c82d0301c2c0c1120082d0050002d800b031400401d089820001c260340c41642048209412070b920340d152a017001030140d50703208807400b0880c1030043c10040410054416006588128490340503000241807164001d050080c10030b5503035003815481d17890440292400134030310084614501e001b1234990385441320f00001d40107000360820f190113041c1103d24070020005001090940440c15101002c2882c0307082c0c80c8448040d007104140f0300100e80094103c5e403156200312100702c442d540c1035190075000c0e5104405580b00020842e9401c1c644000d10469144101000705403003d148028440c609001c0d00280425280780c2c0b6681c0300303c80030f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 548024082 1250 548022832 548022847
    0x30d0e03070602040816050d0f140312040501060519030807231902090106090f0308031005060406050301060306120807020d0629090f0417030703090c030303020711030d0212 76
    0x3081101e4109801000464a0703e455207821034403601d41c800c8282d8003031351700b407070100d035607c0c0c22440f070f003400c40d401016008001100c0c1d0314214144402840c80500380400d02042684007501910980710f54498000020110304000801900c1c405a2003440704001150b041400044c00550443d600a13820600c220460140a80800900110441c0b8100107025140301c03080000c0884003011807a0b40300320b80c0340340540e8843d40c04980d0441e507882400200380002c0c00c01c00220303c0c640000d68120001c0c412107103250f0780b07460114015a00c00c1c0d024100103030001004110069051042d103000e80041100d4985070342c440d407105a65070040c514068464a60050160100504c40d84040690340c0c03088049103010250210384039071180002e2403540251407050000c0d10420358526140d1040d94002c1010380d240c0340200240070103420050001d4281603840c0b51039808034400f8228400118860703503025941e042c5500d0007040110385021514000d07032000306101d08076900031a080d40700e03440c0201c1d4251101d00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 548025332 1250 548024082 548024111
    0x12091215150a03120804260708090411120403020d031503080307030f051e160206010e09160f08100b01231309021e1e030403050c010e030c0c030102040305030d 70
    0xc1c035074802004d50b0500b02e07a540d00c49400045d404d1140c0d0203441c4801c00402c01c004c1114118040004000a5404c2004003d001548241c0a00940070000d800003c0400d10172000f1a211b038402c55864012546240030001010307030403c0400c01019603454140b020703130548010100d6010950100406007000400011080c610907840028541c029420621503807c008060340c0ca0340e220b1a00124041034228006480c1c00155594565900b40607030090009070718044a00712841006070040040780204240a1180306800c0500703000b40403500d224015507841c0c851014a0300001c005200b04a608280403412180e82099041e0311407803e41000f20f201316540e08410000b0b100b8161403601080d144600440c030a2074650107000700380665103030b13200018149400300031749009018880c0c04c5c0c1a0a80802c4029000503409180c016200b81440d50801e42c0c00021513094445c03c0800802c1e0368404a0503c0142108021254038800c0c2031300214542419611440d85900c200308426035626180e042188104c50f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 548026582 1250 548025332 548025349
    0xf012703050d0c050a030e03030c12090f1209040e0d080a020c0106031704031a0c190c050f15100807050d08040510081e160c02060c1209121515 63
    0x40e00b840400240245040180c4142c2100d0312040009181982c10500e1041c00001c0300e0240d01e41c4041c80341400c103448030001e10243d005118005074000c040c2005140007042045084080300810240d48449041040c40120b030300100f40710001d5444412454140da4004101c640c02040d14800581c0e500c0324029250701402c2c482c0e00042c100c2002c0760010312064401005002924460907158600f0001c00c4040811444245d4540452007020003001c4200102403140172035100041c18030b5980c02005445040c03d0400852406010360005004c034104030449a115035407020444c1e024510032800c000409990f030500d8018540a0440c1188080a00070394406840041c2401404c0300c40f108000c182c014200c4006444150004409041b08a0148004001507101749941c01c080d45041010300000c640482c0e52202c281e800c51010009929800010b1000140d0200d00001459440c0c40c8142480800c255429034404140c02c240c0c095460250000103168100c0440c0368055510b04c0c02c000040c5c0d100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 548027832 1250 548026582 548026597
    0x60307170622020403120203040302060a03020706140f090601050613140a0b03091605011704030c0609020a0602070527010b1c06090e0f010606090513090209090f0f01270305 76
    0x2c14540000c211030314a0340003003007928801c14201c0c6803884501000d81c1d9900441c04000d41c003040601c4480071641c0304e94003812a40717018040100e183e00d0060450392400d14180c900e6001034420f501041040ba00c2000703100d004100540da228500200047d42d0280c42505000392007402c280038482401c1991507010400c050703c03040d82615528200349d200aa07450084400d14920320703a40f80c10000700e541c004c042d420094044848031030b90a83e0b072a941182c204c000c40a044455a03660614400036845128105010f05503980040c007600c2d040008000c04605a8415040c004002140200d10720110200203411900407050807501d0b00c0506118140c27070100c010301d41c1c0b0560b142c0500064a18042d81007211044074840944548080c2484560301313895440c051040840d03000e04c002c01690900c020200440c0741c04000c00110640c02d6400502c0e2150281d580300340c6681300e0100403079140d0052001403001c40f1020020000d100b005019080c000c8100c0800d112452601400c2c001814000d01c1241d0780c5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 548029082 1250 548027832 548027869
    0x2150d020c010f0902030d1b030813200a12150b0d060207240e07060809011d010b09060d12030c0e040c02160f050d150204080703140c0603071706 64
    0x10300003c4031080c000c1210f0130041c1d1091190303c1d05044070710300a0890100c5c030301d0f81805102040d096924182e8070342d84007500a110360541001c010020614500ca50a04c6912154820a07503580e08420400303403980039000407034402448905400058444a420310300800d50403000320390072071707800300003020500301d5100940070340d000041d11020060200041c410030300410046c10011590030100d0310441c0c0403100ca082c1c80f6440240e091008901480b10380c2d2b07001c50f6000011400094100440030b00312440303007500d00e003603440340b03c511050310305450f01c1035003d5415110090305071b071103451300b009103000c2d910392000340341e925140d4044070780c4902548014800301a2051007200400800203680303981504d040440c003181184042025040c6048003006c44800400c0c6c100000c50a072154882036029554020440d5805c1200080c0c400d81440348200460080089074011950a010103040050400d0041d21a5904004204030183c220f034a403c540c0c402041200002d0f5111004a01881e04602c0780424 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 548030332 1250 548029082 548029091
    0x501020c090a140c07021011060609061f0306080d26040f1a18011a060c012414030601050a060c0212030f0d0e0d171b0a0e03060f0402150d020c01 64
    0x6a020040d80103241c014403e840d0b40c034007e16102d8003142c60b89401c000206290304840045105494030400c2d10b900104000c0c900b0b105140002c069800c02c8049401d04000320b80c5070141000030031320030b12800c1402d4100d400c0003a402c40b0000c10507604807800b1314024054808c0e06010909118114402c006401c0c0c0c800c408004da070180b0304c00c002441c40100c552140048418124020345281802064030300911195494030084107041040380d1904101d000c103405641e240021900b0701038403c800201040e244442e40c41c000d00389490000c210310402d41160203603008a00402c103503110707000b4002c121116071801c0d000200701c40c400121207809076a030040d02d600c4049600c08080e612100140b00072108200200003800d01403c40340c1e160452400010b021411552002c125a10002d9130142d00125090740c410682c40c403448123544c207402c2404064005500019500340e42d090400c0341c42d801001d480290121460306500080c0031802030075014032184804108098150115010703503803030f00a81d800920 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 548031582 1250 548030332 548030341
    0x80a030903060b0103060f060c02011809062c180c100203040f050d0c03030f050d0e031201061107030201120e2406010816030c09120b010614040501020c090a14 70
    0x400c00c401602003a03032898584407480503a503000b480340c101140c1e0162042d00915240031340130342e21620f1503103050303040c0454408060140c104090544019084103400014414103040c0c5281500f04e28208001c2020760422070340a500a04030415907009900d850052060b1054502860824009808807600002c6101e01d0724503680e004800307041030f0340d00900000da06070355800400c01da561113008041c1000061100c14004284155129880c62820f400d0692820040c0c8040e04201c644c90f454402c010b800205012486540c00c0c80054010f0811340b511800c1711b04164042501d8100c00d00c00281407012040603111402d01c16003040e07808904107808c1e0359050541d40002c01d5803010003a04843c10484050000d030196028600f080c1c000d000d118010312a84400540a8004160320303420a400e010401c10700065480400101000c11481a110b45400e540b4048020700855280c03004650361400521003400981d070700280000210f00105e4440101f40c880002c260b000344440e1030920340341c030001030401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 548032832 1250 548031582 548031587
    0x2010605010305090102180d02010c02060d0c021c0834020604020a060f050417100518060609070e040207080f0c0f060f01030c170f1c1403010e1906080a03 68
    0x11000c40e402070b00c06001c0341c0ea81c60002400c030700c1400c0501210140484503980c181c1810b40f20030900d1031042c100b601d00d03150f42d9000a09030750020203180401c59142c400824041d1350520034040c0300d03082c03482800ea084090b4440640020720041c405c00e640f90705a86825000c0041c1c0702c0d4415101c840c030039a80005011400004c9d100c82c0102d4040e4042c003c900070015400e446043d0700c4c04145030311f55507581858100464000084c600781d5a031916485031594616041d10346101d440d010f550076199001c1c4405029000e1818039400408443c4190005020000785070f801c00c0006600031800c6800580d14411071900b0700181c01208a0641e0320754010a181d4400321001030880b900c1a04001220403658805081c05140700d000d020082081e00d00400422400040c0c0c80c0c04514200b0000a561800c030500b180c9074945410b1500100c1030840d8000300030b0205801c91070004010790360501852640d030511140c003024a60140c98004003400300f111540d00400e0a07400302c0f000e4802c1e1825545c0c0b6258a0500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 548034082 1250 548032832 548032841
    0x30311100f0c02151006110a05030a0f1806090b0a05160b071706010e010c030203070204050f0105040b01140703080711030301080102030414010c02120d0f05010902030a0e030c060103060b0a090c0201 87
    0x42805481401c000d5000500d4110b032540c4200d02004114032078601b4002c08450802c0b00c0600f130000c3e4440c40811800140d01400601a00901b513581c1040000c1d82c44001000310030b00b1540c03a5030310030189c1c5d01030001684c09081401a211661a01c03591914450801c80c1c0b40d05c00d13800031000440c140c40542d000c000090700b045004041540d80e02c41c242d0090280c00d404c01900b40d41c006e010440401400009502034001c072403c02d8000e0059a0070040150041010f840007120068239280200d001400603203400c2c4540c03240d4030020300e00504e1440c0c1c80b201c00031244c49070302c6003c0c0c144004180003a800500c145244005182c43c03100392520f039695074000a020b9001034600b210b0a400c40003916100500520a004074a00c4650080401c0c4c80d503d80c2c0300c3c00540c0303e200103000c0c503600c80c0f481c0012030080740a884d00034101440010790300c0ca0400c82c3d20301200c007400a1100d05030810003080c0000d000001d115030540e900040c001414900c054006102c83c82c2590010000c0e6091101c00803405806521 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 548035332 1250 548034082 548034101
    0x2091809031b07140f0d1a160201090302120c0a020a0603020c0c0d051509100c11060901020708030a051003060f05040c080d051c0b04060f09150b04030311100f 70
    0x10420880e440c0c240e42d841d03e445000d0036201440100075400c1c03600d80740e40204d00790311025201e6400c2c103140e921005140e4102c46003229414a056040c00b2610500a000900812651000304080c640343c0e0303002910f0b92080c0034000b03003600c00800d0f040d21401041c8480255594001d040802080d40c031580070700a5000100c0950260142030020011424455452407241ea4444090400480c4151030301058030400b50103102648644105039110000070702c2100300c1c005c030a494035148041d51305062882c246008200b940e4a0740107000c140c0005a841301a81d030450761940010a49564814825811902c1e030f91010f03001c01d040c010030310503502981c0c3c0300354016406030361202100c80d154002c0790303605d201d10b9101e8400030301304000600d40820000445000601f00c1100801c0340b04210380054103072149a000001c0076002d22404100411551040000b042c1c411004030311130900e0581c07120f03214003803488054180805000410b008040c14480b0600c0c04459003000c000004004800c040203146884 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 548036582 1250 548035332 548035357
    0x21e0c071d07140702220b03010c0c02150f1b0a0b0103030905030f011b0c110d05010c17060f0d150f021314030c01140f0d0b0f0105070c090209180903 66
    0x703d0040b00810f550121005107401600c0004040590b074407500700c0303501e440360000c0f10a50b40d03e01c0c0300a0755002e0290340f0300312100e5650552004124010810901e88124005003100b50400c008c26030321400c0310544203c1120788000300e200c1000e40014a0900c00002402070004100000100815805c104e49000340c2e013042d801c80e034940f041116010300302c418904510782201d0159095031801c2c1e01c20355000006034170401d40c801e410442c0038041004081011004c48082e510f40a00e210b45030782c0b0914442c0e0b0003c1407c0040201e08100002c51244040a00001e0051000c00c0c4200c05000c82e11704861604140c94600f000020707a0480f1080007904034107081c02408070780d1400082c6a60041090115151000f405040c0f002e003010010b580409030840e031415103110a00c0440ba007003800710090310142480c1d0b6804a2180c0c0079400f00030641c04034210701814080300303011b820041038040c543c9105a4640c0701006a45980300ca0004028800c1d0000000c401e10130f040070001c0040703020000d44403006c03503034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 548037832 1250 548036582 548036597
    0x80601080a12080f0a0203091f0e0d02060f07050d06150e0a050d1e1a0f0108150103030f1409040e1006090509030a0804170304061b03021e0c071d07 65
    0x40700715a200c1c0150307251130f00741c40004086581d41010313a0043d604210041e045a016445000b884075600e51000b01a48002d5640e0302c0b001c4040300284202c01d0440791072720181c141340c41d046a0b403a03c01100034000b0002c122011a6840c07000c0b0042d40300304080e24801c1d024000101c0c10290041910349070511041c025548410002498100020040030304d65100503c4e0441072040c03000040d0705210440141c0340e4042c51031000d26440d00050070301d40108010407194040b9810b04510750701d400c08829030482720307828203001000403d901400041d0391000520707011000c03039400c02603550a4090001c0c01580585070416003000100006a4648100c4a0450502007540e49912400844001b1242242c00d90010881d400b140e51113100c1080d40603125031000c1d100384504040007078840d00b0856003210041d9031488401d400b90384c00810310301400c1d0740d441d0642c94103007001d0714094410100c00d226108200c01080c0307078181080900043c4054540154442d4002e840301c2104850318105607042c80220344030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 548039082 1250 548037832 548037863
    0x10b12160807120f05010912110601080307020f063403030e0106030507030b0907092c1216080d0203040302012a090e1305011103090c0f03070302010f09080601080a 72
    0x850700030704035a03410481008491107512070b01c0a0841135001141c080d5a0f41005900240900d003102945040f01c1d40c460010b2469105c45138540030043e0084c07a8541d100303014890060b903a00c0c154054021098171820348461101442d82010800c0d5010042900f40030041d241c0398000c000303c00859980642d4050001b070314448a09404c9500300c0c003001e000d64010602c1440441c000f111078581145250084400c034945c1c400c1940100c40d21035000c01c8080185401c480301d50062144020f08568406001d080b0b07040b454400c104442c070810042803889001d01c00c3d42401d0100610649450301c080ea0300a6589181038a4024020407c0c0e03030031800310f220103044480280d14000e0704059400e645031941101c05081510795545041d00910301010180d000110000042003801201180704000c03800584030308004645070704120000f1405c501a841d40c002c0c184165500068000480b070b0203081c84410b101c07110204444440d2640c01c072124500c110000000c0205000894036103c40c0940740501003d0750 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 548040332 1250 548039082 548039099
    0x7022205071803170c0304090609020a0e09060109031e02041107060e16091a030102070c050a05042003040302030f03070906080604140714040f0f0504060503010b01021b03010b1216 79
    0x2910301002d440130003015243c00b01c2c240c10030002c0c001d024202d800c99042c42d54440c1103005403251608401c192540116051440c2500304180e0360701c01c0812100342c1b80070300d04a40001d08202c51703440081c24000d0480020030710301550343c24051034150040c0050219050000c5c0e031600562002d5400c483c41440c3c000c5603560700102240380700208e003025007000107103481c200c070000103084081803a658146081c0406202030f90240b009002e030600c81d08400e04400c3c681400c0080000c0d06034881d6004e6414400000c108404402c000c040c0c2c50307030b80d0000640302d07140c0c0c1c02c0032407a40c0196031320079506800006c18481c075181c010320031201701c6a80d90303220040c50343c1d02400d2000751040c007441c1d02d000220360170120b50403c0c00f40d0700408110b8542c0918a060907921002003100e0100f0360f0104040c0c0303008840c24085802d113030040d0000350406400030720904400300d0000b903460402003044c49550404644410042c3d40070341040c0e0b109000240381032202c80301c0c11070142d1610700111328074451504440700096000d4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 548041582 1250 548040332 548040377
    0x30c01020d0c06020a0e130f0b06090a0b0c0c19211110020c09070f140f0909070507050a111306060e060f04080105010806070207080a0203030f0702220507 68
    0x807280d0391030300b000c0c003010f0343d89001940100c0091410f20400ea40d081c1e20a848200100060303040f05031012682e5008100500110352142850714010401084031948580740c0c04c43c0303e401c84100da00c0e06940c45103e48501d9003410400f00090b40c4c80704a0040c3c80b61407d808804900641e022042121461614a0320703408489001d03007402004040c2481a100300c83c0307005c0000b9804001c00d80182d0302c44104c14000101e0200b011a61175000c1008104540da1003a80140350b04c44583c00c0d1b15107585440040032480300342d401901e101c1c80c450001000014a070034800c8080c0d0f50490350200440e0a500c4c0945040a141482d0102e00b50041503d01a8603001c06050700030401124940d031100600d400103c402c0c000700341e0141d2542e1074001420000090747c2c00f801d206d568001e00381d02e405880c150916240007801c00307a107644400202d9001c0448003015071b50110850b84d0101c10754040c0380c1d4a80142c40030820700213045400e15100541a907103400c5003000b98000074881c400c03176a035540503e03071802100031350030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 548042832 1250 548041582 548041603
    0x1508030306010c14030d1d0c0306060310021b0304060504210c062703060501151e050a0e0d0507180908030604050603011b05040302010815090610030e0111030105030c0102 75
    0x1181016100c000c20610b444110459800d00280c0386800e545203171040c1a034540c451b40481c14280747c4114001a081442007035070007503003200905903904100c40080d5031a56804000003c503a80010070020402d003500c031003000300600000b40e030f880f543d031500c4c050042d030000d01c2041c0d1004021102c900ba03035000310a142c1d801641c8145106040c90501c40115044040e0f41050304d0619503200ca203248a41e800640900154803c1001103010340c10702c1d03070750b16890041c03103400c40502a00244d000740d6159510a910703200119441c00e00d44074024503c0c21100c91510090054001000f20981e409125004c64104284c0e0b659015a01c811881062030304111039141c2e601801044060000c580c581c64160030040d003010004001164405500c40744c20054420030400d20003064000400300215608000d0055001060080884030302d102c010100c0c50341000109400e20806110308034608860180d0302211052040c0d10081010b1565038000c0250755000307004052103807040341c002d5442c5610001d11042d10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 548044082 1250 548042832 548042837
    0x30a0810180e01021c021306021606031a04050c030703050601050c07120c05030f06090c03160605090d0b090109020f10270302060307120f0908030c0d02040b040306150803030601 78
    0x388004009071000400c1c48003500072a954007008545607210000100101c1110b201d500103907129014a204074596030035501000a540201c00401c030081d9019403128225456800d0100b050103400361081100f660f50204a17501c1440c0c003051002020300e80010398403592140e10100081c2c0c5664006480b0360140b04c060703d00662150340c06004d64100d0000c04010148a07585a2110580b9140020b0419000b403255144a50141c02000a42e0300100000d540050045e0301508000c18002c1c80c820110041d8010f41041c450001411680b981b50500c006107582c0e0880c0c0b000105003008807900d0301030492080203a01c2020f0713642c8032002900d00010118500b101680703900e03070705602c680810160202c1c99400a0400d20041c0400400750311780000441c0b091400c0d54581d8650800039800300c0442d000342402e1240149002040e000184101c01241d41113540354041c2c1d40c4504040c903d00c00a441250008104180c02160000410005801c034092101060b116487c103140c90340d001a9403800100c480d10300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 548045332 1250 548044082 548044109
    0x103112202070f030e330403060207080903100b0a031202031303030306140114250506070e01081e0105130905070b090301050106021b100e040524011d04020a0e030f030a0810 76
    0x42029941b5203101c1c06400c800c02908190f0f50f0f031180c000320381280300160b030456400160030180b49406e0044542c074040c4a0307001c0100d400000302048107000c6c0703404014180c015201300300303800c3c60080095410040070407640b6a070386078603860020080c00700c5105903140c54011025001c40c0b9030003481c0460b44164845007003402c040d10401441840c1c8818801e00c40315194502a24010490521031644551034070788400701414000710004208132030081c0802c56083c054031810700000000c030700980c115082120f04000d90008050941d004182090000f841403240413400582c600600b00545400c0e072041300200031a03a81c3c0c80c4140d8507500b1452014000d0340485440c10041d21b4641e500c010020190700e44411100e40000c007040450b03d041d5409060301200c480b112141841c6040c85c0c801c070303c2081c600344a2000042c02c2602c030411101d14050301c44e9402050080140744110f0240e01d9030007008003102c1504400089442c2c41350300c404410070001e9050b40025824070740880240d400c55042c11240708 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 548046582 1250 548045332 548045389
    0x201020f120403091a22061d0a09020714012a2d08090705060a05070303050406230718030c030b280606080f0103112202070f030e 57
    0x740c081e5004008030709004080001083e0103460b03801020842c40c030b54690703c0d5035005400e03c42106925a00030f007180368138120300a00c199a408500360340b0400d10301e420000b40c050480000380c0485095040f81075141e01c08540340c000d11040603600d1000304401d8008000c1a204070b040b15824800c00f4030414480c418640c001500b03648681c00c501d85580f02c4400c400d040030700141402c1c7c2051911110040042e09142c1400808001030004800803c0110340c02454501c40c910040c0213402002c0018041c565038600003001d000c2d040d0000782c050b0300c0380c045010700901466403070000b000050700c003880020310035110109400058120b500035241c01c100000201442c41d40c03502c6000c0c1001703014004e401a800c0d61036103d10030764a1108174001c0c03490808241142000d4001744503040040041c540040d0000040011031505c00d904010f102c02902e8400c410210315452002141a5840d078009061000600c0020301c42c100c031f94075100510075a10104040d90741003c220b204006401d140040c825040c1012 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 548047832 1250 548046582 548046607
    0x90b041d0408090d0f0b0a05270111040902070308090c0a03110d0b01080f010e011404030c0503070803070302130803030906070e0409052a091003030f03062408070201020f 75
    0x507500a1040010707a14000d03520340880c02040441c2012100c4e540700b40031110070050503040e03407a40850b07007c070308003c689080114080011314038404d03440281a007010325907821000703400681e6540008081c0507902d42c0e6030000304000390b02c0360078207a0020b81518041420300c000460224000c203002070241d00000d040d511100d42e52400c1d4010f00d03501810404107000082d50540c2e60354005d00100000e48001882034a4040c2951903908511210307174949883c40e8070360082807800b01d42080d010300d0a94945401464403e146200da0744007c1c00044011040191103a40754009004a86c5015000c0111941da8486c050380c1e07010580c5d10507501d400c4500040c0e0403911a0050804203a070080010a00f80440c0e241c05003030505500c45a070340c88001001103070b0000c403010303241d0034480405d880c440c0c00b503d0000c40e0700440010a00008082100401c81004858442c0d04a03401410240780740e44480d2032007446000e0741c0d6110400c043c0103d00e00c070002541c007a00602c280c80f00c90b4414440070340ba00305203d080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 548049082 1250 548047832 548047889
    0xa0806011812060903200a0b0c130e07090e0103121805060c0a0203070f03030816020304240f0e0a0311030f030309030322170315060d0b01090b04 64
    0x100c100c1c020400340c0001e0041901c05410401502400c00003450440c41d040007000d1114414542d000000814220110164005170700c041c116007001400c01c03151200c0294885c5031040d100603807005211380c81c001c100d00303094000f494040c5c006a11000e89840d41c0d0304c02c10801c814240720140c00c003000b07101101d10550040ca0300302e00008800c00c01828a075101e00c00943d2540080c181c48085621005045046080c00c100c41c0001d0071051900443d11440c5560051141c9001070550661090b811888032815000300306540c080c0c038010380301142c0300c041c0c2114072500664542c808400114032181c1c69880d02d01680c20210005c40180c5520031050a44d141d00041c203d0760310a098040c41030b0712031421101b900307001941c02202070354080c55803030030110080110700c3d10300002062401a242030010028007010064644e1041c82d0305581d80b0380c1d0f01e800d0800b10b0342482c50003450b0004800203601039070003116444210801c800342c884107035a03a15080e03800c1650266005031052452036054507404001c40024 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 548050332 1250 548049082 548049107
    0x6010f0504060c03091e0f05030127050a020d03050901080f0601020d2106170609030a1713020d031206320d06090b060901060503040507091a030601080d03050c0a080601 74
    0x2007030449170355a04521845860300c4180041e84e0062003809010038075251540c1002004110024001d942d2032900c50040404403052001c250030036a0010410032105000d40b1000715001890107500c0c007000c4c100030b40650300506a2900080c840b00c00681030925400207540140010707030090085086503801610703007660390f034290f50901d64001440c00c080c2c0e40b03901645002e8050300f9251224210341144c01c920b01080588980d60541081c00107044003540000900b28060918503085501d4460f84c3d00441c60003080704001e908031a904100106042c0c1291071125200e5000c42c040100e40c0d41d82840c20822a0034840c640850303028058900c00c044401c0014030001100100f100102c0259540c070001194002c90089071200740320020001940f410401e05801040d032411300c0361940c60203036a10780e00c904290007a42c0c01603688441012035610400c1003002c880e6000307012a03d4030b503100e02025039104040e00120700003d0500c0c00280ca404849400e8030780c0104984c0302d044540c3c4420005403a90f00c1c0010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 548051582 1250 548050332 548050337
    0x100201051513060b04080f07050916080a020f031305160b07080309011107120f0c0b0414120a0c170a211812020d081e0a1103180606010f0504060c03 65
    0x8a020030316081460090000b403080c00e00600ca0341f51650075aa0508540e41e00c106d10545d4420100300c20720604280307008502d49103290640059540d84402c0303009008440d640154088040100301132509550844468103004d1030448000a010403d10340c80002d0728001ca4854510602006000030207030805140c020010030004600c0042102c5401400c4e00121070585420500c414241c45464020602e01008007180c684002c10484644441c038082c9000b400c0180030501d0025034030318490301403049401c1800c04111041d9a0007440600812181e0400c2042d0781d00540186540e1100464004440320038070303e13840345154903544507000c000c032a4404040d5800141c40741c03825040d0341000a80640f0251042050b03100302c00070f21000a19003200034020106202180b81071201c1d5091405290b1070070b80103101202d0650740c0c0c0307072801e02c0540140d190151114170040305002c990404a0f8002803620140d004658403a95034000454510310b4010800021500411091010612603c0b298141034000d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 548052832 1250 548051582 548051591
    0x40302150d11070317070e01050904060902031503060105030d080f0901150b0a020f01090c120602070602070507230604050103091a010f0515070b060f220209100201051513 75
    0xc0746100540e0307441c0070103564040002400004040e04540300f0403581c406a240403e543c0362110340a058003215000c658144403010401a4559540d608690098642c0300019516801c0600e05805111030710380100b40301b402120000700740f0303003400920402c0c004919074820029886011201041c100090501100e554880310140404590182c0c0e0b100181924034400d591220f60340c00c001d04001078140702c0d00c0b8503410b0030302c0b650100740408066025201c0046011304041e482d403a141000340324075440200083e00110340c1c2c00c18088041181002c981c40303039030118455010b42001031029110804042d6008005010178020341d44a54094245039120b6030b0901b82890f2899040c40e10b40109038045150264a40e0b824809414070341d18400c0b900034a039480341e08101095130755440610300145200d000b0302a00034070f845244e07103221a114003a41140010107102128648084c041d43c0304e8007040d40038000c40d20680c42010301c14401d05105529074640740c5c00780490711007040040e0800c000781060080e200d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 548054082 1250 548052832 548052847
    0x10e03030708061f1d1f050a1812020a050603040803010e07030905100507020c010c1709042c01050c07050604110f060a0c0b0606121503031606021206031204030215 72
    0xd40314104081130003502d03107400d201c840c458949650841181c1003405001c0e550242c404a103403a444005590151f400c01a480e60384c10102100c82c03595030055a102c070f10400d440041c210540d00b642d20fa545000b0768405030099118400c0c0000c911007940c004204d610304100400c5103000c010b01e01c54115005103008601010382d620741510741892000070400d03280d514401d02c580140c041152800d491403e00b440d01c851a86900c40340c0c8103031500216200e0851000610440c035548903840920034114034040d450060500000b031255900401128540e00e610384004a00c0300400c0720240c9140c00d901174002e0a2642d501e03501d0010118851840c1a00181c002424541e642d031410044c041d0180196160340380b40c4014180710081050140a590107400c080007003141450b405c42001d41c3c0f11040004c590341641020000c02e285215028a404500088500f40e208001168000b0240f80000820288450f15060205920f90a80340e0840c03001030010001000182044100030800000b40304055007803644 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 548055332 1250 548054082 548054119
    0x150d1506080603070501030605030c06070f0f050a050f0105010b1923132408070e0315010e070f0504060e040204030b09060103030215010f0e060d150f0608010e0303070806 75
    0x9412480c0800c24960400c080390504000c0d14008107000d2034203000c101e01e40001300385c803080790a2a02c4d00508000496505108801105030303c0703d40d001800d000f106030603091442c2c480f20496001c581d24081d046d0039120b03042050158506030303440803030703194030b00040c007150f50143c802c00006080500005400031964100440082c0000c0043d1030110b556508143c0000d2815032000c1d0059000008001001003840c0502405288492020f04002000780c403401400d1703804418448c5000c3c2d152040e0004648082c1c000c4102da8100c0c0c0030603900101c2038560010a60307003600c0e61100c00c3c001680078482007020307922503041c0200308040600011b25040e101d4507030581d5800c0484113401c09511031001041010741c10418807641c0e9286165005140d41004211116071466110f5800d6140341500407a03059650403541200349603225154402404241411001801d07040900304812882d003840000c41207018000e01000704c034540c02440c0340d590341980c00d88900174050b007855007000032150121041003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 548056582 1250 548055332 548055371
    0x30705060a1505040c02251a1804180b0408072108190b0d0507151103071104240e01080a0804050405070203160c030b01120305030a0c020c0a0303050405040e0c150d 72
    0x80c1c03000d4100341140c1c1442c0400c6500d90780c1f04c510042c482c004101c00c1d060040c27032042900c55039001307c9001c0b40c0750040d800c0441032070030001d2015200e0b03000c0c141400100040f0000070100742e8468a071224100d101c40810390801d12880baaa400403510410001c0c0b01c0030110f81070300358000700401c3c000821030740d010f01140e50521588811111a80440f10501000036003034580c411703001103071070422503883c00c0d9030031951240250710340180817042428115000e83c0d80c42d00040c804101107411800041120030240c050482c0d00d11969a59118a1001144aa6021444d08de1003600b101003585001d19020510000b000001d242000f10300082c000a58100c0d80b22086140c80b501400960b60840d0450401c425500b01c1079116040f41c0c40564110390000390072109a9600c01c4440c100014213100354a000d9040528a005c1c1c01c0c0d0240d0395030340110400d6080005003044d242d058504020140806807016904c001e80e03144607034040404690ba100c1800d1500062024003205140840c1c00302c0b5410320300e000d85 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 548057832 1250 548056582 548056633
    0x1080103120e30120702280504111206040e0a030804050f0304032006070b040b04020d0213090605090105091c090b030f0105040c020c130207020d050d02030705060a1505040c02 77
    0x41120301e00b01010f104010541020664040c1c6500e0411564001021070081d01c01b030110039281c29604120400b840d00059004240c043d01c00c0c082c4481c0440c4181403540048000c0030f59542c014082021400c0a10891800d10b107400001d060341d00711174405460441005100701d03940d1160b040c40b1102c428040c070240000314882c10485034a680c0e40c4503c00c14000391603514038082c0d0f40501100c004202d1400003140c01170b1700031040d81050345443c00410700740d402541010350046103115080c20280c002d81d0203141d0311401074034100025141d42c10800c0c20b880043e1401c0c8810340c8542e00010002c000e9400c2600450114200124034964a48c0d186800b604215070301d284080c4000010410b030b0419004401d0004054030261070b061000a0009090b0f8426000c51005140d02285d040c0031500c03030307000c60f28189402000f00c44004201c604000d40c0c1394051442182c280c01400c0100300c1d074500c3d40c000e8290648a9054140b049800c1109010007007064042080c03c520485078018001c580700e03a000d4966 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 548059082 1250 548057832 548057899
    0x120c0c02011d061c14091c0f020a0c0303020c0a0f08100231031416060f12020708040609050a03170a0c1a070f0e060412020a180e01060501080103120e 66
    0x4090071081030690580103203035101503003054010b641d040b50140d58032060180d10b800e0001c8140d818448c201d18040025a0043c00344040d200007105268000503400044107003110540d03042c5d40c4503440034810010760f01c200300366a0b01911484c0f800c15001d801414104004a4107205280d140601815004000504c0040d048403800c9080c404d101015100030700004401e8020040c82c240c980d0a02e1302d4000e90b100d4001081701842604407500d01c0b907a8491000900c3c01c0d0709646030185410149007980c17041c0b0409022441c00400082c55040040880301100c3d0890307901910070000d4015140a075010081c10400c02501c09100c0c00014451100e540304087d06c1840070b807031840c1c04c0301c000e0500044084050240444000240c20b140d0700c1d58110380c29140062aa0202c20b401840810030100c0107410844400090162006082d40143e000c030214141003c024020150744000541b001e203020700005d0a207500800b445800c60740139a0300c96450041c050140900030426100291965041007410101c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 548060332 1250 548059082 548059091
    0x70605091507061514040f0203070f0f0e0604090b0f040905060408070206090a0605120601050301050a03140a2a0b0703090501230408010b0a0504180f05030d0c120c0c02011d061c 78
    0x10301d8107107842000d0340100c07900e07c114914240703641c01508408900b44004200304070915859034a030b03c90481040051800ba08240c1c907140c442a984000d80038009a043c06050000700b9039506142c94055200d245030440050b208a4450f07448551950f4071000090b80c11810400c03880f247c0d501d40e070b00c0010003031100303580b10b43d25020b8030054003407946000780c07005041007030500041c440c1d90f03290881e01040701d0307004800c0100d80040180007820600012406007a80d91590210140c4a07a001a442e130030105210b0701c0c072456912010442c96a003d100401790000c1c1d8203003018412540200e0074181388001840400c16151202403069105510940003480c003651208556611802c000c101103016103022582400300e0800b4a21105554190400c00b810a2001200d10b4040c05800d104451480c0e5182e0410300c28151000d0010700130790b000c02030072036442d80382128000c091449400545510750341651010711003590403003a00c0300f00c8070000c0503561100041198221000c3d440500b1058010790590104 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 548061582 1250 548060332 548060369
    0xf0e01090b040615030b0102010b03160810020418020c0f060a06170f03031f0e070e01120516031104080102041d220b070905060310080706050915070615 67
    0x400356044410000e000b141000401e1165100e0002110801c00c964036002030800d51490041303025140c080700709500341c003034540c05003409403920001c03c007074504600c11120f65000c8100c00030224451442a1200d40a00704280884011150020602240140105c03001141d1642140382081e40c05c1c3c848080c0c0d5561240c0030400c03800c0c1707031074072160310b841e0800600b070840c074504075075030301c0b03110040064aa4052100e28031095070f00820070040a800111850324651138241000b60825009521090104065106414604103a40a00b91180d03844100e8031003480c03c0031505a01400c030811316400c200304240408584a0002d04c058801072041100c022400c0c0001101c50525800c050850820000d42e1394984c409800c0f12500102555031244840007180e5a20310708a41184c030740d411096201c00e00009028049824000000070f40e100c010a41d6803040c1d030341c0790940c0c2910a01c61031981012880c20501040d0f0340290141c100c2e240160390105000380d9004195400245680004039801120503040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 548062832 1250 548061582 548061599
    0x120a0e010501050429060408100509100203011211040f1811090c04030b04020406031a0411030732031911010507210908030309102f0a03060f0e01 64
    0xd50042609490030010310040c10041c0c2040c0d1042a26003003007080c0d507400800305d51112004c8500810a840c1558000440000600003403c01a2000c0249204d400802d032805c002d113200305da040380d0b019068480c803492030f0340e29144514004c2001d198000c1c0e884103c0001c903802d50040002900300c10810050014191a10048000c0b071000c0140c0940d100c002041001411201204c0540f074202c041e40c00350780d07500d00c005400341842d03400c010010103101c40054a24040040198021071096141c00e282d499054240f603a10a114031138216912002c0321500e4070017140301f07090141d400207a400d20f041c0740c4156012130720300480f01e05044940c800e0b46800310240035040c40e002140c540c007440c0c4141351003032945400503c1d10031a00440c040e1001c1d080c454000c1030048140d6001001d00c1016a43c40b4603201100e03070b440b210b466030b11017815800d0103818401d07000d02074880848440805c564540c44c819081400c1e106c0d420505050042c145e44610121b003014000c80703000020401040021060b60618428 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 548064082 1250 548062832 548062841
    0x9220f091a0103111c0219030303231612090503070c170d03020f0c0d08091b0d030503040c0e1f062f0a0f0606030308061c110105120a0e01 61
    0x155010524036401440060020f0950603400c01044940d00d09503060700d45c0c5140c000f081c0e21002980504140f40745460002e042010f8400c49020391030400040700e0b500401402e24811500d0588811102e1000804402c82c50071551400600352910b8075441c1f01000b080b8040711080c0700152445e5001041100c100004102030101502400e031350008115001c0c00c0e801c0e0707070b44100710300e100c10306d90041010500d0f920031030155145844030b001102d01111610b02c01a00b503900646285d6054041c40341c2c45500c1c0d0803442d40f021503d1502500761700e40d043e0301e0703102141e40e60800f41045901000c841000540c040c0c071541050301504d0304d0010703100c0300d080e03e542080c0b1a1070103601400c1800308615504040140201c1c01a88c0e99402e400e02e500c42c0c40d00300032454140406910020000d5030500c1540342400040e42c440000d072032281d00c0781089034481d0000c02410303861003440749020364100313040c0704d002918401600c407218206050240c01d12002c180d03101c4100608480c08158140d9400c042c8034042c0d8240035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 548065332 1250 548064082 548064113
    0x12060c0d1e09060b0a030f170f190207090b011b02040e06070203031e04020306190e0d0306050a09110706020904510b09060c0109030c06110f09220f09 66
    0x21038801c428910b541fa4040140d05a00c003030300c109001c402c0030302c04075401c000b260340644c0c1810441d49d40f1041c50390880c9088481060050052289a802142000b814440d009001105864000b17100c0307074680d0000c85e02800c003801203800c00c0c2c032107a03040000785c0104003180c0618055005541c9a16012890509501200300c00c89032600d542d40a01001d40c9021803416000481f014004041403030101c810070250448454048007407141200144e40070340d01da4442400d8410485540d842076030703191418019079101011441e2900410080000000c00c47e0b401051840c0025001064205c4140b01000040c1c40040359002c0605800c8040204180c8c2d4522040ca00365507030b851104070003c40180109030f486240113403e01d9080003e200041c81c0d17200e0060b03418454a513402800540c40328a03009100040310a8100ca03002c0c01c0608004420080d401520300084050010f9402e00c40303400101301004580302010700301c0c00320315260041407070080c0c0240700450340440400700d000d09651612245c202170304803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 548066582 1250 548065332 548065339
    0xf0e04050105010c0b0601020c090c0c060c0a020d120e03030c030105030d080c27060c0d0f1b02090a0f0e030306010f0212090904032006010f0512060c0d1e09060b 71
    0x3006104581e00f0030403038040c070754002c0d01c81c84e61a91550b0050345444014082541d21034074071420801061510b00013000c89400540a881d4161110700034006a400380c468a580981c103c001c1c04c1100c103100d451038501540c1300349804610404d448072542d0950b0f02c00e40b0ce0000381b000000041c083c3e4201004000c80303680042ca0003c495103040f2042c0034190241550f190544010b05110110403442c000d4400c902880042401da51140480c4500d0740d40d091900b02a408141d2000202003043e00800602901182e81800e5030000300b26a4200302280800030510072074550751700040300c14840e042c4a00c1007040c14030f00007907a50b4102800094070140444a10008551140280c100d203140214280c500d904015112a00300d41c80780e240540d014680e0f4011120750f01182e5800182c60040001c1c1d0038101c6003c0e400140055840e0820710207868040d60f08450f142c0c2c08000440c1403d0301480c010708400c4204200003408060030982c180d031700c1d8514440036000d5600c400d100f0040c0a564401c0c40d6a414086 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 548067832 1250 548066582 548066591
    0x290a030204061407051e0f0708010902090610081b0c0d0903030e062502120312012603071407050a09020705010506060423040b04060e040507090204080718020c0a030f0e04 75
    0x903a07a15550b401d102421400c03800906d1440001c058042010000ca6500c05040d9080607844480340c030300130700c1c1c00c0304180e2142c40040007007502420011013983e001d2245549078202d1703944c1c9030789071424002080a113903903103501003080d420603040500040c0524807a5a4500c00303180d2840c240103065400c44000c6900c9503400f0080071051003400d07a0b80100c010103001e140f503150101c3d0700003d00200c4e9078640b10045070000140100c901c1e42c4043c40b5a05807000308145100c0d50610440c403101040c19009005400e0740208503440214000e15681c0e13100d0098001128121a140c80125007180c80d90f0703010025a540104140d800c0210a0003001c7e4054000c0d41e801e401c040c50315950b8403038502d8100c45c0f851280038041e4030118036101c079040300c101c0c0f50001d04184201e41c0d0f203c64074107044004407070682d00c90054450201b00b449240c000c960071038015600901c2e9060504044030304040144402020190f420010700c004840284840e6100301d000f6102c62540304070008000c4d08501d8840d0342d039840f41d0b250 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 548069082 1250 548067832 548067847
    0x180f1103010614030a020409020a08071d070203181e130c080f04050705122505040518060a0c021615110d090b03130f060e0f0102090a290a0302040614 66
    0xc1d502d07138517980480e00850403404a001041000740f00350046001400703000404203401204160000718811040e241030308a0ba20f068040703031280100041404144d80d0b41002c240e0ba85001c184000105d40c400c0740445103186480c000500841240703050144850b00c0b54000d2080c10707040700031a81e1200ea88c1d40d0652080c034003a9035a0340c980c94180140761042c43c100d031004110540801501500900c188000074005649a0510030a080c6034820203101d281072100240d0360740340d51162034210a1503a4000c00481d191602d40d0700140c0350640546085100b042c1541c4d28041e01040039200420700c8a0108040c5c5090500040c00c41c41018181d400b25030203092050201e541c0003500404587d841039120340c603601c6041409101c007a500c0d80140a440e20022101c2c280001da5100d1350520419504884500100090040c240e0040c65440c6034800c600d40d0b000c006559610124400c080c801c95481507403141020031540207030700014200d0b030000c0d90126090000790b4000c03100c00340f0b0503c18030345541883c18 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 548070332 1250 548069082 548069089
    0x504031d120a0308090f1006151b0206030910091a0c0c100f020d09030807030518071403010e030403110907051c110c0a06051e0f0109180f1103010614 66
    0x340b0704002e0811043c48002a1201c40a1040300c418400035030039100682d2080d011403016000d14059503950390310306101e000d052070003151344001072040c8545c400040c0d40e00d60200905a000200007007a1401642180300401d00c040c400c982d0303031503c42c14070030241103464600d20541e514018039600007800200290360b86d04100040341640d142c41c26001007650030f100d00f2000043d016550000706000e0800404000b090b4006c4812485005e583d42d003000707180e95004081e41030b20b040001500454105c49000c0c8041d114144000702445006000030031015464101649180e011342c1c0240c686003180e030340314489403a01c0c03007415030868028900f040c03e056189a2818000f80c001000240c0d1070f580305e00b09008541544191120b20341004141d4004074902d0034a10003400301200c0402549081040c0e8240014400081d2800740356a5500080700c1d070700300b94070b500050011249007a10a0085150703500005c0844442c1d0100310322854024000d91080d80a0600351880c0e6009039010505002e00c55400d0345 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 548071582 1250 548070332 548070343
    0x60405030d09030201060e010905090c03070f03060b03010b090c0a0318150506031f20190507060f060b0715050714090d141e0304030206040303030203190504031d12 72
    0x140c1d11000200c1e074a0910b4164018240c99100110b01c0341d881c0c00000c1c02c42819440f0764401c3d50048183c501c034005010415840e041c4900031440e107900c072030780d040c4003040e460740c0400c80f41440640001703030035002040017424800d400c55800b80260380000b016140c00c4c1e071501070684894091189d16200d4045a500e95122421071511034180c950703902c000822591b820003650300c00e910300e0513003008481c842ca2010000b80091300d6900306008031700e04000900720f140b001110162070351003412070980c80a800c000c0314242d001481c20346050351039080a4186440c284501d4000740791455400d075584000717191080c0360082000340c0c28101454102004640340c0c115580d031420030340d8503440b56560750b050800100088411400038011141c3c0300446030f181400010095401e0001260341c1290341d54480c190b650fa44240c2c04000e40241e802e0004000081c0070ba0013a6412010501c1c2c25268a00ca10a01104a8030101c1e4140c00060000343d00b041443c50300448a89107242c1030310a0410320000801d0304d1b0340e84 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 548072832 1250 548071582 548071597
    0x6180b120d05160f0f0803010611070b0d051308040e0402090a1406040c030225050c03030403030e090612030c0a02090c040e1f050d05030a020115060c12140703031b0206040503 77
    0xb82c00d2143d0010400c4081c100720100c40341c0c030090106080255051204440c1c1003401400003003580e00c0581081c104000505004407031200107950715013034041043c0c0020340406000c6e0300c20790075003c4a0b100005c81e0000504003401b4041701c4284186410700412203160000303008550700034070781345501c04c407080c2201415522035415100410b814100440441c024850082d039503518030007103c00303000c01070b4480000a009600410445a0480d00d2108050b200e1145100040c04186942045440d03070405020080d8000e5004110307002920840b9951420350380042451045600a44044011840c2c482c59a03038201d1000c00c6003d08040c24194248410603001e0200c098402081005400d01048c00d61840090103002d801103081e00c6152034101c1c1d07243c000d1401c100243d400d10035010440d410402881080360300030740d10b81e02e400403070b51219003d40f09101b01c1c0008100b4030901400b240c441c480c00074180c0e644243da000a030354003900501c4c03002d000e02807075441c1150000402e1001141d400070030b48281c3e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 548074082 1250 548072832 548072857
    0x901051605090310090c1d160f02030d0c181e06020106050d060f090507170c061806030703060321120506010503220c03110111060103080313030306180b120d05 70
    0x5081c11b0000c4501384075448554120b802a001d021002c0403000f803a8043d0200e5540b00d5841c4803420026a15900740b5003030b41d00103900c00d00c07103801d1800c955004100c0005032420800004d241a032400080740040b504800c1c00303054414240010031128140a00040c0b14600c001c024480c2050001001440030540141419485022180c107500c815400031141ca80e020040302d64484d928002590b030422000c0c80180e0030b024580d000e2201d0304001d02122346a442c107051a9001c4c86d020010451503410251007079080503543c0102200103a6100711102d60801c1d2011025850b0a12050090080b415401d034451440d00744000d105059800006480d00000800710130856840c40860345d401c000d042c180080e1403091308c4440081400110355645140210a0f43c82752a2444038a01c11940c4050a110007400100e0030000102c414112104c58171001d4446d1401080240ccd4807449140940400b03224586581d684d80082c8449103410420682d14408400c0a0310005151540161440c0100c0c00402da0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 548075332 1250 548074082 548074091
    0xe0910060509151b101e020c030706060e090d0311191b03030501050f122d070806060415060804020d030519032004030b0a0b030c090901051605090310 66
    0x40a030b03a82c0da40c61500e80c2d4200703810307901d13042000000101031100c01042c1d813440c0114207488840d8002405840d000e05084424000103803890500303580207512280c8600401e00040c00800c000408a010307810080c50000c0400d920350a04281041c2040080360125091500d4010350241c0c0040381410fa41d4020340c20760360404002c280d242c0c20b0b40c48002c0713009120380300c1c4032102d8100c3c01c05803d688120b060b240c00741d4140c1903034041b5909000b40040c1e400c074178105c1036200b84000d4817155401c04820030404496000380c0115487ca8403950b242172095085154550400020070009081502c152400c4e8002c00400404031858244082d001100140000c3c0c0203105a1a524080c1230140080380c03044d200300c604079004295108030017401081e03280b0040000c0815480040c00d41e90f020402d07201507a4114584007565211b150b5501c2c0244500c0100350703058052400380704920ba81d140d0f041e521900c0c00070000706141c5403902000703079441d00c009101403d1240a026404640e1030000e89081061041480043d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 548076582 1250 548075332 548075347
    0x6070c02010804060b0a1d150105120f0a020c0d0c0209070801050d0b0a15120c090605060405040e0f01021c0f091101030c11060705071401060e0c070311030f0a0e09100605 75
    0x44001c802078100072041c046440c1c030301500c904c1194085200c1c10348c0070b01010601c041c0d034004442da40305000481d403904a030103001ca0091030300e8100840d005940414014070345040c40c0c4c841d6050940009000d00030424041e01e400c15820800801c55000703202d8607056059604040001d01d0407801004060030080140000034001d81c0070341c0c000b4402d03055121101c01407640d83c001740781c400c490818007122071507401000014101142cac01054161203004103514101410842400020322410b0b40b0749500303110303a2114840f22082031008203100440c0140d40420014025142c0068484d01172003542030700d20346074541011400f40d1280703000c201c500b442c01182c0e05044020488541d02e10300303102c04030b41c007545042c0460316800c04000d020441c1f0601031507606203c0903c9540c202ca030306100301e0403402d08603070000390840c200000502e085e40c0309003004401d100031007a09500d10740140f86450200300d0009400f041c0150440b07030506650f84102c822140d00c0c030b0107107078405040c0752034440c03142800000304450 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 548077832 1250 548076582 548076589
    0x2030904060e2710090c05120109051f0f0e010209090108030c120d1b090510090f06260a02090f040218060d1806022a150709170d0206070c02010804060b 67
    0x11400760240513050005100500301182c02c600b140c800d1500c140d80070005041c034524180581504580c02c127016224400c0b001c000007400c91640745d1000851941c62844a070034902500c11442c40904900c001030304c0382000c00a00010315410f800c8201190300074081000c540d03a0015200e00180000d21140742c4a802d10403002000d04603204903074039072854001c903007591143d001210f0320483d64100e47d03a1210920020095172075082750301031a9030002402c907040c0900c07400342070a001c5607100c05032446061012400c048002060a44261266640008003480185440000c104410008680441c549100018041151004840150301554011401c140886081d81c08180c4840b440c0700c0351b80068000d0700d0304000941c40b044480d64103a50100040a00080604403810401c5001000340005110000f0131841e0b2000101240100721301c0c80408960740d1840100c01e0484814407004004001a030140a0300b4607400600810402c8440d03119500542e902c13420998010b40c000400058030680e0f240407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 548079082 1250 548077832 548077843
    0xf1d07180c092402060a0c080f060109030c060207031a150f030c030106120605070801050d030c11040914060f270309120a03090503242502030904060e27 67
    0x91020014110010004140e141c1c40040442484d804d4552690361180f501c1c044580e502e01e0200095040e400050881e00c40403125a000f9105041584100b59079175901c02d000381450304003000580100100b04204a580018842c0201904504504501c6e0100000c24084484804144241504550903940d600c00b0f001c0342d4000171014009001c49500e422044c03009080b401e0080350781c0340c42d203000103107010711402d02c07141a01d4009144d52850240781c0c400b207034904e40401042e20404080480e54140d41e40d98810780c480749118940c8000340b070034406a420305001c40200036143c14501c0b6400c00480c1c40350703104c40290207051158005030490000c181c5a1450007501c2995810642c540000922400300244403081c181c426601c149a440c1c0320401e041d15006400141440114903a140b01da002c102000d11940c003040724143c140c18070300790020040c04002c0000310000907800010ba40d01150501b4010140504050f035030701c05090510104a40c000c1c3d0100d803a5a240c6040d540460301441c009004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 548080332 1250 548079082 548079089
    0xa1b1d0606070c03020a26010b0a05130b03011505031c0503010603020d060801050403051c0c0e010305130b010b13060504030c05041121071b0f03180503010f1d07180c09 74
    0xc080c421a888140c614400e547d00200c035000c02081562031120b655050044813102c07100500a00e0802d40342200b4400c004030091000e0031240d0311407450480d283c07400d2040000d480c0060403840140e514003828981800702d21812030150303503001d615145040d0380050450381100c400c0e02d8016614048854401d004028982020005509020600c0181a8400040c3ca03001d04840c0806481c143e07034001190840e007100c15900046005000c1c0f0281c15030280c3d00c010340c410303040540030794a0030f803960b0b44000c4120301360003640445502051402c0a40e071103001c9040940040e0900074900b07411034884540c4c0f000c4c141f250503c41d54036110046207840c0c5230000c0e6405003103038000140c1d85586c050b0008040204c1117031a20001411500c0040d40310640901e203806a07508110202c02c3c4143c162400c580ca807001640300c00383d03000300e01d80000d6541c4091060f062a0341c06a000012290541e40c3da14100d4010980141d1007640038034030502005004008503001102040d0300041e000324195419a160040d0380d1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 548081582 1250 548080332 548080339
    0x40b31120207031502220f121a0403110d0215040b0903042105060604020f07020f01020319030e06090a030909051306060608060925050c0a02030a1b1d0606070c0302 72
    0x40c0b9211460051780180030480caa5803070949402041d04007011810500d485208218105910304100070132000d81010300d9a0300a018008001c60070810040e038100040c0ca0442c006510048030140104080c400d00d242c910941c4081c00610081c059510684800503002824400522000c10b20b150000c00850300109100b0f611030080c0b2000d40d02101c007000c40c000044d00c6a002d107400140701498980700f140c1c0ba01e60b40e03038036460074080d2035000e024854860540050540c0b1003004158210580082c60350703d030190f00d0341c0c0440c81001882c00e190900e60007620701d0328207030b109010060001ea000524082624000c00c00007810359100d180703901480601104c0680900d1a2403808110f0700d40c00041180304035000d962080403a00d03540c850a840e48000800800c0d070943c040580f1200c60302c203400070000e00ea1240115103d4480a800003814004050801c9030321840e401c80b00d5411034980500303403004141c1070f0140080d000d58000d00100e1240c008040a20400d070003d0f0302c42c10060402d94420283d41c002c1c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 548082832 1250 548081582 548081603
    0x4080607020709060602030f0a0e0103090219090e06090a030c0615030303050a0506010e010f0509040207231002211e0a0204140607050c010e1305040b3112020703 71
    0x2204007a4582c00d8070b0107200e074080e040c014041406800081100c100c000e4683c42c19184c1400070808494005031600b0302d904054071780500d880541d40d480c0c2c00940d402804c010020b905490203641c41e08844445a07002019080305080020308400820140c11403034040c2030004032050760b840c1440040180c5aa41045031740441004400c1c1035141c0d0266200300034514080115880f142c1c01565450b00401c4107a000410610f861106c2a21400107010004005000503080140303503601d002c0c107045000b1a00700008a01d40c00400e461a0400c00410310440b801c00461603e210854603000d01c80141800b030060501460205001445900b0200310b400241929042d4900706000100701a40c0248101401400450200b05d4245032031421030f8000c0e580100102a800d01800040d0b60751501d0781d415581c05041010415003188043c06510722452061580c9007640c50a0794001001c80d29000c1c0310b20001c071f928004160011008000c4038180368110605640329841c2480480c41c10301c040d00010f02e6909003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 548084082 1250 548082832 548082841
    0x5010309051903030b09070815130e0703060e0601050a030c030b06010e060307020d09140a170a050a03020304050102070608060f280801090209010501030e030316030f020408060a0609020f040e060402040806 90
    0x541d01c1505d40f401c007240c00b40d400361100c0c002212641d07401d4031500d040d010000540307050340c502008480c0141340851004a40c0800c003010301410503000d0f41c015030b8126140c3d44030000e00351051003028017614084906035160760550700da401110f803582c04001c00741d90800c80840c400ea8080c9002c240c1c282c1004107403580d04d181151000751034051070f001a1020802c9081c0100d510130107400281c90300f6002814409420b49402d08442d0740e40740283d80320503940985448078010400034050b90414602036001560b0f118a0303c4002031804d19554045010040d09801f40500c40c0d40d0b08021012101017164401851120100600c0780e081e5070308400407000000410003d102c42040d0404034506008954110842c0e9a031030040d02a03c450104944035a0420400501501d015080c0c50403954031600d00040d03209220603401e0200d03131054008081d194041420050440060b0041c6000750030781c18010750070312400c01002200713070240713025080c14001084002005c5889641c1610024031201301180e046040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 548085332 1250 548084082 548084087
    0xf09080a0302130510050d02130b1303050609120904090c1e080c0312031f05131d0d0915180308040608090c010905010c080724200405010309051903 65
    0x100001c9000f0315050414002524035003c0c40d00b24401403a6202c0364580a0743c020341c60003e5019030000c5511040c000d10104080f403850010b0700d030544058072007191507415414424a4108000e01400169000d448030301050702d580000da644004041d140865001e04501e000210f90700703190042d0740642d80818222401c114a032000c0e00841711a038007074460040700f42084c142c4601c030b2510f1445088408001143d150001034030042c402a144408a5220b651100001074022290383e145c1c41c001070301e950503071803000301d100d64050100d00346c40010880700350210030181c1841034a100e80159060004505070080f400703040b01102c1090520b083d40c450584034604000160040d0041e4070004a05500280506600255207801410140c403901000c80c586401100d4940b031440c0126403450342404108005114081203902e00280d02200040450030ba030300c1101140c082000c1104807091501d0030005256070403007140c00b954000e28011910103041d003031241c5080620540107411254110f4048285075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 548086582 1250 548085332 548085337
    0x110919090c0203070807230f03040e060306060a06030e071205032d040b091f08070f051c09051213030201080a0618053c09060f0103060f09080a0302 65
    0xc0d440802001905980303241282d4a005040e8002c2c0380c4c2070100040c0740400c0c400c00100d804200c81ca294000203c140400c001d00304164848012003640c808941401409024a00326034000429002420319103090303000564801114803814040c1a9194003c0c218094140300d4400900341d00c0824107100c02003807501c0d41c3e60354070022801c114072440c40d040001c11122030420b4024a4030700d140c2e1500785400c0030302d4820594448000e140d8049410700706125411020301d9582392844a54481c012640b0706900c0242c80321601003032100800a0400c0181440c0465506c0e40c83c07000f616210000303100302c00c0d1400a107810303c0c8194020111401040c101c1104584031141c1c0c091324800c2c0c0c2c2c3e0526540301e5840000589075035000c3c41f444904030a000c0d510003c0d10b07502441d4070003541c01041011181000d41e900d001c85846045001c030106044158020101d0842413541009088006103050302d00400b001c800380f1018080100901e0700d84aa000494000390003045883c1d13080f4104565820503040050000d5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 548087832 1250 548086582 548086589
    0x70f03080c0c040902010203070605070e0a08010f0606020d02250e0424021206040f090c060903021e030c010c0302030d02040b18010c030509010e03010906021219060f030303110919 79
    0x28030800524050b00d0a242c021030780701682c103800550415040d50758440103801c00a1101c420010301d0007001d942c07a80c1340740c4041c008110440c00010035448400c9407100360345040d004482594025110031040fa6030000e01da45075005039110b81d0800400d8140400c55401c810b900c45891603e03c1c05c1403000f400581e0040b44040d9188a6442e0001c01541310740300d0690007803800000b21002c0c10350021b40541403640062005400070307000000c03404250b40ea030044002e40c90304031500003460880140304600304800c00e600382080405821400c034608000083d42d07114a2030380c444c100325202c443c0508043c001c100361649507246890654445485203005220394001d0f480c003940340c00454400384815409030154942032601350307032002d24001080c0c00540e0039603640c101554140d0750b14004000401c455102614051a14038150403140c2041001c8040288a034030440d183d082c5010001c200c21400c15488400f00c0750b043c02c0104411240c4824a8490f0040c5181c40d40c1001d01c0012110070400e42310081000d8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 548089082 1250 548087832 548087857
    0x10504030818160303030c031b050406020c1e010302091c0f020114031e0613090b0403180b0405150d05040b100b1e0d090f0f050616051b070f0308 64
    0x30101801000796032003d40c000f088088410740201440840d20a811421b2000001d080125001c0540d68000f0310040c0c140d082e98000034000304e0305001d080d07414801907111000031100c880c0c004a0030101d840016038000101ca060503400502000240c4501740c550a5191141030094a041c110707040c03035142e100c60548101c0c0010302c00f022502d00405038905a0b4040c1805a101c240d810965950b44800d03002e000c2d28a6500c01e581201a1040240c54099140d000c5c3c451003c03c8143e080610300038002c1d800301c4200001c1e840000200740b05d007a50000655046400840d000301c5150700040220000e032003111900d0402900b0801000140709820510600600c101001c03240d210b60340d88008481400f900c1204100441c1040091140d50141006001034a0f080400001da002050341c2e003000983d59088119503c000081d803440c14080e0078081194080407100c40c00c422802c20189c014010710a0b00c0300d1552260800e0118035140d40c040001801400c2103000c0840c15588a0030f000f070554214540c5502c8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 548090332 1250 548089082 548089111
    0x1e01091407060905120606120c150d0e07061b061808090f0603090a08030a02040905070c14010216080c0109051f06051e010804060b0a0312030c080132030105040308 72
    0x7445d007800e88a0781541c03c0c02c8070280c2226203d10080044030102c21044008610030070071003004035a9114041111700f0001c0f601d080c0d9a903828024942690f5401c41c010085802400c4204034160b0010f00d000441c2580008c04410400c0234940f00300209440c04c404040310301c0841c000020005a800140b040702411a40d4010203d0750b603040041a110440d00c2d0680c5030800030707080b8000380012014542203007503204050f0419849442c101c013111011590b0070300180031556030b01d0912540c0040000c00d0203d240080d45084901c0c3e10b038104c00515024028031100001604c83c115400a42c0110360040c1d00400f602e81d51000d0184116454074282d015800381c034604180010941380c501c0c40301409807101926002441c49106c0151490320004105403a5141c4880c01001c4560341e240a0a014511481140e203c2c441c00b80c00c010b086078580c06a06060000580050040c000b40000652025804024039440390145454000001100e20010341d055800c160602003090740080c0d181d4070403582c07802c035640b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 548091582 1250 548090332 548090339
    0xa030903081f21080a02010519050103080306091905090705210a02010e010c060908120109020a0c110109030b0a0902030f0a030f1206081f0f0e1e010914070609 70
    0x3002c85518505a800088900c481003000c40d102c0c0c0804081200d4080301005401c1c219160310405a0004442c540140d541e40100206501d980d03004443e00441244c040202d581180d45508040c440030700041d104d80310000006260520801c0d09400334802c09ca018001c030300700940490f91b210014019240b0964000c1c60100304910190003a030b401c843d07020000c2210880c5038005644200c40450311604002074060401c0c00720300039000e1250300f248180b4442d550b600c41610440314480041e00700c040340c40e004006080141d17510010306403003e034001d8519210300920100607200501540e03c0205004890130800450f4202030348039103400c6000390b0584491001001c02d140e1140c80002000f170100c2d1022200b0341c8883d01c2108030081043c01d008000440f0794035108401c4c9800c0c07183e0344490300d8419190501242e24a00e0080801466698000b4828000d51780b683c01e03110000240c04004801808040842646003504a5510160000910380c0a400064140f0352152001d00404000c18490700000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 548092832 1250 548091582 548091601
    0x90d0606080f3408030a020a0209100311150d06080c12280204020d0f0207140d0509150d0c051809040209060906150a091406070f0b07020a05030a03090308 68
    0x1c086040f48040b4400280704007600c0c411680c000301c000c0d40c6100070304a0011440307943c00c2004000200b0075400500300b10089104000700c80c10020030700e0f9507000c1810000c06c001042c100e00e4143c4504111401030b83c410601d607040c140c5018080c0c40304034071070030600000f480c41c4010981c03c50759042030740d100308000d0f1700e241083da0300c4243c01d4a0186200000c4020100c0001c94200041c006100a10143c5882a00c5120b80c06035101c09480d80380140c2c0c009505e508104106014051081d086409400074101c0742502400c140104c21405000e00003058603004081410780454480100d042c45c100841011150020481d800039200302c80305103400e0002e65114504229040e00c03c40d80180543d10695401003880603d40015280d0b6800c04400b019040e2040d40c0100605030300c00300b5581e0030045600d0010101c500442c0640e1160041804209907000300e128004c68104c0140c00c000813100c0c070b88699034100d20b40030a803180580207000100d8648521a8543c121a0056010759211b0105464587e0710 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 548094082 1250 548092832 548092843
    0x130302011709030a110703021f030b0d020a0b07050a0b101a0c03030103020409051c0e040f06140409031806090e0a021c0c350c031005010e06090d0606080f 68
    0x2c500303940244003802c0014400c2088400140d8850180d8079469540d50100c1c1070a02e83d801c0d50640074282c40300e40c6074002c0d454030901c1404102103402404813492900850f120301058091400113800008407182404030800c0022440ca84c420107009941c68000340001c2352603142d000e1401952502e4581100044000043d14504200301014600c1e591942c0e081000629468500700d480703025010703a00350303044403000a0b1050341500e502c0c1e038210360b480102008203d41001441541c041d04c0c0540030712400340d484104100601702580c00141440540c10296200c01d2103010f001200c200b032000201e03445901060000844601409181040d1a2584581c003a0301442c200107000f9500104841c41d10341161b0092509030003181098281d407600701d4410400704241c454414140c013515103500080240c454807041c2d020811200f09811801c0c58090300601e031140b440340a040085442000354943d03140c1d802c5a01141005021070611200d0b0700d01403010301000d128524090203207143c2d441190801284 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 548095332 1250 548094082 548094091
    0xb0408120c04150e0d080a0201051f030503030a050606120a02090a151b060605100e1804020105040e0603100e010b01031109060429040e160905060d0e01090203031303020117 76
    0x20032202d20152080843c1c4c2c000c8a0b2544030f601c461013048550100c2c40b01d500600190301103174004a0300b031610307051542c00020140e14072580d080100e281000451004002e030f03034116800c81c0005c01d80b0b0301e8120001c2d1b01b50180f45000005090310000340043c04200b68002c2415980c1900c007069101d9171102400343e40030001440034081070b81c2d030484c0c1ca45000000706c0035000500c50700000940030740720004240d440c8400805030020130041c29040310b5519003030901d8046803981a50300c100600e030580c002070680c05107114106210700700d480490304542e0148015547c190756140b0402000302c400008a0107480000c14260120740f0381040c03c5140030160080701c10441014001074605850402241c0004d42c071034410310a4a001c01d108070006031030b050003c000420a0300c3e4076000c5070030002c0414065002041d5030100b8022242020445501c03172006440c8120300c0884005505111030003214058407201e40000d50501000070740407900b0810049030001e0724000e030b845072142c07005500e070001c0c06241a00c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 548096582 1250 548095332 548095349
    0x6180d050f0304020103091b030624050d1e0b040209060d02010e0d0219060c170304032309360f01092a050909061c020112090b0408120c04 61
    0x1074400400341c50011030b0418810301d0b00147c000b10036140d200007524028440c0d550000e841d10200309001e590f0044012000944000c00261075103440c0f0940000c040340700d400d020700c0807450305105110701c2c008010803404990740d00400000551401c1e105910040350102d1007503071110085086800c01c48038030400158180c4079120201c0845003000410a000d1070200d0b440081d41c00b1004840416280303040003040300351209203142042d89400e01c01d1040d0862220b10030315040c410030020947c00907034506155003500c42c00500c8064010103108620486000315003000790000c0580c500000000300041c00c3c1c07414600400c60400d0312822020507002601c2042c021540c110051088002c0e0758400103413400041243d0030740ca1010f41740070340700d8891a03500308041440441c8481a5007040660390340c0c000b4040f1a00740042c0c000803030040360f850033f8100c06410010795169024074554140d101d24007403604009020010b00c0c26140154056000740110a881c2c0c4040c2c000c5030816851406039000d650000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 548097832 1250 548096582 548096587
    0x141090a06180b0c0318030607080402091012150c030b01140a02030705060a0c03050606030c071419050105100b030c0301090b040b0901150207150207060804060204050a0806180d05 79
    0x110444140800900382c8003440c14501d00011100d003001c2c01070500314900000366455580d10318040c0c0c01c01d65484602d5000f034005008121100b40d01580f2164041d504803850051600c400b081e45245500035041031801d110400c45200520070301400d4500b92605000050000019100d400c40a594000351011301148020740d01103040c4103000042e00c0d29004030f00c1101c1c18214540c450500d4044141ca031011941d0780c0380120365640d981802119444841a070740545142040031040341c45203d211005814a0b0350b03c2c04015007000148051a14002c04104140e844003e80c280980286410b40b420269940f0080d8000342202c01041628400d01c82d191540382181e19001c0010b0290030900502130788241e49842420b503d41c1c910172024080e1441040d00f840c40c141e107d01c040d00d00991a081813540f90018080d501c036040d80041e090b03058171601e10340120729403610310b01600039001ea80c001035440010701001240e10301c400502c0521032030300b41040c0781c074550350a1074440c2c490702041c0c031400004204 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 548099082 1250 548097832 548097839
    0x52809051c082a0a080a0e0d031e05010605090105030c09040f0603020f12060a09050f0708030322052a04050403120b0307080a0209060141090a 63
    0x15482214900d004206844600380d603085603019669101c40804040b03865401880300356100d030503a041c0c1c0c002100040151611494205070311502030302d0403c000300007600c8000b41d41d160ba40d1b0030000c0d14a003440c2c1203e50201030440054090b000580c1509103108200c845070703c0e500d005004042c12100315413915403a007004800115015030008001703c40413501080310b0605500c4503c40d80d08a40c3d100f010001e0081e05520400c0b00540407550990f1203001e5410503a0301182c03000c20402d800091081c0c000403503203518903015041a0340d0351f42e00f01c61402502c2c000604a100800114403961520455034610165141507078002c007000c44000e001d41d03000115140381c4944d20460300c0540401d0700032200c0d00740c21100000c0c003030703407002c50f0f0441c005a0503042444640060740625000c0e0503086000c2e02846003001d007040c0eaa005000b001a104001020200e50305034000c40001010507005407160800c6044074040031511a110080701c0c1d503048008840412102d0407a080d90802e4200900c130b103910919 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 548100332 1250 548099082 548099161
    0xc0e150f0412030309060c0e090c0a030609092012120d380f0310090f0b1014150d050a0204080a240e0312090a0b011805 53
    0x1118042141420400010400d060702e06031030200544241d501040c06521880c040c0300707a50100b03500c0810700050001e0300786940d407054005584482000002510b444002404401800c2654810060b42d49403135029800c5c03200414802c1c24004181c044e03407114590038001c0c00000244000c00b881190001250801c041d5013001c004c1030180342c168000b240d14a10001c0044482020743d113944c440e5510418000d03a000003800322050440d41c00c5a8044032102d03c540420384540c000020a0f5032a41c0d1102042c04008141d0030f00d4203c9504121451601c1c5852010300003540007174011001c000300da40507010040d01e405103442c00a4450700b080b00c0e013400488a1080d001c1c0c580a003c3c0c0c00e10f10780a10010820540400010383c14500501007200d1801e02101d41c035405810305044140b4540c1026800c00ea00e0780008101d4661004441e40d5060310780e0f1b0040900d007000810307000200140c40c04070000554403200b03901d4880340703600880108296151000500340440420702601c8498803411241c154945 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 548101582 1250 548100332 548100337
    0x303040b04030c14060a0e07050f011b0c0e040510022107020a170901080901021921020d0e0c01020d092705181204030206040e0c1314040c0e15 63
    0x600c2814514801c406944d03490291100602040c0340c0340e40f0503001c0110a1000703000340359280d0412070243c100c080c01c110208526003402c4403d075040c0071100700807400f44050020010380e10b44d0800140e0b000240c0780c081c000102d4205407415119840381385528038101c0441e00c00c56a584410b21a03c0140302c1103600d4030182980000c02c0602903000380c0380c220004c12203140510300d0400c45070007556034605c40d1400141c5001c02c00345c11220756a2041c4074003071010118013102940c00c121410100050920a65424814140c42c0c03001f00000740041a4407010080c2d540040c240e1580340c0c420b40d120b0482880c012640d41084903084000074815a1081103017041118069607496000e030001d80cad01110085522098882c00d80b46011395080b113014a8041d09030903c03100310b24070800c144075480c052850f00040c5076401140203860002e40000003107404440d98a0407a0b00c18105e1002c103403240d580e92710f43c2c180380c040c030031121038090750822150340c2c2142c2c1300e200c0d2082c0e100001040c805065051007072904858 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 548102832 1250 548101582 548101591
    0xf011203110f0c040c050705030d110706020705010b04180f061d030c06070e030601031a0705040e070806190b04120201020c031219140712030f0c0507060612050303040b 74
    0x40714241080040711010301a071080b2510000062840401c01c07400d01049030b112400750400c0000600c03018001840100495502e00d192603004100010600884110b520520000030049440051100100881034009400241c401c880400240c0040000c0346070b03041c49118004c1c40091010032150004a0b90340c4a08000c550386245140d01c0189000b4962465020f8403803d400c9a001070108940264013a4030b66008c0340050f400740c2007952544d51217032112038148030044c0d1201c0c54800002e0042e071084054400925659181e808641010603014240410540301c80340642c0b4140704000340b00442c10039442c02c07103021a551a180900e13090f80c1009460101030100d046000b072545203c910b690802c0810145d11144003429611003140c050100300c103408032803140030311103014401d4915048d00c1c4180d4060301d402c15440c0f18080d51100c01200102681c41560340320328941040e030302101d0740c80805084141e00c2003804100c00d6031101c0d0401c0360942e192800410039401040040c0c0011701600003076070031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 548104082 1250 548102832 548102837
    0x1f0911130b060408030711060a05180f0d120e0103230c12010312080603010c1b050f030301120c0b070b060112020904020a050909060a050120030906040b040612050f011203 75
    0x5001c1e560005010340c0c401d40c8803510541c40072801c0424400a0302010440c40d81c11079046241805a403409817040c081c504410303600032000042d08140742c8070320800f080c0c503c00c020000c80c00034040340740c507115020381208070b040028101c02100c91603501030310540d0340c3e140b0201c1e001c004640030101c1801d6254802400d001c2c044100340b10041079038403402c0426001e14891001c85030005a40000103010032801405a40300740e0400c1d207003142c49904800b1042420882e01c8186c0e03020301d09420300f640b500d14000d4a10344030340b200000009242400b484542c501500c50b500400b01c00343d440304020741600800401822024809010840d59070140030045c4900a1194026040c50321040016080fa08040c94500c0410800620060207240c60815035a0008046030f80580003810040005d01060303d048003a04001c0c00301400c0b070040360040060341c1c80e141005244591701c42d19000c03195103c2e0170600c00c14001c03405800c0454480340190040c0c510495000044600985c60315445010b540c0d0044020740c00e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 548105332 1250 548104082 548104091
    0xc171b15240315240607110105090315060112060f0510090807030b0a0b0402031302040f0b0405100608090f060604020901030b030618060105060702030c040906140403021f091113 78
    0x2807502e0a0215040f280241e9801ca400c038a00761190300c000c003d0001e13060b01c01d00440148548913545d20b000750b591003038000c1281506550102d00681d103d10550342c5665040c45003401741004a840d00454a01c25a808c2c1c0c0d50402100c10155030800341c4529005081028a45a00030310003420311501c01c4032100347d0b920301400d5035a6241034060034007020360001e4404188120801850b02421b0040140c00c1c01d0076102146145000e1410040e45084050006d2040b038613070148000816464110402c44400200700f00a40c0c02c0c24020200009013503c11040450b511600085541c1070202d0501030f031104a1000c1e10316503480e00c00308002036024020642c10705a4640200392203450800542d485000d545006150381e400c40015a85000720503840244120401c009040041c0c8010910040000c0f050320041810102850448041d03c00d000c0d00003107072202d410400051640c00214041600c5090a05800381042280040c050b42d11006002d40140d040804a0046040c42152400c00722032014000a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 548106582 1250 548105332 548105401
    0x715050414010c0813050301050606040806070f0e040c020f0607090302090f061f03050405010e0f0a06020322030c030f0801031707030909050c18041802100c171b15 72
    0x50980e00b008407076061761402e010040c07006080902c116600018101c400a0800b1700c0e10319056642c903402409a02000345201101d510f250103007648030b0b0b41002c01402400040c42c051002596009250b005031401c3c411403000c038941d5030180050f601a04c1d00501080181c0d91103d04410140c4c0c0d0140001d508800b074501c440300c03225404944915075550307030ba0300030809003005c1c00e00754291210038842d070880d50041c0118100428001941d800b2083c0d1040c005a02d955807003504407014240c124140000100c250400390406520003688400c180c8261550f4044001c2d00c0002c4038806d100740001002542c82903205220001d001000d410030510900e0100110b03921604800207482c41a58101c901b18404104501c52100c01503a01c10064019101008211106080415800f0b46640042d003c0d41d1010520000c06200d01d04d424203094214a01148079501c241e0003400e65801404608201010307248454030710140800c60082c12a01141e02280d40c2c1c48824212035090381c16160940c1d81c02035036603660b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 548107832 1250 548106582 548106593
    0xe1501090510121a04060b101110090f0c0b04063203150d12021b0a0b1c1104090c030b0d030f0306051309060b010f020d050904180c03050715050414010c 67
    0x45114500c19078002c01c120500600303201500c2c021203500e005109001c0741d54a149d44c000955000040e05c0c2080102c3c00c58000c4c2054011600001800780140c0d50501c000320305105200001c00072148ae0b40d4418010303402c4c100f0006410f800031076203510441501e580c51803404100f00c02464108950501400c1c100e002400010055913802c8d13401c5504501080014039069010311141001015190307401140c1d10081d4001512413080303008160000e03101150a240318040085070000821241c0002c1011400c08186420160080c3c400c0d034400605180c08140441c2c801c4c0119100c0040180140701d0003030312640d081c1c40400d50452654101b568900d00014580d03500f0039003040842c012000082c80f905e0b24200002901d03008140386051100c1a03001a80043d8000f83c2541050002c0c98030b60788413903848001a01402c288100484000c10f4080409d0034800910b19400460744240c040f1800265505080c2d0b00c4c01081c048810301041061008111304101c24620313070503820051501242c030100c80d550b007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 548109082 1250 548107832 548107883
    0x609020a080303182a0d03090b0f0915160b042409120207180504051e030c010b01021b040b040612051c05030c0403150902040e150109051012 62
    0x481c00b40e242011540210244c0c14410001c08610b07039009110107400b219907041c201a104d80e82d0302e0060348844500c10038984034424000c083c1980080c1183d407200720039195021500a110790343d20452001c4e40c4240003014090850703283d040340b1070300c0021010090321401d0103228001c106961110544010f032411010340f420300c1180901d54031002410007007500345120106608c0d06410255403000c50103000c507000305411140010021039020405a035246043c074106030340080381242c80a50f002001001840110103031a0f0200c051008020202c146001243d44212041c03600e200c004c0800a655001d0600c0d420414028001500104440c0d540d540d16030141c8064080907540b40d003050580202004500740055150419880c0c00750039400c1c0b4100c0350b00148694071004105283d1502e100c0509001a040104825001441041240c04510000341c0f500c07400446030084200480006c210000940701c0c040c0203546c1c08843c644443d0400002c0c0b2600d80294400b40d4207808040851402246c2c0d5104 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 548110332 1250 548109082 548109091
    0x2040902120a0605010e040209040b101508090d080708070c050703170304120e0f060c0a0b190e2409070f0902041814040314070605010e0f010515070609020a080303 72
    0x1000600c10380d0502c00226a0103800c1b180c402407100003440003595035503c0080d0441d40050b070310a45912001c807250046c02c0e80380e04c19150f4008904849883c65007099049102d910302c8001d6440003504040d04a0b004401107508101142c190b42c0400c40c101d21a084442440d4441ca044414040d1240c4901045910071440e1401701c280000c10001001890224104254400d0800000165400001a94003140900c1c0e09000b083c000c1500d25800340204184641103401c420345c03c290303080c00d00c0c06000074140094450580e07804c0c07060581b8032440c009881c002e400310310311980085141e200c542241c00c80019014001d035105200740410501d01b620420002000242001a9103620b8001146180120240980c00c40e0385840c841c00340c8240001102c83d4040da0618100840c1d480c5022600c44030f002c0e02030007414440c9010004103c10501100d064000e40c0010243c950740e80e40e41080004880c08400300c1902c100040c0540e1000807035581054584a01c000d001822143c1c86140951840d001141c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 548111582 1250 548110332 548110369
    0x203040c2d0902191704020d1106070b0a151412010e0706030c09051005070b0402030319020105010504050f091f200304121d060306120307030c03081e06040902040902 73
    0xaa003102c1000384600d0000c0503804c07400c0640c3c940d00c030a40581403001c80100003034060302042c0307849800c11412030180d0030120001412985c0f80e81c86420404d40c060b03012118882000c2c40c2c000a903001034040c410900440368003c02c4104100904000d02000751030754031049910f592503140b40241c050080c02001d02030401580d001880000c0b0050040c1196003c2d8000c0780110050420a0b00d003650045c1115038550300b200302017a554840d440401e2840c42913400001c914048044114005503064202a0403144111001d04ca1500c030054101000031060303a00415a0784100414002d10540507030246800ca00020000703002c6203650110202d89044031512616200000204020085040c0b00e00c901c4d01114a450142408100950041c0940c5407061034440d05022001a910341d40c1c0d200c2c41c210248904040e2500c0b994185030103131600041e180c0c101c003c1403001c400118042c80300d00d82c1030710611282410341c445889020038800200f4241c6400d82e005a2990002809038071000380a00c94100d905 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 548112832 1250 548111582 548111587
    0x2130806040c0603050c0f1804020a23030906130302010618020d0507020a1707020a170102031009090209160c0c06082d07080c0c070902120a0203040c2d0902 69
    0x18503020300c030810ba942040040c14038004c24000c500e40c8101c00d48056200100b040b13940c0d0100e03c0c2e1640c161580311101954803d0001038200c0c0c003280d100000c0140484032034103100825111501440c60b9000440305d4240d507070b01c030b08000390358403488e1208136095500030f00002800701e407600c42034801105045c0b016074441d6000103600f0000c100c940700c2e095105c0c0e040c2c40a8900024240c1d1850410045882c40300250742c2c02048030b80c04e554410001c030b030080010135021151045900d103c14081e41049030540940f4003410800103150269019007213400358002c104c2c200b00c0d92a4140c81036031950040e00901048140851000000d003034610080281c091032b00d03518120f145c54a80702c03c43e011030821050000d10750350480640613028140e11500156a420048040d80e1b6000040c0d9590040c4c000044844c03269680c002845801540100841d40f44407240c5195a500c40850005174401502d000740603083c000c2c010040404500802c90344c13800c00006c4c1998807641a410f240302c00d4420303040130a003150b00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 548114082 1250 548112832 548112841
    0x80408030d0b10020f06010512011409010c0e0907141c090c0302030c030f100b06130b090102060a090b040b0c09100905120703080406030b0303120703090c080705030c0d050102130806 80
    0xd00000b11079541a04c0180942c00c003101c804c036140c25062143c54004d81c4400121110650290050380c14a040c200c0f0030000d52411505076406050400141001306011103c0d0031799070b040030388080703102c0c20060700c1c9e4081c030380c00300302c403900d01c0398008424440c80c06000305c08091081c0750380c010300d0300c11405840e401c9030803411401014208403240035218803c3d8042c5030003849140300440c410640030341079903002401081c2500810b40328440c1148100c06820841e80116000e070342c1c00050200b806082e0b007160a10380d20605000200c0303a2600f405462a0207050004000642005059074440341c008110b41c1403400d0035002c5110700072801d40200c086200c0000610940c1080c001501284443c1710041040d00c0c40e41c0c0301e001452040e07014150801d48c5a03210141c50b51400c02c2100d92450411020000b00d242241c0001c0c02081d400408840310301c0503641c0000d440d14000f58103001d8400040180c030000d4015010410038007030030142154695024041c0491411007803100c0e200030100240941580d160 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 548115332 1250 548114082 548114089
    0x6090b040b0f09191416150305010f03020609101403100303140f0406081f0b040e07030c141305060a08041707120806010201020c160914090307020409080408030d0b 72
    0x18001c0481c0d12940c8000003524030a085042c0d50180103400070340441c013007050540002d050100d0a10203044051b2507907400a001c0a006e01008000d02c0655010062a40c941d442d044040102e40300103503100d0418012440030b460f00e031030302c103405c1030060500300a49030042c2d4810a050708103c440f4000e00074181420424103070010803030351401c200044035503d03200300b1144001d50fa014a01600041110713080c0007500d032802603015500280490455484440da44400715409640540207520301c038540315000c0f0310024002d025410b140440e5498603c602c2e22108160540394100c4500c409034a5a19040011552500c80c0104802c0e029550743d055a8909410480440c0309064505a01e03103000700200804903010f0064100d60b44070500d00302c45e07a5122040100e01a01820580345900c0c003c1c0f400340b502205c80d4120f0001110a003d02c01c0c402c1d0300789210044540e00d011074000006070000c005000c0103141c241c0c054000d29201d03c044500b0561580b004910395004018403000315075841405110900d03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 548116582 1250 548115332 548115361
    0x9010207081609110f030408030a0c050712050a050706240f0312051c0c0f020613030207050427060204091503030203091002010e15010e1806040f06090b040b 69
    0x2049002829080b0031596a850320709001d1280e03109441d52158100f00103400c204c00c032468682500d100a40300d040c00d00700201c40e64025106140f609181c44801c981b01d5002e0030035503500c5d0340c01c0488424142c143d110305072065441100c01000f004410021100054110321920306a070a5440140d80203810032004e032a54250301d07410101c50402c04510800005a22080b914007850452400c1600c1d90011079040c0a10001c1e030f40700c0690181000c10b01d0055646c450485414445590b0032611207881319440030f000326803c0705c80540107801820081c40281010703006910700102c08884032060500a400309240080300c02e01c11101980c00203800c10005405010765041d80003410162070380031749950380181d940d1090300b4242d0301410540c1c060421140c001e602141501c1d01e0f9405440a03000c010383d03487c8038070b0303801d000384041c40c0c1013400429031041194104140007a8a4002806580c07a2a12040300d100d00809003229007640380c108060014489100050007140720b03014160341414510301c044070f01d8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 548117832 1250 548116582 548116589
    0x30f071203061a0c10140a0b06090109050d0510090521040f03120c02060d060519031707140d0804021c030203031504021e0a0206070c03020709020f12010b09010207 72
    0x75040c440d00b4000e9280d25a0724541c01c0c0203a42c10f0b02e03602c1c061540e0305070420003c41008a405482c0c903014003441103d5040140c030401d100c510400079408401c003006076502507203e44500292a03550148080d081103064544124003620440d100c01d641c1d940c003038042c0d40c0c15100c1160719401c40c00320090326001c0085450104403071454041c0c101401e281c00502d5850991001401990485410040b02c40c0108031644025402078111035071600ca40401202822162241500418030b5041214035a140e4285070f50907130303130b000c10340403008004100c80c8011a08468025501c4e2600e0b070030203104078041007001d5181d01131140c95095aa00d0700340108039091100903c110712101a070071f004400603501004495000b03400d0b0081d410303a2214403000c01c009000b00101442e00308640b40e0070702003403450b0030b0152602e42026404c40312140d68840041700e25424022700200560300280b8140204580d68004d044070f172100c1c541e0300781000b0f008842c003031400e24207900030095064001100030040d40c2c10300021026 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 548119082 1250 548117832 548117837
    0x8070501080a0b01031e0507090501050403050319050f03011d01090203090c090907080102161b080a111813060509031204081605032701030b0609120f030f0712 70
    0x54a0100040c11541004102250495031a105011980c3c002e5010111110360a240700d07000c50300c1038151070000c1100340e50f40004124a06d600244a40c0304070211010b503075002003e542000790944455510b2818480220140401070240e0480401424041c1d402003400c400101e030224451003845c000d280c01030700f203400298010401c10a00d1100001c00c22107501d801d403050080c0f0381d03440c110a800e009082d0088581d55000250342c049034040391185401c51402101c6008141e15060080c00003140c0ca44201d1426401c008400e0011840714128a541d40d0300c0540a00e0600102c059900c1c900501103c00b40c242c0513000100e4400d0201314460305500403404d4004514100000c01855810240208010202c00b80014510000d49800c1021954141d000c411692503e80c4a12001301c500708180c1c01074140c41201811903269807290003803801d0340274080c010b640b03850110380610a0340c0310103010f00035040c403d03001c101030b0b940c10410007080e50029140002e901c844040c90304641195040ca030340c004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 548120332 1250 548119082 548119093
    0xc1c03020a020606311422030e01031b050c10020301050a0e0c1210060f05070c05090402040b060d0f0506091e180307080c010c02060c030612070801020310030c08 71
    0x140307540c0024507681c001600710ba00c440710701005022030440d03002940107101c0302c055442a4a00c0005960408290b201500c081c10001d03940c2e520881182c55480042c0140c40000e841ca100e0101e8028040d445920b18181f4003c5100c4220008600709910951b80f004001640090885000c15003031015030500c04580000b58595450f080001e00090b2040c003450006000c42d1000c0f0700d031280c50708100c0703280103264142c04010b032518980c40c5821503000c1c460f00000c80e61400000524520460031036007201c0d400070f1090341c2107007449c05010b100d60b0018001c0307810580d50508907005964400140507007000540d00460114030703c01e843e000f96403000d045103005d600380c5c406010802100580041005c807035005030714240e40e0340c1101000d6440c410000d1040501001460009101e0000b006210110402009102c4800f0300b000890762070504564406681d4818008100d043c40d03c40300302c0080b5041d40301100c1e0000d03201c000d00c070300326802030b0f542005030041030074100204021402d2410040c00090080e04 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 548121582 1250 548120332 548120347
    0x160305060a110d0c020a05070e1006020303071409010201020d1b140301120f031b0c0515090a090c02070513050a0c050a08071b050a050d02060c0403032307080c1c0302 73
    0x820900400d850400f20f40d485401c00004a0301c20440241d8a942100032901e07070350341e2078642103010403041d901440c614001400204000d80000100c074055a02d5581e807062018003107034020700b1a0080040941155002c01880002c4031142c0900203214548244c01e50350707010070510140a10349498502401000107000401c000001058080d14060700310441d0302c0103009030b10f0100c520f2107980d01d0420480020b009604103018003c0b5600c0c0942d1416504045002d0804161070444d0149902e815031007404154144842c002a82001081c1141c03801126100340e1118006015010760414081100d6907400c00c10083c00d015001e1683c1201041c14440e16141c00c0600050088a008090005102211440e500d000c01c15580c10b0380810307040002e48000c801070b494410349404091a000e00148120004284803d40400860703048075032544030703d4241c205140c200c06101071728902d0f03400700340020b0103400f0106942d0340080c041100301c41c0151170360105411902d05407060350b00c00070080520600850 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 548122832 1250 548121582 548121611
    0x32090d060c03181707170c030d050f090a14070906081c030c02060106030e030f0f030405070f0f03020108040c090e0a05070e061305100321021b0105070b090f160305060a 74
    0x103c3d8101d130103000507910f80741d40c00c0042d030016903400014014040014510000700c0d001c400340080d403240103801d100c0c0340c0720004000d81000060b120302c05c207601301181050014028110000c641d201820075103c00c00c0e82c0c0c048036001c640f00c0f5070086106400c04c48180481050305812024240c07220b080c104024092244000e5886005014103000d00d81d4592813071881c44801c109603a945107405030b0171540d030b03482d1464078042c0340c209541c2210244516400800d800d1a001003c1c0265411650059529495a001100c4145020f070041e603031a43d541c400881d569880e40124180c2c504464024190842c007403804502d040c03080c0d4051404902084240310340c070364900000d049841100c1e0720200e02500c035507100d50080001ca5000a00b842d080038141549252001c5018112003626001d459402d40350350307001c14064410034201d0740000d404018100004180c2c6420305e80204040c800c81d4003848142c0b0940d450706d015950460b0b1119440c0c035007001000800c022480d03002213404004d104105041290 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 548124082 1250 548122832 548122853
    0xa0c090b030c090607080715110d0b0d12091e080c041d01060306050a0f02040b07062703080f01080a020a03080a021204120b010632090d060c0318 64
    0x611549800010101d0110b41e400001e075040d94000401c1d1554504d1140361068160744141022a900b641c48000316504071180e2080d0301c180e01c065140146450510040000101302e4050b03202d9100d0100090000424400050020b2180141e00d030303d8917203804c0035412489400c4202d20500c030800e5510b02400001c10100e0a0350801006880208108100704803e01001254105203882980f81034000014848140c10060082c85810780401c1401c6000700d100007640300d5409000c80c560020407950000132495400201340ca40d080d900c0040549034140340c2001d4028240041c0c0010f40d00c0820700c1928070184038614018005480149030350740365640403900b07500461101a10821001c84e41226182c024440c80002006c00e40c0001d80e201d45611800e442408030074426181401d40000100d0713980e01440348408d00240c0060240e08c0702104103506064a05143c050581000c1d0502842d0060713100c100d00c2580461007402c0102e07864030070f01801401c945404600480400d021101c000128043c24803 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 548125332 1250 548124082 548124089
    0x60f01061b020103020f030a091709011b05031908040201080f0601020d1101110f0c010c0c0b041709060d020a080f07050403170f12090d031103060105070f02040f0b0102060a0c09 78
    0x800380000c0040c2d0005800074098a01214081d00d00081000f1846071564400f4403190320881010a41070741e00d103595030480c01000b0803613002c01c5110b409030100a000382c000c602020304c40c0742103901e00302200e9001c40e03140300314500403404115020140001c42d0381090420f5070129840021410b00e00d0031000003599821109041c43c1070005625603502000340a40150003002c0c0040c260b0b0b80c2d24051000ca07803041e5400340fa13040030f980d407030109005176042c8500e215909964103e03200480710749403900c580e164858809003420440c0b00030803406100751500406002207001400d401170b118690303a0b42c00340004000810081c06400030302d0030809490f40060903079007603d81001304450007400030440451207200d0445c42c4820f40e034001c5154941d03812400c5090b4864403412081d41c0e52001820f4081d010341c0c100d00b441c0d05c060030040c00090b146503c40c20240251500640d60484074080603000318041340c0358020914599501c0350096891541c040100503000700c0041c0b01003124440103c4000d041005901 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 548126582 1250 548125332 548125367
    0x30a050c090a052e0c0240230114030d1e020a0c080304030c080102090f040207150e1b120601030b060a080d090f140306010e10090e030c060f0106 64
    0x703100d00c0d407a004130420007480883d00040f400380000d00b0503001c0e00c005482c1c1c0080307100c2c10101129802c0d9526044180502c004c43c0d8540345108000394418002541100820072106a034a0314240c0ba040f800c006000c000000482030b041c0e495041042a5401c00c9803003102138040e6104000c5d9088203503020182d003440b05005900000fa03480c90071001c9080060200000d0200124020007194207000440244100e070b2144078030140e00740c4d035003180394240c0c0140360125600c80c40f0b00880c90442e092a8005000d0a44101c41081454409110b10400c6556111082c210390b07120343c10348201c0c2484414500c0001c2001c584889a155603400f034a941e5860502005050501c08000f00d80c482d00c900f000300300a03220000070f0f0342c0758900c8a030000340b100b27031944110019010780d041c000a4455116001e00c807241e0024001d8402e0ba070a1507204004480080c0480b403103441303180c1c400140750b40b25210316880500b13801c02460b550200c10b4005894407601400c03260f920502c006c0108110343e084200901c02c0d0071000b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 548127832 1250 548126582 548126599
    0x6150e01051c020c031209150906010b030105131806061406040e06060c07120605100e060907080613020a0503010e0a140a0b01030f060602060711010c020d0818070b030a050c090a05 79
    0x4002c0c3c0c80c1140250b0585101b200c6c140010720540360004502c5045820400b24448821360b14a80303c40e559600a200d4000c00c0441080180a2414108226011000708000c0030070240e42140030a03d40070851102954002c1d40c80f1824441d02c50384101c1315406681c121a810701301818403912850380000a41940d01c030300400510b40e02420f9050003880700400b804640d000c050303089404c0c03001c0a8007045030703201c2a1542c44100400c01601c015281406448060b150381c6850f5103110040d07481407030140000394482c0c40d20301c6501e503910f080d0000b400d01c010141d031165101c0d454440c000544c410042c080520b01c0d414801084688856445065400522204e01182404080c00160020402c01e04100b40050400c9008038007103400150b128000c41c6076030782c0d1200540202c6085030803914400341880050700920074078030710b2074420f84810341c121210a44441d0011002c8025504e0940c443c2d000303100440000c401c10000e0a5070707105407603110030113140c0c99150544140008500e5490750140c54443c0d43c96 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 548129082 1250 548127832 548127847
    0x3090d03020711060a09030c05040507080a02071a10060809030306031221040f0b070206070207050d02060c01050907060807090f0909030c06050c0c16231306150e01051c02 75
    0xb11a005249a0f802800007950384000d620000d041c01c519020036661003100d020001400d04251268034814040743e0344a150903103c1805c40d802035404008251002e085652205a060201c4040ca6015041003102d2003501c528229000c1c0481d0002441e441d030b039030002c4c170402c0a5528007061074501423100066560741c445040c403032140b1b48000d04034a0032809850320200000c0000c042081e14025009140e0b00360190384402e800c0b40d070740000303e45c0c00c80160405e0008120600b4101c240156003031000f403025007054002c0507030500316242140c1a006550146e00c0070025941c200d1500c0350403849078904841c0c0e081c20128200c14a04007417041224144e900c01c0398109140c0b14225503111541c1c000c10500c00b03418807800300c1c04141c11a5203442d200d80664240210140e20450660088803160210004840c4141000499065022001c40e40041e02400c1103a852003861041c0000ba1a50000c030f03413441c403800100180868005480c580c103200c03040200300c1c0c5001c0c20b0241a45c0d403030600000981d035042d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 548130332 1250 548129082 548129093
    0x231060e0105280b120c130b0a0e0414010f0b040806011509080d1701050414040b040218250c1e05010e070b030f0609070807080a09021e0406080303090d030207 70
    0x9403504820f1034440140012400031000e000824042407000210003240d00c51052010070351003480301c90380140388800303c100552010382d0003030108598a030a12403900b511640c042001c2e9a116508030030700088003401031103804005c6c0d2000c1c000d4002040700300d08050030b210300c156a0341018002ea110320070100c0751541c2d045214801070800752900c84180c5242c012540005447c94001548012401c9408400420181054890103907419004820b0513820349464032084480e010180060360031030314204690048980d035218480c0191844494000c240030780019140e454204181410301300080d1107404c2c0c01042c512704c9203500c080300c10b07803007034003242403910344907004000c18420010036000c0e010780054070355040d6024610030f0840111646841e80c50004025400c4000c5980c000813132800d00100300700754400c00032180d02c00b0304210001990011900040c2c9000c07400716004030341400400c090b00007410a40500b40081168900460940c1001920b0503100c00c90b0701100410143d010640c0018002d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 548131582 1250 548130332 548130379
    0x905070807030f2a0f020105070203040303320307140f040320130b030601050a03031707030f050a05090f0105220309090c0302090a17280231060e0105 66
    0x140030442c8652090744018981d0700410406400c2e00880c09030341c05e04e09580d0041c0141031140b0000e5005e98900790442e076090340c50035840001c2c4107012412664860000c1e080380010100c9c0a15900010784a180606008192804da40001d2540d243c00340121915000e404c025203013903d82c03001807040c0f604a80c64000d01e0600400c41400e40c4081245092007000d4195404142414810b5082c1c03003040c0c2e01c0d0800d1011807425840010002102d403011321140e04600c065040d0020580c0c40c0c01701c2c402e9001c03c0e080040d01c2c410b891404101d41e42d4024002424070412066018803a036100900040c9403007801106448118500d00c405040c0381c040c000e0400d8420f0a503d80600b00402e010060f41000c480c0050080d04003003411401580030349404100b032910a212074082c54408002000c040400340e660000f070a11400e80000d41807400c00d000801a076400002c41c02501d08401e80320105403020000081e100e0152034645140c07450080f050140403880380d040f90641c1c60640f0310020001446a84031102e4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 548132832 1250 548131582 548131601
    0xa05130b040f0605010e0f0307030803070909060f26061602010b091303111501090f1b0f0e0d0c030b0403051306080601021c0c030c06181505010905070807030f 70
    0x6450840c02c10301000c0e00f903000d201665420b03650854115460018001c460190008260340350707028000410009100c8030045038009060300c0d180c205a580c440304201600c3e0a90801e80245144201c1445489040a80d4607500c041c0d1b0b40c40c01004032405140c080d20707134030054642a00c58000000306111103000350464404e160029060715518a05806892400e10103200110000344210b408481020000103404000700d81c5403444c1c0d80e542e441c2440540c01809119075804d24140c995210480030315001e5207603600b407426a11131a120800b01c080081140c0681801c580c42041c2800901300403502080120041c0c030340c8041d03443d01c01c2d02d66080a440d01c0c0255864400094001d2002180313040d8440703851402000203070200ca0001042e1911002013402508090000414810070000860711600280e094940515000240498401c010030401c3c001008203951510060450400591182c481d16004200071103082095040006000705020006481c240405445005890740400b4650085400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 548134082 1250 548132832 548132839
    0x3020f07210503071b02010e0d050c041508070e0a020c030a110f0a1a19061403070909170c0f06010312030c080c0d0c050c0f01140c04050a05130b 64
    0x320406458103061030340c598180c4207070900c5108a0704030010300640c156402946552200030381c1421100f02c00c490400325141c1a0704000034508505c61503100c00c01c52006003070288016040304c0c00c141c82808250b851006001040b07401103003041003a44008500c80742030743c840b00c04004498032250300240c0139000700410302829000024181901c41d4010140d40c0c29900c02000781c0d14502081140035448d64030316803003c0c05040074011300303145910018032038951184100c5014000032581c140501c1c01ca90003500198502098050303019690b18003004804001e2240110600000e40c051791011641e182c20240441d00c0500417400e0103a10009001c210300e4502c92608880d01580d59060055000700d00a0314040840d26003d40402010320600d407651080d501103074814500400038440034010052007100e0030821038244a02c0e10441c0c0144649915200b5003070001c581c1c0b5410b140e0740c1138900d40161a0403c020010001001070b610703090006001c0301e0040b160784029031501510407000d0408242c54a91 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 548135332 1250 548134082 548134087
    0x10212030601053031260f2d030c03070c060905010606320d020913110702010e0405040506070e03010b0904151512031211160b060a14040b0301060509090a1b051f03020f 74
    0x540e40c0e842d01d0041c0c90b2380794038035440d84810b500941c909424441a500c000000c40200001003449004104c44510584500030005404c002e58541c5403c440440d0080380005215110b50f05100ca070460f030f901003101d2100b0a40b100000343c000386100900c18411800b51f829004108414603545015241d101a481c05000b40052500009020741a50086004a0119039044044281818144102c2d8400e82c0c0c450700401e12901d42c850199080c03905611100e51564a4150030b14246e107c400d101ea00840c450240036046d0f04500d8008003d664003d0300c0d03524000d1101c14100300b03100d4003412100034540c060400528140d04000144040c0c1080055075119000000d0004002e070384c500e0f46001a039010340302d1060551280810403003442091310443c816400048124040c600d0300c0c0d40700600480c40100002801070781c0e000401c02041046890003801d4010340341c810140401c20a0121500c0b02c2140c0c040c1e440e40c180720014204101d014000b01c403003814803c0100046000e079040b5a03481c00d800400c2074 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 548136582 1250 548135332 548135347
    0x711011e05030702010f06050d031d030307060204150c0209011a370504060c2307030f0507050108070801030311010605031209010212030601053031260f 67
    0x102075501c1520f01000661900d00c400074034240c00d224150a03281c0040042c80210b0858504880003800082c62115060401403001c4940e98100003d210851003504056119031a101c00b010758016491404024040b8002d04140180c2d515880c440c1554820019440a0361400d00550258002c1894040304299100d01800d0442c040c14110501006111880004802e408404440d50b020754030403600030401c140210302c0000c0c818855001c0d080600c0b450440c60600202e003103441e1070416441a6260300724031140c481070100c140715010203400c00f0300b03241c4007508051400510b0754105210160400003401804000c0000a4002ca0f00400e8010110780c0441800c08820b50710368440381c0e80601510504c0000c04460a0f003c09582c0b241c241616003a0034040c004200c1c00030070b98820001000b42c0b18400400c0e5850200d2021a80140f0314a0074608201c42c104606080381c000c120f2202c1c1c0181c030040010400a0316000051a41001a501d07207001600c1a098404032800350804030f0012907004074502c0f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 548137832 1250 548136582 548136587
    0x10902030c3142030305030c07050f16050a090e0721020409080d06090e1902060c0303041b29162a0e2a09040207050a030806030f030711011e 62
    0x3199031607494840410001d20301d0f01541c2c2c041c110b8840200131030b40a00020f07283c03a088402034110b4a0160050740c1504610354100b5003441e28140482a00351a1018140a20706003504100054501c90720200080c503a42800c0594071003a901c00d0b040d2001c03183c1000f140305603000381c41148a9034003074800d10068400789400d0a143c1c01100e2100107c41c41c0c035000155031512400b800080d030a040b805030207480006400505200d01a1a00780c0c0c11400402c80d48070640310410003184118020010005c3e903912100700c069811b40542d000c2c40b548011642d03660005d10760200041c1d0003041e5104980c4d500c85414600c01e12147d15840302910708034a002c80c0c00d060005008000f62040b000c148210b01203500d507100a4080a0b090318280030740c003c0245c408001004840902e012511020603860070303e2003200028045c0e0740100d00803211500480c400e03000701608a00d6203500010304801a016421503204450303624011880090709415104e0140e0920340d000d8000800701007401c820800c2c034002c2e100c901 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 548139082 1250 548137832 548137901
    0x209010306091d061003110f04200d060b18010e1203160b0106020610030311151602061b0904020715020a17070c0210030c090f08010902030c31 63
    0x40e000c3d140a8000041c5002041103038000c25a94400d100c0208079100d40280040481c60101c96a00142e8031104040c6240c620500d80f01d03c1505107540e21f0745d503a03500044400f50b4440e40c4c001031b0744e035200748000054949074501304207080c042860410089400c1c5400218407a40203140f8a106000005001500f8825042c1e0024900c0c0100125a2966a14040bc07603403007008403410787d201e542c0d00d4403c0c40024460381c0303051002c107414000c07611000340e52646c920403c0300c107507552803045084540030b44100c0d405020f840d0713200346254040c0d020102c080000040d10311408100600c00c80d400140e040801c12501c005000f0410a000c085440c1c0072000c8c8007511501030a0484514200d061001500f807a11490440601907800f4000709007003140210207a003d005501c8030394050240400000c140d1a01035441c020041807410000315241480e8018141440c0c088244a030260310700049040044001900c160985143c02907910450081d58049500030012040c040564014030b42081c1c0c0d40c07002e0350b4074 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 548140332 1250 548139082 548139131
    0x190f18030815091b130e09010f050106050a0e010504092301090509030d18020d051b03011104060c1703090c0907050304050604121110060602060108120d020901030609 73
    0xc0d0603540c0e807030360751081922020103250a50f01c5200100001c20402c900106003030a140c080030102d062401e00041c902003000c00c1d42000562610000c10000e11250901030000300303000325807040020754109000244180301e010040e0050113403809290989034070510840340107000e01c03001040002c0c00d28016550040b80c03026070071030f4130550314000b081c140114411613004000680003145080030700d5040700003030b0003102810f042103080504071001607103c0c008500b241c81d02c03510160403100c40350842071100040c64bc101078042d030b1510700c0c1c1a401c10301c0003044070b007618002e0070a09200003440c900b4103001c520421480504070004010b004440c0710014012420280458038115640d85d2070000711140e0208480c007400a40c40200424003060f4815000c00c00c030754480c40d00c803191001c45c8100301d14281641001e4a001c0341e0390541000483d5050100c1d501400607a4083c00b00f0584144102001b8041e074460b040425030b0004048006078006c0c1e00042c001c103040c440620555444000e01c80c1151110710303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 548141582 1250 548140332 548140337
    0x1080304051008010b040e0408040b1c0609090302071e080313050418031e1e08090c030d0503041203230a110322080906161203020a0503190f1803 64
    0xb140e40c0306103000d81c200038141c618410100d81410303c1d00c43c0201030b803c0080e10036101d106040001003001d4200300010680c01c0c45640a49042c41004100001140c12540c0a01c80c0a0300c4d000b0984c0001e5401701e960422503140d82e00745504030300c1034820001c26242580c05600c59202c0002c502c40d101400b90300003811540102c40c10459400000c030842404094000010000381d03030310444080003e58180c240c02e08600b80c0c41c01c1040704c0c290319038440c8108202d050280105049004100c10000304010040b5030302c000740c001e0441d00c0c11844d00907000d0b02001c0d0000b400883c50a002140080c882da204116045140c408a071800002a43c1d4940ba284143c44084015050140f0108901d400d0707403c0b68054403a83c0449102ca43c0e888098094140e403d039011a00038500f080742011990390b52014115210241d40c4552240c580d902d05240c013000d2407006201803600611104130505e8110b82502c1c0d0028000b000c10301c0c44103000032118002c18105610450003446c00c240c0c50042100c0c8114054440d21a4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 548142832 1250 548141582 548141599
    0x1030906022208102a090f06030f15060f200303010906081605150a0203071a071b050601050f12010f1a0103110703050702150a050319020702010915170108030405 71
    0xb80c11140613125040c00000c5c04003031804034050300864038103c0701c860070f40602e0000c06041e01d4000307140d800502c644c003140019407278030300c0718403070080e1886181d4100000c00001008a0328219001e042d144184200e0800e00c40342c40c000e484985085041c24030074014000c00c0d25500d6840d4050180140705034054a03c1c288140c42c1c00049841d007100521046e154010240f221318803e0000c6c82905500015110b01140402d120090008040d10f05840c42032241d90740d01c155900d08664000d08141c01c0c4458002034044030864500411030110700641074035030594500e0340443d20b82d004070300c104d15200c81c9104151710707200801c80d40c0281e503480031036242a420b00e2144103000f00310044055402c0d0288581d0030003010132403a000240518020701d15180b0240807036100c070000c4410018960070000c0c041000c907000204000c0c600c034114001c0c074040c1103021801c5003401c01640008206041c20b0090f1511102d040b80840355460003944120030880320002c0184140d030316201c040761285c01c44c0c4503140c0560001c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 548144082 1250 548142832 548142853
    0xa1208060102060601080c1308031602010e030d0804150603120f030c180905090a0f06020d181a0c0906070303091211030f0703140301060314090c030c01030906022208 73
    0x4260786001d06016500c6c5450b075103c5c1c5007069459071000004003420b0f8a100760004000300b092018040c1c10072407007070040040c48140005032030060003481c80c9101c0e070000192490302540000c110768000d0381181041c1c216142104008004000300c0e0005401c0f046103020200e03845912a01955012005581c24884a0890f6009443d0090f50305a101020620044140700900b8264407280d03001210604545800c0102d40b1400c0e1085102d0409441d16500054405500c0c010ba008900c5a0740e46003096038188107082e110302c0301c90346a42598581c551406030116030040c04440c165480010004c001c1990780c0d60914020b001046c86940886440103200c400d00c2d05140151000f032034680107400550701d0120700c108100c00c154040c000407018000d58214843d09440c0e2035001e180a801d440c0c600040074088070046004d6a9001880d40d00c981c3d00040c500305498802107440c0034000304c2804c0c003007415012842c01c00041d001e62054000506400c03a00007141424402a540454083d0800d031100c00b242e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 548145332 1250 548144082 548144087
    0x2130609051b162d080301030c0f0b180a050909010b03061e1602070807030303020c1c0f230a03021c05010e010b030601180b04060905010302090906011107080a12080601 74
    0x10f803030003521100000010b41d8085000f0100c0d000b0b600e0341020b500990350102410300303040c81007091030540d1024804001841040b0540140c00d010b4140e20305582c100c5890084240702c2442000c2650801c2000d01460410b80d45a601c0e0050240c6401020a50f551620128441c0244002c0544520a1240c9408515012034003101320152000c0303102c40e000542c0d01c0a90101c404070084010380110300c209d2000059139402449500c010350303c20741e005a03036004005089460aa4100310140d420440302c001e189501d5001810f581c0003c215040190700c144c180d08040958010364100c10a40100c0010340c0d91019506078000c3c07210511800f0b1000c000c000022510b03044079424000c118401000800503c1891900b001a580c002c0781454131042051401da5400103c0b001d9500c0800310a1000c81e00303008044e0005203600180c84280b1b811400d1a010000095032001c002d49914148402000c8503030a5030024044003024002800403070b42440300701d04d23020801d9880d10303118000081c60080800d28962 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 548146582 1250 548145332 548145337
    0x9030706110d0813062304031d091006030c02010b060c0a030201150e04020d1e03090f080d090e040f0f0c0302150f0a030b0102070807030b041502121302130609051b 72
    0xf1280c0707a150000c0b10440da104801403a00c43c0946c60a00c921520340d9648607039100305039203e01d10a40d10b6038000328814000d04102c400000d01c4512030b050001c2000031080107094180101d0b0300500c0c01080781c3e19404016070041604000703007508054006072680007800c0c0050206c0c5464860303402000200144031900d1502c1e0304900540e842d0109840200e005071400410519043e802513101690040b490f050311ba0300e2201c0b8a00c00c070046040344100f04240000c005c9104014800c040c041d0075800c40542d80202820198041d030000d50202e90003203014403070705465a0030099400343e0803541841c1c9900b444000c1e541d070380c40101d2080d04660000030040030340b00103403a44000c5480c109400d12160076001e801030190340f01d0640c114482e50100080c400030810074540118040c0115a40c9030805003003a00141c1d013400540640d15004000c540485200d00d510325500c00030305000c50381c40a00b03d10000d00c1e1080500080545103090110110705244558480e90013035a2005140d03015800d900c20303036085030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 548147832 1250 548146582 548146591
    0x10e060406050415090315050919050a050616170c0c0a1a060102070302090103200603180111030f0f090a12091811090d0501020706050405010c17010806040f0809030706110d08 77
    0x7180c0c6040240e4205040780c000503000309c40d24080d18a005a0544026140c5035551390a6540313920084640c400e210041c070903190811000125083c040b40031940140c2031040300c400001440d03414100103a01140707003d090b100c5055100090f1501d00c401030500c0031101015252448254402001103092507000007210f004407980684080c5045e03195456810003180c074850032040101c144001c045460752030000461040151000c0e04101c1545004500d00311102c81c2c1450303074020803c10510021402c0707580459072160006120800c940d0b00e108005c0e041804a54009120801c282c1e900d01c082504146000c09a60b10b00b017110402c10000c80c9800c09403400401003284500041150740400d09014441100d400d01a03400549480c2c2181d4a10b001c0314011a429130322030f55a0203038075080c41e50241c4081d419516410004005506080d19240c82e0440030f4001885590008400300030000c0e80d03820741da01400010140c0744102c1e41d0313501c094040042c2000d03500c0305014003003015181c0d40c00744030000d019 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 548149082 1250 548147832 548147843
    0xb060f1f08091912111c02011e060b090f1201090f11011806120b09010b0d050c07080904020333100201020c120d060f030305070b0f010e0a0b010e0604060504150903 72
    0x120304c02c9203000d42d0b13440518502410140a44017618940031710000312914940403641c0002108009828659210b00654802d596074900f0041c1c00c0081c95800070540d03505a0703044a0f4040c03605040c80000b9050b084425840c04a942006900014495001940c8540c02e0091001e0701c28200850300454004114601e2039580908021082c0070301c5104800e50f13041800b0640e400a000d50045002881e07844c400d9124081c4100000f1780c501002d04203016581c0c00551002e2080e0428205980c1d4825030b0050759a181d01481c1d02200045080082c003040e8402d401d00c01d4001301d00800511660384070141305c504d429025410751030f41041e0507403051007200c80c84104d070405804014140c44042601d0ba0001c0030328a00ca03500c81102081c810300d10703074003d8021444bd888141d924103051824030400d01c8001d064000304c41101c0300400100603115003065000848500019200440c080180c0e60400000d410540048020a0120700150810018415140015200040c00c11141c00c11a00c000450100812 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 548150332 1250 548149082 548149103
    0x17100305010c1412480901050f16021f110f190501110f0315060403020d021201141303020705030606010504031709100909050a06030b060f1f080919 65
    0x418103410103982c0c0004a000f030f000000401d620400002c008004900040305c000c00100c4801400c80c588188a6040f00400550414002c000003820602803520180c1880b10700166120940c010404040065540202840c0421001042c0c019010102444650102e900e00100030b030843c40014001c81041c0520004000600c4c200640d401400301d1904111519034070380c0403286485203140094810302c0d1a00c0c42c2542c992800342886421103480344010380c01101c0400050000d0303280c010010754043c6c1c041d62000d0b0700100e440c6443c1c1c010209074500d0800c503a10704003486403e00200b00b001d107445010350700702e5510984031810075807960003c0d1445400300700104010070018017040102c3d400e855184074a036061010b81c2001ca180c1c17540f075050741d200090724040e052014241512955400151060f020400c0c14110f54a005024101502c2d0740c0c07052000200c0b46010350313580183e03000c0c12444c4c0781040c003112941440c090300c845000d440d01d807028010701c1449110140941c03901c210881c1c1100d441007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 548151582 1250 548150332 548150347
    0x2110050303030a0908271c030503160e0d05030d060801050108100c020a1728021b0d0606090501090e03030f130c1d01080601050f06040b0a17100305010c14 68
    0x3e0003808007a90032039860301c080c090000000c50700c4045814800e4645812819032214200b0803d00d14403140c0b182e0300ba160a04000404030354800b007030306c0c2d00c04080f840c0052041101c0d1820740380c04540613260f0368800c084004810070824048041e01c0c1c22046504103004454a40c00380c103003a6002400b0300500c030703803015922030900c500300e40000e04c1c10703d910b0065614070700507500d500c501e421101c41568048180050042031422824034001030403202c41d1198101c440e8600b50082d1a02400c1d03005170800100041c000300e256507807407020359a00b580a01e040080742d60700c0c85808040d14007440790130b01d040d00d030901d00000b411011003100d108612a0b9074449407030340d0f0301c2c8502880a6103000144e6011111340d50210760381c0c00e11061000c11030160180d040441d803501c106e281c0ba222050f0496401804420300d101d01c0ca44401c0300b503c3c10f9401070300a1546403401e1003012a150704c61041011f007141e0100c0180442c0407070300724605041d2401840244000080c202e0250380420308105201d549410412440 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 548152832 1250 548151582 548151601
    0x30506040c08041b1a0909061c0f080f04080604120c0308011802040b04031b090b180a0213030311100501030c0522020309010212091c110c0303211005030303 69
    0x110701a08500a0207454681c42c0c0350b40d4400005d071248005020240010400014a001810075600c1072040307030000c01a41e07034180704500d295824038000304021803814080081184402c00c0d80c40410b40c48a0540c0c440742e80301078460b5558020380b0151003482840c50b18a004034807800800210680540700c08071183d1030130207004181188440c400f00815401e22000c614000101c00400c011030007140200c003d1500808402031040840d0b2000c0515407400e074a0000d82c0d2964400d081c401d258103161125281d440561304000b85c0f04e00b00601050140e012004000c16400004400548604104a80c0042c229240080c2107800030300025005945450007000303e80350000017540b0030890117003841a40818407020f11300340e8105540301078659401041402006421500d410f9004482c00020828290000d0380503104545505c2c200d8100201e080a005444008101180b00c00f613000e070440c0c1c0c0c0c1d410111000301c03c0d0310b0030340d000000910815022862900388a8400402d4890042c05545145c8444411 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 548154082 1250 548152832 548152853
    0xf13051f1a04051e0301050a091104060510030e0a02030609060f0f100513022b0b03010923190b0106030c021c050c0a061103070201110703120c090909060c030506040c0804 75
    0xb00500c28000700411213282e2804c1c00307641d0151600c4000402d02d11a00d02e031440001070910540c0d8040c1d0300d809c604010725030312200400002e034070783c0c10001074001c0e82c0c41c202414650729000203500740c440c58061091454000491764880ca02c0131a0130310300c0e034a911201095021040d00e2000308114040800d01c0141340c200301408403d000040c005160203610400c000d84200a000007450014080f1b00c006629081c9004030821904d040b0000c10030b4036600d80d40c05103001006402d14a04034410b240828904900300605880c00c20f00c04425580b02e403203481c005010301c2d024024240082d040c51803200700c6034000212035070b0740d00d4481c043c00380e0280d510204039866049043c00444a01c40c0c02000781c0130481038807a1901440480a216580b450043d40c007a003511618511324890b01c008001c0b0703c010a501003080800c0e40b04948004c681c40503007060480b140702d181e8118103034180c1b401e009030b4100899a4001089042603480034050703923a4280801046034429000e203804a01100d0002d030004062100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 548155332 1250 548154082 548154109
    0x318050a030f031d06060a08120403060504060603050304080c100c0b0a050405030d021803010605100512040507031703060a0e0601020709021b031309050c040f050f13051f1a0405 78
    0x300084c43d00391808038001822034519044202e07401c440d05000150510012010241851f00c0c01894540604a114140c80c4214880980b24681e2074011908200c074a0700030b140151307084403c5030380300d60310b0b800380036140c0c2d03840307418640304408a058400e012401399664030b1107550880e81e4041c0ca030341c0300b16040d0060310303004008581038002006104e824040e40d101820110044100303040305152554245821a503064010034851030307107804030401e210f60050454030b044c2700b14011003405403918601246000026000244010a08100400481100005107105100032a402d0303068a5a900440702200c07070560303006005802443c1c090000c030101d0380052803000300705a0000090307284002094155004cd041c00b041141c904041000400b08a000e8140c011074402d00940c60030340b0b014a00f24100ba150300c115800343c4d2031422104110703034428005500b8280390341410b001d41e02d03045540019090744c01206a0385800441404110926a40d16480300460455403d0b440d0500344410400e0748030302241d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 548156582 1250 548155332 548155337
    0x90c040e090d120506120d050406020f060c16050307020405010e091e0d0e0f102705011d010210050a0501050a0603051306050405030c011a210705210102040f060318050a030f 76
    0xc0610951001c2003000030420740380d13588c0c5841c0e40c05d02c000241442c502d1050500315610100c00d00c201c40400c14126841020628080c649040e118900503065000702580030f54410301d058000580c800740a1203c51060411100345c48140100d00100c1070020304060444ca01a88074400c0b042c140c80c090705000714030f0300700181021590300000000452100c503880245000500600710f000c255698411034601c82100c0901c4c1411480c00e20340000c11114030400c0805803900785a55203440d42c2d0090000d4400340803560b40602051401e80204000b524082c81014091314001400042e02c6100348146c5010b40720103101c04150190f503407103100280001a10548840c0810084002074140922134103026050311800320009142105c202b000c11880544111049007502c4680440d902c0c010860000391001110107014a41c1d0070900342041051000c04150550304c00100841c040c071090f5204000c4407915a010311400402d01400000600404030081c140e50080c00f01000081c0103805032182404c5a1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 548157832 1250 548156582 548156599
    0xe0405060f1e1009080d030504150507021e0102040521120d050618060d060c090b07080d1a060403030f140a0e0307082d0c090c040e090d120506 63
    0x3600007004106151009a40707500a68082e80750b60600c0b422001e20407000d8146890420320f000d68054a40004074492010540d81d14001410001c1e0b074980b050b01703041440d50411032032404c008040d44c0c51407600054441c141c00101c1c1004290014000c42e0182c800c081e102c1c0d00702d96820700008074410a0b041f031a051302e0080003440800300e0768040251100800315035021070541412800c0c07003040b20703100c462500740001c00c4080086c2500d54014010050368000e40008000d0051a001c4a540480390042c05011000062040c10310840802400034824408030410441d1402d15440b1421600c481c81145c020f035050008001007806a024107504c8410760400344403c4020308107121441e40214811000316451a5003501c060504000ba500501560001000c0c0042d90210400030300da40501c0741300c07620b1811940300c610540140949100324401270118030860408140301c45c0141c00030b008540e860000400040c0ea0030300c00080d070515466407601d030a240d1001000c008405010300500c240e4202d13815 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 548159082 1250 548157832 548157859
    0x2031012062d05010603180206212404021608070f0b0f0a0c020c010e1903060914060c070f02060f0702030616030b030c031c02070f0801050103031205070e040506 71
    0x2c00c42e40e41d5409000306450412500090b0007400c454040c0c006a040500d040c051400d104603110f0700d0544140c04890302e079140c031904842d280d001c10465810410f042100406d1110180c07e40342e400340704407401080e9440f540c1941080c0f01c104d0051103507202c0003a16078998200810b85003001840030b00e0240002c01d001101d00c0d11040c0100c40c041c0ca4100c2c0218040c8208a0301e286603105d03a00e4041d8542c03010b01054102c403400203045076561348007584545002e41e0300b95a81119074001c10010742d03004c281444081c1c0c1d10b0500c486083d55080c440d00c443c0c000d2000017610ba21001017214046a44640c4111032000c058003489aa6040f1390511042c100081040c40c0150341d040244900c200380d04170052041303080c1050014144c0e03151383d001c10700030303485001c20360550340e00851190681c0e40041a0902c2e0b80c40c004004920380000c0d903002540382000d1088c04500d0b9401904035505903070098990601c40110081c2d06812980d0840308000010780b140044035583ca0250052500420b0080081c06500b68 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 548160332 1250 548159082 548159111
    0x7090e152206080a03081e0a1d120a081b18010504120b0610140d09060b100c230d0e190902180d020901060807030204030b01030803040203100203101206 67
    0xba141c2141000b40c1c01140440209170340410600d51002c0700807400750800d00542d0044c41d55a10141180700829112410320081600c151381b0121010a41000c03a2130840c01900c41040c0c660050080d0301c0040d1304c5600040352300005100900a9040c00d1441a241810f07070f41c2041e8403d0700b072101d0300f030410004000c00100c0804203000000c1450003050f91442d00e040100c02c1140c0c180512444905001c101c500706942240c00b5401d80b02e94500c10a0081042d0a131032418100070143d000303030795500401010b002c000b0242c2c07101580100e1482012580c280c03008080101103120528050010075034026000b1050080c800c4c200b00703041c150081e001c10080f840b0650070314000d005541000e225241d000c81d0340d200b100b048910740c203074607001a2821205582075401241810005025013018404080081241244240d04030b400540c0c10441052441d6102d01d00350405d68000c1d103050344a071043c41054441c0705000e1003160300a00041c10343d5000c5a1812001045403989804151041550364048501d402c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 548161582 1250 548160332 548160341
    0x30203120c1e0d030b090c09150417030c0c03030702130e070911091e09041712011403010506181602010609020d05060312090607020d020f03010c0807090e1522 70
    0xb50820050f20760560100700050072124240e0005201e401d086050120182d5544121048110290381c1540e220003500f04c0c1c2c1c0b074503215a07400003480201007200341040010200103890000703203000c2640c030a200e12070101a83c9000d2004080d5220005031506542420543d014101c07407900c0c0c0301a2146950360320340c80d908442c510320781035160340340015000c0d60500e80141d8203004520300c1002c81c221111100f010400801c401040100301030b1180c03105101c1c100014045d07401840c00f80c2d081201942e124900442c0d61280c11a41c40e01a60a10300440c401e0301d040040354485140300350070310f4401e590f120303031114807115910101011742d542c480005c5641a4507000600c05440101d102203082c0c00c0020074145050070782e49240707100c500284160001c80d03440400312900f580d01101d420040007a81e0000611a4959440d0381b030345513203408241d2070300d2900245e040c2d120b102070380c40d40942c142d61801810a1302500321348600540c0f85c10400c0603414a070403000400c1c00d07101089109a2030b01d44590031130071207 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 548162832 1250 548161582 548161633
    0xa080d0216021816080c07111507150f09110f01030b12060402030c090f0a050c0c0109060f060b0c060c18090103031e030b100c0311011e1104030203120c 67
    0x10f0070840c200051074403495039014107210203251a00c06464400905405401100002000d01d281400303540d00a946501c4604401d08a00b40d9071650344da01c07454400c03080c0200000540d2414101804d60050031543d10860a103a40c000e5104d0444580641c00c20550010400d103650606a03034111050550310344460b1640410309600090040e410107004251900c2c4000d2000c61091545078104108816401956a041341c20360781d01180301d8484136552650340c020320b44014031540c81c10304880140002da41203007000c0c008080d410040d068a61071400d0480c07291403e40007503a806a0f012808101c440310040201c092403990038800a00c8110015181c2c400a074415000918a000a0b030480580107078403036801c0d14030342010031000c1d90140c00704160706d85480d2204148000301100000341406540e040721035041250003000b0b00d1029440664140d101314146c0c00b40d203880c0440114030044080220340940781c00400a11011601c5440c12200350301c024003e4090340541415200180c21068035030301c40 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 548164082 1250 548162832 548162869
    0x30a0f110d09230c030705031903140d02030405210a050414190b0a030c0306030b01050f0d21030b0a080303060603040c031208060102160e160314091501080a080d021602 74
    0x40301410130406140c8440c035004948284c000030300d90031040d916144101546549803d000684056100349800c0b01d001c1d03950340c84001030002003000200032010880d054980f40400303d240c403011082134070f11101c0c0210010030f40810420081401220007104000503803800040452030780555801c0380e002c000c2c3e0345034000030382c0607008990980940e0f014000c1d80c1c038801c068030702000480d14544960340c10300018440c035801590700204410094803400810341c40180c1107a481c0710408000c44910300d031a6841d491110029291100d004154a030001d48442103e196900940c10341e1610300c10403026600141c021140800300c2180040040d070780d041442507480894503115414940203001900342070700402900e90030400f62205000c000000000070f60022203881c0c58001c030032881e41c000d4005091102c83d480503110b81c01c04002102000040c20741a00c080041005031607680d070716040d9503039580404001c151150501540210209030380c0a8000c500c5614501c08210305541c012481000c0300314a146034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 548165332 1250 548164082 548164093
    0x1020403022e110c01030b01122a020105010305060f190c0c03090e0f18030408060c0a0917030a1202070f2d020303180a03080f030a0f110d0923 63
    0x48140c215808441d0024250030801c0f84a404010200d4980110302101d5040c5941c81302040d1007644030b00281280f040700c004080244a82c14500c007a071402000d038004c105091290400044e01c0d1060142c24100c0394408000e10068548401502189200410302d030040c103410402d407140c52070b180c06488090f248a0703c07029031880c071f103007001440480c0340d405c180c69000024050081a441122040340c1c803924445845415000401c3e9140c114881d60780104030f540b02c3d4a050100025454008145902d05612006000c036500c0c0c070758401c01500c0d00e2010140390420300c11440007500402d10001c00c02082440186410b80998801d505440120000e6801d43c00c80341605c601017030066204540ea17038124540802030300c22680026940d21030b029038111099018140102c441d00c401040c04013039580b212300c032512114544006e00c3c50b80c00894400c0b64203410b00076486490301003031003100f0202c02130440141c58030503070070044000340a102070125001c200b141c507005c1044d070207808503120f40c0000401404c0d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 548166582 1250 548165332 548165389
    0x215010e0f100b120601030f020406020106050f181302010309120f030e120a05091201020c100b2403041a10140609090f13080712021b210102040302 65
    0x1114034004011000802c1105000e2200c0120481a5200180003200750800c940d038a0b001203011301070303c04450050500118001c107038181c040d00440180d0b017060300d06001015030901003100b04000460071901d00c10f000c3c40802c8a030030022803800034413070040c14081058111a6200c14040030305c45889400030311640b20350164180d15020780c0100d10f209000605200e00100a400d080d4440c0ba0038807002d102c00000e0b1484551111600188130103010002151281680e1b5811502c0380300c200212031041e4600107c081440c40c103a05062907010030144101030744840c51101000544c0058030030341d0292a2042003807008030030030000910811034090401e4620303280c840409907090312001024850b603421b204003941c94480f40005070384020a200040c0e43c540303d0446c5070b200d04960440c0070f84038480000300c007010302c0580292580400180c0c0e00b12441496540d441101c015450030a803a8800c0d909840c0440f80d100402041d1000d81a0b07100040c03601da41ca5000680c20b1240d414405520943c40348580c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 548167832 1250 548166582 548166601
    0x601020f06010f050d1407300c030f08072109090513030f180b180607050d0809150a090b100303050f03100902030901051006020a0c150215010e 63
    0x18800c042030200208155410410f120500402601905000391490441002841480808020a002c07140199002d5940380e082076a04c107003011511f03c510b24006440c2602021f0903242420841d6000454040e0312411030341c41206a00d0f0b052010707258603d003805500003003882d0000c1c0f0030841c1051011181182070386134001d0320805050b070140c0303051440c0c0801c00c150403500341c04100c441540b620741540c0045402006132020001c461080b0003560148002247c0819500c00903d0241c81000f4140c026552503010484a07114142c0300231300ca60400711700381000500940000e03411140e0321090b44c0c5150107400809010510031183c03505810340751100c050070b04c090b801c0d03440e4000880d41d018034441811510040c100307104500d103422910600100040348490289401005000c00d460259920b0508081582c080c280503540302c110505c80d41c1001441d01d000140040000c1e9004200d110743c00d00e05003800e204a8419402c0300150700962224035150142490308601900908040b81c0c154100070700c51 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 548169082 1250 548167832 548167843
    0xc060c0c0b060d0302210403141b040216112b1a0903031902040504090809010f1b020616080c0706230f030a0e100e121809040821060102 60
    0x2d40c041c4114107211404280e001c030711105028401450003c0c0c900d082a814030161080d50300103023104007240100c881000000c07131017100d08130346001d241b1f4000c0c40502c05c0004912540344c0c6801640110201d120014152084403c14108001c1c18406841d612200000311114030750044bc0d0995802032500080141c404030520400b4260448081c1901e000c143c507a40e64840502a101e80491042d0107101624090701210060080900184510303800ea00d004034041d00000e1034280410700c0310001c2111320b40b083c0301d09500f19181d0001c05440d400540c080c050b40f940143c0030034100903070003e0030300c010a071440002c045900c0d040c0b000b442d01a2810310010021200a0441d44191000c560f0020102880b081596082405141c55071360301d0b100c40c40341c1c00090620446820709030180a50201304a400d80d407000098107000d0b000d462100e000c0d12242d80e82c0c1d00c2504035450401c1a68000418035042101c44580e103d07110f00303a814506404510100b809442d4402c5c101500d03c608000c221965905004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 548170332 1250 548169082 548169091
    0x181d010c0c020909070906061125051e04140405120901081602010b090a0203011a0c0d0f1202190e0301141513020705071e06020d050a0c060c0c0b 64
    0x200300c11000d4590041401a2007007001c2d11504058010070360703608050005030002d103500c20707041102daa40d41d135025003865010040c0c031801d40608a81040c01601d90900c5000d04020001c44104480c14501080004079000700d403044e051030096105000340c2c0300c901c81d040c150040c1d000702c000c05103081c1c40c12502d8450100c88100b2441d42c1401002000d9801070b608607000f0940f1103006400c07070034000c0100d00401c462400715600080c00f0085c131420f00e0083d030003141030b900c4a681c40a0a0254a103d03c5194407490902c01616032051140d5000721b88580a201d40d44510303031402505010494829405076001551507034481c0c0f05481480c0c2465411108140c0d4150043c0c0c0240500b080602400310b403a00010002103900c41c42d40003039219565011044001003101130411034445210b41803a540da0202030082c00000c000c1c40d543d615046840c18903202c2191a654020984184e038031004548641003488560180010680303241c0004026000c2c1d0000202c181d82d90101448541c10580c011000261 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 548171582 1250 548170332 548170391
    0xc04030818040c11060f04020f09040f11031b0d03030e030a0504060e1c060e03090324150d08090a1d0702010507090f0302121c080114030d0512090718 66
    0x703a4542c0e925a001c0780c417551003609140404090b503924004221041c51a240d180d0303200c0b1201c404c01041000c483e1003184081d000340404500e4441d020f007450342c0d6103900c1404000403540814480345c6ca2030b1800840d81124030924022880c558503e11051540d0003900b030100c0810300c0400c09001541d404910302c210141d04841248100c0c400340b100c21001c980d0070801901c841c0e141d08007856803000c02c01c112801d443c1d0280c200c5401c403d54507030314107036004940051701d4004611008503c40c0c1c5003201007444108070042c03c4c141e680915689010342d5a2000c03840c1a0405070914000030040c00c500d00c0021404541e030003100e158586500000d08580000740748005010407040f052011031840e81c402010340350b042d6104d400014422014a26101c0c01c14092401c1488415a9420056010b04050304990000c0f83c8400e546c1590001c0548a141c085510400030310180519200900350705081c54101030088247c0d20b03003c0d201c202212011801c1c2c031504030b6454a90340364213202104115940210800e22 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 548172832 1250 548171582 548171597
    0x10504050f12120c180604060507050111030402060306061b030409020406030e0d140a14030a14090c100309030c0203121305010201060e040803180f011406041b080c04030818040c 78
    0x1141c00080b500c1e00a01500e4440d01e000c120302110103025401100e0045c0010403040c0c4691b034400f002001607121f000100c0b500c0d401c00c6c007552080d0a091054a0007107500030989411039403290280702c030903000079407007025501c0c03078800101c80f812081c40140007400c1080f10159643c0c0c14218042c05a80210a40c035816600a10f20130040a0380302c0804181c020800342240d0fa90f0010070001c840c035611203000c84046107000418000240107543c4081c00c24125040d0705122547c03801d211580700e4031480343d007640141c0c0003d000c500031031195102440035840f90a04108000068010a1505400e81c4806007031410000344202c0040c80341d100c49004050900c001e1010b40e041c1100458081c8010344020800c11000c004141e81c440e00149101070300142d001101e0301c9829040301c1c54060481d204118034000c03083d001051080c14240186006c203400300c00c40b00024400c1002c221840702004201058444082c0000b10004d03d06074000c20f02044164900a8041460340400c0101c5160015020500805 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 548174082 1250 548172832 548172847
    0x10c020102070623180f220b1503101e05010215090132070e090402100e030304030507050901080105010807150306090f0504030e042009060408010504050f12 69
    0x3070382c0c03040c0e481614108a8800c9540850024807061030100c1c051508082014001c40040100c501c00f400000c0740e0403070700b150086e004e00c071048a50380c1c842c0d84040c000c00e507480440d21158220726540760000c0c00055240310741c440100c10541050b5203008042d040b031102003100c100e207109030070158130444071410703e003e10703000020b541c58202000c80c05050580c00005001404294049000c0300c0f0700310f1000b82c042003105c030404220503c58000c0c00140303107080c01041059200e01003e2190030800f84c503c0300385481d80c0e001c0003c0700c1503c00340c2c042080b4180c3d03c0c800c5991011700c09000218030540040003142c2c02c2208000c6000f50581150b0001d80c9050300411100000245060407100c2c0365070258251001e0b0a022409404107030488844181060f140701c1000502d031340304a01c11030084e954803610250490030481034814101001070301d0815422024900100034001740001c0f88010041480d140e41c8141190950b60102e40079140c50700300044050030b002d414030a0200724000c00801c2480c2220 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 548175332 1250 548174082 548174087
    0x30a12050706150b1218031204050f0a080702010309020424091d0a030c05030f040609050f01021506010e0f09040303021b010c0f05030a0207140d020f0307050601031106072f010c0201 80
    0x314466a1703041103041c1d0129032582c491008442c21041450103070303544e900d81c82e1604404200c2c19542258640304d04c4028811060f00885d160540b02d61080440d032034961150011406008980f4003640c3c840d940b46903d452940040344c054010f134010b4146491510300e04500e400c100c5072400301d00c01d6041100d091300450174002040c482a10703641760074070100881d1103050107451405080c1e0a05c003100030005002c906180c0101201049890440e09508441c03030003001240c070b8a4001c1a00710500c040030f008542d4540c01100404860080079028114540c032940025405000560381503011070360005200070182c0e1401e0701e0805505062000b44060340c80010005d14204840352114200000400400c1035131503560100c84400d508107140700703d0b002009a5054540403030f0300c183c0340584102402448103c00100035038090b40e030400060051a842d540b00e504890a451105583c03003c4100941070000d81e5400101000710110901e000c06926460381d10307160291820072640c1403141d85547c180041c1c0c0e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 548176582 1250 548175332 548175337
    0x106051b330417070312020307080a110a170c070f0b01030b0106050f0a08060409060e010b190b032d090102030106120204210507080111070b01060e030604030e030a12050706150b 78
    0x2140914030315130f51403503030408641465801e904c2035409400003003441079644c0d01a0016002e641c000e8410030414800c920340c1d031820720406000c9004103d002d0780e82d00d0340c070301c241c4001580003401000d62850556a541d13580702c078862525040b600d060208005100b030100720000c840c0500624241103251140e62039201090b80500711010382004007020008100b51280e400c812919540301a00307210411b1180347d018080c108030002c0c503004079002c3e20505401c1d03160000c004101d40c0a42c884070318603140c80780d06003e000802983c6540d02107010580c5802c0407240340042d88640465400143c59505043c4001c14001c00d9256801c5602c0c0180300500900c000c1c1059048410101c203d5008000b04510b4139600381100e581c04801e0b20351030000900100c040f907900504080f486001070100380e0b80c0311007041d40da2941080626425500c01400140000e0245c03d54005c400e4000742110160512682c42030000f074198000b48000920100d9034004110060140806d080c0200d44c001c403046081100f48007160 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 548177832 1250 548176582 548176613
    0x60c020f03070b0424051608070f030b0d0c03080a030c0302070c090b0a0305030a020c19081c020a12050d0b0108191e0606080907080a08030106051b3304 67
    0x3d80d03c0102040c104845142c0c142031a4a8000403910001c0702161088010700b81114906401c43c1034680e003800c00d61168000314030550075a1620295110148001c0300148041410580c10004010368040454010903000e03004510802005070707204036840340181a0784d60b0070450f60a0500500c180b070001341141d40e0744400e9940c500d40002d0342c0d40055000a00b51045940040e005000020b0050a65580804c4801c03418800340c507044c641484880043c482c0585603c40d0380143c3e00310441000581c00c41110781d040d0700c04544100c0d140d03c4165114031030740d002c00403844400b060001515400c155018090088003150900706000c241c50200910340b14441494503d610036681c0e0024584011a00003181c2c0700c4000c00c0300c040140d1601e981c40540043c0058075402034510481c0000a441c002c002052502254001d55060950340b9103841510150010a541d4a4000000021016404041052586801c0642c40001490000c2507608010701c010760075800800e0b80403030400c408a5000e09242509 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 548179082 1250 548177832 548177843
    0x3020901060e060915040f05090118050c070803010e01140909070b0901050720090c0c0a03030203060418050c1002071a0c01090c0608092e05040c1502060103060c020f0307 75
    0x441c2c0c02000012082d10408403134580c80b25001254240c2d20b000500070300300703907a0f44070242510305031900b0401015038002d10555840b5200400ca00b8030202c13a40c0c02c15608240c00340940c0d070520015980c0c1440a401c00d8009105480001c40100310400e0004403403981d41401341e43c0059030f41014007810b900c640060140c0c800d00b40001512034520f234858022541c106800c1002c0301c542e46a5001c614000034400e01a03503201e007507040f01003101c0d410200115407580000000500e6038050543e0250043d400041c255580300d6a9001114041c10310700c0c0040c0340342403146003d403061466490400c0347c80d542041c0c89000b12350080400340705400130b001048001c0d60800c0c406603115032912038880e001d0030401c040100a4000005d001908540003c05203001d40d9012058803c4801c12840501d41741d41c0e130285904043e01503030381080c900f0307089a02243e002800340c2045076109864850000c00005403e0800300180e003c0801002031051511171584019841d20140110103100110944c1d6405400e4001e0301 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 548180332 1250 548179082 548179097
    0x1180803040b0402210c040f0b0a15120509100f02091011070801151a0a20100e030d06090b060910021005010f0303080619180603150c14040302090106 66
    0x1590340390312540c0581c0744400b41170920861108515070705e82000b0380301940201d090490052142e00c050080781c0c01070202a1040391601c0c0742c81000c11110324010340440602455014001c10500f01d4001d50b4421030491005284000a10026004481001c024491111320511155070540d9941079590940c0104c0e2230001c3c544812229182c0c18013000383d001004544c81c2048a01d407600214112408403094240070744481050100c10040307611079440c00d000001c5617509040f5030044140d600e01081ca0b40340c2e04840300410150810303411650101d21040040c2d00101d50701050b0030305c03401010081c010f020b9050150543c108045201400766410042c803480c800411011124030801c0001c803003451283c414481d0b960345d01c00749040c2c1c03c0c10b808190006442500040c6c040c0c00c1ca1104507803c500b10079500b856882c17420f03148200301080c152070a040d041c0c45000010200d0a000e02c04418030664040010b40c0581c6100c010b0080ca034075402c00d4085840c284010405a690580c00904560046c00c1092 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 548181582 1250 548180332 548180341
    0x81b0a0e03011112010608010b03090c0907020a050d082d060402090d1e0c090219030b0d0506041109010e01060203030604090320010603050d0c15090602070c080c0301180803040b 78
    0x70b0151912400b00040d400c1d002c110007014101d4100080c1c120b4140b61585811a6215541681240700440d0203980503800088503440f0360825000346580300b1142c0c4103680383c4615035640d8908000c40800d103d0002100042401820510002c0c0b042d0540e200b40c001e40d044443d14100561150340c000c11a5101f950702186900c00354031140c800306041e0350310101d4131160340c82c0c603403100304107500604043e80c034548805800708204100c0d1017110b0121007100b208441200009000714088c001201d40d0300d0700542c034611204c00007030b0104803c601861081d0003200340170083c0c00074000005c03016032103000d009480070300400403280c01100b200e42000381501c02040e8102c082c2000e41d03e244011081041481e2848500c007954801035024505407882a010340f01010460355048850051083e0082c04400801030001c100400903481010418030510002d1709001b0551a189042da0555018108a170030010306002075240130712500c110136040000c140c41c0c0c0c00d1181c407140218000100010003140200c000316 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 548182832 1250 548181582 548181589
    0x706020a1101030917120705040e1801020d020d0207060b0a06120506041506020d0824040203090f0a080c070b2a10050c07050c100c0305030a0b040c0305010303081b0a0e 74
    0x3441803078100100001045d04642075584650100e601544000b40300307170110707800a210300103c0b0f003120882484406071b511010742156003201044017503c00e0399401c2003075035480307200b03400a401200f0821200588800c03407410072005480c04290041d1003100310b00f205002050304109110000c01e19034000180541e2030001080080030980000c0200c010b03110701c0010882e0340003032080d072079440554a426060b11490b8075111010f040004040303141c0e903105000026818294007459220346100100d034017074020030110504010306020103513240035002800d083c06c030f2001c0080b0401000c01416107803400341c0500003070f000295410000311a0b0001009405c81c00391082140c0b494500792540108540e0901c048800207503403240380204c4140c003604007507a80b113182041c01c0c0c2100d484c0e2510f07024130728019640c04882e9948001c0c0f400004a0307888201c0b2446842d5445403e014221f503031030002c1e0550540c20041c0c003441e0010201d0400c16841102d07055107004500c00c2d6544050b20b0b080c5010f488102c007000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 548184082 1250 548182832 548182841
    0xd080a080c090d15150506030c0c070306050106110d050315130213060306051008390304050d030506040c0e060307091e030c1205030403020d08040302031006170706020a110103 77
    0x1840c2e400f10503071060400380702e208080007150111051041010080500c81800c5422181c816a50700103400d00c0040c111381c5d201401451408200c4080d55406600e90340ca0100721070007a003207080017030340d03540c21620180400c010043c000101414101c2c29440d20000100c1c00c4200a002d460084030280399010304646150196656583d0b4009620030894881e07800500130038081c070609104560800c440d500030741c0141c2c84c1e01d000d40b010641580340c07500107100c0304c4103400748c2e100f5400c5214400151180804402070286014511035005407070040d0110f88010b09580000d02810f00c524a07000c4200080c6800002000d0328031030a07103030f03203403243c0d104d2070141d0b161019940200e010a203141044489120130350940d0b0b0980e442602c22407041e545544070300b00365603001d40008105500402042c0058034280f02c91000441c030460b00da6107442e13201d602007030074070100c1c113007036211180c4820301803001c4806128001c5502c02000c000b441d080385040070003561140c40f114094541d02042c44c0101043c3d100790007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 548185332 1250 548184082 548184097
    0xb06030c190b1b03180436020a0b040306090203060604060e040b0c04080a03090305061302130b060f0a020c0a150504060e0a0b0a0923061c0e06180c0d080a080c 70
    0x15240c0f10403940841c178442d01c044c0f580680c40b903490300a20b51b10003a03014000c2c1c07000020400030040c1c4c00412082425403c20b4400080c0c1e0310107428240028004a500000c1010f98491400070459100510616241c07440240c0201d200b00c0c10100b050290706d03c11080c9950081e0006480f21003500c487c00f10740d0070742c800c1760098a1680a10b42f1000245038005035070808072442401140c19503990141065445d0810301070003544004449422800d0406c1c0b80c00881c4d0036180144550300c2c1c0541c6001004180d400034000d035001d80c0141456080382d2809040b4a0300804040752140040407900c3c000078482d10941c0100c2e0203002007a09400096201c0c540c500c005046510407040e52508205800b4110380d905d449801d0442c2c014018014800003103000c140c2d07800001500c0541003810032010600700351004000007240a0740e03190400d500799002c10101c3e008038400f40e0800603c6810001050a0030035403000d0500480d482c80200002071080021942c1c00d829528150354075441d400c4072010305104441 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 548186582 1250 548185332 548185387
    0x7080904090203190c080d05042903071e0e1c03020106080a03031506090f0e040302032101080d030b030a12021c09051e0f04020a03020d090b06030c190b 67
    0x7194484c9000400440707004c1c6402100b070a101150b950705019954510310105400050051100f000600388500005c80c3c041c181c60600002154a0700603000540c1080360aa0001010402a8200c0b1882a82c1c418003103410392800d98810402800400c00c85040c00b1008a0703403a000c502c047c0b081c180700303500031000791445800303071a004009400d00501400703106075004115401c0e20000124a8002c80020b0101c4601e4031000004501e0702450342501e020007001074007580000c00484221141d10008001041515810307803509504000e1864501070401c0c10050a0620b4040c03400750790780d4000b0300101e440d85e01c2035401c20a002c000c2c60413420101c0d5840c10000409140b0204070b4110340101d00b41c000c2d81d0068034520480c0b440c0c3d2540040e0001d49a042c0d43d04940505180007032418540c005107140589814054940b03e0810340f184100c031b0030700740151902c207002000c0c8900707403170107000300241c48108680d0082c0131583c03a00c0b00748200e183d0f1310656142c80340020b0000c0910307602010f102e13540c1d11f545 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 548187832 1250 548186582 548186593
    0x1a09010e0f0604020315010609031b1518140d0b0414060405030706140c07060507050f0d020d0b010504080706030f09080c0c131a0f0a030618110303040b07080904090203 74
    0x1401d4240da61100390b070100c0c4603000c0c3d800b00c000e500c100a425181228481e645004c0c043d40f845e22403440c120b121001c1e000380c00d4420000402d042d10b0007480c0040c03446281c3d4868176034500500c60b0070803c907920380010802c0828503441450940c4c826002c0070728513420408880340750301c0e28036200c5160340a0205a4500340112410002070000c04005040024000c14080c45581c80380c00909004110854a40000d658144406800b2500316845180d1003405810141e281001226888001d13030403441c2e031003080b580c000401001078071050081c00e0446100f820400e09144c201030b44a6181d00c0c1d139006540400d6500c0340d0f44080e0031031617003000ca20250000300ca25a00c045400000d511105582e12440c0501294601c0070918411442515681807540c0c0340c84c1341d800c1e06102040070542c100b00c2203e034454030070b8030048081581c5118541e0f4080807106081105130301072070401254000d44580b64881c0d041880200007101141040720302d104e50240c405550340d1044d400080007000404006501071150 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 548189082 1250 548187832 548187853
    0xa0e0103030c051606080f06031509030403050f0a0201141e04091b021203060103180b0a0518070f0306240b0406030e030c07171513021c1a09010e 64
    0x91204458a010320159900102d2280d102031303106085200c0c5000080e082c10015060440c080e50fa5074002c9002019105407601e2a0248884ca51044e04d1107041071704000340c100308002c003c011071032401140360098505408560000f1b0244103100301c2c3c6028090000034a0380102485400d181500e540075102d85840f180c80c2c00b1600c0041600e0001100421001c00d03a0000e80350000501d001e20510054440703103959a00b50044005d8069821082000b010b908030320b600041e0000b0b882d9229141c8401c000545203001c0900b071406444100001c0030b0340e00042800d000c806660740605050300e41000001c80c440070b00540c400004480c070368158026000800c0c0100340c5c441000c00820446003e598284030346202c0f1210981c03a0b20480d900080103a1200008001003414039450398a002c036040d0a540c0311007030440c0c008031603640440301000c0029900e050902140391540c0c0d440074035240d0720741d030140d1b0404a80c1c0760f009050b2482c01402c33815050800103150074000350000c54507180b030001175605c410070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 548190332 1250 548189082 548189087
    0x9090709020d0903030507081506090a0302120607081b0d05151315050406050901091802090907081507051b011b02070f12031b0807120e01021203060a0501030b0a0e010303 75
    0x1110b14080b4006820700001c1007c480c45103170164015012015542c00c00002003003080940d910150310740e50886e0701943e0000c00f43c2e803200d114012803034130000038001c82d1a0507900141002002000c1d088000c00309000301c0c1202264109a50400040c80000951a12114112401c10001c0c07940c1c01e034440e03101034201001114980120801d66551010101c0e00c0e505c0d0820002501d44502440e5004540c00004101d40700254002c1c000d00d41ca0b0001e4140380076040c0d000700d00d85600854034010a91f2040c0d008002c014010010310000031060748503030002d1f04150100a14a00c2001c017040100310a5812403911420290b1140c5240180c204150114452000b03000c0e44650840c49000d281040c1a500003461503400028005802d0f40341d9125000000074001c0548070012030481690340c074405202d000c0c00200c1c0c207404003c011540f6180d030300c0a42e4001300024034218080c40750012000e41402442119110302c3e290800340e0b002402c0c085020450b042c0440d100304441d91001c4001e8101c5030000084c0f54 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 548191582 1250 548190332 548190341
    0x31905030a110301091505011d01080a0908120f0610080a151503060501110106050f09070908060a0e0613051c031e090210050307050901050c0c0901170c0102010908070209090709020d 80
    0x7003d400700ca1b100b1030341c030f00040d83c0740c4500b45810404003c1100003152035601ca06a0030307500c8440c80c907000440d00d5107512100042d800001c400791307940e0050810f0182000b0414081940000101e03031015403005041c81c02043c5071005002444140d4071200b0313031055400c0410023003002e0b1100401c40c1c4a0807090f2720300140130340b00b1031042d540802c61a034101c1041400600075941525000b4180c1340b4032849103400d0280c4240024861420480019008030b11610140100c42c000c09110201003010300b0042c424608100d000f0b0410240d4100c16002d0000085011039000ca84006041c84031041c049a40c030160301a1084041b000181010300710740142c24003160b170007010030030700a0f507084440d1350316034006495a05c02540c180c00814002c6c098072800e5031044000b13014005110081d00c88985858002c0791010070282c0001161007020740c0c0c004103518080014031084002440240706039012601c40e10071a200b100c3c006070143e000b000c005000184100a107900600d031011003150303500020340681d030061 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 548192832 1250 548191582 548191601
    0x2210f0c100c0504260a080f04150201060f0e0613020f0c030706050108070b03010f180204030609050a060e030a09051c050d080601030f14060d0501060515040314031905030a11030109 80
    0x10448101c00384103804481481720b9852144900610300740701c140d283c0700c21603046481e101d02d01d600300300301c04190364210458000042c80c850b000410044d0a0100c010900f120507003051000400301805c1013400d40e907034040000c2081e250500181d51724803035507120101d0f20034241e0301c413514400014135804010451f40954120b400300b8007601d07901500c80c50344800302e2000f849403010480030200144500340358040082c43d05821030714010b20381651390340c642c425a4402c1c00306135100e400044880c028021030307008018807221a0800355280280021018104604600509002d200102000460080700d26800c105040d0018101c1d001400809401405684100e0f81c150001c1d003000c0744001420f40d41d000b2034242e4040144480c0440e80d800c002e0200c03540800f07d082c0c86564a60100060940310b12a410036001401c00484d81d0303942c2103080818500c58100f10000040d4801c10a200481190010419102e0100c0c6440d9981c3d0b1181c240003400303407500c6c000801d031044000000007070b8015190310036540b0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 548194082 1250 548192832 548192849
    0x80c0106140d0b0702030904060b090a14010203220b0f0304060c0509010806010f090e10090b18060913020406140f011e0c0503250302210f0c100c0504 66
    0x803280c030341c0c6005964415044046412501c154140e400048401e28996801030083c81200e061815540000f420394269600c039840360754000a5007465410300403e0000a04503e40c040c00f11440e00b034000070340c1d0b44030f0881003000b0f821451500c0d900a041c440b80400090044c101d52a403113410701c000c14450b0798002c1e1000c036074003032400b4a5512500d01401c203640341080142c5071340c1d1043da106001501c04031801450401080211100816550000380c1a58041c003000070b00c3d880c0b00da051052010441b071640f50300910950940310b44401051018288a0f03200a064400e02060b0300c401e19805018181c041c4000c0d07020341010000306030708030302503078403201d2210456080442034004801540c518034848410f5900c00c0b0141440702500b1f01903070140c80020b03c144212407801807109489a448003440d0045503455034080348003400e241e030401c0002110740c25038445c4a0303141ea03201030564043c89598034890403940040340c8802400700034071042000801849051100c0036000300002d00c0c50f40309020303d040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 548195332 1250 548194082 548194091
    0x20d1119031e09030b010b0a030e100c18150e01121a09061c060e070906260304080601140a0306021b1b012c03070f18020315010f030b0d080c01 63
    0x2d039148505090b004480d040200441282d081140c000c48540c4501e0f40103041c992500900e84080703c041040c04c0445900f00000070702c0700f400c02c000820039500c4116240060305850018010303500315110502c072070800d0741004c0a280c5130310b00050703d51030081340e00004182e01c0c1024990b910060107000d5840303544225010b2070203594202c20400448c01250300d0f204050501010a00044d14a81c44610710100308421100c500e079035090380b0380070b0300e85640001403201340c106c02c0034003c2000845002122030060010710300f01414070b64400d0752001c0c1403103501c0d030251910304803080c25181e28150501464001c1c0003555100c1c04000403080a2584250740103107840b0791034004a03070305004d00034441c07030400c140c0d41d9045100c0340c1d0100403070386800c882141c00c8180301a0905403031a54100b1010700103101c41c1102d01c030228a004030030003485813aa103404040302e00400401c000b03003200c9403030030003a2a400d007049054014410000c60040c411140300d0350b00980910045803c0c82400c2c0081e0140e00c442000900 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 548196582 1250 548195332 548195387
    0x140d0f0c03020a170403050c0102072109050d080f1233130f020c060103031206090c050a032a0c0213140615070203060a1409060601020d111903 63
    0x18200c1c0f0815002c500002e80c034422038840002e8903142ca5400c94000d150040c10404080314040c00c9038802d080c121007050454403403918030719400307428100c0340349a03062010f0b030b040c5000c02095a040b43e90300028204200020b418265822907420759900000c05076006480b40303800d510304a160086c02a42c0854200c80c10300c901804854606050400d12003d400c030001121032410301000b8200018040810903001c0c01041c1040604105082c000c6020345e0b6002c44c50800b0b5034008085601540000c80ca80e4185840505550b8000b030499000d25024680000c0d96800e0030802511520201c605002041261205404441d4400442c0f03034803500031110b40b4041c1c00c05010500c100e41080100b000314030002c2001642c41e10317041c00c0180144550180480c41c0219550000f81010011603249a50a5454840460070024016201d5004c041400101071608100303001070350310305205070301c0d43c00c2080d40c41060388280c04c10b00c012110b141c4003a1121480e18200e15000e00300940c00540c500e00c4422880240 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 548197832 1250 548196582 548196587
    0x1b271514122d0f06070207032907050c011404050607030c03060e0a0c051c0f0501080d0c021c0218040501050606031009231302010305060316090903140d0f0c 69
    0x201d6000c1d190040160071042803082206940d401496031018500994220201450044c00224031500c0c056014025080c1185041740301d001c40750100351703180b0002e501428443c02d1100581e44e084203080c1401510340450720107860140c0402544200458200303001d0100700a0002083da01401c9203460920560364100c20442c11036410303200f0b190084000c03c0100d230b00c01800340d115900010007464411b20b4074081024212503d100d510740c61642d160740703099820542e143c4c0d00c036442c09003034008090010083c07543d04c000c2080104a070040c0c82003141c902d14003400c404ca0b034210104c0b188c0c050300c264020310000305072400c1e44400f19800d603401c4d420040081d849180020449114010300201d0303910190070300440400403c001d5090050307140c400c1806442100d0a800140c0c0304142e03502109070080420300c00141500d1014100c1c9002e80c1c0b0044405403003d40c0d05a800d0150b40001c0030004078115141021100c060300842422014040056840c00004094200c3c513511008074100340706891034000d04 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 548199082 1250 548197832 548197843
    0x3020a120518280807090b0f090601030f180b150a06021e01020417010b2b061a090f010815040807081602060a0201091b27151412 57
    0x1196002d220411103052503150a0607040d00c21051115505510740030300400c611280d2190704500840c3e4045a1300704031141e6540205810b00405031028454005e12001180ca450f50103001079042c151510b2440e0014056540203040030041d61011813200c070102d00340f44102001c266a1054441c0ca0070508404078245103140f00200c4000b9030042c555045160482100c000b40c490300140c3e80d54003000300054114512b00090303002c00d80c85000051194a90041080e12000903a000000c0e00c103403540c0000c02d0800800c940245031b0804000f240150580501840c0d41e070f981000a0b41c0301c02020b060110304482e48101d54180e4090b04103c40d0107030860041844000e808807802852081c00700510f0001504890141403100b1074601c80c14005035903170340010495001000f0040c0140e40d01e420b14024810400b07a01c8250f2124556007044040c00c00c006101c614502140380c105600352a2810103100486074880c0d00d4003100301e070610403a5510341c0349203403003845004000352064100300440840b10501081 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 548200332 1250 548199082 548199097
    0x6030f020a0203071203230624030a020a0c060612020307060201020403020d11030f0f030a140301080c270408120108011b08090f0f03040501090617040605130f03020a1205 75
    0x3d6041a1542d6a00701c44001c048001ca410543ca0b00c0b4147c5c3d0980c50f000300340325aa682d510640c0d17840e107020b00c01d01490314550348502c000d180400140351501d00c1400b0440350400310fa60720140c2d48084805054440711001e0000030720b050304d80b601c00a206e015010121454034421025104099600c100480c02d17070185000103503000d024885824002181d160f00b03e603803090054195088000c40c000064104100f000b8450015000012a1170245501c0180c006c54880490440c1d030640d41000101c41d561210445014081c1365510000c2614022407040c02807525042c840c40541d91030300c0e01c1c0860080e0402400621031034001c00000c65080c4060158a0f003143e24158400b50a84138808210751150000d000301c00c0c24024192000e440e050248007058040a2642c0256500c07440c042c0014201e8170300e90301002c200041880007025596440c0d4000d03420907000440410503440d1341900100b000712590000f401c010322044042c040580216032112581c1c01082c490211541411081d036081c0b02d60903 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 548201438 1106 548200332 548200337
    0x5040516090c020606040e01021902070609050603040b06191206230601051e09040f0e15060604180b04021b0601050d1e02180c0406030f020a 62
    0x40d5980007080e07504420000004089002512068040c10882c40b0341e44071921161100c0e402d40540b01d20150f10390005d558404110300c0a50303a01010721a0b00c0109461381e50000d01e03407034220152841260040d18509050b0384040401000070b1103858070701b0300b600c403144002c0781407800740105815241c4030321000561800c030030a1180f81ca002d0003d0007201660b90100f003000a99001c8140c40c8176803140c4008040710703d14110f01204501440510b60740080c80c1050b4144445035982002940100f02c4050b5071035070610180d1108550b408540342e5410101c10041004896501c041140603104400400681464110001400d03a489030354400a0142c000095541c02d071010f21000f80100030840e00c000d0040540e5440e58801c10301820301070701c01031955450209645400108141409083d900d4000c14a014024207803184c00500840b00040c0ca001c2903201d0100c3c0c0c2c0d100300c41c18494140c = true := by decide +kernel

theorem cover : BRFrame.Cov 548021582 548201438 := by
  have h0 := BRFrame.cov_init 548021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 548021582 ≤ n) (h2 : n < 548201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
