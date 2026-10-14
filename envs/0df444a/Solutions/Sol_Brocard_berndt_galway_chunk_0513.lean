-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0513
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:11:47.546493+00:00
-- url     : https://prove2.me/submissions/a0295b45-a896-48f7-b544-86b9fe4003b3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 92086331 ≤ n < 92266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 92087581 1250 92086331 92086333
    0xa06020d0f06120302010c0c0302060f13210207060201020f0d11070b011404180308150102070f080303040c080c010503010608090312090a0b010602300d0203010f060305060307060c0b0403020f 84
    0x140403c03040048810100494483d900a001c01d078a81103049420b15560f1a0050140e4804d401103400c1032440b544460384030f12003c0b00001c0c0280980c490a1100d10407440c038500754104a503810007007660500900018084d140001e41c940462a4030080c080e10481d406c4000c2d0715070710100082080b108004980c1035640051b240034103540c441c01f1504000f461400082d110381e10303260034034210044602e800302600e9015114052290350b0b40d1a000b0112421021540c1180508800032900c1042801c0100c040c1c9601c1c8000c50710b900e4a4503105c94151595085407009600c5407400d00c21aa92000c21641580d2281c81d02500540711726205070318502496014000b41c50a5204002c06220002090802d00b03003d110b42180b20f076a141c0741641c44003200d64250300f00139000724074449805846001001407403081a4001d25049102951034201d8100ba080707060400b203003280420859a2600485401420880c082e004183c07400401400d40d140c5614000c0124801a00003401d0500a001690110030204 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 92088831 1250 92087581 92087591
    0x31b07080d080115030902060304030305311704030b010b0d09050111030618010f05040c05130f0e010902030907090c0c1209081009050c0f03120a0203031005010509030a06020d0f 78
    0x10240c078030b0409000d1300c80812221546807143c58880e0082589070b42d00030307001514584640d01c0450107040010074000350855001c00e0031000d4607510907624030000c1d102000d45070091451034480c0e42240c0c800322603201d010042c4401e00106401000c01c5046039061980c03a0390760003000c0402405270008110250040d440e110b5080007242000c4000c6105120441d500052118400201c030403410080c004c4500d0708003040700a0082d82010b5025151104490400c14100f030190200f8010f004d6064003d2282410310510030401d00351941c41040c00b400d18a0310079401d51604503492550380440e80b1441d00300c2c50711070307401c0c0c0e4080340100e031010082c03600821a4034245040060282c56007400c2e1013150b44901c1800190700d12480c0b24481c040c0301079440300241c4020205a81003242402e40d1406555141c080e009081d50320b508420000c01c0710413401c3c2c000d03548034500a034152152403283d0f40f2290600200b00014070040d5408501e40c04119444800162102c402c11040310042040151100f50203181c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 92090081 1250 92088831 92088853
    0x3060203010f170d1d0604050a121a040302060610030204080d0804021f0e04020c0309031506040b010801080c040e1002040305010f150302150702031002180f03060108031b0708 77
    0x20b058400d080d901078035400307602000c600450f04e030f0328000000008009642030240c1c0d580785060200e505811040140350346c0c2001d441d100080d60495907913000d03000c41c0020288500802510240b19194903100010401d5a843e040e10041d40380c42006001034440c42407145481d00c10343c000c0e4160b40141c02c848003142c080649aa001500c1c0b10810759099125490304481d031624440214410b0480321a103a81e042074030040e020074400031790404c07915203034680410300943e003541c1c4040100443c08525400901894103000c028001160350031007945040120100c01030000060000e441c2d881882e007960300160024403900b4080c10a01c0c0601c248514500000b800814040d05400046118811910800c114100101c0d00d0b0406400c45c80029041103450f946800d0080c090000752901c42d00180503601400da4044965080b81c3c00802000b808507090007040f03942c0d040c444d401d4203030550154000d0001c0d5051032040c558a001d510405209a909480351a14828040c000302d0010040c02044843c66010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 92091331 1250 92090081 92090099
    0x140313020112020a12020702041d030a0314042307031407180219180b03010308040e0603010509100b0103090c09141303170702010902130e2401050103090c0306020301 73
    0x400401030340041c0c1100b81800044902e4801c9407501141d545449241406500101c00030f03402000083e80d0144c2da40030443e0f00d1400f9903000c1b891940d035440245a42e8455844090304440e0800c00344184030b01c081007003000188e075020810402100f09002d05492a1a01c0c503003529104da560001810011513480000d10840001141030a0b10991200205043c0208402d4000ca0003444045020500500c0016440d280141c40e2181031aa00c4030a1070b02c0642c844d400f0030030f03542c001c0c0c1c4200d4a0308000541081000c104015094000204800038090303410841500742d642c500c2d60000300c80c000c0c4c0c0d80c444924aa070095002c01001c41c0d000c044100059903c4501c5c0c8010100d84014007150020400091b103407800041840c85106e5040c0c50750100d06008010801e5500070040c0000107541d81c07030100702d000d07075514031303051240941415001c00e0b20500c0031301d51405c1c80341c4a10300c0f80f00840000c540e43d49002c2c41d5110ba90640b038080c0781c001407154090401981c03e01c00344d840504018400400807400040c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 92092581 1250 92091331 92091361
    0x5030f1909080c0c030a050705090405030c0d020607030b0108090c010302030919080304020306090f0d0f0908030d09050705040b010503060409290f0601080609241203040504050c03090304060f1403 86
    0x160b040f00351003140c4a200705050316600300e07040040454020070b109000c1442e1010400350001d00441c11a810020307601d0005203480c08240710140540d201c030040082041d4180250060f800017843e010845007007200070541d4900d10f580e41103042c1600403000445014041000c401106007032000c0c0d0140c82c10506003112564001d99003680203010300710001e0707081000010601034001d05980104040403030030310215014122501c0e501e00b0021030000000d0500b0042014001100401c400010b40303803a01d20385a45051171541c407050066081407121100c03030f80c2101c2a2944280d007510042024265442c04020b0308092041614150941d03201c1c401c00c540d007074100c641c400e440c4c00b071590f0080d0b200d280040d5680305041b190550701103007141c00209130130103110a0f5101da4051100701c1054240110001c0c601c0d0910014804165101003001c01031450140100d41d08840c440204a01e54200480100e8481c8158081c0d101844525204020301620500440510031031180929449090090190005803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 92093831 1250 92092581 92092597
    0xf0112111803030301030b0705030705040504091a09060106050708180a0f090b06120a0c0201140106110105010b09150307021218041d1e1002070501050609010f0605030f190908 77
    0x2103988140d0207600d04000003240d050b2508500c00480d2581d50070401c4803154002031004007040b000744000695600c850203a504900c1c0315250348100d41c003208460300d0002c1d0340201001001c1e40701c400100009a04442182c101c01c4d0030242c0c4039541c00032000d200c44003c88503c3d0240e0002607007807001408814521214041d00c074015400c1c06500d00003810416907000e2451a81c42e042c0701080440e115001c103920980009944d4000840e0101c5010584815003800742e000d24082040080001a02c0c0c50070b10855001d8019124001c2c00c4c564504081180000c04004480c42c0d60000008114118001c0007490700030040d1141290355065040403201010420114150103541803509041702003540e200d821220f00c51100007441c00140c1078126947d205014043e481a5020301991400d152040340001c000080c0940e0000c25982800710602200b510164030108050500d641e060201541c4241103c1d0040003a800301201a01c0300074490700082058540408110700d400c00708410051000050b100311 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 92095081 1250 92093831 92093857
    0x61a03090d14040506070f140102030613090503041a0d050109021b010203042d0f1b060c1a1506070b060a05060c030304060f140a1e14060f011211 64
    0x2900ea100e80a81d90000c1c0100c90700e082d00707070500080c031a50400e080605000e43c0104403103205052203449803250705601103181202a5000820401e00e41840c401c1c9084541d64480200034800207074803102d072607011702d010b41d40803403191107401c2c1e140100307050a65541e4522690100f115503074030300c45800203501120600c0e0140c418122044501881803080d00d10030b0350807041100781c0300c000580c500c010140001451880e1040b0500000101c0d060459110200d4401c0d5401642503c0c001da0781902060564080404c101c180f1203000d0001c1c944c50104221000c0f030552840d05600c0b5210700d441c8401c48181c6980d080400854040c01344071a9000f510300800f001c2d038400c0c90b01901c86060011601c41c0784c01c1540307994400c002040005210b036003c1c00718115032060020b545050001c128003034602c182c90480c48c507901d8020981c1007180102042d08000303c0d00f4410005c0d41104031044101c00c00003014035200345248140091241d000c0c0310000b0700e000d410300c41040386032034059030301c0b072075400c80360f111038074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 92096331 1250 92095081 92095093
    0xf030d17010906060806010f030e030711091003030c03050901020a020d060519020306060a05090414040515010909030c0615090f060e09011a0607060b0604030f05010b0a060f0e0103061a0309 83
    0x140d424207100f003101380c500d103a5600d50b4555403a401510038a10b00000341c0300b050350300e019000314090280007800c21184901d0403443c000b0310900070062500b4001c0c01429007840203410400003e80c10091046c043d0b9450b081c03035919071300700307500503030a214404038083c0d000310a0070b2a01042103120b0303000a110f0704a010740303944c01d80b011582c01e0b0102d00086840c1c0b904903000b000a403400a004001420903200010004a00943c07240003d1030010016182142c2590180018119402c0391201840c09848010810407120b80c0350384000301902011071024066507941ca0a18410301d02c510b00203400303444210300501c0f5180c0644c83d00c2c0b004101c40d1140c280410b114201054050300180900c2e007001040800b40801426440c040110903800504111403182d554813860410b9111403000c1d1000714014a122085811141070640c00e6561040c421072080c207007a5000d100c85500a040034003a40303a10302d01000c00c0921071005034001c01e02c640001e1000c0b51104070441d00d560f8404000d40c8107024071025200 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 92097581 1250 92096331 92096339
    0x3031810060b0d141611250302090c0711060703050c06040819050301050306180316110a140d0303020a030e03030a060609170309010f1416020a0503030702030604020405060f030d1701 80
    0x30310000a40c3c0f480340c81c444241703451017403511a0141500e842174082c00c1c4ca820081d820000c00e405402c9131041c00340840100410800d42c5000031903a43d00000783d02c0050718117507590751040406000711381035504c2507001007058000e06120f04162040d4002560844406003800d090008841d006503115030b114490103420700c00c00ca07120320b064a0481303101a00500c6552696221000203040e010500c03080740c4014050405c2d0351101d081c0303511006004a240c04548059482445180329030b43d0402242c8031095201100d85444900c00c0251150701450016203441031000202c000d4052132001101511011061204002e1641d100c001210865154581e9a0f0780d150400c264440d00b0141e601050780040c041c0030640d50141c0210240340c4168a08114501310f900c422302c1c4c01e038100342410301544018448050071810719000c13940240c00202c0055003048003c1c0d0011356654001003000f4003c0d9101c05c082880b684402d805480502c8004040e02c148608011008280b15801c0c840c1600c3c3c9020310000007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 92098831 1250 92097581 92097611
    0x90b0a1e0306080303040f1403030403090e070305010b2b020c03180f2805060d0507022a0418050f030703020d08011212090b03090c040e070803031810060b0d 69
    0x304907050f4002550441e9510f0f04e55009010b00c01c041501c40380c0c2c1c09001301c0018a0140025449184aa2100c402c0c0c2410200400040c0000504050606280c08018403841a400043d070380184400304641c981c00c13203e8258422101504040705481070f00108000212250200162580307801480d908021011a80204110720300c90541c0d181d040184800c9080070b801c0306a40c078012420034082c01411440da6140070030000d038003107a1540440ca642d1070902c08056814058036401001c10820340c2030208138004410a40c900110f0b400e8807a0350740784c034503540f8a08448000d08646400070151584076070649440354a1740c0c8000c0f0308400600a901000c050340d40030300f401071705030703503840940010703002c41c6680c0d000c1072400601e4940140000404000f07072121f80d01c40214803a0000b03030b000e0300303054011000744410781d000c4007141d00c0117802005081c004488004190381c1e110b0282c01d011142c00300702c0d022440c21f001d4101030b05140f1a00304440490303080782c3e04000700444030b8581d004000a0401c1401c00d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 92100081 1250 92098831 92098841
    0x20d20030105210c1005030406140106050f0d060f121e0b01050906010507121e031407031806020706020403030815180c040806010e0402010f0f0816090b0a1e03 70
    0x9584181103c4003081c0000714110001038804003241202e8800341003000146064500140c11030003e04000300700820420140200701c0150403407000401a5410000058401e01030720412000040d004034149c0b826420640103c001404000103085c050f603103031204070041c104900300903a00d4a20f2141d560111080c0440c0204500b40c002c01c2a40742a400e0504001940f940500814100f000510484000c034190002d00044142c40740c581c2c2000f44814808002d40c411038410b50001e040c5094502e0164800f20034000f03a01c5422464005005c6c2400c6000c0150040c40c014058042407000c5464002c10400d9030007002901d0082e1588945982c44074480c05102c02103401081d00070f2074149441d10800e10405102d600401d290200501342515600c0040c500300c6c0981c00181d0820401c003d200c02e55030066104042e9550510380b45c641c4228232070001c1d00058024142002c00007400141008040c468650305028000c2d580c541c5646e215440130081c0412425090840e50345081281452079600a06c11 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 92101331 1250 92100081 92100089
    0x170a030612061a09100519050621070c1e0203031e0c010605040e0c0f041e0f0b01031b081323100b01140313020303040e070810120602031504020d200301 67
    0x145151030704006c240600d0000c2c0d80c10104000c40c01010126040e60780c00007074184c84281d401d0741c0800210a216450814a01811000074810f140c00c06c500840d4503004603d076a010a01701c0d49801c104284007281c90f601c901020400504031300903130401d50343d400394010b280d1a0380c000024050141c0b640b007004211008038a4402d84c552108800888038109110304003058000200002015086941490030048240b6424500d260b074641c0001401109441080c22852081c41c00b04074a0302c0e240b0150305d15400b402c0045050040d40310000b00010644c1000031205580066011282c80c110610100c8035060156a10010f00503440d00075013880c1184510501c40d00140c1d2240340444403081c0c0b00081d5072000d4000c0000c8035001300c001c030258038208000e000a0140350390340c2035203180c0b64000501c0ea40b006006415502d0500700108034454441a82c02400d6800000060b900d440354695803545041c060100d980250000c10302c13045520082e40011220012140301e07418994059503120389038803090003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 92102581 1250 92101331 92101351
    0xf0325090b0d050601020f010e07030213050105060301061202190305010501021011040b0d060b0c030304140706080412030216030806120609030a140d110d0b01020a170a030612061a09 80
    0x4070b4807000081c103402050308800d0600585d60800b80055209003503030f107070ba044184c1d950b00c0130104104600308100c0454803400240340401280d4181800980c0520062051904100c1c0d00e00413040400516170480d02d040000341c00c0d0303042036003608030050080d120901c0740c2405030040c403114981111081c0200d250365880c45544030324007130420139508160781240603510003c6541e080e022850001480040813281c0d0792200454481c581440c201e4607400c0c04d40c140c8000750f00608420002d0a812802c81c80e0093343c441c14500c000c0f2100d05088000b40a4010318170020b0311182a102c0600d900700b10694003820081e0341d0204801000002c0c240d40d540107451141c01540104a2152341c184281a00c150050700111001d00e009803000b00301044c1d139071081c00c000c00070500040140d00300806100d9507040b180e082c0007800c8021055210440d620b01e0303a0300b412224a40008004010700d10a40c07060020306561180e01a144006084c03030402812601c062607212082701842014618100074042e22400d01e0b14 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 92103831 1250 92102581 92102587
    0x31f050a0515030a140c060403080903120a08010e0a020705010203040606051e010c14160e010503010f06061b14010e0a05060601080c03131a0903130b13030212030f0325090b 76
    0x69241d04202c0c1608817241c205001c2d15101601c02c0d42c1e244020001103014410380340d15500710408041c28007414684003200e910041103c0d40720250080e80c080d045801241c91811155a0366060314042c0c07150142c000e0141d4400400c1004104030b5602074800e4071007d903801c101c8008065020b00d040645024010302007451a1804000102e950080801c1303440303848262041903e45404c061840170040e0070126030300380306c0e00040c021818244074051054080c5103060000514200c4060110810607182c8200c904040c22541d003840f507481036540040200c20000c104400e90000401d440790240a0704444134060b800200303a15601c038544c8103000d07841f031202551450700c41da55402c0c008941e0b410100da825a24020050500f82c6881c102446583c2c00c101951340c55481c821240c1444440390042481111b060007292020001c241100d010340b54103071001e914417a440c80c0741900e5806800c1e110b001200e400030401049804504500d84a0749441d0140807100541003019200509180a42c10056200b8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 92105081 1250 92103831 92103833
    0xb09060706050a0b0d0b1906060e06161205040e01230d050a0f0305040302040f05090303150103020720030d0f0f0e0f03070618050103090804090b031f050a0515030a 72
    0x207500094020108540005a0950030004264602d440010680c6c1c6000808100b01c1c2545c01190300b0642c840300b050701001421308102c0040c1c07540d0044034040340100000701d401c01d88103018007840144660003001cad05d181c405401c1d00050403948180503200100b01c860000041030301801c081c1002000104000f440d8480340081444a02e032482070080e6028818040ca6101147c141c200e4400c9241c000d40c0e8a9a4a50139401800146c0b450b446400c080300e882e100030042015008800c1e00d8209050300002d44c003040b01c2c400120003a000701c100c003030440c0005880d003e41c0101880c01e07074400c2d402d0a9003a10a0044505026180c20341c1c1c07000d008000c10001522101d03207520801c80b4407402803005142880703007901e01c0040b0b481d00304a500101d01080040545d142600c28584084c4000d0209280c24000c664503a0740d140b02c50701940c403844800580740c00e08401030343c1e01803100076146101d10100d0800e0045001c82e0704d002e0581525000003032031620000c0341100d00703251914400c410010300204401c00319 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 92106331 1250 92105081 92105093
    0x405090703051b0301030623060d03051303080f0304290c030c04030f060506120a03090e070e06030712060905060d0b180a0302250503100507030b0d03180b090607 71
    0x1000305803c001003903c0588480e40140e60010798042c5014040c0064804a9180f1903014104540347c00c030f00b0038403070b44108200380d81e03041c070550304469051401d00d8651219550022847c20f00f40c20003400000d011951000c54090311006d503103d540a1204120035040d0f01240d0f8a240c0d0070021011a0907074401c000842036103180d0000d45e000100740071403d02e8a50b49440304142d16210502c01c0710b0b03040c0c5481c107000d482d2070103403001034000303034000050591400b103560050491f11052241c554040341070030000c0c10450080304803000c61400600300359541c1c038041e000244140c284542c5120842d01c2c203a004205020f562003124490340c0c01900c50101c1b003035141c880440c08040180407820320380030001c03202030400041c802640054825001040b4514485240188003078180114010b400e01107482000309030b1300025120070201b00b803d800102915a80301c105d000e40401c04000da000708101c040c003030030550700c03008203154080c00500050000f604c500781084544180e540d01540550b0030301c2894080742c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 92107581 1250 92106331 92106341
    0xa0e0c16021507060b150a020705010305040224030406060803040f0b09040b0a12050715170405010902030316030f4401030c08190203060703091112030301060e03030405090703 77
    0x80010140b0800307070740d51903840070142d004000865132180c072401c0302c1081d0f08180a400300210400351065003010ba68032402175841005225190426854801207415903c40d5620706c420085401c0c1159845100414042c0040d401901c046030120301c1d055001800a001006450581e0715800c0818406803910140071441e80000d000a0f1f4800e6456001c0b071416038403a4041c00041c1003911481030780003154182541001307001d6100540708041f000d18041020f50044201c0403000b00003180030400e80340c5040442c0101460000203406d032000040c0c08030b04a82102c40285140d1107640c0781080315141c1074003200d03115500201014041c1d56851789000e080740b0015942240910010325640d9460840150342009034280d009407882144110309115090701403103007485401d1003102c1c03c03800c0d548a0340403e55403000100000101542d5000750f104201c2d9504a05000020090603d9044080e00030b000352645d000388074800c04a842d03960001d859003008000e039002c5400081c80411256100503050340604 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 92108831 1250 92107581 92107583
    0xc020d120e0105070906021009020d0f230c0a060c02090103060c030e03041d060d03090317040503030714190c031b0803040f09050109020c0d200f010b0a0e0c16 70
    0x944a582200c0c0c80c0d9400d1248a104801c9541c0e4a200e4910303207400642400001450000c3ca107007270a0b4860301684901c3c13207401c00d03194000c6101d50011918140f040c64030000d404601680200c20542a00101000561041d102c00c00c844192500e540c8460690300802c420070000d42003409000100045420355101980300c0000341000310718018462140e60075a40190850700d940840030103452010601401c080794851425600e81d04c7d41d171400d4802400c181c600d44401403121018402802d58070740044162401000094201c9403940300034503180c441d482004105800e05d100b20100a120700071590075200c403054000b80b05c03d00ca2404d50310344803c180744100104807007014801000420a400704010700041c03c50b50101507601d0b00341a120010783c0c1040c0e0000d2800c80c010f114a10f040301e4040749080c2101541e043c507180b00c0c801c0b00f00e51215030f40c2e003030014605400b03070501400791160306401c801070074042140c8540c1321545844103072041090039101e10712111400c6c01501034400c4c00100f035240103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 92110081 1250 92108831 92108867
    0x405010b220c0e010203030415060b0315090609150603090703050703030903060c081009020a030605060c0c040e010e0c100207050402030106052a1f0b0301020408010e0f010c020d 78
    0x6082600c000c100200d51581c8542078030101d41001040040a03407080300400d41492410441808144000039030b01c1c080504007420020a0711154810b00b0304070b502020081c6681210182ca82ca41000c00d400e5003c000c100c6580106000e0000414910b401c06100303102e0700050070751142200b2600305018150300000c100012910a05d04003001056040010000552080d07554558007400c6190600941c1c44030707410201030110810078012001c108039190400d603000302c6c00c0140c5454010804401030401a4003868000400045000d0b4182c40030510030044c0c80d060f507091010280000210f401c84410000084464101c825890b982d4608995041ca07400e2052048030b106680383d00010b0101c1c0e10a0f03001c40c1c040740c000194030701c07414020241081d11200c0e080590b0200c465804800791254048007015180080f940d1b0743d0300c41142190300c10b041031040071303008540703a076260002c0f035000b8000714401c80501d10503244480c0113440140118912948941c0c0030b420202c24103072090b034401280062a40c90 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 92111331 1250 92110081 92110091
    0x303070302070812010909050f0d050405090703140117070b0405130b150a050304020108010b09010210270812011a0a0e040902030a0309180c1707051204030306090b040e060a05040501 80
    0xc0548071340d40c58080c02d41801d001030000c0207850050701e00780090610760032030f0308481e0595001c41e41001c00d45048075415a011115545c1304c9400702c00409064088480d44068000041081108280508282c10000003141c05554403040860401d000b640304a55115080000300202c81d006604000e0240a0143c00942c16940c03401d40190b00e071700a401c0c404001100031041000b5580d0159185004100b024038492815041d040000c4d29170045a01008086403a08602044114011030580c0750b004444e81728080001c0901d01080c13254403c4a00403001d1000c500003045040306807200d2100800b640145900c0e00340b012800703407004900442c070543c1c020f03511500600540c60502c40c600b10300c0d00c2030f82e8811226040c01c074085c01401c40300c40a03041d001c2c90070131005c203a5500241e2010311100c00e211120bc540d502c4040c2122544035104040903201e00150a1100709038054010105079203408900384002c0c8030950030300040341d020719503502060b40814086103200c4126030000d030700b1601590012038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 92112581 1250 92111331 92111347
    0x427020403050d0c0c09060303081f0b1c060e0105100f020c040f09030f0806010912050715020706020f0a0b1303030b040c020a0308060f030703020121050a06030201120e03030703020708 81
    0x81000f040329820b07030100f50700340f5140c2c0401080c0806030010342142070082191600303580300106201c80081800f901400301c0c00b108414a000103912100607c540131280e9550200c099020368030b910039081e005c42d180d007460000b0641149600e40603040c1c54002d004442d92404001c000c0340d40c04040d441c418190b0007001c200f4507c549490045401111000a012510301460710380145075030044a0081c08100185051001c103070380c0960a603007210f11046440c40c0070300040c240213050013004d51101c403003c010040000702a94010940030f040303800b15020f0701c5559180c440816168181008020016031078600083c80c001d82802c143c01b0139a0007480d0004041c114003002c241250800541880941d03c1008044100b40c2c1c091007480d801007040d500640803540c91004203503141060700009042c0a0850352070720010080001501e40008602e03000e0042d401c1401100000b0300b843d0005034000b8482d1a400750079029240a01d10000c0409001146995030340d4604030000d400c0350700116195201080003413 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 92113831 1250 92112581 92112583
    0x30504050d03050405010e0d030e060702040b040903020a12091d090f01090335040308090a06240506180108070302070605160314010803090f0d060e0d14042702040305 73
    0xa045503100c3d4554070307a50785c140b10016240c40804110b180c8180002c00144000a91203106440c41352800d403021034403840c4600c0003a000c0c0011040c0107801520702800e8400f4103500082c802d055502440030200021000e0038100da00403000c3c001c9110f49040f56041204000d03050392031940c00a980000e40ba580c102584e442403d44d0740900301503000034820130300618601c000e180100fa02d444420302d0300b500c00b07040f80d82201465100600103400c0c0100c0c0e800181105a0902111884980c0a0010440101400680c141040541c028000e008407000070100d510f08220381240c0c0250104000490000900001111402070040c020001c00d42c0910100c0000340080c003516010f030f543c04002604540d0064802000c9403e000b030b1040d64112a170340108031188000c0219019070744145c030318080c200d0700080802d14240f90104000c214614100e07401e420070001040c080519900e90b80c842d4400c01c44003c802090380101d00807e0303200d0b420328a10120840c02c080c0c042148451f00200542050384e41e84401d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 92115081 1250 92113831 92113849
    0xc0613080604060c030506220f020906030405010507080601030509031209120f09040506040204060f0806011814010e0f150304050f0f030c190803010605070203210901030b03010e0a0305030403050405 87
    0x3212a00d45580e00180c00d0717900350040c0c5501c5041620500d41c2e400150b6504003080c90600188081640d5032441c0f88100711482c4c044a40301304010709842d07924241441d01d035000b09000c880403000560000d001c10b07559807103406040c2c09a00c070300d4000e5041a44208000d10321101c04bd000c04210310801e12603042c2d81150001500400501100791604d81c4910700c2808251503000307003c0c43c411803040000340851500440c0414025145143c003d01d9695508010380e0340c0e8000e000c180b2990503003001c0000d20b420b41c85510342c0d131a050a90300e500040b0800c100b8051000300302c49600764416030b440521100c1c4030000f0040c66105004a045804060385c0c60206410408901001c003010381001902409440040110002034131104918004441c05521455464007060117050200400000d003d01996010030014036408080c85040200391600c00107500664441c50181e80070900304a240c5e00035150610445036000f644c04003070802684030340d402321003a5000520840a01501788400f02e03c9403203940b14 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 92116331 1250 92115081 92115083
    0x705040e010b0301060e010e010e0c0c150114040e10020711040617070f0e060d02030f01060e1e100b09061918170a110d0b0408030406050c07050c0613080604 69
    0x504800502c103250a49a103904800e0708040d45100401c400c5064014082c11100800340b03071041074507110300d04407451017600343e03445143c03050f00b000402c0c1d080a6400300e412204083c84826514124070306020944017071205414142e00300740116810264150010301c4120f01c150310f020042d21040d00001c04440140d0800307841c140b100c443e506c00009080182d44058040740400718207251400c9000c0d21151801401680903e0303114482c074046480400000804504010080c4100e90b21030350b41c46540841180e84114010140d8080c4c03200c0c28400d46c11718001e140802104110a04000d10612140d01c40c4071008c0d000340040009040010080d500251815500e0791011040806214000c98400da660840040c140f0b801011140003240025000e09543e0700005443c2104400e0b030010f40f0300340030610050100181602000100b20074400110f01c01d900c0340804005903210340c9030540e5580507401c0d0003412503120b004400c5082c40d120014180c40aa06108803c0d800e071114a01402d0034000c0c2c0f0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 92117581 1250 92116331 92116333
    0x4080703120203030411041a030105040b070305070c030504030206070c0b03040302010c02011d0d08060307080102040611070f0e18010f090b04060c080606090d05010609090302150c0a0905060306030705040e 90
    0x240100002901100c008010310320082d03080d0304150f20744019241c900f9406e10b00c12990b07035944040e03e07510700500760071020004000708030b18901418840c1101c034084543d03900080c9454005005c450043c401c18500c1c079003503620607003028110b60071f104043d40079100030755070b1100c91500010300030412001584a80d10039800450003004a2b4806800d440c2d04500c00b03480a41514401b6401c200001364401a601141c0707817107000c944503003000c60706184280d049070005500010300400e031503422141c900380000c850003c844031159507000666000c7d20310700070040d103c00740e140070a07000c0f1085044100280d00610002030707610700c1010400221500300104031340e40224882003009000262003520001c01e007a00b4100741074a03104002071143c2c40f461070307454480d800d1a032000f01030020945c01800500054041000310034050706000e582d0b04a03800c00000040172680019803140a54801d4440e40c491903100d05900c281070408000c0207400082606416200302c0c03100044c555260b00401490200b400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 92118831 1250 92117581 92117593
    0x40e07030c06052106132d050106020601180b06031512010903020c010f050408120301030203070b09060f090103020d050f01050a080c0f060a18030303060608061f051e0408 75
    0x200c0d10721041c0046500c03580070301000f4803a00000241c0742484100449400807002d200d40c5d07030f0100003801c9900705511159214a000071840950020010141600f500b400b0200500c0a02120303d0098940034090940140c0008004010740e4098001040025040307a4000c241c00c140500450b00c1c5800455125010f0440d40f11b0b0012941041401d5a0000c1950f5009002c440c90fa62806550b4580c0c00400f61704001c400c6050a0303480d8482c2083e50041c0c07a21034155901400840c44004640d0403c2c081684640624500002c2003070810040320f0420402800030740c140790007220480a030390403201c0028145602003180b4404180244903032f6202c0c20300c85501402c15410700d0180b080520203500040b0013076018a545150b1a901c0501041c02c0b4a41101e10740c0d640c0e80186c104803610400c1841461012040c410007108054040d0806415101039a480310102d560354403c028040d004041e41e502020145000c02a1891141001b000c0c061000c600c010482c844003544414103034010b901c082481d40000d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 92120081 1250 92118831 92118833
    0x1c0501051002150106051c02040801020a030b0607050703020d03170a09211205040602070b07080412081e0c0f0c0102070b060105040303120b180702100c0503011203030509010b040e0703 81
    0x1d00450004004a00c018109043c1011680c1c1d200403043c02610300340600825442c04c0e6100d00a1080b2190317548000640d241c0350b40d1a80d00340070f0741001e8928000301c0d0070302329a0a52800c2900982e00c03116080310060000c0c500c1c42c0c090040d4095001d000b85d007004060f1500c807008042d0000780034090307289128000b806000c01e05005d011030300708403813401d1b81064080d840c0c0100303940910b0402044084203000a0941c03543d18248000348034040c8020806100d01c010009125081a4040c1c8100c2c09810490035070289000116401542115031424003030340d00c403000e0201d00316454460f6110540b49081480c24241d0707501c000d401c2c1c0204820308111381d00002c45034104010702440c02d4010200b824a10b05250440d64080c015010001c2e83c407140640da15a1000583ea60380c000d40c811803070503601c500d1a401c209200175140ca03180c0512104490401d440740121500c80c104036412100c0192000d0141c1c9100d6804801414014061807038640d03c84895864607a50751040a280c1854400100744440c69 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 92121331 1250 92120081 92120089
    0x4090b011202090c04060e010509030a051609050f010b0327120c1b09040206130e0c07021e0f1c120228021804020d0f0506191505010809031c050105 65
    0x20138414911800344400c10182c0d070010301a03d11031070b003420f080d0b481d4030352000424902034004401030824410a005c903c07100e0520700440701506d00b00d00003403080d603440220306400d4043c00c0c0300d800030f0103804100180c0b080100600442d81b034003d03c0c03483c42610303461a0006140c4401c00c00600b290301c81c0018074001119042100410b56000c90701410388806260b00041c555060051010780602400a0158002c6103a00000c0008e05215000050310f030078140600b2442c0d8020507800c034083c007020303103100301c01d040c40780c03c1c021074118002c02c445410a42201803210340014540606044050b03d41c0000001e810200c0014155006038020140c5100100c04003516002003401c100310800d0b000c05e9900540c58100039820681882280907a441d12a4408250000c51961700038050305c4002100c0f1041000c08074400340680300900004091503844042542241c5200e000300495407410f0070100019405050340c0c40d8044040e00549040001c41e91001564101403218455015170b85c100502c102d20b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 92122581 1250 92121331 92121349
    0x140601170f060103050a0b070c1b090f09050703021e06070813050108090a0f1403130e01080c0906090601140f0d0536010b040603060b090114030d030b04090b011202 72
    0x403480010b122a52558407196242c81680c0000307808034800e003000410007802212240902948060181090704010f0300c812001881402081c50340760502c01022610f180501400c5402c40e01709026014071032841e400c02c01c014855540d501c0402180400c0905103540c0e182c040c1568902a08403207960300c40c0c0325001100040550440c03818400e0600c107002c940c4030005000164641c3c000106d1104001509101c0403c002c0c480d08141c15220000302640d40140000d80103080321803000d0090b1080e40c8584083da00c1b000ca0408090b00304840300b0000d0a0b03484d213030100641081060611155134118507000364040d501c0b040e481c1100c210b0000c0c2c00540c1d010310340b149070740c8031500c0701c162b504031035001184010002030400c2c041d0f0724403840091402a820b0a500442c4441d41c02401000f80903600e103003400103003203102c0b0304520030b0400030700001d001c18000313040150484008004c3c2c030782c0d01c040309005c0d4014403080d600c080e0010745d07841d40040011110306001e03003e080c1149040f007000a551040184e108 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 92123831 1250 92122581 92122603
    0x7110705060d0203041506030510020c0c1e010f03021905090409050601030305031b1213030908031c0605040c0207170307020a12061a010e040e0322060809010c0206011214060117 78
    0x1f4030b04541000404d0022030282241030070103601680e035440c400c4000d03241104003941f25a0003052002480d5030606c420701840f48045081e00d50320403040f07900c0c41c150104d025407942d40c42d242d071000141c54552807042004110884004200141c0800c0d50744446141076002d800031000710f03c000081c80255070f445904100054500a16540b0b080c80e8070a001d0010440a0040d0500e0a031080f0700c20101405801154041c00015085948646900b914015031003604a0210111860184041128106401003110180c4150001e25030240b41500c0840105010120142d00c0c2c04140640300050f0388418070326000f02409511b41041050710b050407002c42d42000e1000c0d20103018250940c0c8aa60030a0a0940312201264009019104000440e0540c0314541841c60900031040305902140c0da480305400540321170707583e008c07195900c81c032034ac0c0d080b13540400001c0c1c00b5a1001f8010050008955100e10343c4d81c0c8254081c00c2e606000d800c03560324024003a000150101d094801c1c0b03042e1a00c003007160700010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 92125081 1250 92123831 92123873
    0x70c080606030a080306030109020306090c01090e011a070309090207031809050f0c030c070b0c0d050f01030305030a05060a030f05060105010e180411031501120506060904050607110705060d020304 86
    0x3a0414200081d65003c080030300801c682c2002c000642199020340c45440c01039000341c00d0300e040d41f92540c1d2583e01d8a043e465103d010400e08080420401a4480558140c1c2d410a41c4a00300700380c107021010362074100000450407c01c44c480003041e0903080e40090510a84242c50300e00039010302d41d880c1740f0301045030740208900c03a04e0f010801000b040801d2140343c100c00741c1104c2c80c1d0b0700d4848222540c2c0500c0b032888098110150102801001002c0700c00601003c060742008110039201c490810004103400c0c03002a00054080c0040346481d81141d00a80d0845401451510740d82d40e03136600c040380300c10060000c0d1195004000108035558010b03a134041c26120031202140c6140c0208800380004201500c041c24040d548100d402e030366141002100c001d00300b2a07500064560b505e042e1011546162a000c0714a4041d14022810a0802060550146a008d0080c20466450f0a0101c90001c81c0d06c0c0900c1c000d106074200040c6c03513102c400041188034034490001d40d803841c0500b002c40301402d04003001512 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 92126331 1250 92125081 92125093
    0x6060806030606040f02040b0a08160c0803041e120c06050714070312060e04050a03021c1b2102011a0607080a120207020402030a0609050609060f12030f0f070c08 71
    0x10350780030449030303400342080b80d002032101030010840c030082c083c581090305001000101c031540c10790030007000c1c4d10690748461000c540c4400e11170200c803080410003000b42600014400f10f0300242c1c04150500085441c0d03940ba03001e07600d881d29148000c0340002d12020120302d000d1841c0041c40300b907002d010f41c0013416040c00302c10002d880d6031540c0360b8400da0341302070704104c001d60080c40c03080c070185c002038020000c85094a10318140360030043d031140000001280507100305100001418001d4034118040e41c240e4881d114200001540c03803959260b0940111984420400a81e11101c1c50ba401360300600580e81c00003821601480c207400080b0701c1000043d03c18101485890005017014048408200e013070702c1d10b00c0384e070320002c20031501074010240c0082d80140003008202007000140d03c48012110b2007101400300c1e807206c0c010b20160080940b46250070076111450607207c6d050180e40400204500d03000c82e4506030a400d008090350300310402204d01d855000410703909001102c18000301802c41100503100c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 92127581 1250 92126331 92126341
    0x6060c11010e030c01051803030a0905030d0309030c0204020a0509030f0d1803020307061803050f0307030f03180b0c0903010e07060e10020304061b062c0a02011b110d0510060608 78
    0x295070b04c0721300821810070400090b850b03059100001c01d80c1d080706001d801c81380c441240300381c040c2240d80e10340a110700038400c150070016a40d1203402403c0d40c56805442e482c1481d229502031001030741c813002d545000d00ca0300300a45a1340d80c8042003012a800c444030007a04001030300ca50b00030070020005103000341c42514001c00380701603540420140c0c2103412509044507051400c840e14510180c055101511901584180200081d004801402c42da0300c00d5030742ca996101d12081c183c044842005400d2441c03040f048000c0d00003101240741980102144d651541000701c424002030942e050520007400385d4202031400c00100386c108038a1803a2080880f14210707400c0e030701c0e00700031350381e000320f11a000420031302c03032200300b41503a00030855094242c019000340f101d0784000b61000b040411461002120060301c449410740030401103103500c0945d038145d44601400d40b000800007454840424259a42d200c0c0c113401302c10300d555019164940034459005003600040344500d40c02243c1c0340d540f00f4400d000354601000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 92128831 1250 92127581 92127583
    0x30c150d09060608120301091104030519021306030f06050a0c1e090b0703030b121609110405030d080109050a0203060108010e040c0306021b0f0c010c02130f06060c11010e03 76
    0x11400c0104403400107076504603040590180c000395002c1091400348225100040e401e030002507044c1d813402c0c001403101994581d0303c4c0b42e06104520014040d9084410084c5980c0c003500ca0600e2402d0005107003244a5801840400865401c0d0b0310480d0148020801d0390100010b5000e070320750090918100300502c8a44002c0580001703110000e43c09a8080c81d008034170424007840081c00980a4055034507150703031151801030010840051000e108050a14034202040d000044110040400c40310302d001f410326003100310000c1e040c1c185010a1000c0d0603c8003040f0f54800f0801000380098a983d84030040d49002c1c0300404541020303210400740b030300402c100030869070000081411a0300e904100c00c01ea036076508002107000900e410040c2441d000280350343d04030051000a02c100038020040e100300b4800419019a90030301540c850340807400882c1103501600e001700c0e40c089048007402d004100c041d51040b4450442d4010341100d00802c0e2420356040a000c0a03d001a141190070b007407490780c100b0b09100103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 92130081 1250 92128831 92128837
    0xa020c03070e011d04050a080d0204060e0a0302031c020319020601031208010f0302011b0204090303201c020a02030408031c0f05060904080901020304030c030b09061b04052e0e030c15 80
    0x105000340c00f03135002c03a003085010825039116640280320142c46080b1442850041d521a2142c00006000c4902c05544e616080b4103c50450358014014180031013800d5140c0741240d00840003c1c250f0000f80036980c91481700041c04002e04070700798050602c030360541c42e0500107611511001420004104014000010881104070603a81c09082881850709c81351260b03911801c106070b000f50401d0401c420302c0100740e0140c2001b0b600a84107104446c00607500f40b4040c00d50b0040c5804203000103030300c5061292004045d0b0003041c11400c0e603c152031800d41c40700851451580926102c0c424016030f955007043e40d0900b0300c0380c4580c024081c00c0a005078140f4a000981d40d041c00707000500003aa002414840740c1e802002190020350f0f1200400e44021740d6801e140800d00000c6984003254022440003500200052009020641480419504060901050003031100c2285002c41c440b40001d840300d044182c800c01905120f55040e80e484030b01c1c3c1d60b02414141000001c1c0002d078060300c004801110000c4200c004d0b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 92131331 1250 92130081 92130119
    0x110307110607060e16091a0d02030f0a150b04110d0f021e1c02030601020a03080a0609020c030a0e06040b0d0906020904051f050306040209160201110a020c03070e01 72
    0x200e8250200000140c031520400c500140064030700751418542403030110b070100b0310320002006000e101b681c4541035019a0a0300305c0c10079400b1071207100d81d0070354500041d500c01d0341c90000d0203c40106460300107540c0b84c070203050410350302450203000e8031501d00b084d4090040c0b0000f041d641802072000850308a9181e0003078540c3c00d8042d9441d040d0100304104c69a06841c0350307007503080346900724921120009509910901d6070307100400482c091000481150b0086078000e003010f074014810030061b40c808880c44a8007074007440041e80c440400041040c00c500203450581003400256640e01c8404001030700707821392011150300a0005010400114000d03070140c1324031140e40740e400f180301e03444c03444d191009209807040d42d0791091078a014880b02d400141e25080b28110f40540c0b64143d96252400c160381c594044400075800030b441c0f030025070b038030b500c03081060b444250328000881c185d150520700407160740142c04074400507403018154030641d14081292000130001034248002d10350510b1101c4104040c0e280c0b03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 92132581 1250 92131331 92131343
    0xc0902030604090c12030305010f080c060a02030903010614090609010e010902090607080a03050106080c070f0809120706020c012a080a0207180506040c1b0201080604110d020304050d110307 83
    0x400581c5944640e003051102c958004200803182e43c840f6403021142c0c0d030421040e00080d190a0001c180e0840341d13000c0c1025512490700811601040c0000c100d060ba1080d0b4442d800c50000b031003d00925102401030102802071411417078034442e940014010781c070600401d080d20400041004100c000944040b941c1542c28072031003da580c2d0320f0a000305da414426120010b00e00300c400900708900c20b90641c8118140d4204d41c1d100c032002d446e0309203910700e94050068041e0250324040280d030002003140c00100704c000c1c000ba042c0700004004a5003107081c21500d42c0000b0142e0050034506685680c0320f070ba400c541c81d1548032456140308918042d0b081290101900904440d0005190000346000308aa00010a03184110740d800342c05c4002c0e184080c04046e500913020f2070a12410910442c01661180d08c25600d03ca4204c107001c41540046034071314009080260420307a01c06112201084d52802400c6044101e0005a941d0406140561030401c0d03002c5940c0030020404180d00541d60007004450000c0d41140c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 92133831 1250 92132581 92132587
    0xb030a02090726100905010506041a090d0b090705041107030c080a200a030e040b010e09060609151201060206010e13030516120906180e100528060c0c0902 68
    0xc203030402e200070501607110021440f02c100000f03e002030b41200190b41854600b803001c0e0341d81d0000d00000d80030314090b00702d404070740000c00d01400030024080d0801807001014600c44c1c1d1200d840701c16210400ba1502c1c540c54001010500450a2a0061001e100102c031001c6d0300d8105103071030040654440a00003800c40100103a482c80c00d17486950f14426045140444d40c1e081c03102000790658802544030210046890501444217900d0144100503c40006071507810798501c408040103500c00c0c0050045600c0031041c00002030a44800620116120041e038100c1e176103201010103680039032016070055003107501441c01840107503400d03c03a164121540d0307040d483c4103440d90b2409031040d009442c18100c84050510003c001e020b05d41c1c40b48140200701d510748483d8a9150741c0d08032540d84910555500409141204203d0000000602644414065a54a0010b40b9140002c001909400304444080000380b141855584200007000081c951828950401e10341d503a910200281e0b03512441828036404 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 92135081 1250 92133831 92133857
    0x150f1a0f1323070e1f030f0f1506120c0c1b091a040c08010501050306010c061103010e01050a08010c0806010507110a08030c010c020102041d04020d0b0109050601030b030a020907 78
    0x40d4009103810341500c6440300c500c0c0c00c0031407484005001103801000054011800da0a00d0401043d203454511034070092584030040d6071006d5004d44a40d44c483c4060340c0d0b460007241c400c01c41e140305e1314031041c001c4244001740030700e4000700800100c001441e04441900d00444c203881c41d600451000c0b00f40394030915604030f4518140503000307501d655034040c0b02403d0912032804400204641899080c89084404002501c2144412120701800b4011503003c58410004540386601901801c0c18003882844003207561042013503002d425420aa00c20009003207030b0710045c0030a28000300b44c1d07000f4001c2ca100801c101c03187c0910082c05c0c3d4002508407414071800144140170300215072079403010f030800030300824204c955543d9120350702d5200a17040c0d0a25480c1c5074254283d00d2042c02183c0807258500d0004118184410b006005110003030406c80e03101003031301521070009203040351103402410000000107140c0f1f0140d00140039980c84400a5100303412149121005944903030000e900304140746032000300c210711 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 92136331 1250 92135081 92135119
    0x507090c0509061e19090501030e01050f0f0a062102030717070306020315040207050604200d022107060507050c0d0f060b01050405060c06090715050406030c0507150f1a0f 75
    0x911a001803c409403450071781c1085802c24420b504a81c02070b6010403240e840103c02c1400c9a0301620a00d141051040204114002c0e10480300d130403445c20b03c00080c20303d54641d13444a103a0811100100c80a00c0c0c1c0e141030084d440c05203c02001004034034010301940030420b2596850b21498040103101543c0071001c901c001803014504040710710301070001c6680d40c15a05060350f446000700c9040315140107100071b12284c2c411510040007c80006004812030034095820002640c07104003d205001102c40701d4144001d86c1081200010803140c3c84040e50f07201d0505001d801c1c2150925064000d03118403101200041400c40da04648075080b0b4800a01c4d1b036007140040f00c05101e554403490b402440480c0290340c48101084285c0600f403401c00704c8042940d680c1c00782e080403985c1c92154010680c14001004001d0003501b000100d400240341451400a1a030340e0003403c0d060b5034800340304007a5541c0750018003200611403070800700e200c0412030b100d000410300095100c000c90308209009258000d502859049 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 92137581 1250 92136331 92136337
    0x10050a05042702220503030405010504050402030a0f0612050d030c05030a0b0102010e070914011202010203070318081002070311010501080d0c0203070e040b06090711030405040b1305040507090c0509061e 89
    0x50200b040d9510b0201c400d0a014030005500e00300040740310810001030364a0700000b2603040303e0741a1506401d15241104100007900010a85e241194541204104034000b9104200140c00d00400d100781c0c2a8003070410f0391404060006110a16280c5102c481d41d0b940c03c0001c2c0c80d8001c411840100d5040074100041340909640c80e5507038598442c600c0040740c80c0344036070800d4501d08041c004c0d10302e185c0e80e24101c50050018035540640540c004000070309c0400c2c412020303c05100806420a11465540c1030401e240003460503180320415408541c400070545e001d4800c100102c100402030105506202545444680180340300c0203200040c07001d44215141404800c0080800380351038a034602d00b0b4145001a010100e039480e21403622040099060382c040c0c58000079400d0120b00650425003408140f00c024004c2d40d10050b0b1000003851403512004007401803030320481c40365019168803450501c0000655001085080030700005001100300f9849001c00d40c4c951000c003403a40142a524800d2823000b600c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 92138831 1250 92137581 92137649
    0x80c0703081323012414060f120c0703110c0108070f031e0603021207030312110708071406010f0302090423102405060306010c030315060e10050a0504 66
    0x189000210310000019071005801c600d1240200c81e002c00f005c1010b52070300007180680301081c030078541c4400b59400d000f80a888281c0c041889249020091a0a4081f14104507800c4002071400a0b03142c0400d54442c003031180c644070070001007400c504008006002000024680410025404c0200e940c030341c842c0c2c1107a02c0c221345038036010130b4a000e00d840701406020240400d9000740e800702004028541e00150f11000c49030580c4c0c030440c044680c8501c0700050040326140003c10102401a075000c14004d500801e1b009119111518511003d000410709000c0141e0005154490894003000541c8a0b02ca1300307a40140d1143c0401e060032450f0506184030003020055008500c101070001e20018056070019152000307407006403070404402510030034401c205001d815000917041c4085000d079401a80307d404194880d00700070400c0320014680210b011101c5d0700410000300d445040b030086007840102c440325020036203040c6140000d00f0078050800e220302d120360032080380c1d20800216640c4405002821030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 92140081 1250 92138831 92138873
    0xd08190509030105011e120218010611010b0418080904110307050309060a0c050d050406060b190305090307020306010302090c0f030a020306030105091506010309020a03021003020703080c07030813 86
    0x140011460052154204600250003903103000c00104091861016960310103100030200902035007030624540c00748a20301d200700d810048144402c5900c51080345960701810345542c8216203802401200b074251a2420343c0540140c0c6070101d560303001c0c4079a5981f01003654021158659032803030780f4080340041012145201d0103002c040103000405e03074000011801848030b002124001c1e12811a0307030701240c15100a0f00085030041020142207071131358201a40c070034082c4100041282d51001d02c034540340c1c0001c00b10303d00103206140c82c0040540501c502600640041c00450500082c1e80c00300740c4e142410300000e885110030000048203884004120340c440c00380311850030b403039003040071041002c1c2d0806d8501034869400c150000d03514180024a440c00e582e030940004c41c82d81c80707101c010740080042c460140d8214120391310110241c3c42e00340205010912682c1c0043c4d4071410340c01c00400000000c2e00000c00000c0c108001d50201381d2100010b5000040c288154140100c20714258224502c21030303140b020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 92141331 1250 92140081 92140117
    0x3060903031b08060102060103060504031e09060906020303150d210f0f02031e030603010908070b07030506090405030906280906080a02040b0417030c0307080a09050901050f0d08 78
    0x8059154001c202690800c14010411a220701d40c02e4600c3c41c0e046500303030700503800500100045100c90300030b95006030090074042080302c0303010b40300c1c039000d285004c401010a040d00010450f0981c404c00c900000e203090b101860460902008540d821940001c10622403481809690f0a22034102689004400e08000346200242c4000c8040e28560b05c00620a01240b1180d0109010b140080304a900c103421408250b100303401200f40c501e0980e000940100d0300342d0768408090f00040c9840c4001c02c41d0701d000300000c00070b51a1091005082d180020302c1c45008650400910001a40c00020344804120031191982c44116112109110700310b603130454016000000307502d503e403a8204410724140c8444d5a5002c180e640c07010441e1050748280e2044981258040000300003035030004c282070401c2e80310384096030b24103080a000d59103075030040c1d03400795442440000c203d92860b81000001005060590b505e9883d5894072001518060209030403500900300c4030740403010095003070102d840c00c1c003603007403aa50 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 92142581 1250 92141331 92141333
    0x1612080418060503010c05030f240307060306090507050405010512041b0e0604110f2208010510060e1509040902010c0804060507050c060c0a02010f1110051608010501050f13030609 79
    0x4090810b5220b240c1c041d510b4800c82c40d200798465000c6034400c80318818960b10584603d840000030708071100a0600c0044215490003280c1e80900240000b40210394020501718107040002c01180d50181030381013070010400c2300f081241d0b00300040d10202205458405190303540c43c200f425441c681024685c3c8403041c80040480c00d090200c0c88640115429901000f09448a00601405100b1003807560702c0607100b4813040e08141c0d6070100c04001040301d01000017200307507078589640c2525400c3c1e0305502c41c0c3d003820741c050260070b602031a1041c16500484e58240b84c1d02c10740032014420711501c11401d01654884448000703590080c00e00404280d070080320140d07160b542c1d090041554224000450f000c3c007941c0300580003460b01900707494080d0300c02c8000d81800040355005603402e1041040640a01600700c50b0042002000c0c008449101c4284e500414180380902c40140a55125002030303060000f54001440142d90083c29100100384c80c0e002c603552517075100503000a184c02648014000c0c0c0c00c01200c44 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 92143831 1250 92142581 92142629
    0xf0e0d0303020c0c0d17130512010b01021b1318021207080709050f011412010603060b011b03121d06090c04150608280518070816120804 60
    0x4007103a00b002950822442881008403c014440e4060000392108502130185041d08000707000041c000d04440740a556203002244279203240e0840070b012659180352000d09541c0501000c1219680020030000c40e00c2034800140d10403c10880505a95503034031006a10420320380007102c8281d80003000d42d403811105651305035540149000f110118060b0380c200041d50500380c02418024888000319101c140e0a094100b594000000b006580c40040c030025130640b000b0a2281c100914020500869140e0b00c00300058a8400800c01c00c070f2000c0e550081490100c1e41c4000819000040280c01191580041e4112004881c40c408000054061041403016a0900260b40480d035001514180010420850070482c8200c0c0c0344545004101c2d818000340360301101c00301ea203440301440202040b80c2103100304648202c4408580d00303008580c0640401ca0342c00b01c10410b00e0000c24220000300791141c004520114149118030521130845119031380c1904020480d400d48001d840c0340e802c00701c18802221180 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 92145081 1250 92143831 92143837
    0x40602031e09010c35100f03050a030905060f0d0b131509060603091502070309090c0807110102031e060a03050313090b030114070516020402161103060103120f0e0d030302 75
    0xb00c000ca02d00c0d20317644110040002c08203d80c11140520341620710101d0704240c03030b243d40041c4040100c0400c160081115154822480003541c00f4030300805000c08a480c1c0904040d8880c0c1245100300320500034440440074903005c481802e030888001248400c4007601180c24040b42c141c64040c0e945c20038001c81c44c00e6009003800c0c3c040310004101403082c00c1c4da40c0e00940407584000f0300078200c01d072915590f1f00081030381d40060101d0b5101e8a042c03c5410760355040340c801c891403900101c001541c0807050100711a84410540d6005c41113500842c55401c042c2c2a400401d403100400404400e040c000260503507403a41e9007400199000410341c0d50300e0031003040c0c0103817042950052001c40f5142c00444111030a0500c5060540c20050141042c9a02c5a420982c3c240e044040c00c0c0d00c4800007510480c00584030b500151061174203424041070b4000d01450142d1a908600301d84038000d83c0880010408038404210407060300056040c00381c180340c600801111440100c0350300781d80210503c001c14042541c10350013 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 92146331 1250 92145081 92145101
    0xd0b06040b0301090222060f05150c0f030d060302030606090c04050d0302031b0a050d03060e07080a0906142706060f031e150a1503060b010c0b0a09021f08040602031e0901 75
    0x820091f60351a4210032070b65a8107401025081109403c454800b8218000103002628484049400520502e8401481c0d6485000c01924481d102c5508108508082081c1c9801c440701f1075034003005280601c0b51032914001e9100e1a8402e083d201c00b03140c281802441150b50b03407519240c07a810340d8800c132307140681e8907030040c5001ca03054400c40302c40032505842485110103440200c0360445082d11070040842e000070014110400840c0e40744103510000d0514400c2114420b0036505080b41403401ca0000d400c42d019070317800b410800d08030000e00f21401c1c9000c1041e41e40050115403881141d281d8801081c0340c80038070740d03100d8030325614000c181c104080009500c4032000c0c41c40400c20455038851440005030b41030000300c0005c6032441c00c824400600e81e03030070041130100c041c540032600071010745070304007a11070940302400c030039a84040020541c24403c2c20041c07414160302c1011030350410400020108400107002a185030b6020001c0f800c04d442102000f02404400c98815555040a0440d00d00821031484 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 92147581 1250 92146331 92146399
    0x6040b04060e010c0302060609040206090d12020d0309020d02150c030f04181b0c02040e100b040b060f04030605091009140c100e060309070f08100b0d0b06040b03010902 74
    0x32904202d0340c070641c8001c0790315505501602894a50409000c51180041c00803030340314000703109010054441e4122000403034001c1c00b680050364244503019090040400b130f01d9080504001201e00940c0303500c0c018000c00b83e410b85190413420340361511800c56006141421f120b5002c00500c1c02e010f070000c0d801034001e50780624120545080c42c0b82c054411147c9c09003100702c294803607e404207800c034003c8050b251014006400840d1000c1490b0005040c00041c03103914140710fa990080d030740720f81414490346402c08803d4600501d0000b402030402035900540c80014412500d03003001500c030100c24803490520a0345c01209001024203032030524240d180a4080480360f2084032001005442c0640c0d0b42002c02da5140c5451100c03008203000d200e502e0b07000074014031f414400e448000406020800d00d0070001c01820010b020214164070310403064440c90500c080c458098001c551011405050800b50049002c50f0001001c848060107c0c0c0540703000780307010758000043c0f40001031030b4400d44106080041c2d901c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 92148831 1250 92147581 92147597
    0x1803021c0512010302010c0f06050a060816030b010e1b07030f0305090606010e0f010504050d0321020c07060f030e0607200f060c1b0304090f0509030901020c040b06040506040b0406 79
    0x101044659005462036100b0b044200d00c010800b55015500001d5218024010945403580546411040d2242660680400c0d0341e41c04040110b1003060121403498080c4c2207454180c5407450301d510403483d03818003481018500d660003103121a5200b079030003951506c02041c1240c42d03280c1814040e120a920b9885c4001090802001907032000740400d8162280405845002c0c0392502c442c18483e202236144405814010100300205155842e6000b64030307000e118ac2e4564046c02c6000b8901c114510312103c9411a0600511030304441a002003044400d0b50018a045140034186960841c040c02001e4682440d40c00358000784088142e12010140c03800c00140b903100ca111078048500c60707030b4000c030340c00202075900708102140daa0041d40000f4003d0380f02440340c803a800e0504411075030130359000d588202d0b01950388a10441d894440b03405000d0740004024051401d04030000700107511041d00c8001144655a07036412900d455441500762009080007500d001e4031592501c41010541e03000d8012207000c030320b01c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 92150081 1250 92148831 92148883
    0xa0506010c02130b0111010e060402040b0a03030c080304020402040b160204180305070227010602010902040b0405062202130f0305010b040209010507080a050d02070f0b180d080604180302 82
    0x846018219a9000d031043c0e20100c10441c02d003000b8295002d245040200400110380c1252003405240c50318160000030303080d24141803040000f200e205001480c00f0b81064a010008640c1041100f0485e64000c1d0540741e82c0d603943c1c40040c00920645c0c0000a480303c000c100804200d034190240150380b803003658200b10b0915034541614586400c0840100042c004004000c014148405d56112061210048910502c1c0b010344090780c2441c05d801c20b0005070342d44c01d101400d51815004110704c0c050260740030400c07810b002c0702191003040f4803034441c007442110001d80d20b09031034070794112000e01d42d903c14008510b0761240380365941809644020303100340d030070120300c04050710b45031007110b000240c1611058036004c03480c0d0b81d0001c142c102041040900c001130004c40d060314480c0c00203080c8a44580d161080071502c074540f014116002411602840712400c1c21008013050024002d00b04007100c1c2000c00590781c40b1400280074021070458602000010201c0900701600050103095a05074401002050441 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 92151331 1250 92150081 92150087
    0x40e15070201020415110307020402030c03040b100e070315050306090d02150f060d140303040f02131e0f0e030a0903030816020709050718030c062d0f21050a050601 72
    0x285d004003640000c49510b0b10026601a082000b500c0940806803801c0411a4000800f281c1041f04e0b01c991580c0000108010460604004d0741d110f11074800d842e14260410015621003d0024070441c03d26039a4640052529030522103103008007401001c031806841c0c4554101c0d113030402894458098460880a09000701080000785c0c81340e804e2040a54443e522701d010882c0ca0b00740c10390706641f00003503841a170780034045c2880110300c101d0194801c903c034840580306000d6502070718941400114545007110030706030203401c44940d01090000001c100304034031048a800404290136450180c1c440010f95111b00d03600704003410b007268069260841d03030303564001800030040070000a0400581108005001c0c02109078400c0785c01180510302540d40f004c0359589400030a1541c3c1083e80c0c1c502c0b00712000c1044c0b0740d1081c49454268208811092802050b0a07610002c40b03151404000713000b24003080012040c4241030039801244591000d910040b0b00c460010300038801980d0314012a41004d0000e061540 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 92152581 1250 92151331 92151337
    0x111c030203180f0f010c02061b03071e0213051902040311040c110607051b0a060b0a0801091511070206070f06061208030a110c032b200307030b040e1507020102 70
    0x3004c0c24005079109000c004460074040698100e900c55801d101d0070300304220300840f54107124550710040d6903551450400002040344c0f4210403014840c1d480696005031602000c0c1201c4844901021513281c130340380c4010140c0c50403d1541c20500d44081000002c0c040a10310343ca100840c2550b00b01b28240711428100c400320418031031070038107902410104001a119a0051010740020703c0c8801c0c100c030f0044034050804101c03100544510791030321000b4030185050b2008030010440b402c0200000081540e0b0074025988003200c96510f0b550303400c21400f94001450880e2081a40142940d6480d061454249010319011800ba01c1d6685009804541e414589020505440e040181340d802c0d90f40c0e080d40381b80a041c03a0b4807007005402c400e0042104107582003001e0810404c880824900c070702000c00e1111020351aa189610f4842d0034486600d204200142440f540c00380450600b960325509caa03030940c00740c0340b0000e40ca60841e2500080400c4800c011400700d02403040b038490081c8985500390b0490a0740 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 92153831 1250 92152581 92152609
    0x8010605010f0f030b04140901050f070e060f070204060608100504090206091002011d010c0e03010612030804051609020a020c1012091104051006021006080703111c03020318 76
    0x42d011168000b00ea8058210440c010007680f6010489540c0d00003c1402c2e11800e8001800d00305266003030050002e02030003040c0e0301000d0b03001000ea840c0751120b401804000e0303494203240546400240c00001c0f42511080307440290f0050410b014140e80c4181c0204420750442c0d0096a00f43c170411b0102d460300e014010343c608103400402503070030010a003003009010680e01c0e05001c20b540d41d035070400f50084400d04240e07040707803002400002c01d201201c902801c81202940114400d0b454031105000e0000b020901250003a098a4411740b41c6d612460078619001d0501b054900e20015000d0002e12600d90340c0003420182d00907800d45502d014144140015149400c0010303005c0740b660004055030500591040b11041e018007070b62600c181144011908803001a41c1e45100d07906015001d20945030100030138940701c40071090401c03840d0314100c0d0103521040d9a010040101003480002401a500c0c90036101c0181000390b0f5084a05413945006540d80d4800b901000200703094071001c06040c600000d41500407 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 92155081 1250 92153831 92153837
    0x510020a05030f06191e0501030b0603071107170d0e010804030e09060f04020c071a0412030819020c010603060507050906030a0c02010908070f0c051203160203070b0a0c0209010801060501 82
    0x1500c82c5005200783c07500003402144c00031545d070b9405840100d06400c00e03000340703030a00754054070916013188200014511f0b005030b418541050720510680d12001e04070ba61084540c50001d0b40790071480e01d854100300c60b0340d0110081000c2d03040103041020300030407401c9074809a80c8070000f102440d040151424642100d0283c04144501440c00036070400c120041d5011500411800c01e10301480300050403a003200c03882080d6540203417814004003448245480b442e1401d41d1015007458034196126000b10040c81c0001c082202c03810228440700c11a01e40264420011a015925000b080c02120700074407846c07000359201c40c1020041600f03640241c2c00c542c161000506414910740c1c505080b000070b0487c004486045640c1d40100c0004210030401803c00b4500c1000d25044c000c0703080c11b010300885580c1d01b210303120f07113816014920001400004c4600c103000c24500e04200641500000303081c5819a408100c04410008088013150b82c8039107842d801c01d200300e071a00e505980341c020050880e41c0e50302515000c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 92156331 1250 92155081 92155087
    0x70f0e06040c0201110f0408070503060f041104140414061f0b0304020303040306060b270604060e01020c04020309030c010f090203060c280809010c020a020108130602070c080601030510020a05 84
    0x203a08194208640010280c000441c01c0c4901e001c44280c540d1243c80180c030040300c00f081c2031100110500c00440144070441c02842c440c10030b2020703410071040c0503000510f0541c504104403816220b41e00f000300010081071484860b86400d0a08100700c09241078101e4240c010000001c4501e1981d00b07813206007400c48400c088800d4146560780b8002e61000d4010b1740d0521060100000040e064020f034005019200e60030381e120721403021903152031200b5030003808201c41c1441d4043d015442d240140c50803103210b0714140b01c40341076040c0181d007007607802c00009800c0341c0004204421028000001c0040080010080248100c05041401243c02c5008025490b4200c00c0c04111040c40d91406071a0480d802c03940a1a0745d2408a004042c200d03581c000d800200b140b450402c51108000e100e500c0c1104441e0024004840c0d4030360008058080080c010307101c1e000e111400d1400d1090560580742020b0f4807501403d1120784484eaaa595220309100032604c4d03110717684404500015600035103c10f900c180d00c4684c2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 92157581 1250 92156331 92156341
    0xa092a0509060f040906240201021602060a0e100f020c0307050307090c12141506031603110d09050a02030f0708030a081914040303150608010b0708040314030903070f0e 74
    0x465074440803e0072180e000c02d22020034814114455040240aa00e1150084035200c0b11003401400c900d40080007964810700ca003a011640d4990341c000280c0d41100c001e079980054103801e41d41d12020004407600710354003007100302d03126811401c1040c091146400311403034207000008055503041140903007501a00480c2c400c1141c1009500100d00b40442402c0040d030440784c042c1000221090480d000403580f42c0c6c101400034410483c0c510400c070302c60950f94a40307985008013202074010601c600c614105559031040c50700f455900c0c015500c4c1c2030900c080c2070049110340d0070441d58403411030740140d100303010300c0500350170300c1200140100c111540380011398102402180c1c03c1c1d980e4a4014190680030000601409c00618188611600904218041d5000d42043c0c28000e049a4240b0720300c1c074048035032000c18001150490142341c110f07001f0748005d5503034810a1812000031f019982c0001d0001407040b60305031521802102801d1040416011104d001d41e495610340481c400c80d04c10000d130036084002180f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 92158831 1250 92157581 92157589
    0x20609040c03060509071701060e03150415110d050105030c010f0c03050f0408030307080105060c0309210f060103060c030b090f250903020301060504060e13110a092a0509 75
    0x4158800c076410005925a507550200d4183c03072040b01c903100040d40740c030040d00301d88100e050380501400341858401418120140861782d2095015100f140b0000d51034002410400d0640b501059403030100003d014003c00c0f660078042da0f4200c40c0e14003002034102400031965050000f1003000c4a1323016540c6030030390440101c094a0700c0c51030440079810410108589156000410000d100030a600c00065940780b900000050a031f040c10f170071661041c0c10402114003002c1c00041a101c405401301c0d00300800c010701103040440c1c800503e1000c9840e02400c05038115040d0040f5910703048038002d040c14400c00c0316800045049540404e19641d00140c218045484295941c58055004d400803c5100b814041102d40c1b80e1003040d15140d18002520348501401181801c1c00b80c040104429941405100c0c100740025402c5074009004001800e18440b4400c00e20004a41c007003c02c1c40083c001c0c0390180e8450b0641005050368030040c8590750750606941c0e40c01803404030406916074140d9512424054414100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 92160081 1250 92158831 92158841
    0xc260d030b030114040f0f061404030806013e160905010501170112060903170f01050f010323040f150b040e030c0a02060d09051902120d1d01170a090c080a02060904 72
    0x3c0e180589d594840c00d44c40c2c103400003030038010341c02922169000c0c07030404001411068224202454045c44105030300d14100140c0c0c080000300403505600880d5110291002d00d481c40c40c009008007410851740000d440c078180d9001a040e51f80aa0b1003201c9880000c00280c1060300c00c0c400c1034540208461220301190b469072000c100e85110785811005240a240403001541c0152070150001400400421003450000624142101c0030708091010104162034213100c1210540c0318204034848100080c204910796049085150b880341d40211312000041d06200242a0000c0d100d00603891705040d5031007000e0000c1620300280c2c00000402c1c4010842e424400f081d00720080b6004140e455810b1031001850501654544610114885641d03001740c3c01040600c040c4003078000b0094201909012006512070324070412450396200400074048502e004131034007410501c829980c00c4040e401c0c071254803000d030007800c0103a00030b0000c0310a858480d05d4494880c101c40c1c400a520820811001a05003415008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 92161331 1250 92160081 92160083
    0x105011e0e1b2118150912031806070c0f02041505040c030504021011061602100c0309061a010f0c0f0c060807090906030c260d030b030114040f0f 64
    0x15014490200c103001c042c1a0300200303441c0c2c100d209901080b801c01c1e004480c0142d44180c2d0f0300700402848100c0d01c40b036510782540700c0e40056042c200c00001941000100b01151100298a071013690702d2404008030504c8003a0342c2410030503801003002241615100f00700b2090515000392911001e04070a608100003403481004a001004041b00009040c2c2e86512441c2602e0880751004161458544104016418651102000d0200c040d440d1030300d51500280c405d0b405100454054070303111040c00281e1906480200c0c40581c0703030928401ca01300c0b5030306801000360709104210902c21400b42002d031803110481802680c0c00942d00580300c0420a105040c0121000c0c080c4110306c0801c8026219011060700a802540c041040042800002079021000c0801041c402c80d0802040d4215590005145154412460807030b040c00d0300042582c0d503001c0e074500e420420404580305441c0d0280094080c002200080e0310a51070600e00324200e2030784961041c811580a01d40d0080c0600035558090500c2100030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 92162581 1250 92161331 92161351
    0xc04030b0a020d110c0705041113050904031205040c1d04050c0d0602090901120c1a030403050c030c06100801140906070f05070b04080409050a09050a030e0d1b080105011e0e 76
    0x609107400c840c200d0017080c0f0290000094600113062206110079a4003520340e0740384000c0700300882010391038160b44903000d0343d0301204c03410815100c40c11708a070b884918088180c000381c9450140420490704c030600004440d0701035042e595541900740445140601200d0141c412b0f003280314919005e241c4543c145a9039441040c005003452000c80c04a900e1210980215103101c82000ca24000c0c000c3c0680888002c002240700091440101c0301c1c0200c1a000c0035100906000c0c0c0407a921205943c1031041da1402c8034450f049400e00e19040b0200d8406000c0c92050440d55441c1044001101580060507407090030403c00908642d124105d0865144014140344820410180030b144000f450084d5000e010314082c9010030380311400c0480403030841d48060b0076808018a0a61844009100440d2032348921380c160902110790385078040420900364244100030f081c8000390300b0541b00444254444000c0e81d0b1090300801030740e84c86d141d10501018504841e401e080350f01c14810004109140032451740a00150 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 92163831 1250 92162581 92162591
    0x2070906121a040b16020f01110c120c03040b0d020f070f06110903120a0302070c06020c1801030b062404030b1609030201050f07080d110901021510031b0b0307050309060c04030b0a020d 81
    0x92016230031604412414403404a00185c2100e10060420103c022840c0a908007464100d450440c16540d01c1284076140d070300b101c046031442203000c4684c1518240c54280c910f16941c0da025103082c55030300701c0001c8200c48091a020420b04024100c1c001d80d0168080503005040e10018016000038076080301040d20100b41c1c00b0005440012034a042502c01486c0d16001003030510850320401c000d00b12001039a0030048195001000820320480f00c4580040e019200b48010485001c07140051040e5007154101905000400004000790082e04c6482010080c8204241001405c011608110b030b51002a0014000b0f1054608070000340c8010b1007203610440285152403d00700b021026280e2040044510040200b043c200c65601417050207644415412100d035603203089151507044009900000d044050703202004030448449134411800f6040c103020701a201d25003420010015803040700c15018a01407140841c201c0b40105050b50213490b402034409001d640c0b00f14401d80290403204407503614623121 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 92165081 1250 92163831 92163853
    0xd09060603030c050706080c1c0b030601140a1401020703140a0516030312060602030a0c03050d050f01050312181e130203010f0503070f030305030702070906121a040b1602 75
    0x180c4104001503110780c4a80c1101c0c00b140c2005801d140381c0e50f01500a2001850400c602d000b8000100c2e18500c000e01c03107000e2040d1618407103000900035100055010700c2000000714244806800c442e1004208a84c40c509403030301c0d050450314180711704034914007580c0515001d00000300f01c000345407040007131070341101c08504054413224507007100e804150301c0c3c0e0345190105000741a0b214040700d823600740200703080c4102c51070210000d5491085850200c20803000042c21000c25203d44211a5620141c05042c00780e81829a40701c0395145081c840c2501c00d1207400d100803200301c0080240ca540d40849009554549904020302c0768246901e4000302103502c1c20249003006590340e40380710741903484420005884e981010a80c40c20102035400c443e120780d02418003009004a0010080b0135294545044c58494036003003020b0b031074070b0900d4214411460408401140c8500545500b0464501442e50300d0b003906814281c88801c2c201c00e4401420f4184050009400044002580d401012082c81140c1512407c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 92166331 1250 92165081 92165093
    0x20108181b0f01050a0903080a0309050303010b03060f010216060302030a020904020313060c0342180f0920010915020303040b0c130306110403020d1416050f0103020d09 74
    0xd81c05201200e1a0005600440d82450407071034540320702c00c2c20700740e14182c1e0385d10b03024042140fa880010400c110002e85808070070303c030703400c520759441c3d020003180c0e03c0f561544c074121070f00d80013107903001d014490284404406620000c1d13040880d14200369403160050601302c0860107540014182c6004a0302002131030601c0c1c03a0381c80114400c002c030f0306180780038003400d01e400c9054601140e501d008050a10710740408401010480794100d126064148036140d003059240d0490007151002e00079014840000050181c0b400c1c80c800b100c0950b2083c00b040069880039151044a5110b0030280c554000600c01e0b58481c9008082d2000100d4141000d03940c6e01c1d81c503600300300f005000150000042e040481030108200f41111035613001001050504c0c1070a85100c46003045510790701c40645203e4031500f5130111940050100c4003d943c003c3d0060407055124249488050200400440b49203c0c203450312816020580c00c3c0c0059800007030250342403c8801c00110081c0d00000314203903e555803072000c8000141 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 92167581 1250 92166331 92166343
    0x7020f0a0801020a110303100e100302031203010614161401060b0315120309010e130905101e09080406050c100204090603051e0a03081e151302130302010818 69
    0x20450016949110300440188805202c00515009506c10700601400c000190300180584100034080715480c2d480141d07040b081c040d036600194050142032681c5202c10201401141a41ca4945660303103107180c8500103403210b10400c2c8000300c1039031509000000040c2d14001703100f0b8a0300c0140001c1011500c0706460f049030360042e51410a42100d9810700b4560303040c91031720004c504d241c002c0a1170038400e8010018100c50b00d039035143e900c00d019118030f00700c84580546c4241c00b099000300c21103104071000140234005107081414581205040d03005140c80d5901e0f03010b902c0000e80c0c021312003410140303422001c3d54690003148030010320b40948116605844111b102502c01811f0700080460014a9801c00354180382514181c006001d01d40000406102000100f4960340ea03810301d8441040d5035002001d0540c2c2043d400c030300760540174500074080c2c001c1c00b000000300d404034100d52008500801045030800c81c419450310700c00ca110b20100400140d1b0207007100d29032068061548107850203400c00b170142490 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 92168831 1250 92167581 92167589
    0x9040222020a11031204020d05191208151008090129040b090c04180f0207060b090c160b0c0405060a1706010908100e0c0d030306081c0f0507020f0a 65
    0xda400b2525809041d8003070310001c10b44500700041c514162590000c0c101508004002a0140414144100800000300103003101c00310000c2c0c3d40354078100d6500d880e1151413080c611440000d2165008141203440d01a41c0003034131a001004601da00c42c0c1c0b10000c4e1804000209100c00c0341d5130300c01661132800301080c401a00c900d10b00c0b42c042a444050700410041358070b101c09150041c0580c3c810440501242d000b1501a982e440703d075903155003c0410719501501c615204049020300100d241c00810886070844038103000103c80b82c0c007460346e420742c514071540500c1c5000030819070420b85038004901160803c603000000c400c0002d26003a2180301090990f0301080210b80007030920b000c106c0340452824440e0b0740221007441d100d100c041c90102d109030b580100c185005407181d03075403080c211200020007541010f83c0000e131046c0c89102643c140600180920701c200ac04c80d00400e180780c110039039489a184410a196210720034010750000d82101d160708500070490f0442400150f402803540c0c0d80f04450b001b0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 92170081 1250 92168831 92168899
    0xf120b0a03050f011d0a0f02130606030203040c06030c170604110c0607030c080408190903021507050c0405160f020304080102180f010311041a04030b01080d1404030209010302090402 80
    0x20310f12000c19900316034610711900391006001402c05100203010828440c1d480c2c00295030145040640000780540c400310a950070110b1510304006001500741c1c010314803660080c0c103001c111076551441a41900c40e00510840015003c00c91a082ca40c4e551240315000000503000140c1c200300c404000e0002d52041c40c0c0e43e09a50710039020808031581c1405040c1e80c141c00c518082d100da00b01076a0b0104d103230041e40c0c0c3c0c5440641c07108141da0030051084a43c200103540052400e0483c010605600c600c2d03030701040c0309403aa4010490404600c2c242809003900800000e020419050084101194014604040201103020410001407020400d002601d809612a0030790000310a40b403040041a10300020081e06050070010050700c1640141e040d2001c8030510a40c8000303000c06c60b4030104140c803590700018002c0342044008519071100190000d0080e9003030f00c1d034102c07000c43c0e031903070504c0c6008910009500c401110010301c01400c00120791604103101410606030500086205048070b036001c1408002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 92171331 1250 92170081 92170093
    0x23180a0917040306140a06030201051e1e1306020a1502090a0806040302010b0f01020607270906030f02030c1815040f0504030e0f0d151805060103030306050901090203070f120b0a0305 80
    0x5e03061440c00310641080076124104070462850780068100d000ba02d1640e511504007104800071810320204684040c0714404085000e4401c40641d0486600420842d01c1c0800c843c10002c20401d000003400300900303030032800050340700f00840e00a03c040d40c080076130290000d6121078005003105081000b94003135403080d0004600c1c000320303805000d011001900a01d04642c03021090281040e0031503821504a506001300d81e0076039560318810340000c031b000d602c4119080c1c58442c00100b400000814401c80d00c0c8220156800d11450a00f00030b0b032040c041000c0c0801054460215036546d908024480c2c0c0350710041c10100d204540240500300704c40041307906401140c103581c4034030090b01e41100240070840b000c803450307440046180c56100080020070b51143e1003a40d1074103000d5428894030480038100c1d52001c1117403a15a10ba02d0b006025000b00c0c407a080c0a05441000404c0e1264580284c910980345136407117069440101c18111052414102d412054540e141d60070781450701d912032088003660003440106a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 92172581 1250 92171331 92171351
    0x120201021f061406091804030201111201090c0306050303041e05041a010905031c0309141c0801121505040201120606050c1b0109120302030c060123180a0917040306 72
    0x84803864641682c0c03081c2800c001700003180c4c0d94401da00c041c0c00002551200142d4035407034103034018403201145620b02c500c045900e00d07014400001d464140c90020606004404441034183c06861903400342c90762540003800240b0030105140c0c0d03500203115088120b10320041c0e540011030100ea03841110b00c4030103e02c0441c414640c0d604410400000c1901380c0080c032050325110404100c450042846c14105911800000c2c18001400e45503101c44d80c4140c10781d81c4400740c1101840c1580c41c040c000e01c012807065030000541c1c810340c0e85504c03405a0000003404481410025500081c0f9006004034180514100060580807042c403503171002d0174007500d030340342c0c1d1301d0b4000344035454102001c00a1184d07072520810092107981c080910000c0340c24910340e034411504075180a0741540a00072300d0840314410314000052119400d040d201da2010714984003406002d4680a0003002c80400044201d40d0b11428042000d0000b0342c0e0003a40d00600880701003134600942c00315080309500550060b640540c5404800c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 92173831 1250 92172581 92172599
    0x21201120b07080c0f0a0c120f080106020303100b0d09061d010f0b03070e0c0c011a1512071101020403020402030c0d1514090403090503010504050a1407050102030301120201021f06 79
    0x15030840b06a003001c801c107140003a100c00c0c0f203100c1d0482c0203052040100e040e4446078050b154a4100c258402640424001c0d1010003e00c9040d240d2080d03c00958900000075011f40040112030194402088000c000350a102041c4510740c0002c83d012a51691400d5880c0894813602c1600136507641d01805220211000c01058291036034040c100c50007902c0d081079070a9507600000d502003210224100010540d81d1894041c07860700840b00049459400c0c29455003202140d01c04a40b500e4408403000d5007040f42ea050b880b0031500035a5140c0c02c032948280d0210786400e0140c41880d1521400500151600b5100c0e070214007603810950741004882008940b5001011060040c3c2c0d030013009034070780014203c0c07401b010000d4103042080382a001c2d211817008503007490720680c43c25015040241c0240440c0c1040c0c0fa040346e644444900c2504c10490001d603c0c454800049030301411144142e00a500790b900700000080d82c010000c0080341035100b02500d003621486294030b1401924081880001d8152505141b0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 92175081 1250 92173831 92173853
    0x70e07020d1704032303090709050f0402040e0f0106090501051c03050423040c0c1b150e030a0c0b0310060906050a03020c0a0c080309030705040b0f011202120112 71
    0x44080d03410400403450900d510940500c00041e00d040c0e4880d140d21030b4102940c040000080905c02c250070030710702c208540c207104000c60040c040703030003100c1f40036540344800d0089410039118491a4408003000c1400b500c2c2ca0b8000c8c03849031285800740c03400c00016500807800c51703c0552010b4031081d240c40c0104a00c2c07400303020a0603003400c190480c60070344d00e540d64000c0140c0320700d005800d08950b20b4414048082c50556142480840140003000381d1105008007900c4004031642c11a0b00e030040e142c60f54045c103d20070445003119126804a0900d21000000343d0745801c41d00c850030b4143c8580450640403a4420202400a288104030300380e8034106141d1500070982a50000c400303120381032108024a6070f000c3c0c11107040018030310307006032200c034400310781c034144200c81c500903088490140e404611048007000401031860100c003242e09071580c1d04280010799149820a0383d2003800416106610b5015a44105072a1071080e230052030180701c2c210381c0c0260002030300600c14008042c5081801c0205000396 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 92176331 1250 92175081 92175091
    0x2070b031302010809070e040816080a080f0717010501030c030902030316150203270f01050705090112050912090303040806040507060906030b030c0f0604050303030a020c060c16030807090b030405070e 88
    0x146c0851418590001080c1002800040500d60001050b24802d07010140e104034555000e40c100b07a85411400c402000e861301650533248100d1000c0205601d10300540c070700d030707406d0300204c226441c281c1c07810005400a00306044044140744e250034040006907402d2005110160f00c260800102c4040c40c2032040ca807100700e103088018244104240228051171a810805d031080c22608a5a56031240c80d10500702804000307a01310545c2420144102540c01c00c4c06003800c0f04086c0e913070421202c00880041d0559a090300c64001c1ca802413114001011445001401d00b01e1000c0c2c1140d10b403545d1038a800d450100708860941c0c01c0c0c0c002510911043c0d90000bc0d220082c801340c5014401025481c0000b601d6050b2442010f00c82e0b101c0242c51021503c5000030f5070001c1000805030b075200d240c0008000041e40c009503c807421401860001140c031018070303054500740991903c9050984829507816111484003410482c1400b4101c0e00c001038528810000703601c194032400141517610f00d44071204a203800c002c3c00c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 92177581 1250 92176331 92176333
    0x30c25030f080906040b1b07031128080a050c0d030501060f0306050906010c03140c0109061407210902060406030207020102070512030d0f0b0402030c0c07151b0302070b031302010809 80
    0x10034400000c40c0080d00d19003142e04980d840910342c0f03840307c00d0450b0750540d00c08002c0051000c2815010300d07410041880c000c175841c002b9209403000d0000c6a2007403200e9400e140143c2d00c11021080d002c41c1c862409441d2080290810526001c00ca0107101d2501840c4464000003980340c80042c01000d5000303003200c14000c001d090a010050400d0b001130002d030700041c0424104200d035400d660074548290403c2160f840a40e1240344d0325076400c4021800b80103841001d5550a080100e40700c0c0c2c10002e500c0c5a8070a125a40d19800c80c01507030840c4234064126005040c010640741c01400015903200c000038001030125407001a641c040510029040a8540d80b045104850b55661241d040e03002008942e25801050000a006031600210700c004106450f20180c000d4404801c00007003803040001000c0000031403088480725551000048990000300b400d490020718288a0000c0c0d060010a0072101b0b10301c00e00540310596240c000039040d9400841d1074000406480240e81d05550f0071030070064100710914 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 92178831 1250 92177581 92177597
    0x5100207170306010e0a060906020f03030405060c07050309060406090905062e02030712050a270308070f0b040602030a0c02010e0c0603060a0b0a0f090801090201020c0402030c25030f 80
    0x34035001822801c8241006036001d0010016480341c2c0303d44000010410020101c242c56034590200a00116080c00f81d41c002d403107165045898004000305a0780707d42c3d807100003070203540c0e180d45030591503801020b411222817000f403203010b00c0e80d81c400005e00041c007410758822a00900c0c290904042ea440681135a0003001800b15160740400c813055207100362900364102030400ea029580407851445803031805810600f407240c2242006a00100802005440380e440c0c454181c140300507650000d084035521a1107400303e07801000000e8001000e040324038051140c0c1e0300d40c0c1c01c00340c491148d0081b0482e021580541c1c000208018041d4903c80e418280da00d601c000c0104407999440e5559850a0b008020300c241d0b80070000485a85d1642c00c1003000e0260091582e44070440014050100d02ca00450000842c5401a000c100c102c070500c116850b054050340101030440b00b010901000758000750503604030300c1c8200000800d04201d242000d0701c494054071003404e22601401e0040c0907414040003181044030301 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 92180081 1250 92178831 92178833
    0xf0604020a14030705090916080601050a1b020a031a040611040806060d0c05100e010806040e0a062f0c070f0b0706020a0509120a062d0b13060e0405100207 68
    0x1c442d80214044202550707519010015107050061110055008003040d042001d00310210f110f070011041c20351036a083d55190080103580c940684200c001c0000c40d000501d981c070150314a5000142400641200c2c0100d07181d0f02e500880d8041d52080d6002e010b401300c140010000c0c203115031000e4520000429003001e05160340d1640f208805003038144140c1040c4888002c1c401c000e0a90030003043d00a0504191908100c0d012b040301e965100c80074041904080000d8442c101802040300140b407000c00b80000d140c0b555070301c000614203901d2a48102986a83d526451400210954008000307021120380380d1001b43d01a40ca8152143c10141c2500c0d91001700700400c0b2101d5094405981d84001e0150301d031480c080c0d080701c0740d0041d0402282d10200040d0040c40394007001c68400c1070b030342c058003040c00030200b40c49028420035a0a50700030980844040100301c140c0c040e42c410a5813003030051040c60490b01004001d800c0d150541c100503602c1034100c0502c000c0001c01c01210364468000030043d4101042 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 92181331 1250 92180081 92180087
    0x20a0c081617030408030c0a0b1003020d0f14010510091d0703020d030507230f060c09010e010c02030a14060112080706050712050108060a0c03021305120304090608060f0604020a 78
    0x40e5118542d850000309980380701e074000034401d440c060103a60f41120340301c6002e504891f96481d00390409640840d1210080307540c903080c100c10351054a40103446503100c1840e6684130b1000300c400020a03503000c1c41c440186e1240d070070f0038041c3c94040c010b000b6072480c00608003c1c0300022a04002c40741d0041801d0401822600c590219800044a40465000041c4032480c1001d8501d0b1054040080c00e011003031a03503065003030210003110b280012000403a00c205180100c40350362410709480c182070328201400450800e611400c204900e0500600d05207000913003a501180c500321501c40210b80024002c5203480301c6400c01c005d154018291140a4008502c4a4a801c0d905114602c40500384d151500c000401a0f40a0206d07420311840c515800c20a07907075a42443d03605c80c44c1c262805a899400e121070800814424000d843c110700ca20b40699016520344000c11000c00704007440c20006020912000401d0f44c0103103c1d80d40244010300241076207141000000400f504000d100350710582c0b0500203000a154 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 92182581 1250 92181331 92181373
    0x70e03031201050616050d0906030c0315090b030f0f0a0303180308010e0c2503030f02040b030c1e0a030507020610030f12051c0608010c030908070b06060d02040303020a0c08 76
    0x40543d045513540c4184441c017030484028081c081d1440c400c880f60032000c5c90f84240c2c8442110644d5400f001109003d06c0114165070131100000c1005800d00000d010041040e03100c111f09400c010304403a54210445c011a040c4400c4c11008103494000c51000350916405004540c5ea102d404000c0c096001c034a580d0141240310b041c0680601484104001000c6180360402c40f002e00c041640040c1c025554404034240d80f490903401240064180031041d940790304540240d90a54400c1041b075415a42ca181d00180140c21400b810070300141c650f9480690031600600405a9030314541d00031915240c07080e0702034604403000e04420503c80228070100045400701078a1200035501c42d210f034852482d200707411a03c900807581111410100005248410f060550104007100c2564009000018216006508603454410007400910003000301d180001c00f6402c04944c0840d0007004282012140591034017240c020f90011405640021801d1090040c072039012801009207000801c1e4800040c2d0a9402d007207 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 92183831 1250 92182581 92182589
    0xd0b040b0a1e1a03040201090801060b07240504080d110708090d060b03100c03050114030304060f02030f120403120b030c040e07050409060b0916050a08040609050a0308070e03031201 80
    0xe2900c41d441c01c0114a8012900043c0302071002a9103e614080b000303410b96005950803804120400b00010701004180107074001c41303800c140c0c0d0500700300082d12040c0901407843c201464210215034a1005503005104030342c0104d009102e8580c03101503002c0000122a0303800b00f82ca5040409020000001e40d00c40c2c211005040265044620180b07245004070281c52024100c0b5450f00035401003819400c0c1a0f03208040400c00c5960502c00c91340d803090507143c03c5000c15002601600200402c1c0700d07a80c081c0351803040020b2540704807803034500030800380324840d008080c02c3c0e603016525109120031305600204c101e620420b907004c100229151000046c0d910702c80e004038039000f40c2d12401000494901405100d005000141080c80008031907c0c2150081c483c02440740c3c4985400700c040340499164500c02d04001c42030340c466a1801c0354084003511054801001200d12648800c0340400107103052098913841440782d26445900c0c10814400703040c1440788643c81340640d005020400a54642c124568111 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 92185081 1250 92183831 92183849
    0x1401020a05060f0702190803181009050f0c010c05071502070e0109090c053a060f02030f0c0a0f05090a03050318130b030a0807020103091a06090601050301061211090a09020d0b040b0a 80
    0xc80009c001003410400e00da481c000d20185403444420030b014010820703440003c1d0032005d640c9030307250040041d107641d5002d12018049900c000c000f032184034030780318400c901860305004940d01690740301c2c1c415600080c00d800203070541e078407801c0003c01c08c401d50802c0c1001c4d080889140b40340300d03241c0081b940c0404041c0181441602c500210000c1038025580c0716445581001060013401da40c1600c0350041d60055900300c102c0310300000098000b28842c1c060f6000202c80766070310b010300604044216000c3d00410703201584203442000000c00907004000a0148104c1d07160482d00080d815002c20102c211a080046a414140800c01c00550b40c0070800708481c3d80d20010454842d03540b400100d0050406d110001c2000c5d0000004102c0300882812041c880c1404a034281d60b155a07000044a550100b03108400c081b4051312070141403103125401c18001e07140001402405e00c24510005500300c1004d510501c00c03503a000800140c07050306402013089010042d582030000140000114036507000307a129180903 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 92186331 1250 92185081 92185111
    0x9060f21060b0a0f030b0703020a02030a0507051204030318060207080a02040f060e091e0a030c02011b0c151101020a08071d03070308030114191401020a05060f0702190803 75
    0x420080da403100342c0c01100a0409441c040e21142d050f610100c040c001644c00711070480005541500c00c1c000c458401d003999010b9810000e8044007a9400c1d080754204607074070b0140079400c1c070152101d0400703003000b03500a41d15030b20061800644031900e001356130000f90444d04840c40c1400001300001304072448070350641c5c000400044009002c030060000f6000001c01040c45804e0000244002891040034504400c20400001c1c2c0c3d0003c40b540c800e910f48004010800c1040712201560140001ea0100c68980402c08800905992803444564007a00100500707005909403011080e4001504c8030b9181c0b460300218a400ba00d4800544080402000c120401481072481504c0168048644160700c00c0134040b030b901a030b00c0c3d2514001940090050480d07032701141044581600d4241501088505000c40b42d000603818002c190f00c03281c0e52071000368107510881c000d00c2e0005d80104015032045c81492000b56050a04840c000e081c402c1810f80700f04099440b9000801244143c0101d035040403103200301300e0b4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 92187581 1250 92186331 92186333
    0x806060d0317070203040501021b0a090f0b041103090106080f0307170c01090c03060506061806160c0801090c0806071205040c051306050f0307030b0109090c03050706020709060f21 79
    0xc2c0b121052000d9041118100050011a58000010f841500c0c0240c0035256121410302c04013103d8502428003960151004070304110002403a4003c0445d9429202c0c01f207402035003880440e017035403120710b00ca101d0010300208012000000b840749102800080740600358450303c21020940c0c0740070f0349501034000038800d01c041c2c84d902003220890307824010380c0000b40402c820700d05125441d2112484160b61041c01c06000170410310340f500803202c040400324030030b05100d82500d090003283d801118031000419412108070b030104840408090042c402c0e00d002103082102490608050354880c3e00100300c0b40e0182080c03000c4107810006072840142d0507500002d1994690400007800703c1035070301c4184c12801c082e044c000e901d0710035007002042d1751003a2207518441403406c0038199204894031006d030100c0d0341040140f01040d0350341c000d50501c9000740701c058102a103c4d16241c0c03e01529030301000140c0e115100410806a031030041c40020004c002810803501c3c81c0c4520400e00a100e124034a00460628003100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 92188831 1250 92187581 92187587
    0x8010e0a030e04230f04030e12100b040b1513090c08040b06010c06060e07020705100219020a05271e06010503070207030c090204050a0b0708070305031905070e040f060806060d03 78
    0xa250351030004010070480c181790445108030802500d0981c0011103051000030607042910000d00010b81040c000d140384549560780714020140c460006900c542c64180c4040541d940190800520040c01e00305070762228215a00740c4894803ea1101d03000d1410811400d0526410454003540180c020200d12110781d54400104c03a003026609000b094240f43c0301003c5050782c04007004522171800c070b030211a04680c0310400c001070041d0304240080180d0048107a0a145402d150140e5a07207840a00340702c01036502c1d2400601040030750350081031054003074256440488820300509811000d022926560203082c00c1b004101200010038550500400101003140e1910800a240040d40c0007440740e40362503181d1080e4030180d07026100e01840348150f00c1c000b02d07009030018112a980c650062a80d07152442d1940c064a540d040104901c420340004d10707158880c0401405218400e200716512100b44907011030801c42169950480885098600201844101c0d40091801d401c0401204c0071400c00255140403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 92190081 1250 92188831 92188871
    0x30405030403081c15050303030c0a030e1005091b0d12120501030b0117061005010f12090302010501050913030906110a0c080a0b1b041a090d03080108010e0a030e04 72
    0xf48182c60004002450990041c00071081e5540c3d40814402a91980c20804448115009060b030542041001c80c01840041d00142800320a03810b01240541840206a042900301294202d40503110000c00c01a0300080c080070f00d000c65019900d0303a0682d21040461001420150b0003000da18a0195040b002170103045d078005c4455a0301c0040c45150386919060b21140c1c020312442104081440700c20701c840d00042400c40c42002c42d401d40340703207071403420004440c030510754419442030000860795011b03001c0a40c010500d0884c06900003150651504007400515040180b80b13081211020080000107a403254054003154418a04294500c03c6507002e14203060185c3c8009100300c0001c00001303807000b00072a07603100081c0540c2d007100c80b541e1801d40809100d40079903100703003500c20100010304c03240441c0403c1440d060034411000d0b05154180f004142003691a0805901281c04d0000400c10743c0c17424010006048410005045441166030b4040c00940c81c20207050320a03510f5600e1800c3c00d02c0c1000c50 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 92191331 1250 92190081 92190083
    0x20c030304090e25030f020f130b011112031f0810061401110606090a1803020c030d0203030103020d0f03180e1501030606020316020301020d02031602010c020c010c23060a020405010801080a020f06030405030403 92
    0x100800c1100400c0d26000804141c00c6660200301e40b01c030101c03403440002c01c02d0140dc1030030000c668510b07a9580130070140c5800080b140b185d080d586081c04109014100f002d0800e200d90002c00041d0b6038102580312120050001c40f140c1040000e442110303c241021500e2908840c094403082304030340ba9840713800064480e031380c215210408828100b00500d0790000f0030303034400c0a0560580b0300c10500c080c01240c5a2000f40006504003211504040010307000e03004001180f4000c0c0b82c801e4400014890078411210242d0000e08034040b00d00522652000e00c03103403540341607024201007021503d49240a5140d0042c01120a0050300c1c000e00081503440a404507a092401c00c80215502d2800401e411018010700031401d0056103400204454030b40001180c0208560585940c2c6840101d60781e00304108510b0030001405035104108594640300c204801801407030f00e48405078803282004001000114164031030011940a11400341c05a00d4111045240c04400d840c1d95560703a0300e504242d4994484d681c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 92192581 1250 92191331 92191339
    0x7080903120f041805010e06100c20010f0309051902031903030212090307020306010302040b011b030806101e0e0105070b0703020301031a2401020c030304090e25030f020f 75
    0x1076104008a0359070000e00a403600f9030011140584884c080710b040b00e60074001c0410313001d07030320000c55241e02d8082d60304601a1881d01d01803409802c0c03961044015014161146029403120714010003560b005a00700512840074907080004040985402c0c0e41c074900b5407070110710200c01902070f03030664070140300f0360440300c20152062207c2c140d01d02d0010300035841008000b131400c000d01b000c00c401c020003108503025203400800405203642503070200b00c000c1c109503280a0600035005001ea2a1842040d208424180603445c1c0f405246001c0e003c0c00400800683c5a00400241564200e24848004603120368103d0916110120700c650382c00594240c46a44405802004810200a07142f58180c00075030580e0b2003120003541200000011106180b01a9583c003010380c00c125845011114031003890002620501c100d806500f050400f107400c46d4030a411110040781c40e1074150080c40410065200d043c540340143c40c0c5d82d2403c00302d051420b52483c0c00020b00c1480600100c0056540b60f0740700300a02a0018 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 92193831 1250 92192581 92192587
    0x71829060702090f06030106050a080312060607060f09051006230a171011030402031506030106091a1801030206070303020a020102040b19030b0316030807150908030711120708090312 80
    0x84100702c3c003141c1201d040780b087d070030000c010926040801a03041102d9101000794100134664070850344460703005150541140040c0480c0f00481c03228050210110710141000586551701c1c14140d0400014100240116061941c104103102284050380c141c00402a2085805003150700040c0d482003207940803a04a0012000014084001040b9907506203115607040001418030b04191880d130000719400b940c10b8014103441c0507480c8030084035aa03c05002000016115111005c1c501120b9400400d4269900e01445100c01420b00c1204090f10030821828504150704d1540026002d204da004010b0406802040a008850003501918040c01e4050403507504c0380c030b90300303200400c03a240c80e02c1c11400281480e100d40306a060110700d9550031208000b101c1603483c2507480e607500507401340d40300b103954280780b61404185000600c540c1c1c0455104940c62503403030415140003000640e0218002440350031440b08070804440c01421602e189600c0f0340d400d926101000c0009040840c0f281c11007a40f80000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 92195081 1250 92193831 92193841
    0x31b0f0f070c0e0106030903090e090f0d020307060f05060a03120e091303021005070e120a05070f030b07090b03060103050a140c1c02030103050d1404031407182906070209 75
    0x100e07803481503c1519818950f103aa03a2401101600e1201602401240c4044028420711500010180c1c0c0520348004940345d40b82003105484ca000341400d800700040c0c002250710010400b082c0102003003202c2c1758200380064109900061084080e900c00200848410808040120700801e0400c01d441001492042286408644484000a1410300300c0c01806a4501c04104501921800f0f01940403030b030b18122003203405800d01040d070518070803004480c071400c6004000a607042100401030008031100c143c03118510f1a20700c89036a400362913030060082041c5c0a01110b407281045c0c0e54002000d28000c13940752a8083c850700180741e06440b043c0742080001c00c101c0360303080b01c40042c0754001e8410380001800168a0140c41280402c0c00002c049400407800052954411600c0c06140030a20300b402e07181c15660364450755481480b0503c0d00f01d07604130001c200841042009c400340b404841a005002000001c0e402c241c00c001556203007401a0311034002c00a441c1c0700d80b020756445507030181048901d8105 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 92196331 1250 92195081 92195093
    0x21605030703090302091e0c1c06090b0406080d020c04050402060d05071d030f060f0405070b0c01060302040f09032304080109140706020c03030301030303050604110a080a050705031b0f0f07 83
    0x990105a0290b1440340100b0387c0350310b04107000c032080138503030241c0206030701e82c0d85030760b00700d0b82c4842c0d0074040310300c2181c41e0140303d00703030b148194002410b00100c0090602102d03010300c401c0d58002e034041845504915231040c500394000c9194800c981c3c040b04c001550796200c1c40010030b6401500c10f4102c029190504110100b50080c1c600070123000c005030304040c1200d141c001c05a641c1e5801d581e50281d83c01400c0424411a2a100c205402a1080082d290019102c804030540d039081500312a042d0f81d112441001035003024450000ca464075038000f807040094036100a00491003000440c000103600000000d15a2081b00581d006804240000d202800e50390400380d140d004d0030001031032203000b40d03100092594000100c031440c00302c0240107142161b1854800343d005100c0285460341282c0c80e0f2000c1c2100070034160042000400f1911880c10500301112102c0850b02c00a104e2424041c2c208244440ca49c2040045080800110f07044d80d550f034030001c000d08503401207003031120400c80046001010404 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 92197581 1250 92196331 92196347
    0x50a050709050604060504140303040806040503030a060603021611010c0203071d06090106020a0305130506030103030305010608060f06040b070c050a090912020111070308060111060c1305010c1104021605030703 92
    0x10240d40e248040d580721003c009441c4100e105280201350f0420041144442c803144904c6405802415207042981d42c084c26070800400325011101600f0000802a00c004184252000b40070903240441c1482d0000d0300002c141013900c0c001402035001e90b50141384580c4942580e01a6a6000e030644007101c7c2c0d02d2081401c01a680c0006021001c1c407600007480d0342c20540e2403a41200d105a0007800745d00c5540e10296410f6005480045500744204404a22621007000550007584070380d4000609600d41600186050350180034503200c0c00c440c0380032200f175644503801e403019202d0702006d00340e41c4d181c41d140003c0d506206078001a0000d806c1440001c00c50003a500010b0420f0040706010a801d0a500c42282207401400707508103196400d2040d140421300c03c0e000ca40c3c1c84201810014050b10036110101c0ca822030031910700300706480000300c6201101e5188a00c01c014074080c20086590060760752550940b4580b10080790046a001c00e010750b04441410410304d405400c20242c0b941e078503036800d0042c1002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 92198831 1250 92197581 92197591
    0x80121060f05091b0d060203060d0f0302150a050403020604140c0307140108070c0305121302040504050a06060f0e011502160608040302060c0405090402010f03240e010e0f070f0909050a05 82
    0x4012004c003000e4610511041a00082c401811002d40f4041551210002c0d00007410032900a02810b04c01c8000074080710f11603844600030740041c52110003251445405010003001c021201d41404280400246c00088141c0c1082e4400f011504244080b40c50524050143c404140d0506c00c01d00001080e0f400d41088100441d03080c5e82d05016503035070420942d0780c240f04020050014104015005850817500445034020403003280b0a4081446a0009816144203807020745103500a00c0b00c1c00c08009080c46a18001d0950003aa10002480c00281c24444030051203450709445e244070401002c14424001d08004483e101d09004501e0f464200003000d0520441d401c0703001d4403030800070407007014501041d1422200c0060907002d483c1d4030750b40111000711890440d40c09040c1c8520f140031070403402400d40b9400320240070980406902c0d05000c4400c01d01c3c183d0111101c81d020341c083c01406201015065441a684c0c2485001d007403c481084400d540309a1048408500c0c103c1809490311040e00201d0140c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 92200081 1250 92198831 92198833
    0xc04140105040e0606030a081e04030803060301050a27050c0315010e0a090809040905162907050c01080c0d0f0c020f01060b19030e030d0506120c01080121060f0509 72
    0x5501d0003d41c16607100b00503503885038150700045980c00011500b500919240744801e0020701c1500200c2080034141d040354004484c08100802003010740d00b402d1141545c84074203408103008411800b1100d6500102031160045141e28090034541840310800c01507111540c040c1c100c80e1140e00c403d44000035800c2c20b015481c12030714040e010801100003401032a0000e904451214a400f080204110045c01e401e1401c070703050f00414689031803140302d03e0000d10003013401c843c0281d080040d840740021782d50254241c0c445645400d010f81b401042c8001240380501e042800e0800d4507032194003081c07040340242001c0380c22032414040c032441420195003024000b0142034003242c143c8003a007140315081e96954041e6512280c010f01c902126000d80004020412155042c00110b400031144101c3c1554094080d03da4419220030911415050801ea007107560400314000c3e0403103074180c40008290700c6041c4201a01030003100070507140040407681c0000031690021040100b10f242c51641c8001e05400c81e000340c12 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 92201331 1250 92200081 92200091
    0x604031e12020106180f0b030706020f0114040b1b0c010e0102040311030604170f0c2b0810060302070201030b10020c0a051002030316091e03110406030302030712020c0414010504 78
    0x301ca4014003c6000b0313242ca2000e03804852040c24048002484c03100c0341d4026031503c1e0161403a140c2c82c2401590090b202d690302808141a004114034252950322018004c2403080381c0030000400d80301c403030641d04945d244c0c4101044201440303204916005030204c0031250351800c21056840c140550061080720302c541380f074210034544042011f13110780741154058805240c0050074502c00145400900c00104005102410300580881d59840c000311201800b0360f0500d04400e20484001e40e0002c41c541d4070803460410280c0c035002054013140850f9125000a054001c00c088003160f02a400020100b40041c220807000070300900001d5403603146810aa0040010f04004103540c188990054103483c0160020761454a694113100203250300240d03203000700400c201011417a1440c1d10304940340380c140710414507943c90640c18190a0000580d07410380c4903520b0080c04000098001c000c1da502e540c8c11104d180305817000f682d4141d013080002c05080d548286085801c0310b502c100f000109060711400d5504110f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 92202581 1250 92201331 92201363
    0x1707020f040e100f06121b0e010302010210050601170f06090901020331080a02100606090e010308220909060b0405010311060304052a100314150604031e 67
    0x22204081c1d80c2c45069004200f8448200d0400d4100c003802c036858480018803030743e81e120181d14a804461040340c528000b001290b800a40c0d0151840c05042000c00c00c0c031a42d45150f0010b5900c1114150302c00c06170f03840701c00241d00d0760700540c540c880304d03c02c10504000502e010f1100722450403040f42c0041c82040c244010880c01703201442078038450000c805c00500c0344035481a682c1302e010008044007810031810b42c0140006841880688842c07803840d002171450b5404164501e007500c006401080400a40140c00c03c61040502201c2d41165009034505694002d8100c1203c20159054100003019a500030f00088040d125480b0900e200c1c0282c100300600104034041105844081c0720152200300040c0d200b030503a01c1d01030025070b08644160704035a070300107040c0c80e40819140d0b1241d041d40c048612442c101d001f07003881041212072105910b420014541c00e03419480f240c40d806004160754100c070b0708071412a0307141c4000302c40c0070b950081848851000d00e00080c5541d24480001100e0b50032040d00904 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 92203831 1250 92202581 92202589
    0x4050a022101061202070206190207083c19080d180c030b06120d02070510020f1b0a05120109021203070812040602071208040201020105070e0a051302071707020f 71
    0x381a10155591000141308070300c101d60107508072080590f40100100f00c0d170403040204040014440f2250780250000c1b51034880c1a5050401038154980ca0041d04000d054000e8a070078100c1c400d242d402034801210201403201180b40400b49000283c005007034403150741c01c3c402c0c0c100c0540310640b01c8140a11107051010113110070b281442c00b00520441c06104140000303112548055031045001c0c0008581d00303420300429140c10704a000e03074000358021086c2030045040114a2441c2e1078035500080050074500050940d41d06180c0240035490311003100300c2142a035a10324500000c040081946507010410894140200044c584c00c0380701d00328060b14a0301050021013580d5490790401a940d00b01150320f04119001c900043c01184c01d26800c10903c0c00050518002e6112485580d454080c0e914040c8006421030741c029085c1c40600c81000c40d8590700344d640c1d40038403080d140c0988600b0b08c821040c0300101d000e8002d4140003441e0450450b500850442603e001e0010315008444401d44511684284 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 92205081 1250 92203831 92203897
    0x5010b0a030f06020306030a0b040606030b0105100c0f030e03070609141002060112030309080c060f1807052206170c0f013c021608010c0c020d030e04050a02 69
    0x402a100d4420385034085030320f59001c0d6078801070240c151405c03201e1564990b0845c01007200c0482d44142d4555050060103d9018050301408003a1402100c41d40c50040c050200424110028802010b14920100b01441034104c040030b403c2c064110380c1d94035261200507141c1c443c140901d4680110342002c050503450110418200c1221035000340032642d00f8825243c0c9451014441501410707111080480000c0070070b00280003034001c00d0051302143c20005811710040c2c002404a0030b81030803006a284120b08003003240d10071a20202c4102031a41c2070350300410381000024002c009182c2c40c0c0000000e00c0c9e40050340340742683e414401500c3e180922036003089a210580e24000b80080d40400200074181644500e1000e994260141110788070099100a00000c0f0001801c40060b080200d4024601c094650340c40f01400c0454002e0085150780000207007150b0055078080e01c60024801c420082c9070248207131007001180500180220b1600841340f001070f502449000e18a100c562501c1140d0300d81e000b241c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 92206331 1250 92205081 92205083
    0x201060e1b07260703090519080c011d0a030605040213050103080301120305070c08240c0f0306010c06061d1e0105060a050906031009060602030408030d180f0b0405010b0a03 76
    0x8107904003211512100d000304003501c00d04a080443c8480d0180c0e00704104051310711603120396503041219007031109204211210310f219090303100d208003092201c0800480c020651803020300c0c1c6428182c900c8907590b45c050044840007508040486004014096603411031480383d4001d485010040405842036011030307000f441702412249090006028415901e0100c100e6a40286000390030124141c442c0f070011203c91303001800319400f0822060035159003140180703501410f8406034a181c500f50b1030100d840e00c109004601c00580c0000041c041d44c0c01041c4484a154003c0801c0201c00e0304c9042c1144418000b440d500c5070396002e01c0c0000c0d1212146001c0c6c02e6030310495248d80c080c40c1d11300410b005031508601075204c1480800d2140304090f850b26409188211a0880840a071901e0480b5560071500349070800700442d0800c10003800058000421600804d81c5100700144210120246284052619070000d01d241c41e00142502401603070358081d80903c2c0030340000c02c0040076420401c40c0844207844 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 92207581 1250 92206331 92206381
    0x1120302030403170903031801080105060a05041a0f0a03020306090c04060e0d03030e010e03040f080a0b1b040306090b060901060201060f0501080c090d050f0c060f07080c010b100201060e 82
    0xc010303c0010581d82010481c0310301d280c40300341400d44450000381160060b5805100086160480c14665a0b0150045d40100b5003504d900e0f02e0011003039401041449540a800c0040080000e913117031803007038001200c101d4400b8880300d41e11507015180007000703503000b6070f10700748115842c00210307420041c41d0084600b191469103039080d40b50359036801c0c806156858403040c0d0605654021845040e4002e000d45804401d0b0031028550700d0381410011000c000d81c6400000c1d0992103588140001544545003a80180c0b00e00b0016050601c103050901992056800061580d17051400840401c00b4681000b030107480c0441c1d0041c1d00d130fa00d49000f2070072900f103480780810605215004100c82e5011749116038200800d1512546000442d40100301502e0f0311000484440d03100d500321000007001440010300c03080e400c4448500d003054585445455015911f0302510800c00001e090300031000c00d50122801000241200e940724841c448041d0080030103120741c2656038904000281054003410080ca0580c080350 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 92208831 1250 92207581 92207587
    0xf070206070302061501260415020301291806071103100203010315140109020901020304080607050415080106053a0f060504060e040b0711060a0f0f0507020d110a020604030501060501080112030203 86
    0x1035031308580440c048e0065401030301da07070721034882c0e00141c2c0010360103010240b505021840302100188950010b070040c0403860b100500c8860300c03805008206062008040300e10540f81c04190604e40c441d4000707400842d62504c0b4880055000b485950080c5040381e01a00c6800e8903695000c4038181a100c0d4011560030045c221001403200068540c003406054006104a03420507494000961030004156404004104041010046d214403103400d0040c50b21280703448540c42d450220054034030300600c0307604088454540300d2141070b9400b50181c032040310f8800703030380340000c168170f91b03215004000505490801c00c3c10b0400c00300da04e00f4940512001c44059a504020541d51030f199403d030b015024101c6020058441040c00d1201e104000745409014640303400101e0b05000d22101c0c1c112840c03050035151442c282801c0060304c40d004501c805d502078080c04d100e2642580c18141c5c2d401c019902c0fa00035406140410301005000d41544001c041d06d200381c945082590b00c882c021048503850090050045e4410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 92210081 1250 92208831 92208887
    0x2010f050d02040e0103050a060506030a260c030a09060e0a1a03091906020c01060f1212021002040303020106050424170a06140402011404080307080f070206070302061501 75
    0x80004090401c002600181031a0b240c50a62501c1082030348140c030705a0211545000744036a901c101d035040039080740240405d603a1030341c900000007058101400d1660000200a103656000b400311000d0b88400c400f5a030369900d9032800500b810725a401400d0029012038202c1e400d50814581c140f065940010105a02c44440303001c01240c0e60000b0100e041c1c50044c0d416145185c0303650509540b42510400c409600c0300c001d21201421180c1660200c41a440b034100c0401041c0e8085a040c0c01c42c907001403104c0c610021100702130b46403031922483e4000c6c40c1e1000500100b41603040d070294003520800c8a0501503e09a5130401c0a2003289201403070810910540400c80c01c5020360326031044030407000035100781c2c1840d1749403402200c140f0020300c5185240c03c4100811580d101050303503ca42a10714009041500340034002d41d5038004d00c040140111800225140704040840c244e0300783c2c40c1c1c01084d0a6561b0f40500d070094032140d0507503242c0301002d0450007a14881d0f01900c01e5046484801c844551030401e4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 92211331 1250 92210081 92210087
    0x603030c1504061805060103171207050306030106031b03140705030c060a030b0301060e0402030f06070e060c160609170a0201170406181101170c040302010807110105070305071b02010f 81
    0x241080700c5143d5108103101d181202d904e080d0403201d01a0018003a503600d1030078203002a5180080480d034a100c108480010421003121035a0008124589681c603130399842c0202e4014611904003524408800c0c10110384a03000c00c0b1920181c034410403c0d201503900e1003804683e102d030140103c551542090760f940425003400006041d082e8501d1801240b926541740109085035581d8001100e15030041e0f08000c203504082002c5104440c04000808203860812001440c6c208000600c1303202c1c4078001030003007107000d040007000e011500c0c41c51448901980d4100290480f40c0e01c0c030441e50780c209028605880018081849044150181c4a20081c00300e140f40d280c034426402402108c1541d90f590200811490110344541e600748a05541c00001808400142c4624901208200c00b1705011007007005411005058a0480741e081c00d00c21b0980e2112401500c504c2031000c4a10013641c41d200c1000000c0da070540046000d41d2031501e41902c0c12800000b84618441e2810019012460b6040060b401c0d501c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 92212581 1250 92211331 92211373
    0x90a0e060d0b0709060e0f0102070612060f080a050c1005030f04060e011a1c02130c050919030b0112080304031d030a05030706110301030c06050901030b06071a0603030c 74
    0xc0c014414800c6060036034030714078548400c2e01c40000044001c071041c0001c40e0030000c03108041c00d046900d06240521000002d51342c19203030044104101c006101e070030710140e06802031800303001c1981d20817440b0742d252214241d8500800c030042e1014450104003051a0038042a9140000342580c0c1c0d1600e503594001550040c110050b000300c1e80e0542e101c4024204103028802c4242090300400704240c0d41c2049020000158440c0c05504110b039032094409c401655002c010490580006402143e581c01c005000e403028010161400c0d00451011402009001503034500700940344650140421a40c80e5800140580d128140040074240d0800c040f50102e401000340c50503540f11003842c0c40c8449403820200e07041c80d5009000719030765800810200c040240c1805505040b100c80744c0c52509542c55a03c8101c8410301c00c1c030a400074000c0004108905900ca50400c030440003018201eaa0b4a120503d4004000004250442c51080c0f084001c907106190120884034044080001402c400c0342c222911030b2205 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 92213831 1250 92212581 92212591
    0x50417070516080307121d1c320d0c020906030109120302041403061b03090a0209040f060c080405061503100e0319020307030c0f020d0f0b0a11090a0e 66
    0x486108509480030150300110b4018044441c00707191201d2151800030b03025964140c400c41802500700046110311500104451003680859500440e60001d04003c0d02c7d00728038490142c12041c0b0b51804000d41601c2e18180144036400191844200a00340740c540e841d01404031404000914214410300580381c0a080d25401401c020300014180f10744e50390707801c54030301200c54990100760041005c010301059500c0c00d240118058020304428544400e0350300881d101c07422540002800480400e9280208101074a8280e07409404d00e152404c1509000c0d0941c02012412110541011055040f00344600c007005c2c003a6a0002c02468544c8031801702c00420344150380f0258161141e1b0400b0340040b403ca005640c0c5154101000d10354884d5048480840402808003034410340d0301c10011100000c1c0e201100711100345e04020072000341002403002581c07a05488402038584ca00d00d0440ca030510202c0c111103401803d000300c0400024400100c50001805480304c015486032019400300020040060031942c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 92215081 1250 92213831 92213833
    0x91e0f060c1509010c02010b0f03030301152a0c0914010b030603010b1509090c0c0a03140408010f060501020706170a09020d080309010902090f0f070c06061a0d0b040504170705 77
    0x39500d005020700340c4000031980343c0c000340e44400036444d040d0b03020722600d144c0130401d40d44000440c10340c03004a0b5a078030040c41941c403140841812110101d03c0760100d81840401d212091030000003444d8901c81889092605554002d2200030000c1c00020600c03454241c802e49401990160f031070408515110f4100400545c4c00d0b54844041540603030700c81240c0e5044112502000341c9484061042c080080b02c000c1400480910030851908d0800000035904415589413802c460700804072040620311b4080d6601000896090161045500c909034000340d042e91805e908685086944510803102c03203200ea1007603401100c4880104848280d95048440c685001500c00c0201c0039140e0744040e2a540103d81e4035659940d600f00314800c61400315000754004102c4400032085050442074240207031000340c218424030602c80034080c108940754006500904540d128000482440c000d40300f801c1e070002c0074030201c00e0715218903205245098840c55005a4000c80f0881c10003800c0260144d4580c0b1501054940f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 92216331 1250 92215081 92215093
    0x5150d02010e190605071a0c030a02030a0b100201021822091109010b030109060501030209060d150b03090102040906080a080715060b031e06010206150f0103140903091e0f060c 77
    0x128050307540d803160007801103a50f85e42e6148158200a165000e0650700c00410000038420302901001d00419079403c1010214016a42d444407125034008004030041c460300729001003540381c0789039010350203004603a0b01c225201242e401000c04000700707090005802d212100320014405c09409281c2c0c0040344071841102d0424020360303040001001d010099001c4030801c14004014050b484040c00f420340145030a0800f036081841c460b0002d801402a08040460039a0f1201050b80b10180010850014014940b50039038034182002c0ba00d010b540a40110b4010606150b00024028400151007440e2074000d61024140202e50752580002d4804c5880c0c21611f54031548045240003c4c80c000398011448200d051004407412004629541c1c801424141550000c200b04000d0300c1080500c46026001152000c500c4e46403000140e000340788015252105490300010004021000070092a4a2604a82040200343c00e1042c245180c00f00720191604400d0303c03030340c1e14a10304240020700b082680c29402e90b00b07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 92217581 1250 92216331 92216359
    0x1404050d0503040312020105010b03041707060c03050a0b09160509030a140705010813050a020f130e06040506010e010f0603020307090305010f060906090c0917010b0d0804080105150d02010e 83
    0x56006034008141e555800c0003504004005450043c2c420b409040c6c00203001641c50008a41041c0c0402000900202800c000c102700710b0710b429045074000c9074440400c000d4203c0da0900100180b8044030822240c03498118192814a032444603288141d01c03181159150807180c81c0116496000550050f405200e0034029000045c1c0034405075103c6020340d8000c141031445c000006000c6035025004102c0403034880744003004100f011408281140d01510f140410302c46403404036100441c2c40130030381c4800d4601030b1340c1100c40201207085401a80610216045a603c0380b0381e03643d44030000e208021403001030505c10000540a40c0245500940d10300740104d40c943d41c1d0310350341c1c01d488913038090680940c0d80d07850034443c038442d030f101c2c0380040d041c894001c0096600741c04014280c04814000d01a41001c042d43c0c81d28213140940000b0700b003840103400c070103282506250120094002e4010341010b5404c1c0f000183c1c00c00d810b00c00000c4603280050209914100c160011350b0200c010b82442e640020b45803217180707 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 92218831 1250 92217581 92217589
    0x21c02030a0f050a0b061f030c0909020d0204080d050c0601031e200405010b09030316060b060f0a14031608100e0c0403110a050d150e060f1801110a140405 68
    0x102c40ba50007900a040301e078901d444d00c030250000c0240780360321070001c800c40c5c10440004005142c1240c201414009105030004c90b081e05c400107594800303203026000140d26a01c03601d9607009441120213580c2203524402006038180d85030702494201c4038195100500410203c0e00c4861030882c032041c0010450218101c9403aa0860400a00c1c1c03540340c0c0049614007200c29052500c175050041c4a1402c000341018074820000340c891107100c0d0711000010280061009018079a0300c0515039201c01401182d8690120070400060f030040e940e81004500481e0301c00702814909000c40e0702c1038030310043c94000d00314000015078100d040601203000c058800032003c180c401c0e0501005005103800e280b1a41c1740c610314038010443e6240101c016010304a06041001281c03282c00180c940307507a00c80700400035a82210001e000401c10040002502e11070001440107080d0b403050820b0040002e035034506041490461600d00341c4000c90b1900b6800d18040041010745032150a41203050100354459610b8142d6074400a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 92220081 1250 92218831 92218853
    0x30903050a030801060807020c1e040608070e0405070e0105180c07050706081005041a041e02040b1c020307020c04110c0111190f020c040b010302040914040b010f03021c02030a 77
    0x4801040f0102d0050001c150003210060780200b203403004100d0810340780041503181000307840c02d02c01d80305281400409941c4c0c0d0340004c00070f860301401b118003090381e0b4840074060f039509460a403401c5c000d0f00742c00700700143c89110050690b02c018200305180340f00c90071001c0303d45000404c24105001d05100c18800074a003480000c00500d031a650f032013150304128020300682a420341c00113200e84d103003016040069980000d5140541c10890f000036401481d4003d4401c50b2441da4500300d4803e200080111f951205840907040707034508a0001112000400740b0f8100300e02c0180d9039a030242e8001da4040100349480c2d00482c54030545e402e1044e00f00551140402c2c2176a904030004541c001d808105207019041c0090110002c46203464442600d2560724000f03516841e98616581c051900d41c0b164140d0790340660121401058000004c00100703600480004000340180e504070307803056065000040041781c1000610a50341c00034907160a401c0441c0d00318225841c400000c03a054002c148051000c54420068 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 92221331 1250 92220081 92220083
    0x13080f1c05010509010801090f0618080705011b0906020606091503010c11010b06090901060809211c0c05090103024015050702061b1b03120301050603040f030903050a 73
    0x301040e1075040030704000b038104051700300c10345584c901500f00010036803c0118100d004d812620025880c000741450b4100c003803141c0f4010300140300c009000c8040140540c40840e1190240c1048204001e0350041110181c00707a2003910b0060384041c0c086400d0703150960000d60000300f01e0300c03c00c44151010340800e003074640c07203241203003c034a00348a02041618203004001100310212141407405041c540050740510060040e2802c03c19417000140d0031002c10021b1000000994522060035540ca03040c007038040c0d02c03804800180809940c1c0007652481d03140a10210300c0c3d00c1c0e480d40c904125000004500a400c0198421301c000ba0818001141080c0b600b4800f4010920400d5031020494200401000280c5c42e4000740c0c0441340d0044c05901c860307221040d40c0076035a04440441c0d030f07411075034040c5209060744184030f8002e014411400c9400501003032582c5001c1c5040c2c0030b5500c4001100c0f00164075000034070996400441c10000030b400144000ba0303c3e102d00744a800c0c1090100d450741c44584c07034403580c1c1c08 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 92222581 1250 92221331 92221387
    0x10504062001110c07090504050307033c1106090606040b010315060e0a0b030709090905010207020a060206070f1701060302160602120411030f0d030b0103271202030313080f 76
    0xd10141000c01c11701c0700c00090320b100d100a02c074a082680d1031503901d1041a1000e0100b040b58418504889048800e40d0010025413500009080d0030320090b24160707802d010f0b94804183c2a80c00c040c50341c0804170f2031512442c00180541050f41d90328092001402548811a041540d1118003240217120030081c1ca0250440d59140050814400144071001205402150b1a80e100303008000d060307075000e4a0403080d0351610b4004501004c5a01c2c280303019010700c000082d0b0000c0c2c550808203a45074000349240c03043c14940d4a624440d011107005030754403d802d01c2c12028007285c0c0c00040c0306507400383e00100072840b08440007612400d0310751103c104981103d8401c0054004060900007403100d2241c5143c01480c0443c080c1034480071036900960f039010421410800e041e1030b117050303030a00d0b8002d600c104c96080c1c041c2100703000a80c201090a04207100e085048800c6608000d0138102a071000050364030038131030000d651482401c50f0312140c02c0b640080f10301c4128007a0030881041c0200d00d82160844111800c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 92223831 1250 92222581 92222587
    0x409050a0b04060f0f0303050708040801140601020118020a050d051624050306060d090c09060801150f060207090e03090d0f0c0b1c09050307021f030b030c01050406200111 75
    0x10400043c0e481036884210312a680c0e10b030900042140100381421241d1505101d9943c010520344800365005a510040c1d09502c0d003c101040c02c200d13070a000e84104030980c000c01c80000040030800e051041000080e400035604402407095003050900c0b189943c0c09801198042d2000c9116600305c460346420002c0c02e150341202241e0385007110a00030900e071000c2d050660075468000f0100340300b40241c40c001001d150300d41d000e61050100055410001d4081e511042c480f4a131909200760180c10310300e501200706244510700107010940c0c45515030948040c0d9005c1e207501b9251010020181c10744104041490204011001180d9907145600d0f50703162103807440e07070708144043c1800c00580c4040c2c1e12407030b0020700400c100d03801c3e41c0702d02e0b1400c0c0303c4807008100007529080d40d04040345140aa00b0b8002d41007010311500301a071544040100d011240175035014005480400140343c0c5480e01e840c3c000340822028001442464021180081041c81600030ba40c6102c10000040d401d4401680440c14191000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 92225081 1250 92223831 92223851
    0xd1401030c0608060603041110030906020301080a031d090402090a1b0c150c0909020c070509130203060a0204030f0803040203160303050d0b01180e0c130803130603051603050c0409050a 81
    0x200c202135024501302c881742d0861030180c56440343c0d00408140c2d1480761444480e1410281e000b507010344000343d00203608644070360712004030903540e01d0b1915017903001c18440e49030b05515014108003403001820250820329181c88550900080130b101920425210b6110480c07451b1680c002d0302c0c02c0503401d003d66202e910840403400c0081b54005c80f803c601c40054140034204001e030b0b400c00b803a04100c0310003010040e9185844d0302c010b41000041e40161303074015000170070f02908041d4407120b40b01c1c0d2390084017610b820351034074210441203206601c00100b901c03550b41c403494003040300000516402400a0161101c89d24a13110100000c3c440d50003c0380481e00101d141010100d05100b04059550282044034990b61508d80c0000301f4030f02c602c5400d14000c03c800001c0c1590340b0700310944829421018200c100903481e034105a881e9002644000c40c485003176a80064564828007030781d0700070600b0b070002c0c0703915180348401200504801032960703241d1042048000b4110300c051107140e104103103e9600240038000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 92226331 1250 92225081 92225087
    0xc0301260105040c060908122d0712031d1e10020f040303030c1805042003040311010c1809050a06081218040b01080a050604020405060706060306110304031e03151d06040218060d1401030c06 83
    0x4e036416100ea124084034100d0f90302000070300c1c800030015014101c000e481c3b012202464030320034442403804a03001050383c806a500050140041d240302e61000d010782091030408944000400480b0105542060420065400c03d98401d00030143c1d8180f48101000e007841d0006481e60042e14200c000500541c0c0e2142500c1c1c080c800d17075080310103601d020040c2d0a07035038100e45224009802880c480d035684001082d000d0941340c2c070580050006a05841e1903008038005028186c001019021207280250000341247c85c05215017181d000c4140c607450142d4460803030320b000a01c2c00402c200c2c4c11a07800c00010501c0e07074a450113450000c0c800d041c0401c009007146850803d40c1c2060724080c444140c14810301c0700080d04200f080001d0f505030b8590041c00582010708401801d4403c80d401c484800c8440040303506120868024800e42c0890341c0c4110640321003051004034400e1a800ba080301036600740000307080c46d0100c028000c0c603c0b110404503602d144406451164002a841100d4254000c001040580e0b0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 92227581 1250 92226331 92226341
    0x1403100606020a151b050c0712080d050c030f0106051b100e07090902030303060607030c15090b13050c0d03030609050f06180c0301260105040c060908122d071203 71
    0x201d04c04d000d0000401060400c101e07084100c00080502101003000c0541c003004102100040c02c25202100e81e40340345061150303156110356200d0f07460703505020004580c00d00c424216409040c07962600c1015030b2902c0070489040e0054160000b103c03048040d030140c01003040218070f10a86c07a10b0800212034030800f80091512965600c003008060420782e10f0f03000341e40e011099aa1010741503c09075610a0989021100100c1c6904000c04283d82c2d150306d0702c041011540400d12161060b1200e004649414000c0581044031100040c0240e011108400c66400e061340d1500f41c1e00c0c031900b0007044e15601e81400005851007114400e0400c803c1808104030303032400d844500034621201032520458200010380c00383c940b0050040131400e0b402c218920600f550410490011024000c0080003507040034a400c4510048600c10800001c07000040482d4842c40821869a01400b41201e0b0303103040941f4203c00c040d0308641215a040b10054852078000c0c0c0880d0b002424401c0c441c0315240340c0303101c0c500c4020b42161 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 92228831 1250 92227581 92227613
    0x605040609050306060a05010806190305010b0103140f0103200409110102060c1206102a0204050c130306110403170406031109101d1306080c03030f03011403100606020a 74
    0x1138020801c4c00703210740303031062080181c44080c03801402e5075455401040c041240b81d45615604003142100006004043d405070031100e409980500041190900601c0b2007001502c40701000000c8100410010b1860721603140740702034449100e20081c030203500103002c503918140b05544070245034000420039030307040c411540d0059031105030754184407040c28141d400307040080600d070007032000c03845500b102405840444103441e40405591403c0c02c50302d0305c1d42e100138100396040380039909002c0071403e40c440780d000b81d0f42e45c0c40f000d01d85000081c0c59902c812020313280822817082201c40c100004000309150700c0d0a441143c0000c10705598907858158010100e950500043d115501c0a004030788150341d91021103400310007949414034002c44c2c0d240c661542c0d0025070184941c0035001c40070144064045130803080c225407000e003e40b12900781c0b43c0141900c9104801006031020f03c02c000520400104086445403018007034221640d603140158100100e5500760031035000340e4000307a812420041d40d4291705180c6 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 92230081 1250 92228831 92228833
    0x305070302121f0f020f030114100806030a060b040b060a0906020613021008060406170a1104050c070b15030106030602090321041503020f030403030902030d03020a0806010e03010f050106050406090503 88
    0x1964061a03010100c1c2111a07070305203c1d03a15a40b01c00c0c0001c0682e015a000d9a02205026942c1e5a481e40d402000300c0b11640b980d80903254000c400c0c1c011034007030b00085110710005809007011001c0c0307a4950b00180a800550b640c0031345c0c1e410360000306403142c030003410b40364146407207411908ac10f010010345454001094200c110409181d4000180c0344d04449441e0118030b0b040c182c281e5200e02001034080c04241e00a0308001c040d0118500c0c102c040041c5030440309005111b5041550920805e00043e90021600190400d804000e014000350f41401c400d54841000c002c0030108946120019007500c1ca59031040da4141c0d0042401501071a0a11910b030740c002411b01c07640c0c0b40103020400300343c00380190701c07810304085500c0c00304000c40e5000f90109c4102d50709102e00159a0700d041c0c50050000c203111a0b044c0d0203845141d0380703211414001d100311440c041c40b0b03494880141d610140110741c0f207040d5441d00c0703805548401a10190764100c0c040ca41c060311040d2144ca450f42e0400f00d0003820001941c1c070041c4a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 92231331 1250 92230081 92230093
    0x20304030801121101050a1715120604021807020f0f03030109061401090905060105070501060b0a0206011a1801030f0c0206090c01090b0d0209190b07170408031c0b0307030507030212 80
    0x61a03402c40c207400c8100031b083c0b007601c1c0c07010804241e8840c2c040341c60341503800c0010400c02c100002c0c2d4007505800c0920445144d0005189000700c03554883d412a0000d4000c40c401c3c224484415050301d019900002520444280c00400d5448a0401049403034410482c0d00120050011031082c1c0600707405002c2002d030a5481211503c0000c208030614400c49003400d0f42c5002050550340b18070100d41c0c3d40341d0404028042c60760783d030041c03040681c0140c0108006000b01c0c000401c1c0070141c40d910000d91021a170b0600d00380030f81900c1c982c25440c220000709052642e100c0996880e0701d51401a0310105183e0b4001d400b2030300e4031105060400c95480c00c400d041000c4054144522004001582c40020302070f10700585600f1940c0c00f085624588003030b1054186d00c40c3d900081c1880c04074000b403151a02c503202d40070303507510042701194060185009420030340d0028007418121041030f010000c2860341104001c00c928030081d012a041042c90341003a00c0da900508002c1c41982051310a006050340c50b480282a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 92232581 1250 92231331 92231333
    0x6030b010806040b03070b0703050c160f170102210703051501090e040503093007030f110103060f180b10020d0c080c01050f01080f010905030a050d15080102030403080112 75
    0x1240c1d4024a203511496955811070300a40b020044880580440d8070400e81d40d10711814060b2071604524025680d41c4603244400f40c100d02d01100070300481c0c0c65500c0300c500190500d0411501200d4500300c031004c07036609012288610401c6007440502c45507100c3ca00c00036003080d45000f003d5030801441a1041c0e111807003076260b0b91764080d841d58200c07074801c0b0203504641c441d407a01070b0851241000c49544046541c000d100c0010f040380f01d4600310002448461254643c0d0065107440341d981d84806480000c4c15145640490384d041403880c0070050502d000102192500d61150034442c2d59081070040325604045102c40c83d09504c01c11498250440e408000064054002582d8000a64803c400c000f811039035241084400400d855010350104000d0240d4501740840e070021500034403d004141c490040c5500380d0030010300c01c034207405030050051807a101c122403068502c2c2d40801d19001d541596440003207c0b44010241d19805050200d0015a5a08007070600908008041e04048403c03040004014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 92233831 1250 92232581 92232587
    0x190504051201090c09020705010f23181c020118120f03020403050d0c0503130e10150f1407060e21040e040308060d0209090a05010c09180207110d0308090706030b01 72
    0x204440100c03c0c00f5a40708201c8ca011405801c250409040141c2410305003400842c414211a600d0010384c40303071800680e605108986071700101c09079425607070800c6800c624150000c807803006500c4058000440c000c0f14802d10841c040101e10410fa89680101052451043d4400100008480917103019030806003581c48040e03c0d02081c0d0f04100610542c0c80706a0100304042c001c0e14051403040176007489031641e40142c1d04038840d080390a00c2e498101d140300481d00d424042c01c415014045031381c0e11040400c441070190348040061500c1700f01c2e81c40620180340098424095107a01950000c003a101d40e1504a1003481d850328294034070907180000740018040500e41d1065141c0c003d42500d41b403140c07a180d95002c039a4442c900080079400c00d0798a0100b1015260000341d0f1045a44100003c001204180c41d045450182d6030254102c0001a03907c60460300820b81c024254150045840c0084110710b0070000d5280402303032000310040f0301e01400300b00e40c00390140b2000c0b00a1529040901071002c00000003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 92235081 1250 92233831 92233853
    0x161d120a2604090b04140f15100503160210091407060e060a03020f070f06140609010501090302011412070f17010e0103030804140d0302090f0f010c150219050405120109 74
    0x40c010540d40d64400050356445c0e411040301001c0c05200d480403400c1c000f85000c141c1608030f0b9600003040b150b406c03462040c00c0000c28418001c01c43e0f42d4941c1161141524101803a40301c8003414210b00c1a441060440240d0384290032020784038228200c1e127032941a46607410000c860740a00b05000b822901c0c040651038000450f4010300c036610b00182c0d107000580b10100c0702e000f0074401030138400c01c148101042040540c40004529600f4080c010030740e03961801c0010b01882400b886001a086070010001035000304408240c0140c10915a401c10f003a00641d54031a450848503040051400e201d2032200a4101c0d2155543d0a4000c9442081f5810252500082d41c41803100800308051500042e084c00003161201444054800590f0001e014a000003030207500003601e503e104481d00843d014482ca804d4100d540e1825040e100c0c0c0c00ca054840e10348031503a4036482e4000180c0d503005c0081250f6a80f01d04002c80d04100c80317844040d1110b0903d0180034000340d064200c000c151b0b261078001004502e5107424 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 92236331 1250 92235081 92235089
    0xe010f030318080712020f040b0a12021201140601140301140d0510090c050415080a030507020d06060308030403090803120402040e0f01061202030d0503161d120a2604 73
    0x2241c18468441c100400b50344415601c07000041c003494202042d05c1c0452540b1400d01402290070005504429080000301c4445d00d002036481080000f04000070040038684154142c001003425088070181e00c0d2440c02c2d21011407501156903007186c01c0150543c0c0103090300c80303902e200012035402e640c10055664440700000e807150b4450441c502011013001310403c2a804002c9480030103000451b2030340341c00081c1c02104d020f1184a242403602055030044444000710449505800802e61403083c0c0d2002d4645034072600050780c1094403c0c10010114159004813001140305505150f56031500d0b040042404040f600806581d03003017041a0030901c00544c0c499904076404540000750030009000c000d2412040d008100046d500b01680003502c5134140c050182002c0c0242e0030780d03203001d1806000302c03441c2c0300c100c035901080d02c3c64110211000b440f904904156460942d603000c040000000025400000601c1c0c101956002a03100410001440316118079210030340e0040c1281030b40443c01c64000d0040d03000e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 92237581 1250 92236331 92236337
    0x80a05071d0f061c050105060a12110607030302041208090405062d0a0f084605010204030206030a020a09080c010905190e1305010b0f090c03060a0308030a020c070e010f0303 76
    0x408a14195148404600800d030b84144d00a425021840d245001e171808031002445280c11000024a10121807143d441c443d502003c500120400d5008024050704109015420550300348000f00e041143c508218000d40d008078041500c4d00d00d914208810303190002c103002e008520b10b0290801050b0400e11800b140d4041e03412000b01a207004021480341a07144d8420050b04e544240000380c040008138103440345413044007001c1036030380c494031401d4a14007000c000706219408820341c000c1d001d8039441c0c100c0e24035480781001502c0c7c1541c940004190390400d0ba90041240d5000440e03030402504004000e0040c0001c03400307040d41d203005800107007078035111744907260140139030b40e120903980c0c0d8202800078050001c810000d032003410416100c00a05e47c03180c00072907a66180588040e8645807155400e1288030700145035001c5070b5260400ca1900341c1019010b00d8000354600320110015a00742c0107107200d1440800010788568800c000b00c0d19044c0305501916250302d03e14018040b41c00802c07a0341046d00c0d0541 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 92238831 1250 92237581 92237611
    0x100c1d09060310062c07140c0102160c0e0a0b030d18031709011701050604060f02010b1003050a0b0901050306040206220323030c070315090804080a05071d 68
    0x700400d0820340302c0780019003600c0c1307800004078603650007280d00345014444028040602400b507408009001058030b1003804141d0006850014041c94002032400c0402540058100454440e07280002441108115191000d00380140005104000c07080d030301c00c0f403007c03042c4086160200441c4d224071441d010030040000f0b0200c0c6c0014070408a0200000b0344d4480680109e568529406807501c0e04000c0d5001e0015101241e1040000003a8134401e058600041283e49460314001c02602c07407040c80c4101e2170940d500e89800b08000d5581c440304140030700584d00d002c030701c600e0003000441c111000029044e228400040c01840f01e5280001c02d0703903001da130542c1c9465582c4140c0380300c444440710398060441c83d4014148080100301a011508201d01200d00c009144113907414803080e224040c07241e40c190386610500b410004030306003100700d55410b414500c5c0002d448900e6180e0000b554001c1d0001030f10382e4841c1d60400200030b8204080801400414a207400c11494512114a480700180400b0701c100300d94 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 92240081 1250 92238831 92238841
    0x3070f0f05130317090d140c03030a170601031b0306030203190803040b0c091c03021614210f011401050904020a090c031d0a0308090304120312060503010e100c1d09 72
    0x140100d600a41c00244401d0310b0007141d18150854a44654140000b80a26101039409007000000e4880030799054079070700941c52454cc5030000581c80100818105a05c405150001c544c4441e41c40450500b20354010504a0440c0141840c0035a0206100c01030356500000401142c00c0c00217513a080741d88810940d5642d141c00381c91300703018000c00100c2503005907565000789050498500b20703490140300341c0980f034480641d16100d10000354241711391401c0b90039550301c0c54218900325850240200701183c7c0304429405005019142c11804001940d1030303950b480d08171010b010384070074903401842c0403600005586803e50100714807409a12440d08601e0700d03124a10200c40c0a40c07c50780c000c900b0030014582d0b500e0042402540d81403403200c00e5011034201e0740814000440401101d040d5800200e11603c8503269a40489103080c000381c048480c0c0b075403410041030568081c05051100f0180b01d000702505462105080704130340c030300c444030418401162581104015140000e2108000c11202c408041d994 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 92241331 1250 92240081 92240123
    0x70e01082a0301060608040c120f11210d0212031005010c0311030304150c0c0b18011409010c120209031c2d02010605040e06040f050f0303070f0f051303 67
    0x164040d040e82c103500b44071000c00e43c079500ca00070901c214010710303200a40641d1402181e041d41009900900600403c04680021841c04071144031200405413a181a2440c00da00c040881c41ea030210905694111101042c00c00d40e04005049940d11030381102403460910083d06a0312249074410b044c10b0201200134042031600644d100016840b5000590395071f03142030300d020112603132a1030703622011500d0500741000945c810b149080c142544001c0c2502662100c20403910074000d0300ba0051600d649030100d02c41d02042c122840341c0a900c140340003140c603010303454001d0b19864110003685803452040c0a400c0b1030356030005045802501500d6280e21200481d0822200c44c00c442900b079514808241100e03c03802c1d0809400c480a540780d03400cc0145c9600c1c0c0c000c01065409058200c42940e000d0001304005c547d140c0030382d141885c451411aa04501840001419508101e0390340700869452502c100c9890f4101c00f01d4203e031301aa01d4810700c2c0407100c4825800c0d8100030302000c3c0c04030100d12000d8112501c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 92242581 1250 92241331 92241403
    0x6010903050f0105060a12030c0605060604030c0306020c0f1605041a1e0a0602030a080f0901140702010204080d0e0d030e0402041d0907090902060a0c06090206030a0e070e0108 77
    0x5004400c1e10031007090b00c2c202d0360181000b518858081c03203e0b02e2001842080b141185d0041da940341e0342d00409041c494a4400241c9809030010f5030140b010040040080d403000b517110020f41c410714000d81c80c3c26076201d01c141000c0d452980c0c401c1e180c018802c58000b8841d102c080c0000d5030011900005d002c20300c0d0555035500045414456000f1504c414100380ea55000e101e08141c2c0d002c203c0704402c1907516240304988a018074410380000c500e40b1008194070906450402d640f0500b0100000b8030b040304100d42e050b1703800060b00c0100142c0d60001c1d05100943d0140080c148159090a1041c4020328600125800c0f4030048000340820100d65410b58850395190115070040c0980c541d50041c000c0c092900d600789450a60f04c002003132040010003d42500740d8061200700a400408060912201c81c070151041c1c03948103000c540069945082e0001a0b5921010718082d482d036000002d0404106800c0c6840d0032001d0300100910314210004100070000041c0550190019400764118008514070b6854154 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 92243831 1250 92242581 92242583
    0x901060c0f200a0602010e030a050f090402030c040905010902030615070201020c101106161b0303060504060f0501030f05160c0812041a0c04030c060503060d0606060503090c0a0e04030806010903 85
    0x4041c032011200041400581c02d81c1c408002c0780c28200f5203a0303c201c180e080300d2800075103080356007003482080019801100644013007103491114a01c0c0ca07407180009012640b00b101c0701c003018100410248040d4515110741c0303000d408000c904500e14148480028211401c1ea024a040140000344d10021a4030070f0180c0081c0001c060320304514440360010151031540c0d040812845842403400040101c148481724201000b8151216841c190340714041c5c0c0c20f101c016110a1707051540b54040062503445500c280c200510b038031842c40100a041ca000181603d05a03486140c42c581008c091100c07005100340d43e85038128407402c1072003041c0b03107918100c400c50040c3d03800c0d051101040300c20081032000c04c20000c5030303031207081e10607031255500e8094907101e90150303010262841700503810078001d840c041e200035604004000d014114500655032400706854094009400050012061206014082000207900442124208e040500300244102040401400a0108694007001c0350781d40e4020b0704500091 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 92245081 1250 92243831 92243843
    0xd0209040b070f0201050402090408030430031803140d06030f050d090806070f0302030a0902030a0c0e0703060308070206090607050303040b0f06010306031511092713020901060c0f 79
    0x80c80d241c00c001c01800c600711400800318800014100c08544184540c0d481583c0c004c0824200c2e498030740350402d280e00010000c031010703000da0039a1101e8080703445826141c2802050710b054941680310006054a4981c032002100b03022501c02000003d03007001140300b00c03c401088468580c030a00c1c0d40c40d000f038855a40041e003a841d2695444083c01004142d8000c80c012944034041c00a513505002903440e0000c0362075000080080342040c100710700c660000c40c0c000010101c04540c80c8000e80019040500b003403801c9610303502031201041401447c01a0f194804418203042140500d907840b070388828410684024421000000e0842c0c0c556290415074408507000422291285050718040c506c4c031000b9a072401642c40d4020000f10b01e50701c03034081c100a0700d134003550400950380140105400342044405503203150005101c558415105c2100103071410301c501c0b8201040400f94075142241c00d9000d007149001c4a001001c85000d40c9032008220304403074841c035210070008494142515640e5032040e0040c40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 92246331 1250 92245081 92245099
    0x121812060f1b0512130206030a050402010309022e02060c070311070314060a0e1b010806150a030f050114060316030603120c020108070809060c1317011b1b110d02 71
    0x105552240140c108564039556045240e21034005c45401c0d1803030500d00a6004204000107a01003c543d0044c5401900c11704000c030b440b603420344c001004e8000714250090788405080540b0b07c040403032a40c100d500d402c00c0c00644843c4c01d080d040584180f14020002d010f01148191204501504104001c0199044100d41d113100303a00c2c510745515450b0644020045c14180400d480708203801166801681d20001e128155020f501030055610a000501055010220440d03080c101c0000c3d80c004c007901001f690380000c101d0f0b10a44c1c03d20441d1010303000081d40c620341c80c1a003c078a848803412260040500109409007911119045001e00b102da0002010403c5e0280400300040d000a294071699100b40c032444290b650302001225032000444182030a80e10003004180c862038244028111002c000221301c2507207440c0d484200700741307140c24544c07811170303648245003043d4489110400d400004240350030344011840800c0188000300c4a040642011401c41b83c581b101e980e1094013407a1107502502d01c82d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 92247581 1250 92246331 92246381
    0x100f0207090903091a040602120a0804020f120d0509150c030d15090c02030703030501090509060115030902090108070501020c01020f030306011b12030c0e042018030703121812060f 79
    0x1885d60014840c1202501c80c00c1310740c090580615040d94007040302c036542c0d02c5c807595560702003085034420b00400c550840c402c0144001e110105100e213161000301d0391a11313507480740900c080c0284c440e100050070004410a01c0041c510001c080b084503041003e40f039010a80c0006071a4070300b00c020040c0d000f00182803800079071301c450a40100c05809401c0c0651001c0041c0c0e070381e0701c0403441550310881e0f51109070342000d070041c04094481c0102c10f204000d01c0c600011038103190307030120348019802e801403140c641c8210300800c075541e410020344010b600e003840609121500107055a82d00c1c0400342c41c090500c1038884400e0010031003512040c11194101100e1504502c00440280003041c810903140c0c00100c0005400d00c05003807600507a9041c41c4030850f42610b81031046103071b00e20f42d0412818130100a220010041c1969003c025a0f0003443c05134074640b508900c013800150141041c03e28a0f1511030540e00100700103910300d1403110302c0c036070082c0010403400008640030004280e00e00c429038040b165200383d44 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 92248831 1250 92247581 92247629
    0xa14030a0501030c060c1505040507120b1602010b01020a0308060d120e030c040b180408040305070b0408010e0a03140310090e0705010e06040324060305030d02030402100f020709090309 81
    0x30b040324000c02208107090307198401128294000b4030040c050043c02c4800419080b850b40c8841e500c1401201620a00e50700c403188001c00e80309086003607420511940c14080d018194040b6800d90010340e0000b0400f00e140d07100003030f440d810b8043d00a407d014a02d40000c486894254840103100d6010260910030f490242001e0300e81904910020f01a02c0390400c0210b0034101071045442c0018014446440c50540042101c1581002031040740c40744414030001001440411008001d07020601d4550349660030104844e00319040048121000d50003c1150004281c03c500820581030208480a03170b2651030f292a1148103005601442225140000b01c0448290104024040d40c800340d8481041013114010424540034600010300402e400c252a1180700b80034051036407200c6c04100002c100c8599a4580340d0440d0004115412443c1c1c0010422046182007800562030f210703d403c0110582900640c029030340d001901505552a60b51002c81e001d05000d40a800004e1048881403210ba0a19560603 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 92250081 1250 92248831 92248841
    0x1b030c030403030510052101090210050a08100e01060807020a021801080f061501050702010c060903120e030c0a02060d0b04060f031b0b181302070b25050706020a14030a 74
    0x5900191400001c05c980d1000322015100b1200003c000f06e4524414411080319071010320085c00a42d03507901401d00043e15004100041420300b0f0311815190515200c0182c500c10300140b0720070518064a00034010b44055100d054156000c0c1d1038091445ea84615042e854041046030181d404502e412036554011055402107040e076270352206854544400201090303032103100341c030004001c40000101350a0b55104401a010040c0145031081d20010380c7d44612040b62040c84040e000165420088018501540150705264072030000540c40c100351420300d2600d4402c040c0c030080c46000c0002c0c03030031000104d6400c0540a494001d0042000c2961f4588600e1386404621045a800380b042c0c4500c29006000c9100d0783c100c0b01442c00751864000303a040e40501c41316211030b42d151300100c404502449101d031031015100240c4112402071b89400c1ca04005141044540b0515005c0001000340340b45240d0703c082a5000181d0000300961241490300040c1e49001c20040e2234000101e01104004000885400c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 92251331 1250 92250081 92250083
    0xf100f0209121e0d0503150d150203010602070b070201020d0f11120903060703020c1f090b15040b0402040501140f070210170601020a0804050607050f010f0b090901051e1b030c0304 79
    0x94242ca0001603e0b555440d5500c011000c4c2c08900240005000b1a00990041c0c0210000030076410740904644c0e01c50030705040c91000400c103603501000600c103054042211601400f40058402e08140050740001c0d41c40d6803a520b2142000220400840600d0081420104c036840e580152048903a116210345460b400246010788207205d20808610300c24003034400c90b184200f02c83e000d0207040c440d140786884298402140b154296994011107404911165406401144500680e9610646542c100000e96000c000c43c60301c10743c41044200441ea800602c3c0300c2c1180040440329481d20705a0360410f045d03006007540a50081b202d5140d80601e103034028650f5414140c403411407000c0c2e442c1e45004a9490400450003400c0c28130800041c0914901000505070182c85101180c3d500b443c0201410f00399108040c0c81c0c0e4240780c071211060351034545103141c0350744007507000b0081084bc58024000181c80551501c1f0034240044500072503242d0313410001d0680782c15160046a40d9030704188840e92007503401114 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 92252581 1250 92251331 92251363
    0xe01020c04060f2603030f19060b0904090201050d02070503040f080624040f0912120b090103021504090203010b04050f03032113020306091005090f100f020912 70
    0x1003a500d2480d00d40310b40b07000c1d03596040c040b2103442d0074501c8607010501c0c038400c0304071403549401524004190030001540314100081d0768040d503080060708609003108040c2c050701c00030f0520009003c1c20b4000d40907130b440b1364003c9401007011609800141c0e0b0600c2040307032801303641c0d000055001c1840710010080049501e03410081d001c882c3d44091040d202d0b901030300d210800b8250f0045003c0e240c810fa604100c8503480003000010011858030718074040f81d854503001c66600d24014880141c1a800c6242d43d000345010081c184200d010850000b20b41010500000313100d03208201c044104100a00103690103050444421960f9584410176880380b40c0151042134130035640c5100c000078509022064440c1c031481c0c80e010401d5481d03002400030007188003c0c55000445c011001610141e42c04000050055005001a01c42c81c3c1c5141c50b14820303240d00400100d8607511503c0c1c03500b8201c1c00003e00488403400103d00045101075012400041c1c170400076180c2e8000840c0c40301c00505100810300030aa0605d481e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 92253831 1250 92252581 92252593
    0x2071104052212020d1d191d0403021b0904021c080c0709060909031b0615060c02210d0f1803060e0105060307050f04180f0c140d02060d0213090c0e0102 67
    0x20000c80c1d8000440441c0350407046ca444d25810b640c2828480403012031005821000010b40703a002902642c91418071140d070400c003403002d1209164051007145290704c0c04102940b69a200800441d0511030050300c0280120860060606040f034414048034440e640a950540d9401c4031510080d5164030030f00591b2001403a00a0000300741002c4c0c07103403000e0941e168079a03140750009103003080106002004165000364452008030b14407601c8103e0000a0800307515840c41d0500c450061000e0180e90321042003038810315030070004c0b5482e40000e01089280c500d01e810300e501001510304651510010210307001d264941c0b0b50100402142d60098150119080c00801c195902c00c0200f566406c643d01c95183c002c5a0b4880042d05030030b0a400080041080c0c0401002907100c540c0c50b001001c207a52170507210b0343c5800d0b2044c4050341004194140403c3c00f1985400050304d6500090f42c18400c0404800805130700040e40106da0300310a80b0a401000001010080901030303403c0a8841c100b02da1800b80140626 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 92255081 1250 92253831 92253853
    0x30507060503010311010302090a0302030f0106090501080102090108130501090204180302160501050406030f1103071106090303060f04050603010b031006060306090509030a0320071a060102010207110405221202 92
    0x1442070b00e04072500401e03224528080780d0015402584000301c0d407500300030400c50110150710200400d118501c02480009207081c0303000841c40840350185c00014159004104103040d983e80b040d99950810614060310328503036031600d0030600600d00000000e4002e402c009840100182603110011014000d1f0207840c90059215001600451640112404907006000500071280300754020300045c40003e0b400104544407618900d10b41d0000c85658001800c0c6190100c0b040c4014840c00f50007000c45801942141460f10009150703288d0a444d090182d6540c2c40060f000e81d8094000480104014060b1000d10881100340d00244c0a0340c041c0b4400300e82041c500184044241c45010f10420510014505101c64100c0c11806403017849140f40c650400d0b4600c40c0190100b80d0020300c4564803680800c2d09440340088020a4550014030181c1564414002c010104042c01c4000300e8099003242d00182e59514045421a0384010880d50000c4000e14003070081004044440c206030600c0c55000c0322170082d40 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 92256331 1250 92255081 92255087
    0xb060d050703030818070b09010e01140d0207020402040902071506120510200307030b0916200f030d02070212031c020901090b0a0c060b09100501050d02070b0103030903050706 77
    0x60004100c0c1e48036000410120b889402c115402141003031304031002d4a0440741e0140781001c1d40c2c10060250100180c841d02968110710384407401c400038207060710009169010714050b4010180041019500001c043c4115600d03541100c2c00b07821072078011034450342c5508001300e5403203006007134402292a2034400b10384420b000260301940d543c80401400310f0074204d00c2650180c0031080084100440c0d081d5141d0311503c140c80036600c1030901c0c0c2d0300000c0e02c208440070444e0115001c0c10803482e11031042626100d8545c84003c010b02400c013500360708005c60100140c41c0ca07200e07030601c50305085d02000ca100d04811400342c0047c61814021176500e04981802c81c6001c1d164860b2081c201d1546118001050f10010b41d40c014040d03600d01414400c00555940b5400015a4401c04204002030141079491040000318400d03010005420303a54024a1f1500040000b9900041c3c01214184030020030110413003019501180c44180e4131030305984495950f4034000d4091592400200c4103405011000300745984 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 92257581 1250 92256331 92256349
    0xc15030f1a06160c1d070f050406260a0905010605030606010e1017040303090510091e0507030c0807150203030f01050906030307050105090d0f0201020c0c09130f0b040b06 75
    0x500441c40030504034084040101541c00046404040400040300a011604d50f1a80c48014190303501056180a00040ca9504c140c00c001c1a0006004c09003c4003140181c0c408292001e60b0424204000c4a1b041140081060450150f40c2160704c05c0d031000308296141160040c060f80c0344201c0092001b1134584040544621007110030b00c1c0050b1100c1400e8170079142010b2103052030482da08084a058100d800c0015180404480540100e41c540301020100802044090342c100d00900b010099001d00c1e5441d07600e03001d0011960b000511420a001042c050184a41d030019a84401c5d8040d05a82e52220715032244030f03c2c45180703054540e011000a442d800803040741c0c803035908001028602c1c0c0c01c0004000001c2400342501d41c06110a11006000407024800c007400b4490100045c00c20003000d100080c446101c40d03000104690050051f420325000015589015900480c0e00206580e141100300120303040e1824050203400b80c1c49211401c0c410441300107401a40144091081c1d55111424464009 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 92258831 1250 92257581 92257601
    0x3020f0d090812150109050f01080a020c010e0304140a0803030103030c080d11030718050a06050d0e01020c0a030305150a03051504031803051c170a05130c15030f 71
    0x840801400c940c1088550201da2070921604116003011901003201c200c02c8022070340030b212602945030079000356802541b140001c00048038040150034031000002c00303141000d0020000340d9000304078030444d042d084d00100da40104040c200ca413078581e40c02c246401400107031042c501450300341c200440c80d10740c080210b9040e29010388484200d003101e5520514607030700c102c1c46040b2155484800d600f810b1032905c0194050603040e905d100c03100c008000c00000c00c0b09980d000301e00c2240d000000300401e81c0c1100030703a00d08040419000a10f0900790b004540a0312400d00400f82c40d0194928410800d500f6a10003030003004900250a20340c420305062001c0c020503404003070026801414a44200d41428203c0ba6000f40b01c1d242c161030802144035000380c1070406030011039440d00610507080711a11800782e40340c040f40191605401e00c15403c2520354131010302404260503c4d40f83c134001901406072070a840d846a0380014110185903a8441c503940d603410341c0c100e800000741480b021101e15166800b0f400e0201c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 92260081 1250 92258831 92258857
    0x510060c080c01061802090405101508060414180705100507140a0209190f050c1603170708091c020c062101060c02100f02190204201305010302 63
    0x24912511441c006070404500306846640b10180400c8405c0161040140408883d00150b128038100c0c0c00c1200350b58000701000940b20140504200c00201d25000104580280c205110540c030b8400100d40035000720b007800c8a1418450b000c0c80308405420445060040715042510300c0a5106c200300121003003c4183c802c001501401540c000c41d0300014014204000e1004235080c001503640412180f2100f1190038000d10b5404104402440d4240900b6a54260b980000c20207442d01000350407950090411307150b600c80400c6861000c041c0500c2034485c5046924105c40c0e40d500d04000003c000810850300140c81c1e0280f40d20042c6040c441800d00064011950003414607541504148601360300003d4a85a008541e600c410f901010302000302c1d4042e00d0340c2c0e40c40c103c004174240180310804001c9008801006446804100c0c81c40d8080b92440e24000c0c2a1850b40307000d030703081c000500503050940100c41400307148140507095a016500802c070001c10f102c454203000795a0700040d8104d00640c004007030f803 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 92261331 1250 92260081 92260097
    0x20408030c0709050c040b0a020f0607110c030105060a15090306090c0302100509030a032111070611040305060105010309060209030f07031b0b0306090a0e1606030f0c0c020906120d050706051006 85
    0x107d241000003030044260b15104480101ca400b01d030f4a45001415140c501c0840e0f4a001d20300030142d000d2000c000303144400d6000740058205000461043c1e0640e02c21408501ca0208107030074a14401d4203018004d5400410030f105420311810010042d0240b41310480c0304d49202002d90702000d01420170344420b0003001707026140c0b88400b502e09840c4001070b00907205207021241601c00d224511442042614081c00e01d41c1621190b5504c0c11300200c400e484001a41640c05100802c00118000f1300700741902c0007032074041a81541890008087d0003503042966240c043c2200c0c8684114000a80400300c0c0c0c000c012145803030b51125100c010b98000c1d802002c008003c200005486818465441380d00010345e018005190481406030600303010705000c0054440c0a588003c122035035260050200c0400c894038200b01380041c3c128040e0112583c0303d0001e01840c0d0007000581d250382d40c08940480e0410300e100382c41a91600c203600402551011804590452509000c00d40d41c01e0201d4100703040c4d41e0b683d103c40f04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 92262581 1250 92261331 92261339
    0x3010c0e0d02040c090503030d021b0106030210050c210721171503010204030b0109050c120121140d11010b0a031b03080a0801090e010b09070e03030409020408030c0709050c04 77
    0x1001d84135900484061014040300003400341c808100070544e00f4850100140c44590740040f292821860030300681c2660304114003400940c1d1201c08451595007681031040d91510582007041c1800903c0984d00080b41d0200c1e06a446103040c80000e0400d41d100d00403c040680c1e03811942c5042981120382480001d01541900038261641c41c400342d04203a100c1c40c01c40b0350f400d40740006400daa110340c2041340d500e00d07a900104000310b111b00509401c45001180d007818042d0240308620103510510415640002d84504010380d005207001107103034503030001c1c0315520020444c4801581c030070007580d0150002d07014000e810b4818206108030500c94900070103040c499459500c0380c11680b456030422078190240742d0000000213520740000d0950155980729500190700d032059000441d40c3c00d41c3d0820190341800c030458103585d40c2003410f070740c41441801d0804541d11040d000c6881c5014503042902d070f1510006010607128030000261205200c0a0100c5240f00d4503840ba04050b6541034408100750030050100340 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 92263831 1250 92262581 92262589
    0x103150b070f170702030d0c030c0305030c070f0b1b131a0d0f0b01080105010804030e010818030f04030b130507090b01110a1101030606020d02030412020a0e0403030b03010c0e0d02 79
    0x704403540502c0300402c07809001d440c0c3c10010710311000c3d512204600000d142c0110b0509000c011015030b81400e0605034204282c40151414070700f00e1005081000000014416442600543d822160400803d1048503031610300460310a10646035134000c0740072095061007800b0000111803410241c0070030f4649031440c001e103001300c00180f48046e0030b2100c014402104114503034485e1295261400c0e0012640c0e50199001418050041c0c10942c108a8410704010109810200035010304d01c0a1810740115529407401c036400182d240480c5009000000c0c15808054001c0040d00a9074000d8002c104207888505150503294200c64000b13140741c01100081252841131ba0000421540606151904500b595241401d0480b40c0e10229010002e030340403002d10356810700c00c4001030300d80c500040646000310ba001a5582c016440b0340c04400682c42030080440d22404200c0d001000b00403060102ca0415103006409001d0360140b16019600e414510340c8807030711400d440d90303010001074000f02151070560280 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 92265081 1250 92263831 92263837
    0xa02090606040513060501030f020906031501110f07090605031501030f02010e060d0515090907030f0203123402100503090f250806010501081f0b04030812060103150b 73
    0x216510090910000030113841c0c802650110315100080040c0083c18040054101c1d0488880303e40701c00d2060001525548580c8120f0350420725284140141e410907400496100001140480c0d1138000c1090000410300009480c50580b0085075040c0b008603103c80915543e072142d1306a1851010344030300104080f4090095540c111801850001c00b001c40c081e0100d00581e2142035024081030344c680c100001000010a8015140d0301214615030310304100d284551744085502002e00101110606201156001c21100400150070701440352100705218128408003000c05440d00d0101e20100740a0001c68015184801c00c3d0780100104c0300e0540d9940308a81c0c07900010038a107801c1c407031107070b2588980c4003c101e01d5088400b04078000c101e1100d040c080e501c0d1181c899008007041d030b10400041c0a1a0303004211940c2c400001401410b070300307580c0c440000e0382d09401d520602002c40c00003804000d0081501c010703c44550f0342103d00300daa40ba00e4004600301c821035130351550715907950038051100d62229001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 92266187 1106 92265081 92265091
    0x61203031409061b07050d020a0c060306080303010b0c0a0512040f050f03030a03020702060d0e030316021b040c030b210d08010303020307020907170711070f080a0209 73
    0xd1a5074510b4080c1010400055003001607203021002401d80d1105c94104044602d0150300c60000ba44400203a94161000300403800c0c08a40749001c1d025050840300054011803440e86400d149a1880d0440004000e0078050191040085102080364a80c0c540d24050b8050340c80745031404509a80905a00460080e07c01140381082030303401000395541c1443c40c0c100035a55203c28800180c8030312580c804100c00c107141c0101e034031076810000041c5208060426000b9440402c504041c0e9030b404908404c83c6090000c0d208941160070709810403404204281004100c091181c00010304c98080036441080d0328600301e0191039441d10802c25910000c49078180107905504580700207480384500340000c0c2c010541e1b000070941040c40782441e040c0523520344c0c51400c100d08200000829a14141c1c043c810184661400403170079665040750720307048840380b03401024144015400e0190540740108 = true := by decide +kernel

theorem cover : BRFrame.Cov 92086331 92266187 := by
  have h0 := BRFrame.cov_init 92086331
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92086331 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 92086331 ≤ n) (h2 : n < 92266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
