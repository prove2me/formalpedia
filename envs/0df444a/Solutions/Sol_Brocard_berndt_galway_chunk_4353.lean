-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4353
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:20:49.342075+00:00
-- url     : https://prove2.me/submissions/a39fabe3-b4aa-485e-8204-218bc3c216c8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 782733812 ≤ n < 782913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 782735062 1250 782733812 782733821
    0xa080f0c071a0d020f070804080d2c0f0d120903021518100e0409030f030507020706021f1b260606030708090c0a030503040f0b0c0705060307230409050a 67
    0x30070002c032541c5000300d2020020003d600024020507001c606010319004074040341d0140004014800140c411105041c00050003503071a030340c1910802501030070948990307105000340c1e080c02e0420383d00c080c940d90400c000515500c0d90102e000701501100100b00142542c007064040c2260700c01e4034840e079111381358550100c041c0691414a004440c0b08402444a4900011005203448050810044050b0358a001c40c00750743c103003407080d40030510b0101d00e0f5003a0360b03051042d603506c00c0c1180f015080d494100381009444842c007000100000594a0840109171441d902801100d0311024080d0002000d0b10005003031510100ba41d0000c0d200c9680d8200c012054001c4040e01c254001810b82d4a9a03440c0c200079148903501800322429441070300480c006a464104a00c0041c5000750025a195480c214030b8600351701d400e42101c48040e10a001e440940900062400191342041f54041d4491307503040c4044441c200051411044240800e5801c02910440070082082d01c1c0740e40d00600460f640d4a402c00d090700c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 782736312 1250 782735062 782735099
    0x3010b03060a050c0c07030f020f060304020a062327010504081015030204090f0b07090b091003140a0903030507031e09060e030a020105060a0f0806070f020a080f0c07 73
    0x50300a980007a8404207190b1085520a269101082c106002400881d1071b001c0301e070704229079441001c07a80c90103510701085000b0003160102c892a19516083e4046400e0319100e00c510803d1111030341e010501e254030403020302c112030095810580c944a4440c20032000030b50900c60000c18102c011581c12195200700100ca040d10216001800da61092a4100000b0230190706410420b1081e6200800140c2e9a80110b10050340690880043e25106083c2a41d0f00180584828180102d4540c20421b0302518000d0b50700032a01250b007110909a040401d40103402d040c0c0000c411005100100082038990790700c9210454041c0d80c04201903902c9040030f0b012958410700c21412041c03081444464030540344c210303400c02c074804c003804103c40104010441c03840d0481081100541d440303c0401c50300b418003049250080c411600e41001561404005d180c035130a01900728001c100030b400810190600030860070b103840340e220181d6642c482c010300c1c407004103420004502619010b01c03400001d5041b0114503402c0304 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 782737562 1250 782736312 782736319
    0x510020c0c0a0e0f180c1e090a0c020c0d0203030717041517010b21180f0a08030c0d150f080120041203030f060b030906010902070506070804051009060e0c03010b 71
    0x942c031000c419051076851881c0340c0702da030301c1006da001c941e9460306a003150b243d80c0c0c000341c900350b80000c242c108400c40400030300302501c00c2e1030302020311000c60740010490840340c01035440b01904402400441d046100f445400341c0003580943d00c0c07001c0c08000f4001030045400c068016030384403c690a04403041c5503900d001d001a4100800144004010040201111000440941008082c07540079035400041100c0008100d1494100c682d903000381440048050020500074120084a69680c00d1960201400c0000410030200c0ca102500c03041d43e016064296001e1a0140c41666a4611750050205801049215401c10407016001028803044a4032100c041c000c584c10f10f400c04000c040032914028055040549410503100007145501c03400021781489030819a1320310b00390102074a00041a07002814940c0704001c2c01300810780120387c0c50f80140302d0349072008590f10f0f2410704030b103851040c103451401c240c40c00d1103010410405900c022050764012054440300e20101080500b25041c100b1110341 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 782738812 1250 782737562 782737591
    0x8032e03051f0e100617030906070b091207060c0f021c030f02280e01050703050d0506060c030a030e07171c0c1e060b0a0302060702010c0510020c0c0a0e 67
    0x164414181e0120104101c40300002881c030380359506030340340c84000041031502d150741703c000744507030401620099003070485000194507101c540e07804281d46100e502000b4040e00700517408189081014410b02c0482e05000d4801034440f506c44c01c0c040700800201c081000800c0882030603004160012400b20034164400211000c04c05210782c0940203094801c0503002015400c00c045c800030082d104c04040111701e91142c0e108041e40d54070014108190750003885041c003d0512051001075882000c603444808804004143e6450300c1010034194000c40e1100c2d09140404507128080c140c0c994440504648080116002d003a50f440c481071104001802004040d0040000c1c0c2e011140300d000c0e0425419000d10300398400b2100c030740700c1940e20400703040001c10803190b951000c002d105d000c0c00b4101b61840308030344601e580d51a40c4c0c0082e56a00c030394407009051084a40040c01400014096a8629000c0210035591090a452555210300e076940d506031142d405014045081020344c0c103003d225000000d107540 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 782740062 1250 782738812 782738833
    0x3021f0615122c0d0302030c180a0f060c062a08040f0816030f09050d020108040c0314030a0306080105101e3203010b1c06020708032e0305 61
    0x1102c06665041d039841d80e030740f11000641c25100c4208032500e11002010103004196054200c0c0b070400035040c0504040500500a002240b451803045030400454607800c4443c4030324000106050980690141269204000001a0568010503000f403d0b501c00c0000300300805d03098a0241c0e080720724101c80f8014a1588095009050042e9002ca40183c0076404070000d6038034654800c0c0b40d0b680440030f58103481501313242000805821005011101d008c50030079002c85818200401c9403a403211401030704004003400401c007070040c0603e00310087d540007501084098626031841d90f40b54421580c0c080000c2c64030cc00003c13241010300c912801003c11410949405244c9000b80c03a40d4040d451204d55800d41141d000101d20b0941d81c1c55843d8180200c0003001e4400a092794000801d0203505054026414450203504079603442042c8120400f0441c517403e0b424840d0f00b00800280628600207040500000900c160302d1005e020b03840c0125070400386c01d0546400810241045c03406440010859441880c2c0071 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 782741312 1250 782740062 782740067
    0x50f03070b0a030c1e1b03050c0a060209030c1801031b1203030f0c0c050a230f0a0c230607020103270b0a150b07060b030a03021f0615 59
    0x10000000141203400ca0380c0c8403000000c455101c0c5851002280d5151143e4082680108000e60400ca4071104110140403480c006005403d040240300141d804d0100a4402c05004409071407100040ca03003240d048c0103403840c041b0001d43c84038201034030900c5690300e4242c04e464101c508005001c40451820116440c0d9500e90380a50b9802004441003c0f03101c42c045a02000792070a0000d0ba400b130303a000700e400e1039240c00762400c0301c4000305080204000000c109010640c00182644141d52211030f0f501519600c000c051903900e0001107103d40360240000d44010104001807200c070f0705021f020b00c0158140c0c4c46101107a07a8a42c0180448100710303402000750a8580a805401090300605000c11103a0ba455a81c0c59403030382e25103c0a2807034038018414024440c4c4052203903440071500c00c0405c071883c0086883c212088240c410784c0c0c81c08400042c240100702d070780e40011004c1c040c00f0301102d82011051030003079202d0310300c41c0c0210003074030540c22222000c4940b80924001c40d01c05402e66020344114003400c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 782742562 1250 782741312 782741329
    0x40302040f0e100b130908090907111905060f0105100c02040b06030a09030f1b0f2108070e06090f01030b0a0b03010602031b07060212160c0b04051804030905 69
    0x16001610703500d090100d1101c0080c08403696890f1038180002c2c0300c4c101501040101000c500904034018035114612000801200031a07a42501c12a80010155956181180e9165040302c501e44103000742c0d000c4964400c00031002000a911071015150160343d0182c50503140e050900c40c1e26440031550503102ca85500030700000d600180081d0000c1011202c2d10b01003803840e402552644026544e41c29840300341603202c200f0480071070b00c5260841c0300045541810b900d111540c10041c0840b409818400104a03400c200035402181707032491401030401c1004003903c0954220381c0000441e80c0d018040301396203411030445031203400080c156561039403030100450003460007154250700725020030b41c0800c20781c003103402a50092030301c1e0b801960b03502c096240761220786510416181c0c059100c8803050040d81d4001c41c500b000c0042d46001c5a49500300301c0441710b1016a101800782511040c1003001c07548429143c01442034070015140b044010502c030020b421000001c850240000d1a006024070252628800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 782743812 1250 782742562 782742581
    0x6010206070c0809061305090906071e120e06041b0b0706050c0705100c14030411060a0215070f0e0102240a0902040204150915051e0d050907082104030204 68
    0x103c41e4104811000490380c03550140c440521013101840040005140ca80003559110003040003030052410034400260020380e060201d0b030004144408200105480b804124502c50042c0e242448004507001700c040e1100019201035481100c091914400d9881c0e4070001c000300c40300000e5281c40c020070341e01c643d402050094030403c800c0c1e0040050f080400c03801c10141d26038030340d030326000614081481c4002c5d05c048910700302808044810f0003004049880c64084150003001070b1140740e46c40d40040b00483c10003001c039124180030b054007410b00c03110079403044081070309402030b4036a010204c08900c01aa036a011040190038a42c009403e0f4500010100070035a070401c880c40000f003032104a60f070003e0187d0704150040c50380031003081142100f4590200c0c0400060100c408403070f94207821410001c0841c4515080c1408450469007031210350101e042c1102c04501d40c209042115081400c403e5440384c0c1c403031041040c90301c11907000b0595040c1040c00030020040400c42c5230318040c0307142d0a1001030440404c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 782745062 1250 782743812 782743823
    0x90f021c0603121b0b15060a02250303210209060c0303010609211b090e060f0705190503060a21150606270f080a03020f01050105060414040b060c0a020a0e06010206070c 74
    0x14040d81c01e0315140080d1482c2c0803550082c26035114407490001121414481740c0040070750001c02013000c44c2c1c00003800b81e4040c22070405c0c5007801c060010dd80029210301007809801ca8070001e0001000400440a9810b94500e0f41d0344c4130000c0d0340e40b01200764a06000324407060303488610610100041e000361490b0180060204100d01490f900c1e1501c81c1201c4000b0300150158014404020002c03c040a20740c0e40041c56040c440d0610f015210b09025038428072490200b4842c00102184090340c0300310180004011108070201020a04191210000d070250780445224880f50802070045030580102806d8825590b2020030026480780b070540300a0383c070a44a01e6080454a000c142104143c81580160516000910038070a041c074000345004001e180600711a49040010300456880c2411217080f50740625500054002d01c0e07000400800050b4080e50388080005042206c0c0c40300800c0800c0002d00898860700300a5607944d180740d04c800300303c88242c01030b0081c0d40000d03262406919103004040c0220b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 782746312 1250 782745062 782745091
    0xa0923040221010807080303160908031803011415040b010c060912080f0115030506010216030b070e2403040312060e0a0e0115090f021c0603121b0b 65
    0x1101180882e4805402c44009921581a00700920444140340c0c1c0108501c4000300314481c41c00e0030303181e264003028003103100302192201c03041000c1d44103240c3c031b0010703010317147c00d03070b45d8400c028250a01c0030b85120340340a019500301500100c400107040d46262180c1c0c0145c0c00c0160203811582048024911843c1c15414062802c880705e0104126200d0600e041c1e22648541c0045201e10101501c10740c3d00038202d042c40003a0100501c00214480380481840303d1a007404a4251203401c0142e04100a05140241241103100000b06102c0d103aa600c50080d5802d4032040e03800c203d84020f000501003500300198003004240000d550b1045003500460b40f003406494442281070182c040002500d107150300400120041c0304c00e0000d0440d582c821590f00011520003040a5825805072440a207828840c42030703000d50312550070f103014206804413020503400d080d9030081c00d500601c2c0c4400400540c081518a4188403550390800c0f40a40707080e655202400c41c0b046040c032010340d0782d4240e0490040046020300400b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 782747562 1250 782746312 782746379
    0x11e0e0c01031e020d021e0304080d0c140a0915110c0d03110709020d0c170402090402190e09010b030a240212010e16020c151b071d06060a09 62
    0x40d04c05052050a170400140c0d8400c0380009203841408505c09440162508200b40000034003108220b420400e0138480120790006c2c0308006547e5007205070a050031303158000a501d445194003610203015901844110310350000c5070001240e0b00d5541030700d00001da52202c42419003d203004040910514845d1401c0070225122202c1d82d0b04019075940090308582c1c0100c3d140340c070040035000d034a8034103041e85000000c1503046443c0b503040c000d01520290103038454102160554460841c241041c1100040b1100e9503a80c801300306001c180c088403040c0855117040c03580031440c075010a01050003604070308200341030683c060300d083c1c43c1b00703c0c0700801ca000c40c1e080140d84140050031079401d000740088484000c1502d000340303001000076001e510361002c64002d80103540850751a005e080e50aa40c505010729243d50302880c40091f1034800d0300c3d400425100d6810002112801d01c44007407075a200003010034626451352014050780b401191003160106411a9050220303100c4254900240940303d601004a84403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 782748812 1250 782747562 782747621
    0x110903071e1203080a18122001050702070602100c17370f060b0a050c1513031805060d0e030d050705041406070f0803100f0602011e0e0c0103 62
    0xc000101c01041e505010440b405d4001c6c441c4459021920081c02c1c440c0025546600010300f041c0c215030b01384006000c4008250450a20703030000050030b04003c00050409840180d580d202a105840061154230360310b60008081e80501d140e8100c4980342c1e040e10482da1a100a01001e008000c0700c2c1143c9810b806000d001c031240001c00c042100c040c1143c0540740070580040a03540c55065040e0044c0c100402004403900780d4003141c1d1071071641c2c908a078444118200e11360501c908604012901c40c6501e0500c08c02d9082852a114203d109480d240681d564603000f03070340c041000c1e21806a11135024081204800c0c100c2e045034107000d1146d42600e26200080c0c20724801c0ba50299003c0002910204042c402c01c242c00703281c0d130240a0111000d5041105030790343c81c20480c000560082012101002181810038101462000342071a41e8145032003680701c0340300030300074110104065100500154214045070387d070b11500015880301409440d8001001c001900030340542e085e54851030201d481c51058841 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 782750062 1250 782748812 782748839
    0x80c0f0307020915130203040605010510020f07031115030a050108060f13020f040608010516020c010c08040b070206070804031b06030513030f0905030d09090c02010b09130804030602120604110903071e 88
    0x910030f0740c002030154133080620001080c0c2e01a01c0701954040050b01000d00b500184c0c0c3d00803240e0140c55004c007020704102040070158031800310b030340b01400442401640703001d54000e64141c0ea40309044a80980d1054100c0440040503038800d41009090407240c030150800c4e088414040801800203d01c05a0710803510703003182d20803580d00b008840300391018007280d40d0520a03442c00d103000346840300c88050961100300d5117208a02c82d2120309440080d802003107444550a8a2050b03800400103900d460366801d01c41040c4000c25404003000c0c09210001ca0050b009200d2180681503000e141c0c207101c00e882e5415030f04080499001802c4c000200000101641c00308201b8100101a07518500d88900d0b00040d8003d90351031b0f0400c2c00542e41012a4000e48e03407a03d0740c140c1e40c40040d4400115489010b814100024415600003030000c5000041480014030079000050040b030099070704000340d00b082600e0801da40124800c1c264140c001e010104516a280b0714a90a04500c0c10000b09003070381d94034144407250 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 782751312 1250 782750062 782750071
    0x30212060d153603090602060c0909090a0506010626010e04060b01030b120d020f03041505070303060e0c0903060a050622060b070609050d020601060906031a0409080c0f0307020915130203 82
    0x40d5441c03d4010205a845072000005090a00040c1000c6c02c00c102030400900031210000c0c0503480b441c1c00210000001c1003044075035034209054414a503103940d0010302c5421141f14011508042d90b1904503a401d100d02090704950440e107400c0d92985a903541d01010309104142c15040686a99111a06035a0700e0149002280241d00410105031451000b81c20704181107500507042d0414042003000464070000315421400b20f140580d510803143c81c0680003049950024040d04007504200702d10000d0450061506400403421152075964101c80241940c0f4103d868503004500210700860b1340c0d10030b40201201101d94140450a65226141d003103464010010130354480b0b44a44c1c1c1601131290500010104c040540301034000e543c140341000d40100e0144c464079040550329a0203c100140d640100e0400329030041c02409801d207141800d041d150040220180300b8000d1280a0501940c00004c8900260f806400c1e41d080396075908404d104031004266030b40e080070307a0f503820300995042c3c1e2002750321a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 782752562 1250 782751312 782751401
    0x30902060c39030a020607150e1605060c1f090f0b06180f0103020d0c15020703290f041406070c050111070206121510030212060d15 58
    0x300ca40c005008a0070345240c020a200c001c0412900480e00c2c3c4012804818440d01510a15954409807070301c2c4083c10b50580c034051000e0b2600034004902c510100341c01602c1318000140b17049081d110001c014552092942c80401503010007001c5a15038a9080402010905264000381c404407644031441c0069070120115001880d001c01c0010320f140925202039030b01e039002200300462404151785051000d0600000c2d200e1240c184819041211092481700549042e185d03c0048001100011b03503500d03050f0004960115030640c0100300c020380440003d60300710302c14225103216110a240300d88075800c0548107403080e4402c040c00903810700040007240e001d4410783e56101e080c66002d08005085819000070280d0310007040208a0250381c42005071400000c503d8a4038800d900e402008003088034890483d25003040003804c179081140c2d050360150400b80e2111a40c58401d1360b40800300241c0782c804c820010400362200c0081c8403540602d41c464024960038041e00700c012400d02c1c1d948002d080810030301602 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 782753812 1250 782752562 782752603
    0x1a0910051b121035031e13090e0304090207020a0305030f03010806060102010612110406080d230c030f0307090315020403150b060415021234020a030201030902060c 72
    0x2540d0b514180700700203202c0a400e00501901c659041d00d4000341014520180300090a004d2507010310510489184c04041c0c19041419119481111059089103180740a00e20041000144942140c010007014000007800b8501d06410300304100001c1d00840026a002052110040006102080107000b2440081c80307903612580b518000610740f8000030422411a4141202048880c03120081b440000c1c4d40500130504807001d04020030001d002580c0540d41900c10699110320254115211b038580808501074001d064680040e158140c0c03090300d00004240e8404c2001c2052803105202a5070051000d03e880715800340c0e29250b183c0324000e03c40808210b1540010104100440c1c1c0310103a4040f00485000e121414420002135014011442400602228000a424241c1c1300b80240040c50183c0456161540c0380001c205143d81117403807080400100044003500721141010710105c0d0306900034811912070f81551300440c090048030500b284c00c4801804003240301c64080c8a8284402c204000801 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 782755062 1250 782753812 782753821
    0x90e060402030f0f0d121401060305100e0c0703080c0f070305040f06030513020f220b01080708040f03050901300515030604083001031a0910051b12 65
    0x141004110022080107510240c600b40c4c24441c04079001586104509140191485089984024101106d0000c801100c03140006c00c99035010340c401030040602da8000c9499031b032207207a2180c01403000d84405505500c14450380c40003d20407009258080c1d6411540c90419048003400180d03034029140403030101d04041001d014200512035081d0080c0310928041c00f40d4109546003141d020842c81c4040d01620850001c03203141e45a0820107113003440d901802c07481411030101c0340b00050800070502c0340003a9100010640c45842500407c6c090341c3c1203100b80000080556042c3d8456120361042d80c1070080000c040544600002075815414044a40d407101040302c4a00d071400b2594003c0906614a07149000320b0b03100d0720000b52483d0b02c290710840240d96050141c0c074055014100f65122440c0c401c500107500301c0c0200b84103440e030480788a40f840c1e40300d84204603901160240c04442c00100340d88400f940000003c45074101c10740190360320396016810403d40640b09000d0b481800480010003400d010320 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 782756312 1250 782755062 782755069
    0x7020a0f081002090120210c06060603010317030718030609140d0c170f1b070506030637060207170a0503070f0c051f030f09050c19090e060402 63
    0x10b80d01d00d001004110f1900000d20b0002e0600c0c4840461205540c90985c40c440c000b036800c006005221800c0c6130a10502008090031742c07881d6018510501c06402040301107101ca0810006903410303640d001c0c541c0f07048524a52001680da80004000804201c000380c054031220480c415910095030203030310080f4a80710b00b41007051004540c9085500254442c0002c00b040c594000c0d0304003051035012000390f40d50300310500081501c6c014680e20407003031080002d100490703800c5000740c0f01d4241e420409481656a0f43d40421115000454100d504030424119180009121408064900c02141034000070000310314034140d03005207e40c1105c40907030b122040030701240d400c9a5400d11101e500ca00148074042095070f030b0544900803510020448000e045840d0204080e1452920180c2009464451804110462000c06498420902c3c022a1811351004a034000b40d00641e20141e402900030003104425000744001448118584824292040c0e0080b85114041c0a2420000443c00051a85007010f0041 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 782757562 1250 782756312 782756323
    0x501150e030606130c1101020a0f081012080901050d09060c090e01080325120c0c0902091e010509040516110f10020d11031f290f07020a0f08 62
    0x15a10070b510110070450a903456943d00d01900342100b801086071514040143c0300c1e402103501700c00d10fa5002095180245500010491091031683d40f891142e450346190792440c0b11043c0a81ca2101250441c1080441da143e4010f056900061400600d058090340800c4200c4081910884581d9110b440d070001c000c1e4401c51160251150040310341155240c5a14a40e40f80b049140480e10303000680004190403c0c2f80308103c0c8003a80103036850b000440618001002001d4450044600d03051048003c00c65080701c8c400c1d02d9110b0005007020300c4903510700a50407001c5201c02607940c1045010040e604258982d4040c1500505d00f562980500600185000d0980811a585618140c1c010f05c40841d104c0360000b08102c858492580c0143c0e100000b0801d00b0140c50303d11010b18071050000706002602d40003510708081808200d00204660303480e0403040c800e80c540c085a02130b44500309051058440090f10040c004c40309510021480d0001590100b0f00880050744040141c0b102c4907410000e0640a012 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 782758812 1250 782757562 782757587
    0x1207080405060603280204060e0901020d060f060509190b04080604051c0504170c04050106020303150f01050901051b0f101401050109031b030b0c0a02100e0604021909050115 76
    0x50000c4179141d101030220740218164004401c03e0602c809401d40d261039001c2d401428884e6017003000c0345844c2c003100e4041e5000b500326200e1607180203000030f001d005490940c4103840f80e903980d091420281604000300c101448030802c684e04c144c0080001c0b9032020340020401001024050f0070a45400c2c00c00905024841c4842e80c0256503a98441c40b08540c0f250494041d50500b40c0c186151103c030044181ca03100c00c820259401c580b805002103512500000594412080900c0f120400340b80c0c4028811003468103030140c3d001c150144002d6a0a60113003016207044030301e68101154001c1d040f41c50901d0088071046a072802d80214511302c81c0041103001d400c115800c513002509065140900007812404144030203040c180502c08200c0f911180c124400c00215000030440700c0744c1c10404590780a51303228480040151007001da001401410034002e2802c0402400c002c0e1040d0343e00c40c0c0030b00c5619110741c528092480d80c030000c00700300d44101d4800c45000e00b42840341d055200d425414050110400c80e00c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 782760062 1250 782758812 782758819
    0xf0b04050f04150b090f0603060717012303030d0905061305030d0e16231917150f0a14250306050301180203011407050901050f12070804050606 63
    0x1801c000d603000040d0002900240e01c42d101c1e030996018a00610000c2c410f0b6621164428040b00500560808844540340603d40450a45800e40c03180c0d030381a00e01481d0644500f810130403c400411042440f1000d5110800c2c2c0006090104201c41000a0030b5038850402c186007556034088200502008000796540150b260801c6100410261142036480c0111890501000d843d101040c2681000384080404080d656009a140640f11045065961640c145e41000307404050300c1d00c242c81c6444104100c600c0700da032000214046c10711b20300e05130b041451101845144144040700603501c1600e5070b000d1085074907204045541c10700c03031400015540c0c060380220000301e4070014040c0003001403a500340034040b07000a41d100c03040340702d800794050b203140c1c2d105580c03551800c1080350a00ca0222180117101c0d100307c00070080e14142100c000c1b8080410340780c41000800602c142c5815500440041c01040c0000c403140e401c007079140400e42c080410840b141d60000c3c14000500c41000003c100294106d00200c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 782761312 1250 782760062 782760071
    0xf06050d110402090103021606270309120507080d020706030501050a061b061107060501031205070507140a090c0f030c0e0d0201120f0908180f10050d15090f0b04 71
    0x2a140c1c0c003501048800c216126590000b03641940303078001d50440310060b415007104848210281001c2d80144440d5402042245200b410790600d60300e5903912411195254481004840c2844031581904001d000112803901c211040443c4010082103890f800a903168014100c850030504000e0030381e08103030702c480c0c00b94010030420301c8203503041040700d0707080c151180c0341c03840c0c41c0c4c01800d0900c05400c2040c01502c60716400503061040c071000c1d8111a06a03401000400040d4041000855044c41022005072040e00a03d9082c441306080c001641d10180780100800f40140c1c943c1d03c035404403840c10044401180c52032504400ca96054040d995504045003055001a8806004205900c0408800070b04000480f4400101c0f400070303912029410703100c1c040c10820380d01e242c684544079034414074011880000444402144d441c04003a42142204083c05010003443c1c940b80642d0b03030307800500008403042c1d00d66007140c2124180710b03030120007000c400c0d0003c661075013286803200071202100b10a03406a800d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 782762562 1250 782761312 782761339
    0x1a03090705060412110f041a1e060405010c1505010909030206100608010b090409050105040b010302190b04140f120303060406060e0915030a05060106051209010203041106090d02030708010f0605 85
    0x1180c4c8110140343c2000311441d014040c800080e0341c482c1e0039400550701510304452840350000c1090003015041094410303240c1c02e4000c841c142d0344c02c0c43d400d000c01da01400400c0305020030751040f081c4001c150301c510700f20844c400900d22881c0964509030801e212140c3d442d4a22030616030704026060f04031030798048622500e400c2880007004140c05019031050004d002070640081d032503990000307074559008402000103042030b140c805002d0100303102c140c0c401d484030b1082141650b5041c0c2414100d402c441440d6292520b005c00440725205803680c082d9002e00d0b41c0c01d0919440c1c1b502c21408840d2100d050113156640344c41c80810044581d02c0c0c220300100622100740c0102515148805a004501040c0c10145500400d0000e4581500808003c0c80d40c09010000510141c00401628800c0e2000c21007010a6445140f40e500700d00049030b000e08283c200404044d041e081080041c14610b0025042500344001c54007c2441c2801c2c40c0e200c1440740e03554226180d00d12505200d610090041240d222001103007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 782763812 1250 782762562 782762579
    0x409151b0909090c050915092521050604090b040f0201031a150c28061a03030a030b270619182313020a1a071b1a030907050604 56
    0x20354003500d4006c0c002c03180030411800d40b441c007180e400040100044003c1c9021802e10146808800e8400c003101400303082d84041e10700030b0f2401c4801f0109005048500254255100003a18015010b6900240e5030386800012030002d6080f2442240105e48030800850248001412070307500740d6407081c440c031054802071000d55804a0b051084c1751008040e90310390120032034140c20826004a402041d07420003101c8682e076050640d4200e01c907801b400c000c0080304cd011142d201c544000d901410740c103400030041008914041c2d40b00d805686405007160500841c9109450351040800c0c5640b03d0409086007000440c0c50851056004101814220f0042e10b2500076460002c04941d028050030940b0303054030b1003038140e00c0081603128200c001100907072810014022002a807a6100c140d004100380e24010880383c1c400040c8018a00303020022030324005c099203920649441c16441d08441030f061040020701c85001081c4803c0065000300b205580c0d0034003460700d074a06000c55004500600c41400100b10105 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 782765062 1250 782763812 782763833
    0x180203070f1b0b09120a02060f060925090b0a0e040f020a08061c050a0b07020609060601020c120705032514010206161e0f0207060219020409151b090909 67
    0x41d80f000850070b854a41c10001070415006001101c0520070125894100d980c1c00a81c042c080c0d4202d03c03440c2440d031949000d0000300942103410b4545a00f090344580d107c0991482c040285241314070305010916141c1d8003c00040d8401a48a80004c0541541402502c1d0600c503143d405420031604624046c000700010b0003403200140b14074030070b00e030320644003c042c1a400b1204002a034080c00f514840d6816240c410341c4100c050301c001005125a000045030107500040681c01010140c00504000c0860000c01c200c14410128800e0507000d0300c2000203007503d003007044441d04c0c90103845403c152088030000d100442c1050780142210000b044000e48140d030040390709600058001408104142c40c0b680c142d0300c0d007107004d155260301c01d2180c860300300c92030b444404002d2815555095808151f503ca0341240d4503440140c0c0c211f46012034008550051409034000c243c0039201c3c9034856810408500d68000310b4181c101c0307209200300b0030340d90b02207040d61040340040a022524400c00c00c001d060b48540c000c030b1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 782766312 1250 782765062 782765117
    0xb1801060513030f0503040323063601050a0b15040b0706091203050405010501050f060f0307140f040e0622050a020d0905070f05090610030f0204180203070f 69
    0x2000641d42d40700100521007040916085800405884030310314000b61360341d22a05c07003903880242c499143d102d2003011000c61807262824800825403500e400213015100742c03100076102c994030035000c0100718410f1f50345803241c1c07118103043c000103443c035000075040150b800e80140c4a1090042c44040d1904000c80c1007a0340555011003050743e240d002c1c6141c103c0040c0b00c0c1c01d202601d03060500080100265268200318456171140000380700a90f61030041c8104102b6040702c0300d502c0300c0f041c8a84d0040d8840764000e10307170018081ca40940c106103ca07016400c6079201200305140c2810008041c405102640c0c0d03880e400460640309000400e1480d408500340704040452400c041d5240e0022464891464064aa00100c0250200048a41c0b458100d90341c1c42c0300c0c4520401003450303044c00100752400820451207450003414804813202e00090440003400e2a4103011000d95013030001180b4070101c03104a521a402c0036100607581c0c185914050404440e400a1a082200820040300d507503030b2480e58803214 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 782767562 1250 782766312 782766317
    0x10605030702060f1e13060b09010f09090606120f14070e070302090a052205060f060322080304120e04090302031605070b07050114010e06030a120e0a0602010e010b180106 75
    0x2141c403940c66100202e00c59040c581042d01111701130004c810942c0d0101011a4460b40b001c02480040c60240a16403009100d01304031540d40d010200314941d1a40c0168801c903104090000d0750710f8070360b0030168211000f2030041c1c98400c1c00c04200f008010144200580d00c0e071018004101081c0790450040209000404072010980c0100f001c01c00d0307860b0300042c00d001d0f01e00100001005100c1da004810309a070b00009143c0c03114180800708110342040c1180410510300075001c0361641e903404461900144034401245000b640040381180480d2426000d94043e038490100489070703020400d80203007543c05030503c06115503e4002d200001030b400204580d0b4824100300c50786508009030615909100c0c86501162000500080d8482004419400050a03c0c0c2a00d00111141d8840205c0e00421741c007129601e4142e4016210440401c44c090403001c0b5001d0280f90000c000d4200e0300204030301485551091000d42e4552010441c2164203014850600303400f95a81ea6a4010301c0503837843c6e040041c400d00d420b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 782768812 1250 782767562 782767591
    0x60a15060507150e0c01031404020a290c030306100806221404050c150f0405040f020423040507140706020c031e0403020918030702151b1501060503070206 68
    0x41112544001c45184046a41044802c03e1100425185e150318a4024000b915011843c07455660200398140100c2d0060010b0400908100541c07280c020031800996a461150b516818880141401000d51103c003070040c0d51241450700030b000d803501c00c2040a1042c045a02d00b044000d450340b800c0c00c0a500722030804460644580388181d0700811030340040d4444c00da904000c0005108000039001003500c001c0c5c07111624244452000256030003400003800c080d5130108070820962405030405081440c112400524140d0389030514407280e0303007030303800c81c41c007403040c204515107900e058400e40354880400c0c1080c4003030082c0394a603940c1e10b02c540840100300c1170303002c0386130800722800b00140c0f03140c0b05100b00c03a60603072440450f0382d10703081c0c00030b00c03040348107a40100c001080e40c82d10300d821100350400c0070011400e02181d58200001a0307031444800c002203400b40031000e00c981501416922020400c00038100b2010305184214011f681600200705100302041800340d86a40024100d0340010361901c0c850 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 782770062 1250 782768812 782768827
    0x3020a1101120e03070510020f0d02090a122004061d18070605030a05070219081e04090c1b0210140d0c0e03100b1309140303090708060a150605 63
    0x854402000c9000d990711498001d0a4034a81400801480e0317a80c0590100d810000b03201810390141d10403030103c45403030b203000e0042601d811426006030840c0c581c0206500a03d980f501450501140c03003003801c0c0c40005803201041642d88445c82c9819060701d003034600b80510750030f03c800d406400e9640c0da0072a0004d00319000152102c0e0003000e5000c01d60010320f09455481e6a503e000600035001503851141c03003450500822900e0303000081300317080003901d200010420701d01600d1742c1049410030700e00030089000415812080d8030004005201500e54404006042d0f034a07040e0080c250401e019031142eaa619105010b40540d07116115034401a60a01d01541d1480e80310b0807841540c00303000c01034030704a8205114050030a8100c03a0046401105400b268611003000725100c00b81c94080b040707950040042e504401111180b03400080241d40141110303114a018041081e2840d40119458081600082424405d25506002040e041a4160420f008a09010040050040c054890030040c0940003c1c400c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 782771312 1250 782770062 782770067
    0x30f0706020408060a1b020c0d061d10020a031503021804050a140109022b080c01090503070c0302030c220b0d0605040b04020906121f1b022103010303020a1101 70
    0xc0340503141c002c0940e03805060082d45c80e006050000030074135040384070f45030320241d1030f10025620a01076801402c81c0301d04120b64861f0300043c8008034071469047c99588001c0700300360007000809610707005a003005070354001c4410020101d40c98202d414500e2009070700d041001d81e03581076100a41d1b021002b812042d540701e82c82c1640c50007000740b038002c003000441c0c90f503520344001c1076000700c1080d07000380d41c0b0360a1503086650854540d481d0584400e1548050701d00b11011401843c0074080b000c80c450000a0b0b0b1041c0c40c0c031110700e142c01210040310040e0712108180300310b04042c82000d001d02c6068810030302e582d40800c00c0003000d50f00200d1035080a5511a84000190f60b0b40d1151074296800c0081040241481c1c204040415411181640900304080100303940707040407070740001660f000c3d002619007012405200603648608030103c55143d82c491103141d410304c3d1a08036440040140c0c6c4c0060018444940a807864248180034061407068240010404241c0200750a898241e2001444507004c001c1d5006 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 782772562 1250 782771312 782771317
    0x90f0326060622090608332a0c10060503070b03041e060e07050f0117130506160e06070c050d0c03080a12050901061202090702010e01022712030f070602 67
    0x403a001407401003000a80c030341a60340100241c511080c2565405a60080c000d921f40d91076190742c500c03d000c1c19080c0041c10b41100b600035000780380341c0da2580c0e030a12000d10545403511102c969041000000030900401c203400c20104005115000d402d001075413615000a40381c004c648500c8076100750010000b410010100c2c40441c0e0300910003c0c40600c804181449401080e0601440451344900d6101084528000c0380140c0c2d0200140c0d1291403d40d25092801d025100103400401c00c851189403801c00130f181400310744d208582e00310307648501550350390005060030484000300d070140508100000205148240c5c3c40c0558800380c601095817002442c115154480c4c41e8409032a0650214484009035808505594a03c200304002d114a88034801c181d4203c90a61003150503203c0c1400c05040141444280700ea400981400000754508091542d203007aa4401e911070a5241c207000b8003180300052030031000c0d1404e0000e849041e0003500ca180d000ba503034404d804d1603a2030000f002c5801010807040780c04 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 782773812 1250 782772562 782772607
    0x3070605070302010f020d060608060108060a05040c110f03070201080c030c0708090d2f04052205030706140f09010e0d03020f07023d0c02040c050c01090f03260606 72
    0x6c555442811021600801580c02084005803468002c00c0c1d8541c8220401400b40358000d044021403031a040c100300003404020070351b509111219119100300c1c0c1d1f003130105020410a40c006540d0b1031041344001084588001c2c41d10754000c1042c0300707008080c0621400d80744001da100700d445a40310450000164030143d600740041c003162010540103980c04038180329001e21483c22a1503480c403d501410401030722703000c881210703003500c0200c0c200d82d4040d025903030110000e0198080d285818402e40314001515102c60800345814800424000400ea600702030661001e00c0310001c00c00003605c1c041541d2100c20141d50390741010307000305a20000c04814000c84101c9507008008444000d550718682d0700c400c5410901100454652812006803060131500310900308541e41c91280c020602d038204002851480103020402009122080545209204003070b0003034014a0ba0044d901041c2c90000e150740c45800c0307a000301004000100740f00407004042c0541020b02100c000b502d03040d0103490035103407040050 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 782775062 1250 782773812 782773841
    0xc030f130c27061527170303010e06011d12030d0f0605130b0d08180a180b010e0109260303072313050405151302090117060307060507030201 62
    0x44a1031440000b182d0190342c0d021000c1000d00c00355989207071040250070316191a0300482c0c510740441d1451603100001055968030302c074800c078400d905c03089403c0b68009000c2c03940f100c0798000001840035000213076031140d0094013480c100905c41c0b0340360603800d00d00f540f071034440c1c0c0130741000d08201101035070078016100c420380340500401a201141e00990094903c41c0f14030390044005064000003064a0300a80e564204090b05200740c43d11503540b00c10584e40301203607502c941c06035803055801982d60007056038010701103200a02c103a038080511000848110702e6441e41071000d4001104e41603608030034554210b4041c000c2184500c502c49010101d0050081c07100d110a02000040084030fa80144a40385d14181522074011109210703d028030143c0700d581b2840c01aa42156010460303803910f0f4000d40c2c0e0080709207007071005c2c180c0c0c500c2c0494150007031140d030300c040e071074000c61059031650384a15070304041069020009103505040000c281c80f4111806036404000002840105146c001d400840900d00c040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 782776312 1250 782775062 782775089
    0x30703200f060c04030212070e16110106030b090c180a1a04050103030305010608100b042601060923011206050c1204050703030306140307060f020c0312070b0c030f130c 74
    0x5800703415904c90701089104840c0c4421525030f2031800a00d100075514500624581503d4900e1655409072118480c9000c21208007008a01340703c0038011070740158441c0603001c0040c1805810a81080744071400d00e4010000d20b841600c1c10008501040d810646200340041c003d01c030010410284114455415042400c4c10300002c20954035900c0981210019980c200705c0b80c60b8025548924503131031090313000820781808144010700018410103000c95201c00741842445a0349913441c00e59529502c03003c1ca80b5070340c40b0550748048a040b520500061100300305032996045c403440707140b114065040540001c0e40c0d400003900b43d100420888545a040030324664107881c1c01d04d88103558030018041200002c0c20f00c44000f40441103800c8000185c1c0e07006002d44505410114212620045030000004600c12880c0000c007a40303042c8220040c0001034030810b42e40e1060b504250000c05009007107c1000d8030200104242c100009000a0700b0503101090311004611134184400784c91a2a0090408003009 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 782777562 1250 782776312 782776321
    0x30c020909160e090f06150405060609030a1416030f06020304111918140411010504170106050a0b0304050304061d0405010603020a0e0f0f132004090e030703200f06 72
    0x40844040c4504c80c884100d40390030002a2407161150003d5a0b034800841c4c40401c500314070f1805401171644118090043c0d41060741100029142001c8041c0583d05041820904400010184008015451854410f4460a2841d51184000b00402d5400f814065011001c2002c20020083c281c1c0310b10b60041080d4042802d05960944500d164450b15075036401d01302096503006c00300c0c060100c0079032108030004166a120384440058440c9210300c1e5040220030440401c081983c58031001c4071010710400003070300070304010a0200d1400c50b038104100b501c2c014001c001c005800007007190140d07251881d02c068401e8900c19403000f595558a0729036402402c010001c208a036255010b411402d50344c0d51070b101040b05c81c03028443c02c03c50f546c42041c0c000803940740c01006030078003081445128a02c1d500000d00518903c1c00c810114500c0c0001034100203002170100400c00d51030040600c490405e0303014515000d95554090030f02e49040c0004600f0f6500e9048014080200b40041c02c5c030b1001000599603d0310b40b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 782778812 1250 782777562 782777579
    0x130510020d0201270201080901091e021c0503091c020406180b090903091909050f0702060705040b09040e03070219080708030c100203131e0c09020304030c02090916 72
    0x101101d91100642c41c0c4910a62526103c0c1d4241408042460741901e00c412140c00440d0244402000047d8942d25141010005000c00d9801c20031091006264103025100c0e104204c149464403d0342d000402050f0b0f030580115802008a4000940807241600506059100401c00c80301c1d030600070354043d15099000a2280c000f80884595281c814010020307200308808000384e004080d240c51400c2e5009000010321401d0607561094020702c0100c3d201c03000c554a180f2101554402c840007000e0100e414144200140c040054542104203420b01500f02800c00740303038908500600041e180705030740b07881d64000944028411182c401e5005003a200840c2000503480109140c1c5202c8c010baa80306034903000079404400300035581030302c03209800341c5091400f522201000e5000a8817030701d649495007504400142000102031200c0100703012005007000b06042048440c1c42e182e018603031039401003041000003503012300c2c3c0f824000d60440d0310344015203c074010103150004d6041d008410840c1410003050007013 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 782780062 1250 782778812 782778823
    0xa0c080c100201090f08030615030405010605100914090a020714011506110303040f020f0a03030206100f05010f0f21020c06010f0b07200603130302010605030c01021213051002 77
    0xc8103540d407107111401028100e00701c4240280c040d0900c20311100c03400c0094940c0d8002c42c1c1001c1c004082d00786154803260200309a6006031412101c0e81c3d51280304026074105017040303540210450800841a40c600581c03404040c0655190504c11503050000505070125641500c5089030083c0012100c1c0b0003e15081d4000c00f104034401c0c91141e00c01fa40001c0e500c1c070500036600d66a1b0498061415604e031a540c54401c8403145004990005410707a51240170344031840c101c80114001d5000700054142040300c0c0c200140311740c1042400511440d4140126604440140051030303a500d4840c900000703125046403229480042c004c07624480030307144080c45943d40c0241c8004c41c40001a60026640e40d105402803041a214001d10b81000b4454100450011a0803100d4900001c19008a00e04800000340155004840c0c002d032100450088800741a4248140b0014000075001001c0c288003c60020390b135182210380080290340006021a40310f0144101c61000701800b50008110420700038000c3e4442 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 782781312 1250 782780062 782780083
    0x13003021b0625080409140709140109140f0301050702070915060207060f0509150408010e06040305030c2b06060f020304030305070602030601020c0a2301050f030105120a0c08 77
    0x82240c1c03800381c086490540304482c4400c0a40c503407140e10304410016007501d40c41c0c0c60020b5405840a110020300c421441c02803044010b0314254510061420b94806007000549420400b60115000319036801d0b42d80080c52a030030782d031b00308031070a010713140d4039000030302c52407411440c580c155080505004100b84c00140c02d07026a442620280422000000500d06025861042d100140c0c0640030402485001345661241440c461030001d00d03068240012400300c00303064000f50107020001408000b600e00c03c3c0700d030302e10076505007001e00201d080a0310024442e01015207210045440002c0791202c600d141c00740c41648240e20070105010151100c2c10b0741c000d1485201d00c41c041504051250031003031010040f20b06680e07140d03c5850502d402134407103800a400c018440c505500c101c282038403a80c1d4034100c3d0080100300109442c02e40265400414802c1a45440b2845c148503091018404024140c07081e08c3c1500e0054076074544070207082e40b0162034203a008901130600c14420001143c4984003003080e4108 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 782782562 1250 782781312 782781343
    0x21c11041811060c0a140c1f02120d090b09032101080d0507060b040e0f07080c060301030b070c0807030207030209060a030f0b0601050d1e0f0203010e01300302 70
    0x100c4801101c4025205894002002e04041d0325809120380341a001a05111004d041160314a0b0140e03521010984610010f0704000c1c0d003c0d01411445280803209126604607082c001c06603980404400b954403035807020501110755011030868003141c400d90001e030b40b403604582c582403542024000c03a92603070300006802d010302818400b1800705035041ca01c040c0c100d0700c0d584002e06408650038812038003604050b900711003042d01c8105240300f40e5107d004078107038041d00c0c601508541700e20a203528a0049103034056103007a040300446003103556800c4207990440e0340016540c1001ea50f901002ca41000c004400242400001b1030b14200f030560008054041d80d01c2540c400c04d0a8480004014003070b43d17544401404c030160b4105c0ba034001f0f40d0304d40301c680c0c10503410f040071400e0030040107410b025a020300b2085207904583e04500d03e4005002d0040328a810501c040440c41d42d4100040d090240105000d560407a4203031600894050385100d641c0c01c103520100c10410010320144c40e000b9111800352440e07084 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 782783812 1250 782782562 782782571
    0x5130e061801030201020a0809040f060321020f071a0c0321060a0308160f02060301090222030f0206070c05060409060608090c1c0f0f03020319031a0d021c1104 70
    0x700c40840c0300c04a030603650160028250740e140c5680c1c004c0c042d0311070740b100c60304161074649411080809000c0c42c0051885429100c00403624028403042c1c84500001c03500441d80013005c0303e04c0c154000302c2c4010036143c0d0481c0408056800c10600340d15442030900404161100054645000c82e41d0071a847c0030340c04540b5800040c6e103500c2d00b08030a44030680405040d50a00700a00030300301c000e4140c80c4443d54420b600d802d40901a03500003a120b90001d0340b1040c1803c0c1c0018000701d1000f004007003071030740b03103410306011604ca410740c1c5854056200c142170080c0610fa0010f09002842081c81c4664010100107040540c0c0b5038843c00b03028043e081e01e10440020460610100d44244070210f10000c4882000d4925021200c03100650030381220703034110a803840381c0e080e00c03031001051080f281000b825020b50021039031f5401c010740500920480b460368508140c41c0411015108812500c4108841011100b01031038548900008440144130268080003103060001102007200180c4000001c5030103d03800c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 782785062 1250 782783812 782783839
    0x20405100207050a171f0e150f01062d03020901080a0b0d12030b03120403030807020601230105090d0b07022103011203020a150905100c08070c020105130e06 69
    0x282e60b21000c0c0112940110354540c2800307417061402181e1207524000c401c031440214110400c022010f110004240010745030707000003940d000304203c91424520441d05601a901e0800000510307110103000d0401000b0545101702c6012495501007141c850901c83c054948041200c0094001c1d40070010761030104101c1c1002482c060818400d444020001600c461001c008680d602c0c10707a01d00d07456110041c55a42c205160b515102004000100d031003940c804da136184c2c2582030140240000070f021100f19441040140880400c840c111410000c6910202118001c3c00c801600d080c0580042984c0000d00c40d00c07481d05110001545070300484080e001e0320500300b50700005403900da804105400c14003c007080108990800c9100440b1414004d1041c4e82c012820b0396202010b2208060340540030b1501d41684006000b01400700d03d80705009200704000f80140204040d040c07100041c800414000d0340185442564000c0e0111614414070040140704107031940300e1020b540030141c0310300d40103064128120 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 782786312 1250 782785062 782785067
    0x6090c04050a050702030d0c180b1e090310020d09120c060b0f01170604090b091c050a0801060e0d0b0106120f06060203040e04080910030f0507091406090301021c02040510 75
    0x83d8001c25480d40618070701441210a0b1002d0081c0c0e910303410410564401081740c3e0381c041d0100002900b0308051160703441401000175881008080c1000642c1d540802420b6003d0383c0c0010492012004401c0c0542c60301804c0410074010111000094006011000006a1246c0c003880c002c002c140300c0d880c20012902c200c014800030040c55000f05000c9a403908144000314040c0c20115070000c0010004a0445041d9031510444581510400030b80d510405152150f0000d69840007820071551400e24180750f5001d01c0100042c406225070024030100e9040484152a182041c0511a8114049501c00d5a54280084c40411900e05c00d50036540f404803411800c0d0002d00400d011a101da6000318181401e1103101c4190060182085484480800c140000c6480d402620042c0c89e0041d140040d039034078a1400e100589000a0000c1c00f001070000007803001e001641d158600f921401e41e1025154007210340030900911900308100a0a141d04140358100403d9800078002c0c1c50054030346245080c04cc8005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 782787562 1250 782786312 782786321
    0x20708041412070b1b0c03010e0106051c0305070b1509090309100c02130b031606020c010e0d0f03030c021614190b0a05030a06090c08181207150e06090c04050a 70
    0xb550802001041214510300d440142100048088000c1d5031b80700e041d030740c0000d0031180030b41c00501c101d944840041040d40340c1849440d144024000120002c1000d990b0005e15501ca140300041126510314003081d050310014040ac411120040c154140900b0324002d0f0603a00d0f004031003900e104c1c160400c40401d04511810211004903030113400f41362141c18400000e0050451800419007600c41c80c02410400c2018864040090007180c02415030007000000041c15aa050701c401402024507110760f90015071500d010040498051400044050003158101e0501d40000d0740584c0005039100003044440c0c0800d40e9240750081150008000d203030609008030b800700c152007a030500c170310103101182009000348000c641c0a203004000040c580c0d01c9501c0c55044404c040c1408000450b5107042000300060b115030590940a80002000008440c3c0700c004058410448000c00404982440070701c00e85080e00000442d04000301a03419034030b08030400903aa8142440c16910a500b03200108d503240d08540315 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 782788812 1250 782787562 782787569
    0x20301060b04260f060a061505090607060b0a050d0516080c0108040f0f0b0412030501051219140a03110c010f1e23090102102d02070804141207 63
    0x401114407200301070a076018003110341226085004d04602c0245050003848000d203d16003a200000e0114100302e030f521502200061864144103007004010b080b035580c10255000300e43e006070080751076003d2201060100303400ba0b000d103130081e01001440c0204400031030302c51f021012624140d00407079560104103075605100541c0502062000003c10049410304021000780d60040030000712410b2250707a2844d1050003201c0036100b6003a20404450b03450f42c54024240101822100e400100d50301038600f544a440080300c80580070940d040c05030401501d82040108a80544180d600f003800300c0c24043c241c07009441e100c41090160810a490310341c00303440d072000b00f8003940e500c40c00102e15a13943d0805c2c1040c4c41503400188070b400d840070004018202c884801d0441d018a0781925005000300191602d040001d0740d004003414810003843d0b441000701e2038200c2641510507030a1025000e200d64000744200030001e402c0a20001d404a0781d83c0a0300304150302d003a02610008000c2c91120b4a00d03498942070700 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 782790062 1250 782788812 782788829
    0x15081e040b220602090102011a01120b0a09020f0405010906090b09060c0f0601060e0310050103080d2c071d0906011e1d010f0b19030908040b030f0103020301060b04 72
    0x1050204100c0d01d121503010340080d00030603031030b084000030b8079a940c1c0da142c1c12546241c00081c2150b265a0a0248280a07600c2c004040358014003100081c0c201c031070000079a02c46594036091b0909654a481130740c001088508000c560b80e484040c91000690705c103001e900e0100310612400a61180326204010882e454444001d0601202004100301076228030086080741c840c8601c20000d00005000f06402071406845442ca2200c688040c5402c08104041c5025440d15000040003c6003042c0216441c40002c2500011300002d00c0c404601c58120100d490340c40c170300340480b00c60a0b14500140900c1555885034544400c1155510141401c0d03034100c440441e0b80e08444c0041000c00c00c1f803800090311004481110003050345138070120a00030a031081100360969071a00401c5186690581007003c3c0c0080c60389030786008403000201c0d0f904640302d01c02004050341c8940c20340034000104180c1d80608500c641c440ea80c0e0405003980000c085003070000340d20039440d1a5000500310348041c1107038202c1c0c00300c6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 782791312 1250 782790062 782790121
    0xf060f0d06050a051b16060902060d0e0123060f120f060f161b080d0c0215060303071a100e070e1002010614010509040e01020304050a121407021e0303041508 69
    0x2003500c8040c0c411b04444c041c2e250122180142d48407400382c100f2039140800000e4010742072100c64203581601c4144030302890f504c00709040c070745038038600240d03c1079040d1408481d2081d1100402e4440074480e008807030a00803070b030044141200100c0c0d081e004011109910b03003251a01e002d07030b60500c0341485050700411034850440510524405680c082c6031301410300300f4140000500d610040d41c6c0c1e288450401030f08409001103442c0c0140700f0070340e0401010386c01141000c185a83ea14114810504051151510070000500009003601d0403005000d07000611042801c20040203040d0448038a0410b10a06102c0303200c4510b06c0c070500c0785104451000169141c0d000c0c00a0040d291a401800d0064000307446100d5000d0070b5009000560160b03100324002e000c030f52080d041601c2c954144100800800500320440404843d1724020703542c080e501160009400f120002c1550001180c668140e83c16020100d400200c51200110000a40c1c0707160b201c610f0385550b03000f242043e203004070245180e04800c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 782792562 1250 782791312 782791327
    0x2210706050a0603080f0702150408060403110322080606102a0b16090b131502030c0109030801180b10050714010f0921080f060f0d06050a051b 63
    0x200c0d0070030303508540d00c10760000e0301c243c40c0c3c0c13107840c0d45074890100d8080c2c4210001e031000c110700b000c4412001c004080388145082501b04180c072510307108041e1015040045282c44d044400c2d078144112400450b007811014844940e0b6a03806a0b80380c504e114050031400303060005486803d03d010014a0341301180e561480c1500e8000c20401c0b013000d10020480d4042601c1010300c002800000f019006035400f1070300d06a1b141c1c1c880801050380d43ca5801036140007605100240c0b044091282110a98074091442c0904420300c8404a14500036603000520941c01d16541d601815044010749040c0c0340e00585481002c410b841044040d2054000d10541103404075034600e09962240340549051841740e112a031152414110031400d540000d140c000c07000b070b942c2c0310f024100b01034004214140c948500104101c420800d50241150f00d00806089114000c207000a0096172040425541a8002405040041c080b4100034008000480b2040d264600d0400841c49401d1205100801349020b2450a86402e81 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 782793812 1250 782792562 782792573
    0xa0e0f0604150306020f0306091003113a02131a090601050c100b010f080402031009050f070b0705010b0a03170a09090f0f0b060412061a031c022107 65
    0x700854094030b1414a05000c000104c80c1d0008040096207004019140c0c2001c008200c1d0b1b0120141668080c0c1c8075800381000002c96107140d0802520303045403010041c5864102ca04110000c005a03070038415108850350313001c80301e000f001c5c2c213644c0d000382c8160b100e0380868040101280c1c0a1841c1e07404c1500b25402c10a0280f0f005401680c0c01700044c503109080807443c50b14189002e04000300e003003000ea11500c001005582c80035554144800303e1501c9845c5003881d4001c6501c600c0c110707032001c804a850388210428007404021a1a049205400b2203118550742c0300c2201c1c0c19004040100ca103075007002d00048075450408441c2007940e400aa00c03112801d00041000141c0c0e20002d02a81405202c541c000358080c02c03881040807810001d240850a0404036043d03c0444d103040c1c00c00c41c07082009000901605000381c80850700c2940c40100054a204005072406001c42d46402582c0e05124004013907071244940c400101d0009083d80894082d40f071120760303417441d140c0c0501d0019000441032040d840403a5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 782795062 1250 782793812 782793821
    0xf0d0b060903120c0a020402040609060e04050408030c090f19050a0e04051207051006122102071a040905040f0b1e1512070e100e010b09090603031201140a0e0f0604 72
    0x14240e01185e045004650105041e43c129901c01d40c00300d104500104070050700030749841c90b86481200d0410040c9415522071419000c09070944c1045130020a025142d41c481620700107621800a08121101c40015102490000b480c05918041c124402e00000ea801b0340c0040c480c0601c0d8090054180310010101069250b04804406c0d21684a10144a404801035108220103041c40e40d501405841c410700b400c5850100d104500382e03078104404488642c03a6404a0440d090316914054851f88004d91201500503020b550400b0400a140800707000030042c584491040062088142e01c06694441403505170b4102480c808803107606012000031880c0c62074000c03520810400410b0f1994401d4401c906501d420440e81040c03a800e035205052102d0001d08103600c000403d5000e050382625814140341200318024071001900a00081000c40e10a0340e052003038030300206000580c191950307950802c408000001c90503a81c0902076148001c00d80600c50740e10f0501c03c0324001c00b18410b0380c039200140710050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 782796312 1250 782795062 782795077
    0x1030b1009110904020a0504031a241008130501240501050301030b22140a03090f1811120901141b07112403060f240f0f0f0d0b06090312 60
    0x40708100100004d902c3d2060581c121200310044106c91034644bc4400c0303600c032402036410031642d80c130707400d12200e943e038207108944044035260111180e200c01103500207030101411300903d03550a024030a0601045107031840e112701210340c4261049a030f02c000550b280d120a0001a001500150008540110103001c65000041205007030ba82500c01d511258000e0300700041400d45c0350041020303c41850b5210b854200070300304458070141214548280101e1203600a140001006d8485540a9000819009031a07000c100d046004049140c020704041c000e0069030340195403003803400085a1300c0146110f101401c2c0740c0d000121890200c258440003054206140942e0b8805e00342c002050010004080c54010703441c0c54140551242000c00c208144503501000380d41c021080030040440c1e41e41c01400c002d800a5061420703d43e00ca20900340101d00d48500c4201c814801c000244000d00071246200808440001c04010807504945004002d007070321544500780d6040c2d0000a100903250240801040007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 782797562 1250 782796312 782796317
    0x60906010915140a0e07170f061c05030d2c03041202010c0219181406012703170301030303150503030d020d02120c0319020a080f06010c050601030b1009110904020a 72
    0x603559074085d01c10188400310340603000924000550082c8007000140c554115803207e030070608928044010072101c0c07800000700088030f83c0389284002482002e00481e0302794031001509002c1c2c0991600015400ea000034400307011540144482c20017044007105480c00d03214488003e444022303444e0011940d6082c00300d0142c2c2c1c0042c0014401e0b500021030889107004000790b407548100030144d144907100302d450915410750301e040408100314190703910039400380341d80f17009200c10040311440041c16005101c0f00c0d04000c241d0203014100d11012054680034604072031003581e05010f0100d0360200c48003804c0c058401c07550194014004880c829080d43c01524695039401d000509011607032219144d0301400f500c1401440d0000014010103503810181c894800750050303419860070420840003060010001c00c4071140c03413070280118806a20030360780540000d800100720741095031641030102d180a8242c5011224440c0840e0002e6400c8290185418002e000e540300b038144508882408065800006002e04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 782798812 1250 782797562 782797579
    0x70b0a0903020a14150f01050102010b010c0b010608180106060302031005030d0905060f1c0e010507170402061b06040c14010c08031504060f030b04020307060e0f10110a0506090601091514 82
    0x503407110380c81744911800300403840c84800e500d01000a401c58a22229a03810809401b0902c0c0224903c221018115440c5240c10714036580c0da0450403c901030780050768546035003090800505903034903801450082400100d1013907002c0d5124201503584040701010b801090310810304010700d24054000d0300c91506010005071030040d962006d81640c0c4050300f00c503001c25580d10208600d9103c248602a8002d0342400c2840031048008484164004001c02c002d20a200c001003c1740420390309283c86294113005801c80d41070341064a46295101074134061100d00d60602401040951b2113481d817141040d030000280d5146490340000f500f0f41c410398910107501b082c2c5482000440c4482c07144038200a502030304d0039886d0b41c1400d00c10941081c83d50781c80f6404000401030404a0781c0d9851000766010b100c11545005102c101800a40300203a04400c010780314060482c1c51360900001050301c0303105002c1c50007501e200340c1e2180707525011175403c0c1084a54001d540002801000a04110507010002c018513882 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 782800062 1250 782798812 782798833
    0x406031a1806030c120a060c0311030a0b0103091a1906063e030406140f09010e01021203150405010b0c060112051204030606050906010c0506071413060302070b0a0903020a14 76
    0x1481e0702d1000c803984101b03610260000e0700b84840780c03040641d06600c525040c000003070021402d035510b000240000340010b07903a518418541e03001380e04c00d030f43d43c0c1d91191a07450100d40e040307542c460f10f80c0211010350440c06146203a02502d40288500310a42c0c185403600300b5003415081b541d61104000d515910311103045241818441c840035000c250070b01e840c5400842d540c80c28080000d0200c03103051036000e045102848040c00e201e12500a840103100c0a10f844884903c0c0100100d10305080c0098032042c07480000f0a0040c014141881074180c401c00f80c2d414801c5980e2a51401c0f468402c0306990b00040d08001d0041c8000c00c00340aa485907a0b0192088584008050340c0c20300d22030344198030407224166034903001c201504002e81d0302580a1030900742104104002e880ea00c2c0c866100070248410050300c081ca500c00c034948007003031f10450200076030441a00b685078540900207600c40c00054510184400018a0795110b034007034a403100e681540a0040340070720355162020041d00a0780c008081c0150000c55 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 782801312 1250 782800062 782800069
    0x31b1511250b1e0f130906031101030f152c01030b0c070c03050609100608030c0714010207180c0206060d110405070314070c020a170606150702150406031a1806030c 72
    0x3821070024a80f503556640303030308072201c1c0c55a101c2ca61243d5003103824201e003000030270000410500d048000f0f080c0840ca00010861800041c90449407100b664442040b020403050300c54050709003500300c070048a072015031440844002004003440020400380c41c81000442c41c000240140c11101d00c1401c0100081c0d449540340c60801c81e0443d00d00300b00740d00c0f000c0034a41444c85402001c00034020030010310718007075142da1003944030b0b4818020000c821940c000b410f881a4420044a0014420a4400c408911500c0c5101004e44118420740006100300c0001c9106840e0141c100001541e101c28418540c0451000344006090001d00c0380c828140c0e0340c00d00e440c40000b914036543c801d48880d5a0700041e800c81d8810040b40b15080d40055080300b5108100000103900050714a80140046a884074124103106180fa07161103861402500b242208030705000354050000900b058603100d4506000c9100d0107164244a44031140c0c0240e03008940c0c091b090032440602c0109608614040e055650096001011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 782802562 1250 782801312 782801317
    0x60b030303070e0a0f1202040c110307030801170d020a031409040501090207061b05120402120f030c0d033605011109010206060a030c031b1511250b1e 66
    0x2003030225903d00010079461400d0019403014112024010100e18100000c5804001d0f80741c3e8020b0243d903581084040c214062495180709055010403617503a003900d4500242030136400e10415091061b9801c803011204004240003030322041682c0109045c6400791401ca41c04000002c1d0042d421104003c11071030f0f40c44a00a80d4060401c0810242e95a4803a14001d0111824030700034080e10b80910b202c0e404420b902c0030441c0d800051030916007809480d02d00004244861072040c02d002e034800c41c001110241c1021000d041c4015041c8180d5084460092042d002d4402140710003240004584401500c1000d4082021171000d5076007c80e040080c0603075516084420b00c03201940c080350042011506980d041000070b51040c0706a1320b6203061440c41d580c10045076010300004088000c8048100b49a410340140040200112103400d9090001d0740c102070b00510000304030301054018107500a14000f569022450000c0b581cad0001242103207807010010340b6400c0902e6060020080d502c040c01c03c84106c001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 782803812 1250 782802562 782802571
    0xc0a0f0e040203072601030b0c0705030909090d090806070917010f0c1206090e0606040c261006080f010e0a02070b2412190f0218010e0a02180607060b030303 69
    0x1502c145c003107204507200141c4c460129905100c684800010f01c0002c1900007501d0b0012a5560159200d24407840c185046014001030143c0000309902044108100003e500c548040ba0b0340301c2102c05500c0c0c0c0e07105a2200c03812901400482c0100200b040303850b1543e09400d0190f55440c9c0001791603401c2c60503070020380d0300102c90b840004000c51410000501e107445070348001d010b204800c03c00d840c11108002d496040003400d1078407aa5a4041030300c621806110426501885001c05040001000982d1498a4420344000500001d1030b040814081c0c01418000e0042d10310440c41203141e071030000300301142c1780c005000c0c1c142d043d000d120540006142c4002a8007a40081c0d4a01d48240440c002e001140c0c001c10200b5072240305510458091603001240d000c443c0001c00c1020b403080f050380d041a90408004d2100290003407165520304600402d0f0b2000a81030311080360f2101d030692141000c1030280d0056400301c444201c80c0e5604040c5915054004110b51449224041039031020040041d04681007100c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 782805062 1250 782803812 782803817
    0x5040806070e28030b0703060303120c180b03010e132102070510090509160c170415030c110105010f0608060d140a060b03280c05040e0a1a0c0a0f0e04020307 69
    0x7802401004848503105c1d50195091508001c06031550310018041185480608130050741e81132800821440743c8084d04210120726140704031251f8a9030901020381c001d1103500c8400c0e44950110340340715000c00c003495416070402d00440d0411030403940c800358403d0a03c0c01c01c056104407000040ca607118000060805e14441e160000031a25100500540120052035808040c985d03801c1c0151003074100d030318400d0075600103000703a41501020300651010b1050350007144440595003e04918170380c1c16006081c58002c00c0d0354480381100c0c042c1c040c40c281c3d2802c0c082c01350743c1110b03002c0c20b00201d88280785c0719511840050401801030641e440d0302180403a4458100c500360400510142032200c58024031034803107010ba0080881192070561855448030080011a028111401840910021804013406844014400c1000c0b01414140641c0c9112a140c110b40f0a01070080d14060b61720005420340c82041900c41061610355101012510804010200380a10521202038040c0d03444a2020b1442109030381c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 782806312 1250 782805062 782805139
    0x904021606141b0d06180e010e030901020604140a210e22090201020309040e070f0b04141002010b091609050603010b0d020304051e0705010311160204020a020f010908040e0705040806070e 82
    0x41c51002c0c256201c0317665103109d80e8010440c03c444c590b070025113164000d800c041d04120f07446810040b039040c440e1110300500442040c50758400301e6981e55001c0504019280c652181180c00e45060011840c84404e140461403180d03284810008900d8000351207491051041d88c0c5005c80b4000041c1c00c54041e8501005250700050041c000c0000c26500700001e05903c070781640c2014641106000380076500c101d04c902451500e0420700e8442e001350424024104020100aa689025001d1004040101c000c0c1c0c000030f003d40390001341078140001240d040e104800000fa281807141d04622010b907101500440d035030b1140c00d84502e481c210444a0702c1c0344641105c0a841180c0c5040c0004098070441c40000001c941c04111100d80700364413039010791324a5415200542c03640d80403101a401c1003054134412006500703240d400810014800010000d03550341d82c90103143c607101c1c0380b021030b80c0d40038a0080c5800c0e5032088020035861802039040400c801801020b5a0520f016481c00d026035410007001a00c560890 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 782807562 1250 782806312 782806331
    0x13020d0207050c090c0901030908270f040e061b07050a080d14060f010c1401020a110106060f210b12030d0507111e030904021606141b0d0618 62
    0xa2080310502e541c2244c2c07041e2142404442c02c005441451101814180e48403000e008001040e03042c1c0700d07652111060441c07050640e90105401401c000d16946c45100c1302c03001c401d42850944100c81180300c001006180c15920b05221841ca140942c441c00d00181050103082d000510800002c103a051013021040d80b02e0346210800801d49407802c1684200d0324001c020000591190b6101c0c5c139050100340b0700f0000030b030590709024150fa481c0e072018030b04075400002c0c02c2d2031468100100c85d000c203100400822980d0380c0c89a0489a81c51101103410000d042c0c00074410050140c11340300c0d03901c42240000050039203184070004080c0813010325503002c0c581010503c0203101c042840395070f034030403000d042243c00000c154034074544500340074051031404907a6403030440c1d003801c04000380d80403088050000c550743c3d40d1001c60070300080030f020b00c1103c2803810080c04010241440c0f487d10b000d83c5000500c0006010144080101c070b40088618000c655910100010300688071804011003502d40700f00050503801 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 782808812 1250 782807562 782807573
    0x2010f09060212010b5d150f0409061d0a0201090506070c0e2211090f040308010510090302030703110a290903010207050601271107080306010c0f061e0b010210020913020d0207 77
    0x100105858401a030411f905501c07a03ca5051240d103245d03045038005141e03040c40ca0282e00400100003100c00500fa00306004411030710005403014100d001340c8031044580d41e19810041035109640c0000d102803c029810440d00403212106e030340041d485074880242c0e1203501c0e00d07805091050241603d1410b0710184542007414203248080d08040b1803040401e152030540c6020302400018411640200049400850000e206807140d1000d10741c01015540c1c0c96030740c0d040903455001c1000310244070b200a1300d00040c140e0b0041c0000174454480a1060401070003142048143d90414014a609550200b2200e03001130310501209001c0e00c009070781512546055030402e00028003101e410496549044814440c0c180e100b410358034030340e0384544910b0343e91b55000d0040310301d06030a4200802d10b6400e81c9003030042041c3c030f400500025404101c03002c0110a07020208094072070030340f0348901580100c04441c0074880c10307400a0481c46009000101000c5500c0110001c0b81e0100072001354080d8080382c006c04004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 782810062 1250 782808812 782808997
    0xc02030714151501171314010c0e092202040f020a0807020705100903150216050c010314010501120c0e0604032a0e13020102010f09060212010b 63
    0x5140f40d44160091480d0000b0f003010800d1401720030035424580014076106520001d20300c4050380101c044410840055880b4017803c00704900f440070480a072000e003424103040020512030b0845001c08080010080d40e464024402498203980058603030804170014001800105407181f01a41c40c03221034a0b001e500241080c1b2180c008902c200d140c0110541c407182e100311036a007136a401c003400b001c44040400703c2e40000c1c0300300c101414000d2024154032060000214070440741e00420380b0203205009031410840c1a0400034000c55021a0104143c07a46070551940a841070218508142000840c207200240464100350700c205c0705040504d1950240711181c14010305080c51b02a56100c02d9402c0c161000c2d5051402005c0c4c21580040940c2d100c25603200f5080081da118000d0010031603000c1c40d0500c00007075803014041103c1500100300001e91101c040c1d046951441040482300b25501051203216003017034220510300400300009500c1e1440407000420700d42850342c254540159003004003c145040c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 782811312 1250 782810062 782810071
    0x32d070b1e010b040b0d0b100504030303062705040c081903110c0904031803060204031515150c050f03041d010e0c0d0c020a06051503010e190201030c0203071415 71
    0x284a044010050445080113071000c1d203854022036a00c030716119070018002c0201229544e03018034502400343d0100d80000041c808d0707a009542c1400503c1d1103c404020380601e1040c1c1852414000740e00d00008000c50340103503002841520a160669170b10648540344c4800000b850300740b54a0304000d2420540c015945a004950040140500194943c00544400c0300200003074140304001e8070900f4540410310000000d158808421503e854036801c01081400100d03441c1400285000c441d43c1d032552003000380b003048a8030250244640400400300701c1d041e51540d44203c0e5148103072182c4442e41c1d0820b00c0070700064a80350b087c0e0711100c00b8108030b1041510040e0b004c50000302d05241030100794404441200ca03040841d440200d01e00110000c224600851008050407443c581010b12502501c84106918900c004074000d01c91490a60f144580750020b8080e84200032080500a07401540203030840100404180152401c04041e80c0b908510390940b450139600c2508605015003e02c1c00059a16400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 782812562 1250 782811312 782811361
    0x305030114042f190306090e0615060c010f05010e0603010b12030a3902030714010e040b010c0f050106051c02090a050a060f03050c041805032d070b 65
    0xd801c50440d41c80e44065403c02d43c1d807041c1168084190005014000c030303140c820055121045140601000400600c0c0c0ca0017800d42044c10035941c4070000000003003403802601c1c01240700064185d41c8040103056485012401000e540302d00d01101000746d144207050082c2a034804070380b05403034064101400c440c4030040b00e40c0b22b80f000b80c4850303258520000075251001700382d0418188110001c55010400440305a241c944070089240929591221801b03054034544250211107606450b140103420901d442500b15002400000f04401c141c0b400303030800344007400107052415103421039440b80c00710110800b000f0b403040e81d100c8104020302e08004102045403414000c001040f0b6101d070b800240b4124004e02031600d22034036480481d0400189922580c000d1205c5001c040035240d903031401580f038440d1047c145e882280b42c04070364600c0c505c40c880c10200181c4e01c0805149000c9400c125029400c1580510481411039202d01801c0c80024000401100e0700a228540711031600c00701d01c0c07000b9140074600000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 782813812 1250 782812562 782812571
    0x1b09180e030403110315090312010905060d081b06240102061902180307061808010e070506130b0d0b09060d020a150203073905091501030f09030503011404 68
    0x12810001c0151003d03030303500901507a40003d60b07200080c41d003280e540701640d030a40e908003489990080000100007036801888059050b80e80c4051039811960103d4000d9000210941d000c000284004020071403102c1c2c035101580081c2c45124a40c0c070b448000c49801007624840000c884078005024201c081da500244000c0901d0f14100031100d0460088154140c0000c2e0007045107240c008400e9441041a9405402c0301c22050f41d40a0081100603c00c2481d140c954458402080e20b44042c000c16095031100002414103916010920a860f4801464024151100c0074042400300300300300100a04a8003000104200b0140010051180b030050055803080c1540c2003410010389841118600315004c400380c1c200403850303401c0705900318422003100510881d0001307074500161010b02e26540c0d4228403040b006d240d00700011034610545081e809442c5e44800070704001242c60411040601c170800d41807401084018107101c1d50400e803038060104401060000c0010f001900c140e003103088086600b12018407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 782815062 1250 782813812 782813831
    0x3130b0408070509090a060c08100f0e0402060a050f0712030c02210315031e1c0c060506060c01090c051018030609060e03040e100617070f031b0918 65
    0x1079445942d80f090901906840000810020341400421640d81c1c00200c103000021a1940080000e0011510700a6560b040c3c840428031051400990302550322250320880e071900c8503000c001c29a0456104e903c10808100040703480010340401415200c3c1c8644841e85e0049a40c81c005400c0e1215150013400710b5021441e484401c171680e80503625440840205a0341d60380324411095050040c02694507010303c143c1803103487e507840d1440c0040d02038080f00f0540b802e01550034403c0e00d000903600c2840000981005031140032404940c002500301c500200f180e803603e60106105429140322751416160310490420822131400d00d000d446610544030300d843c08440908449010340340301c03e4040900002c3e9144c061108214251f0b210019094030f41080726290f0341e64110030b40380520b0403a0040610503200c007000540c01c0c0521420010080b003010b120520380d4607805d08a400340c121a02c09400c02d625800d1426280c05074107001814800c030741c1e450000d101d0801f4005441843c113415850b40040c94140c062 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 782816312 1250 782815062 782815079
    0x6090f14060313020103020d09110a0f0b031618030602030910020310061101090b0103120f02010b06040611150c180307030507030f060e01050f040b070921030201060b03010803130b04 80
    0xb690b003c40b0a5204200546042c00120004c0c0038062100d2983c40c54100c15400f44021140c1d0154880c0e811510300b03170090345070780c0c04c4081000f04d48640c4413045000c4c0302080d08050078540c150802042480d0030300607000d000c04a5071010720070b94029107405078000140003c010041c00b085000038400034055195040512081802c203d41d48a07440800c03c41d8804000f08401c290403204096800c055030064039611780c1031242c03a8119030705107000480e2001d000b03140140d0060040420a00000b001c90741014548001554070001c8103000400c5030249078050408003440d002d00074001c3d0000300d81d01c0d4a54400c1c1001400300c003251418548079500407002040001c200040aa007540c0c0d2100030040c050010745000070240c001c8050004d0154205000c0024010807011068412409050703c080d081e1200309058a406c0528050341c85460b841c0040c02c14800003c1078044545031184c40002142030b51100d90034210b40003a0170040840d0030000d500018038010408400203000f4801c0d0003880d051410451 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 782817562 1250 782816312 782816317
    0x1305150c030441030d0c0908060a140402040b0607050a05030a030c050c0706180b0a0e010305010509090a080309150f2a0901030c090e0a15080c0d020402070602070c06090f1406 77
    0x2c420b8407603014650082e21403c00d100b41c4000c038420b10028005100f00c524041c0c0110303400c0c0603043e001d12445000915200007030041507140e08244101c0b081035100d0b40c0900003c2e000d46280315800403c01c100100016208108a00e0389602400242da107414444000600351030701c0105080c10007100303121300407010700042080ea0458400381028211882c41c249040041d040a5100b51140b140128000c025142c01c00d0b441c41450000342c2e001c00240c1c0e281c000300a210181a41c462206d544100468000118500c0007150407030400011100312000c240d60400c0b002004907041c0e28600d02c1c3d5000d0052402c42980020700307003030309121410030000c1d22014a104500401c84810304064844600035101070044441101400050501c10488e20700541d0740d6004c2d01d81541d903803950161146000a42c12000715a6101c800001082c0b803400303c25907001c21019402000041c0e540582c200420400901401828001080303140c503030b100c82d185000d11903044840300e075000e05000c8006159403442940c0f480304 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 782818812 1250 782817562 782817653
    0x6030c020c1e0a150201050a0c050909070201060b0408030d0f020304150c12021215010f1202071103060f0106030506060301260709111b0111031305150c0304 69
    0xd00007031601d0b80c08a02c0c0019450480142e400c650400c4011030440b0007181c4a02c1c45000a400920031900e504500000f00c0310395003440b00c00a2020710444429191102a0680000042c03002140d456182d14400c0060340c40750740520300c1b40d48002000b105640b082e000b50f01c900580080110305506e4107842c0c501c0e0007200f08802c41c4000740e682e1683e07044280569182d511b00307071100604544560510340c005585071010b980702d03106332030000510b146561141600440541855423950003002e400c00c0c078900650030168044690b020005102030943c0c07000c0050920940e5040c4012685501d400b07805003c0f1080035008501400d01000180a241100c5002c41002c2410104010010844681c10782c1404441d405c2620740d2030a00e0400d100c0400810090101090315819840101d502320028508a5001e0a403869034900c0034000609130704800181d80689500550544000f03940840540800f6101161100000c0c0c80c04018003060141c2820542c20154018203503401984a00f000b60952112040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 782820062 1250 782818812 782818819
    0x30318060a030905060c0a2d03020a020106031e03080a050f01031722060e0307080705090c071a15030309010e090a270311060f1b0c0610090606030c020c 67
    0x5044580381d8480d07440341480513040002d4480d141080d00189507550b1000c00b5042c0013502c0c1000344481c044000b03840702c0c28403a049264050040090009074041c2d08141600419550b0712000080440e081704110442c02c01940380b03102c40c8000e18a8040d01c0d4041c0944a401e80038980b100700141c9440b0a10391030b054942200500034020344002c24400c01d0b100e00ba40c2c0d000d00b02c000001d1100207810900c82102039902507211040d407228490107150f61035146208800c02640311039001c00890a0141c009a042003c80c038000f403920000c1c0c0c0302c890700c0700c604029101020700885c0401c008002c00895064581e40110080c1d031900303105d034000905c00c1842503400c030301c10000400403902030343c4a6481900600416800282c081900341c0f20608000610103040c3c000c90030142e00c0100d05180860454400e02c0002559002c0307884071050041007010310b422080da401d40c2045604000102000050f100e180f10301810101c0d0340c18000002c0a50308554042d1040c1800c1c03d07240080076802107420204542d081c1c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 782821312 1250 782820062 782820067
    0x61b0206162906010c0507050d030507022d060712030506131a0306090d0c120314091608010b03030f0304020607020406060c050d141c11040803040e0603031806 70
    0x4000310316041640d400028941002c600074840c501c001e241440c0744001c0060320300303580e90340e0341c000650307240008100060081d08400014402c6103010000754141c203010f89000da0a020199002c60f02000380a030701808420301ca03641c4003004521695601104500c140c9046081c40902d503660b82d24150041c0c605003d058a40340019655100c00700280700243d280030741480b171006c400c0031000c1c005a4440c0c050307010b0300038100020b0709035000144ca050070b490141d407001c1c50030002ea110500044030898008040603124040501e83c2c80c900d10546015211500c0a00b007511844941040c0242540e4081503050341044c1040c002ca0380c0c0802960600c40380d40020903543c0e5200d02c00140c0901c940000294003e181c41c0d0701090865205580b0f519940c8224215898440410400d0322914407040302801034400800429808400355030604445a11005010495510304a4007011a401030741003c0007a500218081208011031800709801030400d1b000380d0710b0724542031245005928198030542c00f40b80700 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 782822562 1250 782821312 782821327
    0xf0507030e12030a0302040305060a0204032f040f05160311030105100908010c031418211b060a060b0c0d05130b0f0409060b160213181b061b0206 64
    0x820034070080114000064a51302e0000c0c40019009401c24003042e034482c4a036600044440c001442142c0c00d8035000000c2070b04c1105240251450014041d044440311411201114446d403a64000c80300703510f40b1008007040a01d00040e06001c1800284003103810507040244110301054000d003101d05441c1d094405280c105036042d4150744013030f81540071031020340c6443c4407481c82c03030341c558060803d219913051605029103800410f010312800044201c80c0d20307049820440046c1c40d01e440440f20401054071000c0c1091500e41890a8000e88900c0c4210950070640801030070012503c62400500381000e10541030842080300e465440c050a0006400c1c0030000070481c0702d40c00c000754280d00802c4d8200b4445d6485c03401ca84400c102e90030038440c1040350303803c110b03001ca1240c1900050f00e0b022950100390060401d5180c007000300000d404000c02114907620126106640343d1140051050340c00307900c0300068001d13042c49641341c002c150b07480b180400004121030f030f11601c583c160694003d601199582e1f203da03103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 782823812 1250 782822562 782822569
    0x13030c03080606120408091507030206190f050a090201030f02041d070c080d09030f050a12240305010e0c03060f0a051504020a0c060c14070b10330f0507030e 69
    0x1d03072200c3c003a070810a54100410008071380024202e47e442591104086008254118001d000f568401030143e000701300001c40c0f5408101620080030300120000c640f80b14200f0981c401c82d4010740700c070444281c46403103050035541c1501500c109442a03a80c00c510780f500d0030070724007079001c030f65032000a0b0510b444010400c038512440180700391715000100e055a80d04640c1c06d400050408200840101c2d44014408492034010401d6a110414546681c1052648940444000c082004001d482c00e05070f44601103066042d80c41702c0014512440000546181e0261f0342483c182005141501c241d112904001913150700300345503a000000c4070070200b016200c0400b007402103001071062581151002c2144441c0301d500241007030940b40a80c1080101d017803d060100e800814102d0403265200e8100100c82c002604c1c1c464040d07001c61074009000c0f403a034441d911000c8102c050031219455a0600e620800072151103007a000748942641000d41d8411a0280064100d015580001d000e002030310364806210388 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 782825062 1250 782823812 782823817
    0xf02090303131406030103030915140c100f020a020a0219080d1e0809071a1c060317040509070503040f0c0e160c020303090d1e0803060913030c03080606 67
    0x640040a5079200ea401407003032036101c501d5103d020f60905103640c00401600340081181d050b21b0705035480400060400b1000c0400064008801080100300385c5030601d042c91010260113010304a402a20800c42c1d852001000c2c0c40c003031a44415880c1c4104181d2650940026002e10003981c103498214260916640d603041c21526a84090f80070b0041072500074500350700c060704240b01d40e003403400041143d4403011304448043d403c482c0248654000601440f010141810990130804200e84207440c14a140a082c003403d1a200742c41c1d66120b450312010b000b00404c000540d0100c4c100ca100050078245800005103521401074600b03800d20800102080500241000140041e90480c1400d102c0607525070006031020030465501c00125156004515040d1040192100c1240c006000b10300301410b44041060001c4c42c44030440340040345002c40210301601044c0300b03032510700485d4407d80b2807074400223014640c07000510440c0a40784c2e0118070000240c00111181242c0d03054a09080e29540707003030109002d031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 782826312 1250 782825062 782825077
    0xb120a260304030207060f0e1806060c120d2d02091507050d0f030b0a03140705100323010e270111030105031e1005070201020702281403100f02 63
    0xc500000800040c9600003810108491107640c64050f004040f240c111110142000b8180d445800346815028a0f00c11011050b00218002e002e10320704594100350354940851031030f00c001d0b034020110302e04c003c01450380b02d0141040c2503494056450448680b968410341920000c5e10342c800e0f4040b55110061303c540c40c0d8051b05014144440303a82d80d0140c20120354511460381c41200280700c01d15015101072203801440546a0060070014190741035940d6030990400018090302d1902c220302c80080c0c00d0360b8821500d4643c11207500c00060310aa10b074500d4008ac1c0a0511401c4030244041c0100080c0100c01c40d52680815100d025010700020494124801c501003590300300c00c0c3d1f08064091103203681c840000c40c101c4e00100c2c11580f4000d0703190019003c01e1000f41c1040b2907504080300c2c2036000005030300140c1d800003c510006141413070f00d03400181c0411101a882107015803110002c030104034200c2848001e000f00070017041400c000500004d039900513042d046065182c41b402d10381d1000c981501500c105 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 782827562 1250 782826312 782826383
    0x80c070602070f1113020f1608090a030b0717010e060103090611040b181f0c0f0804060f18140f0a0f030503070506070507050706110a020406090f0b120a 67
    0xd410a900780f40200e4041130311254801c050400b1010704021691007150440c16071150741c1070501602e4a4540402a03880c1815110f40c4420000a2072640e102d2420b9005503200745d40c03132503042c10b00000040003080e0100c400646003034a40014050702000402042c1e007c1800d18022510071403514055000c1c1c204511102004100400d003c5a4000b0b101c0280a103c101c510350b0a0243c80c003032041003990405404c00c000c0140204140c0c000c65403069407450101406031003646001c000030341d10861554080c0d0700c00400079508054500c600c90380107000303250032160f519000780403030b0400c02c040d410658603105003442102d40400070081505c1e503070440340090505185145240740d803820401d03103039408100116283d00415001501c1d10303019100740c44050350818000d00003141021401d45022803620a0010f2500c604020f610041c0c0d601d0041e00064903002c10045080c0707214298020555218144552041c00b80040d505c0e00d0040002e1345060103038015502c03640e08042982880c10f044c1d40c504100c90b4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 782828812 1250 782827562 782827583
    0x1d09060c160b010b03090c0301050105060a03230108031207081018060503161502070e0a0b010e09090a02013f0b030a060209011206151101020f0d2a080c07060207 71
    0x40031807480c000345d4440c00c040d40aa95400b02100200340c00c0710800d0055a030301c444140140060309110798400d80000000000d116804032884030030a0b0171132403d03407207412240e000142d041c26007507010350b1603900060582095013590500e102c111514461602900800d802481e0800e581c0c040d881d0015401030034007a09550000c030000654002519090080d814290004540004034620000351001103a458541110450f01c48003118006009008021410050a2071070b95500350b0750511401e0244401800610b001110380c40098200c40ba050039203140341c0600f071102543c0e042201441201c2d1080c4807040d00c000000d52485800508074245050782610440109104000c400c1d4020710501c2400d0700c40b90040d0081403071400940300c590040b006070413680c1c051100014003800c14465940c2d00d22001500340068150748421740d800c18260282c00540f60f40788403403040b42e60452181d0401c1480c01c0c10b8001c83c007045010b081400c001c4c04400c18018001200018410654103031035a81e684010f4046c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 782830062 1250 782828812 782828819
    0x10b04060806011a040e04030f020102120c0c1612062c1f0603020607020d020d1407170606010203121306110306010807170615040306090602041d09060c160b01 70
    0x9607184000d025503000c3c0a000703e40c18003004c0011040d60115503c00f130030880240d4031540c080781c0c040ca000304c5ca50700359902800807145011610f01d1262080400003041610741f084241c0d6246000300760710709000c0601a900c0b040c0440c00c0701100c00043e95400c0100810300d600c92850300e40001c800500040b411180081420020007408901071100741007540d4042c00205c0051583c204407078040c40008e6021108001400040c20100b520700c0c1c0580c0010480c80341070340e40d902c9414170560306c0742c0030346205c0e001118240b007000f400040300700013007607188010890362030034000203941d03072045005030200100304400041540c0304040c600c903086a0301072014011070302e000c45500055081680d00502242040d8000760109106280c2422214403004011801e03071111000e006903005030401c030510324101007101102040306809079803a001d100d80070060381c1c0e501c0d040c079803209040b1000103030080d140c500051204681d0001462900a40f040040c180d480c00d8051412035600050407004202140c6940000b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 782831312 1250 782830062 782830079
    0x11b08070f0501151a030429042d020a0e06060408011811010c0203061524120105060313030f032304020f01030c050d0c02030c060108010911060903031b010b0406 71
    0x442c0c1c0b107000c2482c4c4d4128949030b641114030b480020204907103401c02400090f000c90110701e5420507480ba6101d1180110041c2c0000c2001c007401100c0544078004000c003c1c18141b1480d00703c10007070200c0e0a5851140c5016030b800501200d2139071042c00d1076941d00c140420386a42c0c40d501200e000b0642c0701c0c002c02c08507810840200340c65002d62010f03218170000d194003408550054015994a035030080203085195200d0b1520b4910440034100b0a030010b80c3c254280b4910b401c0d040c13500140c0c1c520f4002e90391700d4090001c080081d1010580005000d0304050040c00148174856080d0100c50764141040b035181c0e200094110002c10441407151034001d51100e035580c515211003070090140d802900c103907200304240d00054007919104142900001c2c1c042201304514203060b0b0001c4001c01d210300c15249000c401049192414001380c00100383d0ba50341d4030301402000f03000201501c060100b0369516050144450019449025800c40c44a44880e083c0504007900800c0d4811721905900030001c0100607102e074280e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 782832562 1250 782831312 782831321
    0x21204230712020a1202010509040f0e0307030801080616020d08070c0f0b0a0c0e0105090f130c050307020106060201090f060f0e030c010b011815050d060f180c0e011b08070f0501 78
    0x59000d44003a400100e030070b01c040c80059a1054060710341d236103020086c405000041c480514003045070f41c1c0d80c0750f502d054210180b00400995000741d80d00d283c59414031001074140500680088610041440201c11850f0040b4080d11481503e00f006066690b400340c0503a1017403030064004081e8041280d0010401040a04c068000d04214a0400001c03503d10015511980074000503804a581071201c0d280d1481c025540100c3c002c006040c40401c400a6003281c3d06403400801c1c0000843c1011040055481d42482900010840c070b100a03c43e0b58041c0c0c845092060b2040030140c056902d5295103c1030802603000941c8064002c001c403a80c0750525000301c0e008004120020340040c00300e00088040c0003d012210003501c65040d00840034040300001a682d59122081e980c690300d4413a280041d0108110702540c0051814000b00c0c0b0201c1d00013040c034012240c444100c10b082c400201c2e46100380307913413281030560114a02151268103d503079061a4555000d4403800524a076001d40b010410804103400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 782833812 1250 782832562 782832599
    0x40321020d0e0c0108131505070305041b0609061b14060601020d1404210602040e16053402040f02090108010b070305220e07020f0708010212042307 65
    0x82040340c50000142d0325140c0508000560010740a0408220503060744034541c02820310680462004112080454040d58011194032010a41d61300801041c00b4090707520904500c2d00c03030074407110513040203005441d00341c0ca40200070800141100382d421241c05942d100302801c0d0402401c07464a0402440350303030746040498641e0700500649a04042e01d41c054200314a42440b02c0c1c050509190400d000c4000e014040c6c04408100441d0648020200f00148018409040c210008007071a207010410140303007245110403a000c11100b00180358200c01d03520602a02c00c500c1e81c1c0d80000e080d0740c0c20b01c01051041030f400082d51240c604200340190035016230040810f09803c2e00d90440c1c60703903520403644943c0200030019000c50010410840d140402c0030100d1681e003860610340d04000d455100307450701d03038108661000159100d40d10070405032204110007001884410020b51801242c9401148012005003008101045481e609800d903000e80c24120320b21103600c03003120b42c2c1a945140360402c203071030b505 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 782835062 1250 782833812 782833837
    0x403200604050717030408100e071701090c061103070f0302211306090f270608030306180105030706081801020a080711010b090c0306030c1002010c020f0a1a04032102 73
    0x5a60418281c800300540382187d402e10003800d000c50441000c280a4020030341a070601d40549507001c1800741d441c0840440c1005c0007400000c1e039a01902c0d1084442000340c000b032061100b250709229030040000115500301d90700c4241110701400600e07060303180007016601e18000310020b1140391000f66409002d0f00580480e900f1950220b9030750041501c5207101c0d405804406042c011050003040b04c40d1400b100941e800000d40182d031090443d01400b1607a04d0340001c82c1c41c0d080042480450f140c4414440811003d000c41d020803035140c000000e541d04c0751449058144410840080c0c40c0700211b0a154400481c01c0009650fa0500e4980061075000f003160110003142c07034071040c1855482d0500c03a068003c0342c082c03c910040e8541101c1d03040350f608020034940e414450a0010411512082c00d204101d01d1103800100314800d680c00c000c0e0601144041d003088a5009941400c081804d203c8043c041142903404000140c130740342012243c0c8003031003483c0358402a01c80c4001e44060302d40e9004010054280307 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 782836312 1250 782835062 782835089
    0x41a030105011202060403120c02060d0e0c18070f200a12020304180b040e01090615090209031905100608150916031e0b130b06090c0304032006040507 66
    0x481d00c240c0301800c0c0440280d0000c0b0180010301c0042c8c1080c0e209510b0441600700b80b4990034056000803002c0e4007005641100030f48600d001c00408004101d00c3d4200001100e00885500380e1406140c1060703001400c01c000c220220540c0c40025020300ea5410908040041e0600840900c14105a88000e0017a0031640060b251440071409072001c42500d043c0c8180354a60003081103c2c100d0701001c2c1c07040101080d40039a640804400d074140c24450500894400c407804140c040d03c3e1604180c020060754050408580100191121b540d400301d4ad9010b454880c1d144921103900c981810341c9002448446000303180d00c2c0c01e00100303603100009403003580a0f070f0721910408280d9a03c0d2a140d2950803205072149a04800722042c0300151002c01300070910710b5484480c0410075002c0e1600c400f050401d45400400461a031510b2080c8400c8041d9140d000303505542084250410a00d603520301d200080010b4200700b8071102800c081c04002010107444800b00013122010305043c18603a4541010384595000c01a10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 782837562 1250 782836312 782836319
    0x200310090906020301240801140a08160e09010905210f07060203090615010c0311031908090714060307050f04090f0f14090a20040c0512010b121f05041a03010501 71
    0xd10003c00440101d0754898007141d10f8103031745009803102070700b4050384007541c0040410b2f0803030100700c3c0301c0f8004102ea014032280c03464a001100711807006403503244142d04205245000ca14006104103c1000c00c0c5901064502d00d22a8040c25003d000446010300707200141e0304041c84110740107103019101c41e03000e44881e920307040b28000c1030f02c900d07030105400305440741326045c0802e014208000035100c283c810741e4501400710f01020a0f40544030000700224070341740709201d00c1440800c8180c004c0c10081e00b00e400e580f11404002111400024101002c00c440041c400311014070ba4002d0724010030403c0020b00c03604100418810290050082c0c140040e49000c0c000d2405004800101d4001d0b00b02344068158030405440c0d0001001c124684840c078023641d01e408080e95121403183c02c4201499a03100c6171241c8801b440c41d00c411506900034000b00c0340a001b0050f0b2660b031458080d400200d5a041e02098801b2a501c21051b174006e640025841172034040d200c1e1922a0041548105100031002082a44e0700e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 782838812 1250 782837562 782837609
    0x30f0f0d030b090402040209030a080a031a040c02120a0908060403080a200406050a02070806010f0303140a020712060e070f08010c1b0204090f150c090801200310090906020301 77
    0x10940c2d590781d01003c1d601c0468003600302036008140846024080d41c0c3c14404ca80c64900499001c2003000340000d9a5a0810865145011494242a008903010700034007800020003980c60f07540646548840305c0000302d62011600030030f04940100f81c004207880345850a1704000d0a01001150710001c214200001e052082c030740403420010b680ca0b0a250303070b400e0a040142c11146600020b4098095214070500440e07030314070401543d40240300401155900e03900394a401801d001d507106100100c01010f20210341c80540224041e01543e43e0039040d007124115504009002d462081130304c02484c052000041060745400e00b1031400d88505900074403038005a404100c0301003000040d41e03495100140500340051400b038000d030110b140584081c201e60303450b81d11185104000c401e4481d02075540c45440301d1000303030456416001002c004000300403a00b00800006681c16840c60303100c5074006c0001c0092406150640a8006441403243c20088182d5a2810030000d5201b801000054009040c10140031344 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 782840062 1250 782838812 782838821
    0x6060201091208070c20030d0f1b06140f0103020a12031b061103090c01090e0103020d02240d0609050a09080d0c051b0102270d030e040605030f0f0d03 66
    0x1a8000c0005580c0182040300303c507402d00140040e001c00c012001504080303810080c907180d40305850041c49001056180401d4070b020f9410030f00c18103015002030a60700684c0c00981c80c20030b4000c4000c40b00b08400c0949800b1000b1f00c1456100302510740c81c142131105201c0c541c0842c0341640d20aa0b0b030103540c84d403030320405240c56443c048020006003100000d10250382c485050903110520504c070100303002c80e00f170b00840030b660402c4503c404141c0c0048200540c0d90b9200c0070842c0208080c0907606400d50454010800c0c556407000042e00174a000c0c101c3c1d16214038010308001142c0841030740c1e261a9024501104080e00c0c5900c2403020440c02e02010a0154074a072007035205140d03200722110310b007000c1d420400010703101c03452008050020a00211004040884803820b01ca80030400069a45c18410f003500b4402d04510803100005040101141180d00ea06002380112509410840003200c654400a400341099030011303605405000e406101c950130000c2c814042d400b5250584000c103080f0401101241d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 782841312 1250 782840062 782840081
    0xb090a0b06031f0915140f0c1e18030d0c062304240c031d0705030d052809320103090201050d050f0a0f02030f040308060102030d0504080d06060201 65
    0x10000f0389000075490002d80c04002018800c48840c00d491115042d8001100c01605d00700c4031441640e03041280030941d0840030344d0300041d400742d01410080b40d190036800545010004050748040013031020003c428918588040340c8004046400c030071010b420040540049420441c0d0a40c02c014600750310303043c00c01d503201c80c0c4990381010031000c2c0d0b2240c8031850042e0040300008900311040c504510400d8090240517915001610007082180326152010014201d0801030951900301c88014400d0380d0300482c4441000c13981c0d00c1c4c02a182c1898041c0403520402c1c010602e240b05140321181c01d034264000c010340d001c80b109060038100e02c0744102d00c01810034480850f50426203181d88983c011035800307a0301140d1158010701d8440c2c1404a5004140200c41e401e40324482000e424004101002ca054042d415004661800035400e42c1014600000c44040142008090043d07801c00603546034401c0041d2170244180400501c03160510703003400c58580d4030250004d1081c0c0d06020021940600500609041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 782842562 1250 782841312 782841343
    0xd0c03050112110d050f030310120213050c040e01080a03110d051e0f03132607060c030209150703090b040602031b1e100c09031e0f0b090a0b0603 64
    0x12035640c1d0f6660400200210040d51282011600340f0100308200442501034051900641d41d9003400710001400b01040d80c810113004510b201401c0c01621080c00d840d082d1050315801140313688901808100f24020390304231003445000f00000141141c40001c02c0140c0c0c0d800f0341c40305401001910615034540200c1d00e1000040780c1d04000388d00801c1b00c5e642e407501982d040040d400e410040b44100c031000683c02030351541c030021b0440440030207002d125544481c00f0120700905c8659244259440c520300e000344180034002c2a03035140080d4446000380c04a0786086802040010310040580407082d441c0c1002d038080d000500014400b05518180a04881c107440e0550020f5051480c2500b184080310300700040c80d01c02d8000c6412140609c101100d00c1200f9840100141c18042c500c400410105c030330b003c044404101a41c01c04001295503542d005910b04011400044648003900701102d421603a180c0003003541e0010810000b00000c04140c042c445403040000710700c0e5888540400d95200b08400a1004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 782843812 1250 782842562 782842589
    0x2f25020a061803060504080901080907052b0203070b0d0f020307050304120c24150609050126131a062d030f0d080a0c1202160204110d0c030501 63
    0x450080da03002d140d0b1580440c40c81d4005850341d0300c040c10b444003910215040040400d0025056070000c020316440b1036410020042d10b403a04001540007030020101e580d06400340d01c0300101500040b400b6008042d0082c013159481030b41c41005030256403040d0f2001803c1380c90404150210700c070600890740941c400d42c0c1c03031900b0354585c3e4840300707a8601203c03484c1e0144001060740b8400181c0d03d941980ca00101c4810705001e1440030031008059800a020b24492680307049820b001c1c03035030454501e005894007868013880850710000c0c0100305482c8902082d60312a0300d001000502c01c4281c900c4e06580d0f11036034201d0781580b04103511729103940c005d441c900c2c1e0000810360981440c0703180a40c10329281d00c00715128207122078014042400c0a4580e40000155040743c5030444080d900148415008198001e0400c034110404000510034007001000b403412540002d10b01400c08115195410525002070081003030120ba00c08000b4943d0004409481090070400c035110303602c1c000e218135030490314251081c22 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 782845062 1250 782843812 782843819
    0x620070f090b0409020306070e03070e0c0f03040c18090c08062418040c1403031303031d100e0907090807051201110c060712060311042f25020a 63
    0x101501d5800c040507003151350340030701401699013000000d0182d82c10352150b002d0545400d00380350825000b50480560600f091080c81480c4c080d110458101034181060f05841391590710303013028184903c0c1d01001c3d01e50701e0040c08405813280346d44070348102d91041205480042e070b41c164641d2540c0044035406c403000c0140501400d1138000c4440e03121039600c0200b40f08051081c45485045000003039505807100b00e000102441030401809a0b105201c00840045003840c8994201c490900c5203400b0040400400d840c910b1358100404021310700c280001441007446000420001700440035245402c0c1c0701d40c14100104d289240200300181c10341d1900005082100d0401c1c05120424000100d245065035840000044100045001d0301024442c0e002600c114100340c0c40007080070350606c04001c2018540303102000020781050900443e02400d90303020603013003806885442c1c095401082c00030b000d01111861035490710910010107c3d424107003203842000340345003101c0040d40b60410009401804140c000d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 782846312 1250 782845062 782845079
    0x170108240115110c03030a030f0506121e2409151515070804080a0c0803090607260c0706081e010b0708160c060e01181203180620070f 59
    0x40107080703208000c40f10000c00e41130100c5e10350b0744207201d207000203665401c0c5d40d01120858001ca0b80c00c01d8040707981600142c150b59034135488036000c40c41c1040c08040c40b40d0302c002c10301d0103200c400041b22003c0000410342215682c842c4240c50100c542c40c03058042c0807030300580c0100742d40d40c0718014805e98039070040d004824006d1007d0740c40204007800c02d1480600c800d0f800161b03800010005082e4240c05030820720614904090818643e0304007818035081805000c0c41516000d09989055401440482484000003c03081c00700d0402c0341041180c0c000000d2220781ca070000510302c0101c1d8980e6688410660381ca0502008001c00504040c00700c102c40801040000c50881c0030b02699070140340c0680c508000e40e190034882641024080303901e4940641304000c8960450243d130200b030300030700b010b900e90901c4244111240295004842c80d05240400d0101818414442001c00c4410480034803203d60b12410050f02d0030100041c01e80c140315030070f000032942140c00300d007040c00c444001d41242d18050401001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 782847562 1250 782846312 782846327
    0x60b091c0b18071a040302150a1b0f060c021c050309030f1e041202090604150504020f0705010203010f080708150a05040821180102070302030f03040201170108240115 73
    0x2e200b42c1c4511000811458010200340304140b0400e0341ca80d81d15851441402003004890000c01380000041c440031112980210507500d84074000c40035104640c81d946402204442203160182440c1e2070900080407460300054401506042c00e40d82c038009031702450040ba5188411642182113030800d01000c003e41046102821a40300303881c108888681030144400450742141c1d011030309000c080084041581082e0f03841c0c94200307005075020301c19010803410301c14011001b40301c0d0300e0207a640000e014480000104c192b400850f80b08000750342d0b950303544002c020019024010084c00b402b550714001008000021a007a10100a902003c041d50341c0021540043c80d00800c01e039070105042000000c20304159840003181308916401c410301e400e05525403580138414407020070311a84100014070210342c00005070b42840c03844403d03455486da554070049a01d00c4032104086800190b00b000405c1c421720125a017540c204400b0140c01c0c0c2c071114214140d141c107400784140000e00e51840351852a451260a5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 782848812 1250 782847562 782847601
    0xa0618181209080a060213050a1212020102090402040801020706060504090201091e1a3a0b0d020409051005130201090605070629030f0c09061210060b091c0b 69
    0x906030300302996004030f142850109201180c445600040b0341142d1101d004244e80906800e07141e41c064681490540c4c1501c0d042088043e20a4410711502003406100350103c5102c160050310075510fa542c2c40da40c031343c003139001107100301c2e44981081c0010aa40c2003c2c07140c614480e030165904c0080f01c0c5080d550204120381899011100001d40303002243c800c2d900c01d8908004844d0100e000e035102500300d02c0c0f2640341c21010011000081006c2c0f10300354880120005440003948000c005007000081c40040c225060720350b00290004d04140004050010200b01f200e00c810101d94244000d6981035840381c80b051040c0e20081c042044040309003d0a0310802c0a092400c0c4a1100021000c0000440c400000410b146042040011034103010050406016076500b00b4688001000c0c1c5140c02c000040801900504850240c0ba6400e40c000703410740c080066841c21038070800100525030300d44170710541a03844159030074042c0c02d251084009a801800c4010b044540146600c1081e4940e01401220741c4607046 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 782850062 1250 782848812 782848817
    0x60402010c0f030c0b270703050d03020f09041d0d0809030d0507020a020306090d02120309100903120612020909030a080a0e1615020d08070903020f060d050a06181812 73
    0x41e2040004104040780381c05401c48000001130118204410203030101c00c80c00010154000f11f1081000403400502c1200340c03800c07420051303100c9403208504041802204019540a400d050110324400403880d11120400303141c00070380340d411403103075400d54280a00b51400099a807007048040b60354000c95101c0ea421040741d03c11303201041c1581d000203107007110a580b10001078004034040c0ba19942c041041c5004000c2c907011807030440c84c100342d4031a100d0000201e4141c4250f107600502c000c061150f8154905200c265404021b0b00d6110400c00d0462540302108038020b6040c034000c07d40e0000c0c00400d5070b800c040382d40c0d42d0040644e60703070341042c01409a0700b4800d4140d21450721b282055007100300340c00340070700b081c82207040d403981030400001d14110200342101e052140d40c5040c064015404401501a241c0654021040b1441c42d030200d1a1441a229105491352600c010701c90f0411a60704141c04030303040e503001e500b0350b0b016801d410811520070503041088500b60460600c005101070000c44010030860 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 782851312 1250 782850062 782850077
    0xc0625030f09060e06101a160c0b03040311071706071d06041404050a2c0a1a040c08070605040e04080c01020301180e010605061c0b030115090b03060402010c0f03 71
    0x182e4034071081d07900f80540d0700059041142000728110703481801d000244104188487d0080b4403031a289018414010554810201500c1301c00501045c1c2c00140010422a0700f01952442c003814000c0480c0c1c0c8100300c4113a00d0254840008010031300484c51a0100c5c801c4020f400e41d03460700075082d1042a101a90319546440700680030800e503807640050300c0140358007c0d2812a24412a003000101d0b4002000444a90b2901034003212264543c8a98080850301b40050f865402101c0500380c94000c80c010002c1014081000b00030b0302000924001d40200e00ca005c5008a060b00d800e1401d4079800b180c02440001041400208501c204030381a0300d80140c058014645440c0140c0b80ca20309983c801d0700b001b03181d8114150f01008038500f0380300e0955803294000c000c01100303041400103100e51094031102c5100000205001c021000f1540c0588103012000b0000c003d400011542c0c0781d280c0d03451b40700310760f0302600d4501c42d1180c905021a81d2031080b94165100f04441032940d40b541c1007840e01000036802c000f1030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 782852562 1250 782851312 782851331
    0x40c06050928090501051f1427030d020727090605150112152709120906030216081303060f1b021c030e010902090a020c0625030f 57
    0xb003101c00d440c0500180346030b50740c141408029425100180c2c460360241103d14189500d0340ca002662681500040ca0300f180c0386034640311201c405000f0380ca0002400c0f18852818450418441030000301c3c010198191000d138201c066003a601c0d18202d100d1041854011168141030100a04860b080c01c4203400c00003070440443d0715000c0032540103c81c403520400d8081d403814095030700b00c950020b1081c88041d0512900c0d01e02048172051000038400c3c86007044040e0340000d0034600c0c1d2400b00304120340c54402040b81614a00740104012038800600c40420059400071a4051290084070307414050039031031004000780e13551081c00e1035002c850b1012950700c08030f00c00300000c1c8d6203000340e0200840c4070502044c1401090420590014400400400d41d03101c4409041c10f0748000c5c0d5114116003440c10000b07603040002c8030781c9002d41a40c1c44002c0d0300400030400c001041240c3d501501031500d40c0d00454042d669140400302e40190f0200a800b0040d8080780303c94800352094128003040c0b02c181d000441c80456 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 782853812 1250 782852562 782852599
    0x105010f020f030705030a1808032a060907050103050c070209060f03120301120c0609030b040f2301020c010b0f0a030b041a0412020105060f0d060b0d020d05061806040c060509 77
    0x4103031401c48142d000040c7c41041145e01c24070041d066600845e1000c4128901403000c0e55901c2044182c0c2522501051000c4d0041001078120300b20709808015a0101d01d0621034041d107a1000340904c80c0802c1c5804042035650004100f41c85030250702401c680030341d459140c01c00c0010808100000c0d4540300f00c1d2010ba490002200240d8001c0c548002480c001400e1441c10001c59182c41d0800700411507030100410101e00c40040081d0030942000c04030f4a00040c0d400c04800845034410701241c00a5100155094148150300500101c020500200700c402041001c0120031861440340719031046100f403050021482c015009504103206202243e003a503000b030f031012511102150f041e18400703c120f400f810701c20340a005080d80480c0803283c888003040030100050120182c4000a82401e654a0f1440c0542e180e0303000386c10540ea0003c15001d0840c4491800701d540710011144015498042807914031004000030351306001d00e90040007104400c5c100b0004450716004000000e50055002c101c68101c3d05 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 782855062 1250 782853812 782853817
    0x1203040609140d02211c150b180405060f0105030a0f050103030e1305240a0803070b090706020340030b0714130e041a010b300105010f020f03 62
    0x34030a0010f0f101c40700550001038240b0010702c1c6203464104c48038041581c1481c0740c600b02c41640c226060744003071030700b00d0b101007000401038245a102140106213000c41c8010501000c4c1201c00c400a15540d41001d103042070005540b4180c0c0c4c0c9541056a09541c46510f600036006036034050400c140003e0100b0340403402c0010b4520030703407050f40403440c4995030908504050740c00e890030b150341e44c43c140124104400c10401c0e006c1c1106180b44001952100520607980b0040070000811f15503003200e4440405041c910350100d0103860114403841114400201c1500100640306456600001c0701103180c00e0300303421441802e0185000a42c21500304000e5031115900040d0b201650041007103070010720b00001c0180101c17280c150448440d01023400840007441200d084003083d1001140e140d4a03548035072504505442c9280030807138032018030390008101c0061013009040b214569000b8203080300c03401d01400c112000c11010b4146510080c000510595000d125a4422800c02e03104461003001e840356070b0f60854 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 782856312 1250 782855062 782855093
    0x9100f050c060a090308070806010f0f090e0c0406090501110d0e06190309110a0f09110f030403020328120b030f011104050a060207080d030507020313060c060c0509031203040609 78
    0x7076a0341c0f20341c4c05040c2d0010506500002a05200e103450030700b00b0000e050321420040d804200b107444400c00140310711400b4070200070300c071420001516040c0841e1440c1c0c3e5821038042e03000000c000010024040d84200c00702107600191101400c9110025101215103640d6016255040300c1e00f0001e01038016038210303d00800400e5980d000800c02032518100707a8540e8105074051180041354400c1c8910034a41c0040300885220321b800080119281c8105141405a118441e804040c04020441490b030080002e03c082030000341114640d078045500f03c560304218803420340000b05200a44a1181c80b16840900300e50741c010f0482e5800e0b110340700443d027550300d906a5041b24403004101000b5078200f0351000300203030030b036400940351043c100046142c1c0d4105514158080544542c0480c1c0498000d10844181c03136025481010b20030340780c07100030300300d01c404c944121116440c00140c0c03902144541c3c2982d81041e0f004010300b41000b0041d590054540021b4006d6460994030040c0d0030014130800e0074001d95 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 782857562 1250 782856312 782856331
    0x40e0709120605060a0e150103021c0606050712030c1d010e0406090b040b100e100c0b0c03040b0f0910090305121302011116030f0809030105010b04050f0609100f050c06 74
    0x49207850818406901c4030b686c0b1030300b1940000424090100545c80350390340c00500c203203001610381d203000a400b00c61620003108400641c3c43c01c04003090582d400740081000714001c49014000490500d8220210380c4000e03251700c0054001071260724814401c4115a203172050515003501c181110200180441d107a0ba407181010350381d00c107144901d900f00b6000302200046d0451794408903141901000d03100c044070a981d5846080366100c0c0c10441030003041500510b40e0000344c4042e9504e0600c60740d00180d402a00c080d2644403105001840400302c040c0340d03a1007441001b0241c500030780c007195880702600c5021411400c3c00f10038440400c403894801e086034841e24130b110628a07000494000941070310140b03850810035400811543c00710340d5400040b00100c07a800080780c00021012b00b402ca049c0c3c02480303884d95040d42043d0001910724030087c06401551030880d45082c541510f0001c010881c0720345080180c20104002ea039860160081d0610302001d18581011407030044036500c080c0c141441190310b00b01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 782858812 1250 782857562 782857571
    0xa0c1401120b06070f170c0105070e040c1e05040909061506090308040e06010504080a0c1a2a030714060106020d09120b04170409091511040e07091206 66
    0x69a40e8415004500030366400c2081000c00d420001140c800d1143d45005000155005c03040010001580080c907914800e02c0c0b00141c82d48150100c02c2d010b00019a0f10000145040c011a815480c0134427444665100c0c0d0346411945040c0096030681e6072101c007107002c052003004c0c40005052021030054500703070b500c100000541c07840300031611144941070317810000801540f000240001820341c411102580e100e0390400c42c1c1560f9890040b26544036a40000c159070050515213010402120100300903121b07200f80030440c3d5080380029084501401d42082c503500e940b01c1c0700240301e14840fa0406a0824850203680c5448601d445101001d4079600070b00c0c0c3d09078061001041819818404201413109a2034412440352400780804104c0380001c070080c0c10502050041400c000c24010140c0070039400f200c83d40c2d16a6664003440c0014008268243c60320314103101304c1603c1c10740030f00c07910151050b510040c1e400c040c00c0070602d02080030001e00310428804604008680c4130310382900460081c4c8a02004103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 782860062 1250 782858812 782858849
    0xa0c082205030f0f1e010603150b0406060f14130b131a0406120b0a0504060b090f090f01060f12050a0605120703080a0f0c0f26040f06110a0c 62
    0x1440d2941605100000c4d402180400e0482c50011880041007160385111104404419a00d5030041c00076610081ca43e100089049c1c0b10760746c0c05d8020240690f000c95080041a907200390613110301000e400440c1c001030743c4911f410300000020020b002c1d5183c804003024100d5484810441281d80503d51482e4600b182041c20000c103580d03401c00d1042000c904c40700c141020702d130200240030044050002409180c89103150900380e01c5400314038000b040300074410b201c80c0341e80340100102279100c002c14130700a9400307010b03001c1c035801c03d0b4030014050380301c1074000c845503840e1241c102e900c0c00490081104001d184140a0071200c40c0e40590303802555220070001b0060314100401c0b09440c201c40c80807001e500811401c02c0803403051010340704010f140f41000024480310b54800c6030703a100c032441f005086810b42c404200600c00c228642c02445d41000480102400803203485010310300503031040e48011021224113120302c606c102c1500821030b09240803207c440003140d031040054402a084148124400344958 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 782861312 1250 782860062 782860069
    0xf060c071d16031a041a030a060c0e0103061a0a0507050a0308150d0f11010207050a12020918061311030d0807020d260403090b070b07080c0903030a0c082205 69
    0x1402c030214600b810403001c5050f100100702c002c2d520f10a00e10480c0d403003000d00c82c41202c094051192801c001d050b00d00740601c501e4620020320420b424040010b0317040001200720750191003007a0650340b004c05c68a00c50520382d00b04910590142c64000100b0000303102440005004011421087d8826141d40f07140c0d26000200e00d40141f00d601c002031050788407101e1513002c03555900c06980e005400c4209002009402c00050b460503449500c900d07008640c0d540d0001e01c200b43c000480984a1080303400c20010f489484d000c1c00b699600342200d44140d0048030200b1034060200620402403440340ca8019400400c07540000d00342919001c0c058041107058080000740d542c1408204200310860401c40e1201e8903907035900d00068014a4103254940003807020506242c083d004c0743c0004c00d03800000c11b9030b0700c86901e0b0184100780251140340c0804d0390380c0c0108080764102c0044e0b4991082c064015070501d40c00c4c100454000d03030f2131318059901c10320400c80f0340c29034000d140680600c114100544003665241c481803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 782862562 1250 782861312 782861341
    0x41e080c100516051e24010510030e0c0607050a0b07020d0c0b0c040306020a0f0e01020c010806060a0e0405010602010204230a05060c01060902030f0a1a0f060c071d 72
    0x425105121010901c0c0c0c09680080640d18581c0640c614031010364280c1c5000d0b4502a01c0c1880c1c042c805030808842820794400140e101c024500031185001400f0102c0603000807080280559980000542c201d8001248240e01240c0b02e86502011280302c1c1401c0c2010500c45d9000810030349441d0050210342051000a034140c0d138115101d840140848801120010040104960010005a0880040703035014010005440286130814011990717034008100203003803130042c4100b840100385202c1c8002c8481d8000702e20186030102c1a102c4500300d5844200304082a07006044510034012604080340313494440713100300b80c044c1c01c0700d400050343d0368107048403140100e0040b41c503004820420700e054002038452103a090211079003660f50b03907115102c11f2020ba014042ea07822211000344048100300d0052800c210250145400000810201c2030001500d070341c0030110103880c0e0700082044245642e03030510a004100e6000b004080e030b14119280c0c41c02c0d180c070b0400090075060700c03070b20303207043c800d054118940 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 782863812 1250 782862562 782862583
    0x405100e0915222915030f010905090109050f011a0f030312091213030c0b0304030f0f02070503070e040303060b130302090a0e010e060a0510050f06090303041e08 71
    0xc0c1c1c1002d81c1400005042905100c080b8600e02102c84041c0910f081d05400402d118614042603120030042d5081e078580000b50580001c0c481d940a11400c50a4411507085a004505094498843e83e0800c0001c1014220240c003107070040d07681d40c03606408510300703200d805e1150801c803001060024420840f00c500c11040c030011446004510cc6551065030700004407982104881030441c556078800c0016820024440940700e100403002440360b24060380d0040c080103903072041d915120904c2c0c803202ea14010307010031a0024085200d030310b09410154019004c644442c041403048440c550b440320302007030078030010340d2108112081203428801096098040c020180014203402802e10240da1070101a5145912010b03004401580c0070458460305600440000c2d041c0d0402481005400c03c61a95150800c482000e401c9251030045042460b84070000012a00020710090407455050b04001c0c0c0c56200144559140c40100800211150f40c440e41905150303040107055522807818002d141001207409 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 782865062 1250 782863812 782863831
    0x706030510051e011b12031103040b28090804080c04021306050703030b0a06080a0507030c020a171b030301030309060810031b0b0d1e0b22020405100e09 67
    0x1420700c0662100f0b8030078083c8210b1000700b8059070502000507502401c1d90003010680040c0540b0000070720900d00081e480300c403081da400b00040c0d21078840044a600041e903004040343c0c0e071350303010400c080245003548102c000303580c4485410312910303240441205d10403c81215004004101000760302001e02c1603010900c000c0d202545030900513817202000890078010541448400b04001007070500c640d2200c000040040c01e20b41230700352111000703080c58808460404d001810400040c403158401d004041a03a405500100081c80896980c240c05026003181051440341c00d01c0130b59030030540d900c025001c04000a0166580303505505004040300e0710754102e401400784c80024801e2038a2419103000490382c000f2a41c60680700103000c0c0020f0740702c050b0f10102100d1004601c10500000c240d01845a40454403500070b810094102c2031401d8074040d0040c40c0d440602c07500881000b021242c6951145094202c0040c500764807032000402000040014500044182000c1c072240d00742000c2054120700c418 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 782866312 1250 782865062 782865091
    0x5180f030301050105070803070203160303090203101b03020a0519080417071203050402030a06050108010b040b0a18020a0c060c0c0c060816050901031112160c052a0d030207060305 79
    0x3c40003900b03902c1000c4005100400001c0080e130b02c244280147c800e007142c0e01603019580b103c81d050090203000210fa099200c0d0080c0c0e1580402c02101c6e102c0c0800d021030b002d00a00141c00f581c1030580003034010030207500600c58100005442c04440710345685120b500c580b1440742c941000c0c10241c070510007014400c501130f00108807401c0440c26032180c80c4404407092a01040980d03a510109080c080c1012000300002d0a0000100321a0010b420111807800265001c1010000c80c000b008880c4255101d00050048000d1000140e9849500207085c0c050860608040701719040e51000304a0f5030000b8013400042c0c038400050201700001403800024886454850f80c141020780e08009c012405045010903c54000380c1d810413039000e60842d92030305c010b10a0304c40d10b0742202e015101900908403803001c00c2e1108450240012805040c48040d410740003001000e10482d0340f800c200b64a00042c2c080f800e0083c035249040a144d488aa0001c030840c0300394054910540f6154016068690142c203044100018 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 782867562 1250 782866312 782866319
    0xb0a020a110d0602072406030803010e0402040b0a060203070b0601050a02060f1015020a060b040504170f040506041502010e07181509020a090f0509150f0f0405180f030301 75
    0x4051030000d800c2090107002880d40c0001400d0805094401402c0394008a0524140012100d4030000d000c0f080b40000c00130b001c82c2594904030350340740c040244109402d1006008894040d40c0c1c81c0d5200e44007805c0000c40d84007080006008052a41c00200141d000041c1c080c10001000b110781e401180a081c0035080c6501c030311000e500c0b500004c14400e101d81d1443c0010360751031044041c10008010745101002c00e2108140000d481380e614940595602e0b0400f1312614050805218081c4240d0f000750030f410f07481d111041312100c2c82d44100f0810140c50310901000c030381070342c0c1d5100410040c0038541c6ca208420840040203825601000d8003405c2e40e400109080207100b0b980c1102d40009892007000050307106212540c101c15034410f412420b40b80f031021440d90030b2240c01011034010340301d00345510a646503949040000d101d5044801210070f0b000210701d580d042c10401c892102d100402040d094407510307000085011241c04460550401202c8895007134014030501075103030054035110141d85590705 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 782868812 1250 782867562 782867567
    0x161514010e01230909070501080f040c180e01060b03190504050309040b0406080607020703031403070905060d0e01050f180102070206030c0a17010e040c08191410060f08070b0a 77
    0xc1c148541c002d40e40e03564030488090560080340842c840001400c042c540d040014956a03500d9507402454085088070021500e80008424414401e56000068040c51410181c44045001c1301c940c075030701c0e0300da100c11000c00c17121028000c0d180070302031215596403280741003032245009440580481c400c03503143c40180310100f440401250720b018810f9030041001c01544021130000c1c00700f5030008030940604018404959030105c0c06c00212402035480ba480d030180b40041508504c01910040046501002c1c10055410b02c0006400b195907440000101207003003803002d900b9607a080312100c100303100a07410070464407510500422500540700086060015544c0400c020348801b03411400c00c1d50010174012580c0e442010b41502c0920240041801d0396034919602da14030b9401d50701100d51100d040390200c0d0545000030b0050541c0000108410465215103483c2034501c8408048140d5002c1e02c4107145c0c2ca50194002d04004100032034424410030f2078954074904000c000d4209025011080050140407079 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 782870062 1250 782868812 782868839
    0x70b071b020406030506090c03031602010f030603150b031608100b0a18050403022406010c06020409060b180a260703060c030b01020f1f020309010216151401 69
    0x46682800e11291818400120268220820081d84542404004000c00030701003000d5002c1c01031841100c007010340b1a8100b603100d010310f060a07400319405540203009580f050116009804440c180040c1c4640c80352030300c840080001e40c0015442e500d030322101e0400d040c03c1110f40038084c1d280340085c04c01c60a001c1c007240c0350424010b0111030300d0f0302d8141d990090303503859007850014200c0d000c801c6c80112005403094040c0c40704480c1078001d4014000480d11041d041d212410181844440c089030135520040151051036203138038241e541e00d03070a01c40401c543c03e01e80708413005042c0080c01c258890941a101280c47ca1942e85618061010b4000400201441c500c6d0854030f801c44115040400352240ca03031714036000660b070000e082641410f00402801e0b806034800c005401c020b82c02e84801b04800400d055517002c601c9401d0461441014802e1070190155010b1900703c04031380d00141c5003c622201242c40d80c10324000540341d40074840500715100e4024840e402d0590040c0203001102d42c58040c0541108 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 782871312 1250 782870062 782870071
    0xb090a0635030406020718090213050901140c09040e011103010308070f020301290a051c050106030807050d09080d0c030503130f082502031b011206080c01080c070b 72
    0x1c0c88070344607000e21000761003031614a880c41c0c0c003100c2d20f4542c1c5400084d40da066901c10400407480c840340b0a00e1102d014040e240c4a950040d00004080000c882e0000083c00c00034407205080d5070701d05d08002c1510010540ca4010b00c90388a840380c81d14901d10420045076900e80104503280e14003030341c9455900101c01660304482d004030000c0e4807807165003884041d04640700c0c4003d5043d440c1c8017403d00b05d0889140f590040019450005101030030020900c240394820380642d9900c4000d9070780220841d251000b0041c04141300d640081145996a9500c3e0b01d0740c0c2142c10111505d41100004412980d40012004020044540204030a0714102d00141080c0420b44014007085170020000d03000c3c271010002501071950001c2c4840344088641040041500842e92400085680b8414a007620b1000c0300c40030f1000d078008020340b07002680248001d8400407021001814080060020640000c1c184282001420070102503c811301c4450001082044002c011020380360091083c8400704241014403940f0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 782872562 1250 782871312 782871359
    0x6030209060f150f040906060e1e120303092803171503190308070e183102011727030f0a02070312090308030f0c0702060d0b090a06 58
    0xc0b19000382c0801c842c07040e05803019440040c00105001204001c000400842e0300b408000c00c1030340c1e21282c00b00c1d4901010f081c40b035481810140d100001d480c0700441646090070051110441b5403101c040c1c0b50031500101d40941fa180c01040e03586100480e950004000a114860000d415080c3c0750780207404000c2b4020b800d50b415050340300003659866502480300100c60003c08881c2c0f0320b60103099040d126684003074110700049016011685860241c0300000400600410301202c0c07101d01204400071100082c0304031031217104001007028450450b4124451700344040b80384100c0a141340009420041c03000e011104840c4d081003040030200405540d1755404a409840d8800328010b8400d0034614040c07040c0407490048005000e1013560b0b0002070b600201e0344944200c001144041409845444442c8405040c0315810400211410055418141d2010325080c5241c01d0501c1900810040c0d00f01a00d140105580c6000d220090316102500f15170082c2d1940d020b000c0d89007021080e480010308004c41407031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 782873812 1250 782872562 782872579
    0x8040311040b04090803100602060112020607062021061807020124030c090c0c171c060602010e0a0210031e0908090109170601140d0f030201021c0603020906 69
    0x10395555680102c0d00c0c0d000003d000b40b2840505080ca0b221650090740c04682c0f0300912000042c500340007050290494131040d02800e1064800d4081c05040da11100044446550b02c2c0400790300e500018041c0441d401800412035240c11422290801040f050702012041c11203030410030540c0d503100c0d028101c0c070352601801c644640c0c0f6464400d0340509030b858000c9180e02102c1e40c04081050102c2908011a402465000c402a07074803040c240803902400105d20000e001851500040351070f0a050540d0070040403881c138030380b8450705110a06841c09841c401c00441d111002000215030900800b808850300c0c1740a4041c0c407000760700181d80c483c26810036105143d03c1e03001540078114040484000359000c0c140c24000a403052410b030b20a54405003465010400b101801b103110782688003c1304500c000320008044036400c2507000400aa07403031035001e91014000518000240c8280504040584650000758403000da07006031407105034084046890040c1b03400302c208056950240341580007002500c403401d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 782875062 1250 782873812 782873843
    0x5060a0908120108010c0e120a031404090c1e0305060d120203091507060608160e060a05060c01061404110d0e0a0507030b0402010e0108191d0d120501050d080403 71
    0x141c803401250003080108031614000078015406401890440c940c55448039041c030000020132802141003241540b03d40d0000088030300107402164001c0108000e6000c05090581c0c5a00403c00d454020b041d000000e0558040d0140ba10450000481c0c200c0f51800c1c203000c6480c141011071003400341031002801d2100c8032545110301e18000c1c070895a003501c005d841101c00c010b505076441e40503442403100f02c40c0c03246000030000c0d00240120346d02610900508131340d082c0300e02e000d0785040300d144050a059403000210030009219034070342c0014172902001c0c10022500905d40b00624501450544604d1301031420701e5404030401e0700250440c0d09041172240001211f80c1700305031841c80e10b4098100180148125440803090160500d841807003140f00340d0720421a10440340044520100584490403424007644604609581c03603000061400500d4024445940450150b140b03070043c1004c0000110300e41c0b81104044082601034070303014250985a4040c00310036030307442103860f1055200141c500e00b4201e4084 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 782876312 1250 782875062 782875073
    0x30c010e01110a0c050a0e04030507080c01140424060515030a0603140f060106171303021609140109110412081c060801290d1a01062a05060a09 63
    0x10240c00b262901220950300d500c1c5401d50121400c3d01400d072003003000308400110711600c40000c40c4a9079060362203d081080c00d0740e030740304c1c20740141045d420555200c407449101e400018041510450142c04034148800550031601c640c0754550060b50206800c240b0141314580740c0303010f000c610300543c92409941c0e1351002c404000801d620f0304000d190101c1e03c610801c1307040d40000c5200b0303da880312061340c006903a1180d0035960313141e03030118802101280740009140301094519041c1514002d00689201c0746182d0036240f103015181e0041d45c602030303403106c441d0072031a10b00707405601606c4844801c20002c030180c01c826100f0300842c031580c2c00300b02074207000c00c040204030429107004112008401c0012180012648054002406140700543ca0084841e5902d14003607122000700143c1c910602c00b1440c4407050001416241070180e600130542c03529003c49108514820b4002c00c0030f5503030001085460860765851103096090941031649401200c004a000400c8540e0820582000050314052a1900 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 782877562 1250 782876312 782876327
    0x1181502071e050907032d240f050306010503070b0f070507060909050f042409020307090504020f0a030812180609010605040b10091a041214100b030c010e01 69
    0x404001c0c80703550340b105406100c2d62900420303a07004a400d000740d680d5880c001c030116815444000b0318080203554100070300e000c100c02c0160041090001280351001d00248100d40320a440d2844031000e04444100404851007210030701914044026140d81e500d04400248e884181e030080580d020350000f0b5401c440e6900d0001c07580ca0b560b10600307840c01581e58010150424030700707100340881682004009868240c3d1031203e144070700e6001c1d91220580d00c4c0e0030420f0322003070820584004076655601c0b0700405a5401c204400040282820101e0700b803809106000c201c401e00c1075010300541e00c02e482400055804000c0d00d00c285d41d842181812603481e90131850030a0380040d030b40000c501170101408803200043d0422070a4480980e401d01c0440c00072400e008010300c02d40a1000020000c150030301c014010485c0e040340c10b09241d880d20b418662952100b2900c0842e404d422281404641004203620b041801000c0310304100e0007007005001c51000c00b00340c0726101000894100500c8401104442c1e028212 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 782878812 1250 782877562 782877569
    0xe01090b0705070c06030506061603050904090807140d0804110a0512011b0f020304090b0f040c0c1202011a061605070f0311030c1513030f0f110118150207 68
    0x5a0034040d04194001800c0707a480340307900b903030300d041c0c08800400c09070301901a00d400307001c010340b90500d003007942c9800b00313030408035a10704600300001002070078000d5417180a04d4140d40e00034a00e4550303800c65803a141c09000007042208040c1d41101c5030004c00107820080460340103401413808101d4a0340440003408000c2244c0100394030040d091194466150154404110b003011100c20560000030030b2400d8400182104800005a004200a202c04042034105c0952410060b180c540182c2c440c00c00076003aa55806107330000100e418014009001200051060404143c0000c1086060803060f042c1c100b84080b0401e4040c110006582c13014070a03101c00c6502e0a50820141c0d0100f644030022800c00c07901511040e9080d03684140080c0080c9400705419960501c000c15241000201141008064101c100e208034980030b802c0d80007001c2000d64450020302031003030107411001c014a103001d040c0c1c2001409800d0401802061036800c040f414602c8030144c40065001c0c4080c82e1820404a1901c40c0540 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 782880062 1250 782878812 782878823
    0x380a110f0c011811042414040f060b22050a030b07020a020907020c032109010305090a12090612020a09180f060803031006050f0f21041401150302090a0e0109 69
    0x14200d006020076410921544801100c00b84201d2414444220142c888402c4220007980f1000702000f960100a11f02524044050b1010846012000081081320b040e075100035250003000407072650f1061018895031502c205241d8880103035051402043c12070344140401403080030300401048101d4000c2001081c05075004200703550f546002d020080d200c445c0704065034040e02c0740200c03c035000404904462038500030086e2036420405a04c00440103080043c0c5000498011100c08c00c0108012000307480250a060311100e00b00d900d8540010400c049a40b202070069206020b5140c1042d80714003418101d5500c1004000c44040c54042d89004162600c40c40c0704641c41c1c108005031541011021f180300d189480c1e04d002c110b41e81ca071402c0d6120304c9010a00c118119080100e0300c42524070101414849040b00190708000e280d01c45015200081610b007035071400b00014020b41205400d010340020090040c0664503e0303451540424401d0300060300001881d5110080d500d00300e04250312501125401a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 782881312 1250 782880062 782880101
    0x406140918190b03011406040b0a08070308040f24080613020d1a0307050315090a1202010e07081603030e030f030703120b1c020607380a110f0c01 64
    0x244480c0700306a4080d03001c6039007400b400a089190603c038050304880310981c01d0100e43e07541f604100040078140c0280364011001070000c910f151003041071801079441401255038650600d203111044980c140d100403100d9107000c000095400e004a2840118842d5050400c0a61264000a03000c0e18a02680c000e0562022806514182e17081c1c01080404113220815200d540b00d0340c062503184e0215020304c80c3c06031b2041c044180c0703000101c0c014980c0b1074411016500003401d6a41d0b00c3c070008404a102e0740c0141c1d100c9152045c40401800f44000070a80310703000f09050000b0512001c184510b80c88050309010409003001d01540f024403074a0118400001075980c0c440f034a1902400b0588000b4000c54840c1c5031407000320590901184a50f03078103007051480d4819040550030410140e0160300c040355000503602c544104440c1110320051020004881c1242d110f0301d2a194699031803000b40800c00060515490701c5800055400301d82000e0414a6026a1a8044034032203001d44890801e2200101c00e0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 782882562 1250 782881312 782881321
    0x1120b01030b191a120115051314031009240204090509010c1101020708041a07022e0e06040603090201020715050702040e1b04020a090305030c0307170406140918 71
    0x1420a000540e01050300c43c46010441204401302c40c00358005100d050100c0600601a05c4100100d44901c88020315029140080140b07050503507d400750300008144195980540d01450300307010f0710f441145100c50402c0046040d4445100070a002c3c443c41e05280c0b000e41341e400100d10301c0d4040394050482c4c284e0a00c014204a6600c0c0e0080890340311540c001500b00c04502c43c0100180220390405400c401c5503400c243c14200b90504404104400e03500540b010003500c00162500c00d002c0c66070324603c08883c0900c000c80b10200c11403080340074800c0c081201c800940c80300c40d95000c040d02d043d079540b4a000a5a4516480140e04d080d0a98014aa281c10941c0e44800003680c402c0040054a10954041c400307081a0b10f840e50340c0307021000341c9010070344a02c0d0446260703003015405043d00c0081c520b401c04000383e494881c80d04640c80300f41d640c40076400014541090042c0b0560444400c1d00b2803d44610f81383ca800401448014001c580d40402400000c1e10701c07031507445101c1c1c28182f2000c480d125880703040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 782883812 1250 782882562 782882599
    0x1a1c0215041409070512180c0d080c06060a140108060627090703021e09210d021006120201030504150c18060908060c030a1418013804060b03070503070206060901030201120b01030b 79
    0x4240c080d2f0720a84180000680c481c00c12030a92030445a1040444002040010054400b030a00405258006506101004001c0800401e000681e10002c80e0034100018001c140801150000d091809140c0108880790031400c10110b04209040e944414a8482a4000009141c2244800802e00400d001d10082d107075050040740c1003620030381680854140680e1100030100340d403c0b610411506400c000106c902650194001550181c45404500500c00c101020700301210070b000c2c61071001401400c907030780d81c0804d64881e40300a00f2150034444d031190729190b643c1d941c1e104004d003d151914004008949640c410f60465a0a1041c480c002c480714600000d04a00921600070361040035800c00030303810340d078407218089525007200043c0744504074a07401040442c0c3c20028662290419a2003000154409190700a14019501540c0d0690341e0f0401c641d00034980940070704060303c1654103500410043c0e0308801401600d80c9035800229140101c030005900030034802e10041e801040544101c80c1068 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 782885062 1250 782883812 782883817
    0x9040204020d020406020d090609061d0d0203030a091a12040f030e03150402240406050702030c100e03070b190309061e02030a1a1c0215041409070512180c0d08 70
    0x41f010b80d80d40054658070380040b110008644207040124041c03040d0640c1032181d4102e10b0400c150050541080d034101640842d00e075074061001c00000400b096000d00c110b5180005e81c0d01003500b034400560030441d9445203140035010141005060604141502e4101401031107061780e241001001d45114a142c03810614410300101c8080744600300f505141c84924070749000c1222482c211455441c100b9080c50420340c8d00707a00549060760306102c2c41d200002c040e50f03140300d400e0f525041580c80d0044114400140342c40e0014a4200038420041031028070410007011542044c004854600882d14000e00e0404100601d50610402d1800c1c2c1d4038003000c40d41088640044d8014110400b0070829814080304142a25105100c1281c0c040c52030340040040304405400106560b00061503075070312880000040340c0c1070f48141d210080c8003080b4a00200c0529120540c180e02402c03d08003140b81c000480c051011010004102500d0300c03804010281a84030108449821114098142152001c10b03091004058 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 782886312 1250 782885062 782885083
    0x19030309060329010507021c32070b09010504030c0807170a08030c0f0c1509060106021f0f02040e010f140a0506072018040606050a0303080f0903071208060a06030e0c09040204020d02040602 83
    0x10305109600c21056114201059052a0000ad0120641070045103038069028006d106c0c10450306000c04030108000311100401040a2401080c00c41c0c03810750000c59640c818550500d103508016000804280d081c01180d46c0041007541c0c0d0340c2d5601d00c4480c8452280034100c015281e81c4101001844102c542100041c005c0b09288200c40700350b80d82c0c00382207a44151440a15081d468814441008920035400506401111311400350404d911a4482c185a00d0260700c604428091440304015403d10a030011002e21405c0c1c1d01d89005c58100380c04180d440c03003003c00082c0881919072034400001060303115220f0003d07000b000b0307922442c5c05105418400c070043e40c0603200d0034641140023130286007013105502241d615443e80f450310b50b04d04400001000b00104a42540c1c0030070400c42000600c2850300c41c0c0f4000686d141c0321180e0810509105280c60300750007400601d0701c0c0419003c4c00040004501000b80401c03541c0c40c1a81e03a035440890302900442080009060010a01280560300030a800c40c05 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 782887562 1250 782886312 782886353
    0xd1e0c06090305120603030a020a0318150c0b0a050c04050d150507050d0e0f060402130908030403080f10050f15090402160521090f19030309060329010507021c 70
    0xb03500c44031704040c0c49218000503000503030702002c0c119000038012822818038503542054410410ba03540901c21082504144400004a21000050400c030140c481660405845101005185403d0000c0301c8948a140109445240849507800412030388142100c240d5104480605c1a8108410050290340010f4a0003082e981008161000c5020002c0c0840c5180d84039402003205898540070b21408007040145120850b450343c41d90300100e001d000085025910076501e42255103131804802003507100213001c51440000c1c1802c10411950b0707101380000b0341c3e00201d80e01c035401501d0f903801ca41c00f032040500c225009400480c00c00503901c5981e10b20400180248150b80d503804080d01d814460000807003001401c02c0e828080c2c00d42a04000710f0344001254082c0c01c50340c1d0002182084082030051794411000100c0750f500c103121840e40b60080090200d0340c01c5d050748803c000c2039090b020703c40e4118455410044045800010340d40c605482c513841d160b0000c02140c0700202820703c028803c0c84410b0300350a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 782888812 1250 782887562 782887597
    0x41e021c0504050a080f04030816020a1e0303051809100303020c0306041e020d08120108011a0604090e011e02030103030201060b0715050a0b18180d1e0c06090305 71
    0x22a0070301440d4803640c1e100d0050103903101c03141d81e441e02c0c5070040c00740101104410b00001c070000c0e960000a2007024840d144400040d08035204000b80e10003107402140301c1c1e4403a103000401e903200304600b03071040d40c2e80341c10915110000d180d02c80c4600001c1a08003680400d044040c00f00d101c0101d4412012789010b503095981d155091000d250f95890196001401040c003420011281611441c00145081c801081020010441d4071054929008000c5c0740003a43d95000040000000900c07502c00302184d15152011001d00000000d0018001d501c10a0341e4141c036140d0b061a040400e501c50790500140c8650b040010382c6a0300c810009400c240000c401661a2290205070552080d0680d1080d6a01003d414010303451401544094038024050741d4520b5146c030341c240c1e49991408c84200620382007100c040254600648040341c1d510384003640e01c031b1070340164580c6d0078201d921001801d400041a111900547d4080700220341d44401c10780d000d00214600b64010007015409801071540c002d88000155 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 782890062 1250 782888812 782888857
    0x30809060f0708130609080706020c0c150d020702040b0604170c03011109010302070f080c0a051207020303090d14070b0301090c1d0f060912011d06090714041e02 71
    0x124607000650395940400c1d4204001380d1200401030703084c5283da01c03038107010a402d801c80d51114041e42124904039002d42d0081064803603072108001600e04940c00315216050510140070b1180c40e80300b86a030503d01c8a800145410075910740e50131202081202401d4265120791300c0d1117040091418860550740d90050011100741032905019260402c01000b10480c40c181c40140158025408054100c41d0700140c40740071408199003401910301000040b016190086861510500303180d9071698405011000344502405a2400815584c00c0242a9031461400e0791a04041d004050700d84a41000c0707205011010444c2c1c101c000286040b9189d0510a209030b00031f080080d6800c2ca206080814a4070015100450300c0c6001c803a0510300c018080d02ca240343c00d84a4010841980c02003c07a40c6151f9100c00c03021400c040c18032b8440907008006c1000e001d0700c4c00c1078401d031515081c540c41003810a040750301e285c44003a940d65006000301d0000d9101c0031106107140326218081e42080806002c40600c041010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 782891312 1250 782890062 782890081
    0x207020111010507121a0a0b040f0609030b0f0c0712020114150904150b130c0f14031b0d050a0e0f01090c0b07030203130e0619050d14010b0d03080906 66
    0x11300652164a9109840512800031030040244181c00b0304030108085030316034144c03603007031000c0c01500d0fa03000120740d51820102c2c40c030100d0034190321000400500860030008a000d414403a0b8003c81080540350b079130307120890003151901603204050200d9810180d500c0c40345030154005036842c1020f1000800c1035a810300a80048003030155916040305414001400186a20341c24107250b01078040b00250360885000030500540f00006250042580c81d46c9050080750040582201c0b07015a240c40061600080e8490300e56000281a482d40c0c44510300f900c0b5540d804c288252442e1544c081800c100c181b03040c151160140402c1b03095148680502000c550b040c22041c022112081d40080c01d02c20414540000710703079182e1009a069007103010601201c0280c000c460394141c000d0144030088101c0303043c01f00030002d0404040c40800e031004030f0040100321540301d40307606c0d40c50aa000b00d981000c134204006101d001d80810200c4c558442810a1107800b0190031000c024010140c0404859065880300d00f503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 782892562 1250 782891312 782891321
    0x190e13030219170c0106080c030102070c0b070204090f110a0828141608010e0a1101030b0f090c071109010536010b0315030a02150c0c060304030201020702011101 71
    0x140050700082d038541d000501e101d180c9240d880c85810802800050050750141541040300e41d001c0d2a5101c40082081c01000c100440c25103400b140210b1401440e60b944440c0b80d602071099501d444030129021041d50744035404a02d80e0b6400107276200180c2e00c0d6203001801c5d15540c80304c071840303250359040108803440c3c0020802c0925000c142e000902c001d1481c1c40c2c1d104031580c5041150f4000b651001590031113414000390a10220700d0340344000150901101a095410102009503103a000580c2c00f0042888884102c1c4d1100d400c0c240000c82d002e00e10089106a4400060103402270b1885040c00701c480c1000c0014440503001e06011007401540c0700030080c02c040207104a942c45001b45113042d049442c220040c0c081003540703005000d809041c0240503288180241e005206480010003003042c3c07490b070102c07a0912044200c01600e03041580c5d60014507444000c483c840b52105001c142028950000c200c0074500c2007001b041785403685000c0c50000d000c2d5200032000c900045c0c140c1202c1100c0303e414000d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 782893812 1250 782892562 782892601
    0x71403010632030a0905070924080609060c09010e150a0311030603030301030b0c1b0601140402030702060f10030602130603110703140f07061802190b0711030309190e 73
    0xc1da03d14503144d10400c800079200982069a282c00b07000c90000c1c2c01c0245106400c11908000b05400c0c50603002c040c040c11a80b03641e84000742030703044802089407190010480e960300104101403107031035030740c2040100c2e8400c592010307494204248500170590140786401401442d00d60ba9003e1145004100302480d0b0b5010640f0001c3d019402400140000f071540c5003501d50041c01d1108040c00e184410401c9450801d010001d034030310703030881d000620101c0001004480d200764151015072860230a29002551345100910061000ea05500811426240c0380032140086400180540d1607407031500d6440c80c044954412440070030300e03002ca0415030030940000c0c0c03640310740c140e220268810402c8aa07010b00c0e900c00f0000c400d080504001c41c0001a4140c4038486070042c003118065002c801d284144102103002c1180e00d50001c84014007042660300e59801c840540ba4002c2810743d4125400010070b155000388105a0b0f40415124458440b500010400700f00b22004400c000d005515548903034803008c80001c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 782895062 1250 782893812 782893907
    0x30f16120321090209040b010f05060712080414030f1801030e031603120504030e041d0c270f10091b050c0f010c0e092202090714030106 60
    0x100100260388010459002500711082c0100e4050b50300d5000801c2603004803411501d08907940c00502c6444103100029020b040140c41c540d1030140d542d1510740d02100d034064000100407004002904100030300030201c0300b10800408581d1503034420b078111401a004040140d480c2903040d00030321103a6209028520320000054040c0d8a041c1e101212084103d000d05400d5050048a080700590030b40d843c410148554020707903404a00080007003c01065900c1001d101134085e99121a14000d0003000c1500070b81e1240848000d8600041140102ca0106c1641d2078414290303500020490131824007548103114590088091803c946c0f505031050443d2800039420603a80b844590700321040c1d00450091000c000c4920850b1441082c04014030300b961181e03801c103800100c0e00006003803039041805003150448801c03402d0403600244800038102081c6284c0d8044d10074614000824400740c0920302818814811518080d0b8030368682c800500900780d8030040c101070307000030000c0c080d100d1440b1600615440109 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 782896312 1250 782895062 782895077
    0x12101803034d0409020a020d0e030304140f04090f0b07090b030a091115090a0807230105070506010305070314010203090d301d07080d030f0b030f161203 67
    0xb090911070316041828204100545045003403429148005040103081c0c1600160307441e046440c00900341361031004170406002d42c901e04181c4070785d804030079103040d15403031b2150110001c0c501d0005407480c28281c4451f600503182c101c5403424042201c0645041d40e01602d00280240c03074416003210b02d011548142d900f440d0b828004100c00c0c08140e0012030307a140c0a80841514281c1c0500001c002c80090002c4117164080025203001504046401800404602300504403091601c0c0c48003140c01544901e00c4000c80c080104111560b001c0c8055039034203508501101c10b00c0d0384a15015959032594042600c0f81d00301003180f548901c1741402200e21902c2e000001e000045213041d4241c50400c1c1e0fa40c3c200100225001c6141101c2c1d0544040705426070006101103114122003441d03081200c050072485029070400001071100000008078500c65200301e203800520030401003103807002400e0202c00c2c035034580903802201c401608001202d4054280c0044121403070f5a441594000c02e603424800100844c41e40c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 782897562 1250 782896312 782896391
    0x204062c090709031b081b03060a0c09030503070507060813030c0b0711010c030b18010e1308130b03100e010f1a0903060103050d03050108030304111210180303 70
    0xc40c0100e500080c640c1001c848040e22962506030881701c504600010700d2482c1e00c1008420410000c903001e5440d0a2505a009003200300840e488180007018a480c0644403e103581415104240a200035074000c0162905c940035440e00c240c0380d0742d81e03109060002d40d020020841d41212050744403141340d4580c80310002e03130302a03a0355154082401002107051040c0403a503910307084020301842c01507505503980011074421040c100401c0c1c580204d00542c074007104c90014040d891015503100c1d00504202160740f0f41759a40e02e80f51605201c0c8800651400c00745003070004440c0e0304500514024103800f9803120f84107841d82c41d04100d0210902c2459030880729103030200300c80c1000c3c0340107204600503a0285890001d1940210b4608002a03004403040c1e400640040155a03161003014050049500a1441c504094483e840403105060709030b803082c03200004038080214104501c82c103002e211030041c4091107100c4102d05441508000503404207040c00d04804480c4800e00005130b8403c4108405510040f0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 782898812 1250 782897562 782897569
    0x4082401060e1c0614012c011406030a11070308070314040803130507030f0f0c08010c1202210f0603010f020306181f08030a140702010e13020d050108010204062c 71
    0x15024410b1342c4090355020b0603180c6115030540315000c2c0c0030084c12040e1407000d82d0307001041d00074180c0000e20f003c0d0307002c4d0061000c8036190414903255402101c0c4103840740c440121500007030a0034802c2c4101d0311400030b80e040802d500581070521414454030200144070b0b420b00400c5c0f10302d1040b540100b900108000045024501448144600c0d000300100c40225440c1da44281c0ba42e01064030030307640c101302590f0401c01c1011210741440a4000400240440ea07181140580070b140340300151071560f50041604c0103000c4021540d0020f8011412040a05e810004035554101c54162503850080d42008a01c96100e1340c2030084034010000030301300c0c1080100741d940b420001940606200c00d948210015111400361500208016103502e5000e19602e51070003002401c0605c0d01244804c945105010550150ba0400c280407101c0409855074200303115103081820081c480c10240d88143c03480c00d1b0010440d454154040c205032441500d40300c40001940c00f55164050b00c10304100142c0c8145e0035030041c43e05 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 782900062 1250 782898812 782898859
    0x5072c0a021e0c0312180d4d010c1b080903030706020c06100308030f0901020c0a050a12020c061e1207020a03080f0c0f0f04082401060e 60
    0x1050071842d511994104411600c26503c007245545440d44040b90500000c400074034030503046658000040091280308990390789810390100020140310310000c0259090b80c2c202d01416801d0f500c40b04030315402030480d100e44415615110070345205900f14a401501003014810000a230715543c8404038100c08c804180c0f44120f200724003c98076440240220402602c080000d840303128401c40e000745c1c840a99207200d42c900400103040d000b514071070389810008110301c2c034101e0f50440e650740c0c14802c036a65904901d0f4007a21a030312688540e40b02d041164828044041490701d081c512451000c80c820341c0c007100072a0707101144011140c0c009402c010000003404804198180c0e564081c4085080620700c80b03900507005003c031403a13000350f004821614105503001c007080d80e11248911342281c6600f070101c0780300c03000d001c0c40500c01c10b50b40c40041ca00f132100111105403402424041c0840b111428506107421f6034817103200c0803000c151000c0e000070481d1401000071000d400406040304000403000f1001c140c004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 782901312 1250 782900062 782900077
    0x60a050906031b0c03040311090103080f0705071505041a2b060302060d050603010e0f06070509011404030501090308010f06022112010314070605030402060a21050405072c0a02 77
    0x20f4542c003098240c0f0762180041e1252550140286840e5032560404d40d81d28214080750b1481080941c0040c000102c1c400180c0b80003e42480c4ca0f50380b50101d91031f00902e0b2800940007001c4150b107030003880703104c3c070b03400401081616905640440b410f248100403886c14094502210702441040b04085a40001440080303a22100d8000120b50503503280c0206103250b006051004465486e0000c22110341400d00a04c175a5800340002016004001226183c0700d050281078030040244c002007014803a80719810604640004200d260381c0ea40d56890410f00801006104802041e030b890000a020010052107000305c170841d030080e008200e50045050760415510219004101080c40300003080c07910301c00c0b0280614818800c0c52414403001c4940e074607140342c541c080b00c1045000c00400005807600c80546841503040c1c2080c100251420030004024514251401340e034619050400050200005224084414aa507030281e801c041162280760001c07954990030b091500c103404140c03017600d00d90040151 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 782902562 1250 782901312 782901331
    0xd02030d0c020a031205030a0c2309030114010909230d0311120411030609030703120903050c190606060801240e0a0803040305010b0109050901180f05071d060a05090603 74
    0x15151665651005210128841c40001b00007004012591005215032080307401c0c2400c040c0b00c95038010a5140d505009000c0018020381d0101e41500315441c250403030200c280d41a03e078074a07990f844d40a1000141070b41070013a14844c4115200070380120400192801c140ba1040150104160b00c4c0000d03800b800701026044a000700400803528415840d40003d809184541000103040c0303080c4041610309080a4190b4096400030409840000e1304481d43c500c2007881b0b9072011075080124103095400c0e00640100d811540a559260004050001d01400c40c16100321410010944c58500c2107070401030900410303080c0e841c0101c925071107a0044e103011120000e0389c5419a034900d0168042044000180c2c0031000c01c0d03001003010b104104082c003d040181c40b080ca03050040c2c501d031100199510038107210386d0b1824030380744600d0000034460350000b681030540c0c450107000c0360805c1c040080021104c0c094040c1c030103507502803580703161400c01c0c101d036210007440c0e440d503040c141c0c56407c00c900c2e40c0c8003401d094074 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 782903812 1250 782902562 782902579
    0x6030c051b0607030e06062d030a0c0f08070506220503120a031a030a0b0705090603130b0601020c0901170f070b2212030507020612090c030c0d02030d0c02 68
    0x860341c01008480c501410030140005080003079025054440380004440a40c10040c1005060348a000414001c4080000400400642c001011017607041008065405006054034071080c80420324007007044580034090a46056940c07a200d40d103d640b02d0046d44e5120301d0412802404602020300044101e00014002c01e9150781c500000c0c3c40c1914400a00d4080c5002144410405815120700c9440006502c8020a86022040025182d40b04100300800401e451008118201c0c070034400d403480114080e1900c0d50781d080201b0001f1110000010803545104a0340005640c0d520100c0d189418000c05000d040c0242d0900d40c200850292045112046210303804861411040822104c8010180022602d950306544407049600203545844902c0e280031564040042982880c0e0900a00350986813881d280c045920010700d4610494450340c0701454070809000202d10085440c0368041070171811140400c0418003400107100b0380b8030b000380d859000a1681030081d030080c0f000c0450307588010504203 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 782905062 1250 782903812 782903827
    0x1170a020d0e2a0a0504110f2b09030c0b13050a060b18040c090c210c020601410a080d0807030525030612110f150406030c05 55
    0xa040302c001080b082d4140e80301030000e6030944810700210440303095645500041c00c4441020410301c100b18032405010b250f031043d4900140180350b09941044210640c41b9585040624500703249084100302d0050900c1c03e14003010010344584204140700e5410340340d801c007a0302c01d41c80c1c1c0003115100a007143c60007541c4803a603000040007031144583c000d01c0f81c5000100d04c248003007840b4482e00c20f4100c3e518012981410300c004920b002c59050111280c0120200b10400c50308001c4440744c1c21181c0c0e0070303c00c1d502900d10706c4081e0302542042200380b09503402c4403d2681e84c0c05803128003032031038281881e00340800c0e88400c154100c4001c0403403440801d4000700d03295010080100711a0f0210750b104c2040d980106030803c0c4469427180295070008080e117801e02850078841d48806400e038490b45040910302c092603200741c0c245c1c021742001c0010310b00e145412041d603a99007070030f5180841900d980b611a0380004010b1520340b4042c01c180101064650b0114185030506205500410707200e1030000c00d0080601070030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 782906312 1250 782905062 782905087
    0x2010110d0c170a03050a050c031e09070e01090507080a020a0e0d05150108030a0806031b0904020f040c050a111504020907031b0507050c09010e06010c02010c0c0806010305120901170a02 81
    0xa1030b143c140c1e0340e1300164518042c1003c0085a101030042c00e0800d1703040051010700da036484e07019001c2c0c642c44512007049442c1c02c4100d07450060140d00204e4051001400040c0750f483c0340e44098855401c3d074031140303541da450620030800c0b44200400701d00400c03000c0c0c03909810703400c104d5a00c0810300c0c490f10443e60303065035801424203001d10991001c0c0344c5500010322a4016a4040e1002d038016a040d8000c06240c000b89404464071901400001d0041c1c100e0320000d000d5580d54441483e4512001d04100681c8101c450000c0482e8480c050800110f401c02d1413002c1d83d0350000440140140b424101402c2c42c0d1500e07420008010006402c0ca020180c0b101c0d2140184940040140f00f00c9040b42c40b01c80c0e86e0a1a03181c49030801c03070001c1604d4071030702c50400100f29051107041e009074000d00901e0100032100d02407005a402a031103060140001e10f11600c08903401c2c1700010114180c9001303004036080d1001101e2803034031910a44820a0005500c5068445604a4a00140c1c1c0104254001600384403128085 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 782907562 1250 782906312 782906317
    0xf1305031c090b0403020906040908091207060e0604080a12200d0801091e183503150103090f0204050f0f061e1c2010110d0c17 56
    0x79012010912000c000074290400748110040200c00c8a440c245455500040e00542c80140001c1c0141c1d21007601c2410422218200c0b4543c0d0001070085d203ca602c48200c42c0c1c0e45010314040e02c401f26002c0c8010b01810f29040c81070301c1c1259140c1c0001d00b214001c0d5940c3c140850303400c020b0041401554030900c1c8030041d1303091900c01400d0050004080c1030401400003000840181d0081d4910b03407506034120346501143c60794203035010020401180c041e52103000c90412014182c4007401c540c081441100c0d0314030640044c05842c03116403900d0180d59440e00d000c3c4540b0304c41030340c2c0c40c984600c0d08250712841d54001e800c103204107405038880740d600c8092a0082001d80e40c088035451608c182200801c080410b40c41011a0032680903121034845d0005500c081d0070714010541e84520a180c3d049041c0c410303492001c0c1503207445a0000c0c403ca14100280700381e4004002101142d84101e02c000d050b0b011191207010140c8005460b80001d240e88284400c09480700b07541c0c5c00e402c0d1000140c00d465220915081d000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 782908812 1250 782907562 782907583
    0x1002090f0d12030533030c0d0803090f010c02030a11120c0c0109060e2209240f020a1b060f0e030406020f07030809210703060902120109080f130503 65
    0x11402d50410081e02c000c2c11110000d24007818000035542142d0500700040c2c448964508401c00300140c1141040068a0f10449104d00b683c00400310241c03008001c50300300594003a03014a0215a110003501078030301d00740d68035461244010f900c180b11044200d031040c091241046004800d9a941444440c05c1904c2c2d641315503c1f903881c0e41e0003c1005115541e1004000740208a545031000480744004002500e2515041c5280795000071079007000c00b00b031082d9002460280d80300011030b40618001e84a0f0400011310b548800b45103242402d00c4e640300b107003130003104c161425507902c5010025030100303105883c20688009503525580c414440071100c031244504030700608190700468440b450404000c0c038003450707140b12045640104204200103407107101030b101c40200c01c840c0c2d50319101c5809001c914001c01e00703261030500c0c03103500710000501400d07038084030119009a5a5482c0d03c1480700c1d411713080e40d0924800a0084204004c400c09051221010f131000c800c07404024540d0b0343c1e4400009207002c01030203 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 782910062 1250 782908812 782908823
    0x13210e0d03090e0601080c041e0b070c0e0c0f0f0f09030706030b0f220c1b030503010302010e060702030601050103050702340e070801091d031c06060309051002090f0d 73
    0x140c05200f2407000b0414564412400d02e40340c01c1c2440d0000c2c2c4504a40210700c508980042900381d03484281282c00325060140c030185d0204c0d41c4405160030110740c51038040c03240c800103d1101d000b0506d9400c1903803c44e481427240d12007a40c90b2180b101c0e92264240e1006400c0901c030b040610058900e0354040c085070004105e10355002c18100d45000401010302400071280d071052034140d059003000b8010410010002c00c500c0340011f410030700480159564500c44078400c052500c400c139440100758102d0041c49c1602d000703a0b0380c01c000a1203141070060328411f42d89c01950544c8614010091580310f03802842d070100c00e80c4107071412180c64006500240c60601081c842031100058409120240e03d24a04020f004001f4182c004c0d08042c00b0240c02500c0c10b004080701e26803941c600107005004030b0620740102864004684d6a00f4003040c03441c3d00c1d5940c4401c220480380c1008d10000754140f00c1e0180c00619030b0040050060300e00301c1d040802c0294407001049030800307402e001c810710b40d42e101448a50301034002c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 782911312 1250 782910062 782910077
    0x61d0f21010e0d0c0209150d030f091401080a0f1518050f060d14033907060f050c0114070815010c0b0420120307050613210e0d03 57
    0x142034203449108009501079889204032200c0c070b80d813080c10040340d160152420301160300d64030000c880f40428580705a810007540d412000800d5408842c849200a5a40c0c80949998941019070702000d08609000e0000305400045403480131a60b1084161410010780000e02c40c014030112a00714803d40d10841002d0030304100002080464002c599120b9450303001030380c40b40341100001307010100c0e0080c0039004400f05498041c65203001c00440d400001d038020fa005004100c0034401c000704554000c4148512a20184001c1c00d1038001501e03019140f041d1181e40a00c2c00d043c0f0221240d0300426907025482d902d510302008840d20b800c2d4854021403090b034903043c442ca86120144130b070002c500b103040d041100c00f031140d8012030001203003150400e51102e17128001c035040d200441c4030311800d2030034980c0c0541c6603004910a00d400000603c502403095082c3c94541c0d40d50b480d195800029a02c2c09400d42e0050061425100100c1900c1292160103041000180222202092108060090440205015 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 782912562 1250 782911312 782911369
    0xc0902070204150305031b16230108040302120906130801090201140702030601050f0301020d05101e0e0601210504061e05071e090e0405030a0f0801061d0f 68
    0x9010304156060503a140f8481189150341c2c0039a01e1080340c14281c070914820820b01b17086181408191004c60b0b10b41c0011024580316554004070040c1314004e04840400780d0b00b41201c2d9401032801d184140d80503000751079200710b42030b402c11107941306400065200404120400002448400c40b202512000000080214092001412200721003071880741482080c008640144d0b0001000c1e41074032802d85044401c1003031200400e005e801500500349142e4200317803c0102000440800c4011910301d0590f40d03403d40d10b009000ba248411a0081041ea0003804000406950043c0c04400706045a9654901c03118512411201158030689084070110303200d0b00360303034460010715030301c08107400070300000f002141401c00010700a64a80b64409554540c030b8000303030402c503028055400042030541500200b901d030030700c0c01c2c0703449521103452980424406540110791234440e589140c140c8200ba151040101c003d640030700140740046e44402e902071420080080e241d12504255200603d01d03010302c4500482 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 782913669 1107 782912562 782912569
    0x30902040509010f1508060f04020a1503060f0b0309030d0b030708010c1707090302011413150f0212130e09011113080105010f0605070813030c09020702 67
    0x128000c00c000b40381c401074202d203a41c400310704010000c20112080340f0003c4210350080072465449500010700100aa0011540040c0000c280c204041e6590108007456000000b54000181d01c07940104001071441d0b0318038014205000c401e50440c0b900500d11941c80c01143c000111850b180c562540b000e44050001c10040e000c06002400b00720f42010001d00042544c1e4a132134024540307003000500883c800d85000d401d60754142e5418200c441d00d40c2d040ea28680000864043c4014507030b00c0007652402003c0801c03211005038558558080540380c0c0a401e00d214403032901c03810803040029001c101c0d403482d02d00c2e003a50704044100503a0703241c8180507401802685001c001081000491810a03104251210100e41c060002482140e8803175030b0800030312019202d01710100c0c10a2001c0c10004840d030300a010b160059160005c03007590f403034895000c840000d40c0002c41e82c0d54002442d0b410b608 = true := by decide +kernel

theorem cover : BRFrame.Cov 782733812 782913669 := by
  have h0 := BRFrame.cov_init 782733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 782733812 ≤ n) (h2 : n < 782913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
