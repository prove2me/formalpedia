-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4440
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:37:18.118227+00:00
-- url     : https://prove2.me/submissions/cc96a89e-c874-451d-aed2-666743e049c2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 798381294 ≤ n < 798561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 798382544 1250 798381294 798381317
    0x8030702010f2304060e03010b03100b06210f09060709030303090809040c0801051234080105010303200309030604080c10051812030c0d020d0207060207050c0103150303 74
    0x4650400880101405115034001850404825070b000c080302c40e40040c03c06030f2101d2401d000200041803c0140314040d9250480c1041d0540b030100300300c82464a071800201d031521a1030003081440c40341c40184804440c00300e030000f44a060301d054490040c0000c45264151751140550301d5100c1c4000e40b00140402c148540030000079000b9000b040f0102e0180c6102d50402300701d00080b400341d520442c0301c003002944c0200103020918242c55004142d581403001003142582044030300034200c10341c402c1e51552020311401c0028a079880c109007809080344600078070065a40e4540a00740010000c030b4071075124180b405d545000d000c000152655407e0050050969495548844006a1001c01d0311301c41c5010702200c1821481480c020507020300340c81d88003d01800e05204445007001e20300b07800700d000c40d8020014003044002d56001d40e4000c9800f180300594402038800907900911610350000e120500218030311040c0300e404500407180040a803014400b0841c1290301c00c1d00d54211303000003404100c966004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 798383794 1250 798382544 798382547
    0x50109060219200402030f0a0507020a0327150206060a05040221190227010302070819090f230306010605041403010902090f04060f05010e0601030e0a150917040803070201 75
    0x94411140c5401c90700c200d143c40e40c2000c9001ea0b40f084a1440c0011480c1040c089510f40c2c40c82100c0d440440c500c068102e00c6c2590341c00404031201075421050b40381c800e010300004500006441001003000d454900c100f038000b448047c0d25068120f0319244502d40200d0002014100f41c0202c0c5c02c282e4940c000c2c4141c00c2c00031003a1404284002e032108551070942001d002d0070194900c002c1c4080d02105c541d0360814040c0309403840f420121040454101401409000d000071001410b54403165450346400d07408401c42402140c2d010125403150b420350368082000698802d507256180040701c0c005c120205190414814150381c0c980a10030040014410401003000d50a003424007901100f00a0010481c000f803500001c0d202e500c15540c3c141481f01e020b09000030407585100d04d040004401c41c00b40709640c906100c940081100510247c1419126240c06420b200d0a2140c54201684070140011161103c11018020b0000c40000c0b40c0201c001000541d40030345007020b0794101d58100c0001e515003485a0300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 798385044 1250 798383794 798383813
    0x110a0e10031e02091513120f0605040b090c040b0603060d02060409021308060a06050f120f011103010501121a0d0c030c0305010b09061f080c09030f07050109060219 72
    0x80c440d04242c1c1d164006002c14084440d40035003a02c0301d50025895400101c01c010442c011100124001c0e82e0401c591301015a402002c8000c84088418225622010b41444945101c001030010300151820b410007040000da580c5031f9000d029954200c800100401c2d090000b10340a071304e611035200000b84001340313151901000c01840d26101404150030940c0ea0fa61f01c0301a6000810420781d8960524414080c2076010801294820458030003400424035040100707100000301240640580d00c80012408030500030411074402c0000800200401380d03004204880c19082802028000b81850395540c14510050242000c0100e01c03800c0b5003060440c600c01c02201544029003100c030041c1040000012a007040c914000650240f8004240d00030b45108001440500810a0b881140e42c02c280c10891442609002c00701802c5040c00045911414541d03078440c0101261070f07901d8851908070070075614002c20440100c4000380c80d4503503280c4c0c031380e40144c3e00c40e980c100414000090b40149000411301890 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 798386294 1250 798385044 798385069
    0x70807022503050a0b01090506061e0d1b0e030d03060602030d0504030c0f0b0a0b1203030703090c050316030b07081b091818060c0307020d03020c0f03030910110a0e 72
    0x2030421041d82e80d0340705810b09810041c16038110141200401ca40000c600469a2000c400c950051404c00412400d160f4101084542c010740d07040801c1041036194607501003422035070343c9043c24501640c6000300600024020007094000e004181810140328001c1c054042519101e40147d801d1204901001c4014400104154100b00342c40035507102103250703480c0d505c0c0350034000e40300c2c0c044a140080e0000e0544140d01801402802c070660389080386003011080c2c0b50882e803d80360108903407040d13050544003004941c10444e07050094200c041b10800d0400350309422a445100744010b0399a44107001c1d114a04201e4074110400000c0701c1c1c62420010b285c00078041c0c01801032400e813400744820350b000c0028808682c031682c401c803250700c0c00da03c500341080510350250300c040003540785152443d0001c0d01c80b50300145500600d40c01043c400c000c1c102c14072021a4100581003240d8403480d081d483c55a85446110305440c034030380303004101c11048001c0c1c0102d88428011751500040895408148500c004021 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 798387544 1250 798386294 798386353
    0x2030a061401080f122506021903110339040e0106030b030a030210090f05120702130e0d200a06060f0e060a1a041a07030807080702 58
    0x24081000424901c00c1c1d1040c035051080d00080d40d810324404500d0242220000b4900d0350100c089180d03004076880444030307000b850542c00e9215103880084502c0351840300300300400040c00460b030460346143c61001d00420118550302071040c29126901030220344010340d0208254100d8800c1d50454594a03041d501071100701172040c1f10f6829034110b8401260b0040d80094119855103001006000d40c94011400e207404100c0140c5242c444941d030180d139507403035a8400d42080e61116407040501c100320302c2c103181950300b180030760760b51211103030007041030b0b40c07000d80c089202d2020000c1440380749040348501d803010441f9200500076200c07003402c20b8403090111258000c09040514081c00d01200c184444c070b1306540724440118400e4106407413802c2803580c58001000c503d5950080114594030710b00d540c1d00b141c910321a82c00121790581c844044501c80c42c2c01c260b5100c8040050044040c090200802290703010343d451400d140c803110012140c03180155103402c010b0b401440120300d0300009150126103903420 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 798388794 1250 798387544 798387553
    0x30f03080c1209010b0108010503031c050603120408010b04060e0103050303040201081302030114181f021303291803030a0c02160f0f0905010b070f02061204060e0c090c040509040203 80
    0x2d0380c003074851040b0116114111a5114803581900c0e580207240c00c0d0152900b18065400c6c40d0104219a06c03d299a06604a219880d600803611546041c00420010032521b1003040e982d5440311100d60182c0841d0180602840ca00003002454a0702c90035a2410380e68420045e40c9036490359001140c0c542000b03040c20141c14070307100c1c1000040ea0240300f060b440a4401c48501c650386040710032921440403010040c07030130f6048044a00174503002e00f0203400750840382d040e0060701d400c80402c00e9500300004c0d800040400c031500d040000318040e041010a0320b40b203003c1002103603995461441d1001341a2004030b40e410b900904c00b003200c90006800440010000b032040750400d08207444404d10481d1680c1c4810300c0f00301c0b620030a00c142244124100c1c060722080e0b6040c040d9504d0710143c2002c03131081d0740c000b5191141c0d0900100455036800c08443c0d48605540c480c900900300b030b080c035000a10180b8050b0b016842a12092895802d00e0144140f00c1d2001c0d48426042a10f00340c00e01c001030a0041007241e26014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 798390044 1250 798388794 798388807
    0xf02010509040c200c0a0e090f370f02040b030f07090b010305011508010303050703090f06090e07021612030311190810030c150e1e0a0609030f03080c 66
    0x155031044400d80c2055a13a10070007482400e07103900740c202c140840b00c1d10980045292901c0f94440450b1142114843c0420100542d41c04003000d062404820b140386190060720f002914655900750303110203421080c80c2110024544920001034590002001040306d41886412800742c9825803000d0079241c40a010b45800c6c291030000310b402c00c00380781c005000c07441d0390711102081c95a0522a0b01e01401d10b4401d0070804144840300035000d040140b0000382005000560001003511458913400280341a1000c082050f4132454040d040054900a58118100050008696910001707403540d14a1929111048550804070072030881e500d0b00000b034080c56160041d16038a0854840100030754040021080004901007800410300100a00f044120030303000c560500c0400e0900c004a001c89000295070601c907298a40103944c0080a441d140c1e030f2185c1c4040c0180464445150200500d80e012202c0409240c2c6842d419070318101103000c090300e0003c2000c1464002801039800702d401c860810000d500380303817 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 798391294 1250 798390044 798390049
    0x114060307030b0a092c0303010902090303130b0a111605060a02010603020a241103120406060b0d060303032019020102041715160c020d110604080601140102010b09040f02010509 78
    0x307815a01c005120b554800200d11070310003101070401505c0c6c220601d0b803c80d480002c0603d580b404180a110341d020343c00075610745155420070072030741d64a42e400d503040c180719940c189207030664021041070800315214041d49000400c0c00b00c0c03404101c3c2c80c820350f820321442c18803003400a03a4101c21410000d5660352100480540c0d244090100200399002100e12070b000c542528114040305a5480820f00c10490005100d052020060355119242241440c4281d82c841c245400600f055030305c8003421380c400195040054083c0d400003c01c0d41d01988052000741100110590f100f810300000307110b586c400707208040c0f508003080403030050b5508034400035044c2038549244440f013800542c0c2c0507805034000e0b05200c40055079580100e901c400307c50f9a42400c80401d0001401c6c121103400300038410804c4080c5502040102400b1400c00d00d03001c0d000c0d98403107407212403680c2c3c2c0c0d400a00031000c55141c01c003042c4100358414058803407140300241c2603655503240c541c0c95850f00100c94808030705108040c802600703240c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 798392544 1250 798391294 798391309
    0xf0f0203071a0c01180f0f1e0503090405011a04052107060207082104050402030601021c0207080c0f010f050c0106030f0308160c0503031504140403080412080114060307030b 76
    0x4420b600d82407655510080c0f602c90031543e01c6209401c8062400c45410702050149081d0b8060030b41200b600c03141000186011403c03180c5c6007441e5503000d0406040300040c418000301a000c4804c0540e0704000503600c1d4a0407841800d085e252009507618100014845030801d0106150b0940030000d04020b0348002c100703514141551608100016403110108110458003048400c9070b418140040a461001040745014284180e0251038080d0f90000301240040c0d208100444502d1000010102201641e00e8000c0d2940c585208000d200e115140000c1e100e0700e407200008040010503181c170043d6152507101030b40c030b42d0840c007120786440d580c400001003c155149003002c100c030301c2640c2d40c000c076243c00940001d00305a010107580410040d10202c00000c0c1e030000031244c20256035501400c02003e02d4002034054403203814151803004400040c4030406400c0190710380180d105120042d891500d2502c2103400319024456540422800a00543d850610320002c5400040d58940400c03014040000f14414 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 798393794 1250 798392544 798392579
    0xa06050c1e0301240509041e0605011d0f0a03120918020705071e031b0e180706080709050d120905030a02010504030213090b01060f080c03040f0f020307 67
    0x508a00003000020189890324024196441e01d18041c15541420201c0107410403600700341c480e01e1150300d0700d01d2a05000702c09640342400018408d115554482d0840380d082c03407642010244442c10f01c000401c030766008108a0010b08074112030751800460020402600d0300d201003140d80c0003101d000300800407850340102004125001d4841004c15072038001d03440000e03118245054030b12407040c040740001400200b00e08003120120142c2c0151758000158440e400149940010b080000309240c94007a100104101c000b1982e80a00002041d0340d9114040009100e160380c40a19402011090050a010b40f16194001021f03140c4401c0782605c81c1c0c08602e0240302d1020680380405981c455008066000c031244c0e020b0300c0282c0190820784290350010b030960249001c000e104901d106051080e5144e56401840b503d07402c07001802840d607481c00c002d400b4040d101c0d0b003000021441c100140401e160901100d0140d940401c0607982040311380c4440761075950010080364940110000081c0c1b00c0c6078002186103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 798395044 1250 798393794 798393811
    0x6150a02010207210206040204200d0603061a01050d05070e040504030215070908031213120c060b0d02090c070f2f0406030b0c0c0c04020301030c050103230c0c0a0605 73
    0x2d50708041c0c10030045141384c0ca450408034181040c40d00c1c1000b680841c0140d04598140c4010440341600800300d000b8150300350480b14009000b003005c6812803603540089044a001c0c4c01c0c108030545085113036002c500325140e895070104004104420f1109c00d00e501044e446009450114110340d820400241a1041a2010f600590100d0b12031282c18400351030550300030503181490102c5501d040c1d2607a071a4010840c0c1c1ca0307540a05c1d1400030721b581c0c41c061048005141c1c4840154803880e49010054400078507002c041d100f0074075155101060b0f00b4410005007803d60000e00ba0381c401d64607038903520081d034040b80d81100c034103651408000008907074080880300d41042d42c0d0f4443c240307464403018203590031824802601c03803410a00100080303400840549e42000200d91026a2050103000340c0d80740411100c60300740c126200100010a20025801c1c15007a2202641c6c14401462440e22980000c000e00c500101d00c0110140404c25012001000340030114048090312051003058031010102e80040b1707104032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 798396294 1250 798395044 798395047
    0x3130617060108092a0d03080106020f0703020f0603060609130f140f181204060314060303070314220f030b0f01031703060406090524010905060d020306150a020102 72
    0x2034880c000c160420760040d000c1c0707411891868145907907036594042400341144521468161404808980d005445100000d03080c040e60b51444d290040000b0300c00d00ca410018014007040701031f00038022a0360011179400030002400328051104001481e48040d148070703400601040000d036a6190a011014800b050a10000c1c0b10010403401c201610722000501461120342800c0014070021041420780146040a8444104842c0d44070603243c24041144c500d5403910100340010301a901d40c000240e0030302c00107151034190300ca40061507540c3c006c2c00c40060118000c070030007124000c8070101904d907465250040140810085402c0c90000b1007035040400600f031690428400d105507040e034190402d400841e1035980d03614646031a0302c11620381c0004a0100c0001010038465950780e0031101c041d00800380200802c1c00c10341c004040700c105602d4a1007980341030110f0a20380e9800341032141b0450701c002d0034442c038ac42400e0400c1c0c40250300081c600d44c0e01100442118080d40d07150805030248454940005 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 798397544 1250 798396294 798396317
    0x94603030b01141804020403150204150c05060a1104090e0a0c0b04181109090f09060a0227030f06010f030314040b040b03180607090f080f1905031306 66
    0x20152880c0000940c1400f50002008800301126401c13100e042400008150030200840000390103486541d0000d80144c00e0b00e400c10301240c04503030062049414811044001c840a40401d66071100850380160968002500203000c2002c01d03000941d1314824a074800c0e24198440707003c40200d031030514456600d64000c184200070010800d02103005400307880340e007900b400d00d0710300350101e020743c1403400f481d2081e100c0710707a0301d00d075980d000a50b5109070004020b0300c82444c01105090400030103c4001429115080c0802c49040c910f100322030119110210350207500c0001120002c0b0340103036102041d00341c03007100d0205074003810038040300c2d01a000c41a100e1011340d2540c203009005054042081030b0b01c1c48208010480b154400c8104c03811182d1070311500361243d0701c1045a94801d80a001507110303c1c0180740070044041d602800c0c44060710300b01e4070f1803080152200d0406580d44072060b406041035202c5406202c2c444041c103800200c4510400450740b030000000e9011584101036840907001c5443c8d403640 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 798398794 1250 798397544 798397547
    0x307030207080c030d0f171815220302030f03010b0301081e100506060d090c06030e010203012d090609020a09080a0b0c0f0f0301140a0806094603 64
    0x1c4000d0120800034881c0f43c00e0030002a0b01c41c0c0861041c9420310880842c081d8210b0301440482d40c4050140c40003004502d000e181c1c14200d11103400704641d00d8045c151008290700f0701c0c01300043c000c1044010110340ca00d04242d1500100f0910b200c1541540320a10030740105c82c1003000154080e01c20044115282d515044031149400340100019112680d94410040c0b1202d0008010500012034030011600361502c3d0081404c6200f040c0c1600c9800c1d00301107188003030005841c0003000700d40144d64104403071490182c0700d46c200d0000380604409803940d141c3d400074090700c0c5602044546c0440080404060380d41024500319101c40d0304c103440d400d40105060340c0450300080c5150060501d00e000d4520002641d403840c0b14810028810302d030112012520120b01c080501c140c8001c000440030070382d507958641820901c03408030701410724400c0c040007001044e03441c4c020030018043c803c2070000380250326040c29603410b4091803140c01c3e04100c6c6d044003500b03045039507550000c88540001c2c120410640441c01c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 798400044 1250 798398794 798398803
    0xf0e03031005100804082a370f020906040b0a0e0609010f0806070f0e06130f05040926091804020103050c1305010c0813170f0c06030a0b190803070302 66
    0x2003c0c81070060301c0080202050800c0c088505543d01c01c000540c69080e50022030000341c2c84403c10300014804c0c2c203003000080c0c48036181d0941004d0b070714580110030303901c840710300b01710b4001200c0c028078402c040020715006040405c140c03078000d40010710200701000d4000205841d68410350103007000a03191340c18803050341003245186014241c1c000110300c1d81c605014800d0b80d6940081c002e4020030101164060740e4030702c00c010340c21012400034903090f55136a400101304c00301a2203020300403900582c1e100000b441d241034400d8102e91a40040c40c0d0800030018400034001c261100542982e02c1d20810440e0416600c0600001050310007003c1040c44e8102070000404442c0000d0508041800400444a00020710441802210024070704405140682d2400c059540140f017040d8018114440c0b012860a4000f95100c10604407031084030402e254400065548a444c00c01d0960403400030800710b040e0040f0b940100e10143c4d000340092030b141d201d2101180403101c49178016140c54001090340410180e0501 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 798401294 1250 798400044 798400069
    0x7140d1b0e0f1008030708031305070302040e030903070f06020d05070c03020301050a0c031b1d01021f0c121506030914060c13060215070c1e060609050a0c080103060f0e03031005 78
    0x1d00450802c4000c0d9900215844080c09e8a0151309914504104001d010003c40010f960b01520910040403509041503598009403041c80c860701403100007003802502400700b442103a01c240e0061508015042091310a03501c605810b8801c00349482d0084091f85090003030034000e0303a071503800040310320850070010100d60030300c00180442041c2450807816241c0c00503448500e280d0030241c038610310f01d080c0c1c01070b4030b0724031258000010a0107a03c00c49070010300756440071224180c5900e030144807101d14a0300d0301c1100d181c40040300605c100e03a841441a24401d42c081020380380b082e44000403c41c3d1032402a8034120b01115a11800320300040c0f4100303040100c8601d000140304a0005100301220b1111000f072880313004120004201101d8000003d010b0803242c0079500d110030088446003070506081c52070282c09140a00c80d012030400c00441d440039624820000c2d15811a559241c044e42159580d1018001209101942c0d43d150203960461000170310080d4010507075112002c90152929041c030180e00802c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 798402544 1250 798401294 798401309
    0x1109040b01110c060d140411010207050d1505060103093f0801050609271b04050306071815050408010e03030402010c260705030c07140d1b0e0f10 64
    0x31140150101d80001c0e42c61103c14200c440707075194442030090070014000c0f210340511000d010303000d20050002000640300c421744280d0980c1c600759103a000780a4081d0810300001d0217600c440d00000200f91040d40103a030010014074011410300c59984a41d12903000003480e4101102110301c01c5902c1179a801c030905007a81e0070034034507d030174414150042e107041e40510840d40582d60000d00024195641c0e071484600301d42c1d0b010742898000c02c25802803460b0030101e400d401f2681084540d8102040440151002c4a00c002e00410542d66403c200b10f40546d50082044426000780c540441c410100070b01e044d22540303855440c140c4071450018180c4c207464002c003140010303420030014400940d078403801c02c1400350781190607007002181051040324000001a0324001000d000b03e0301400704840440242a0740c401d08084400954440100c150803009403031135240d2202110740a100003c0c840941d03400e40c8601040b109020380c3c0c0d00c07001060640b901326810303060110440d0810906400c09560078002d000301 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 798403794 1250 798402544 798402557
    0xa0e0405070e0d0308150901031401050604021305010e030f070605072f060c1501030f111008060d0302030c0105040f03081605040905180d050a0201060515040915091109040b01 77
    0x500b0302181e4a003485200c05810080c207440050450404c4d5110f070303a00e0780000750095503250307500e0419400309992006000c0341c0c2e5081401281182c0392038000c0d1140720250f01c0458002c64500b170019030303101c855000c1658060007842111130302c2030000d0081c0c600400c22030b2501940c400d8a450021304c8a07140a1507a582070343c814401e0b090140021908001044017aa4040d603540d402002c2245028805100d02c001086848000b1080010300e22008401d40d02c203010810b18030019108022000c42c48582d1355000132440d03000203c0311301d0b10722801403c440c00390040d68a01035013004450b0a5510860742500c0303c00304070f440c0c0d804040d4442240d036405403444078182c10301464140014494803641c801e005005441d43e020854100b03024038500303007014901e0304690744c011000c00054626002450707404095460540001918240088400000c01d074080d01189440d00b004080001080581c030000740001c0081c20104003100d0a208650101510300715160300d03018100100303c1550028000203041006 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 798405044 1250 798403794 798403817
    0x921090512120a17090109060e061b1b1203060315092d1b0a050a0819060908280905010c02042f190309020607060b0d080a0e040507 58
    0x1004500210031000b169030340303540c4184490b002c554070545221000c05040c1400c003805040d0405600001402e84500c5e418445900151070303041d00c0f8482200c0c83c4030710740c80c03880032901c8800c07079400103103910b80000010a072a103154820302840e1010186054007000d00001c24400c0d5440e0820403811300c10b40c0341d002c031000d5180002e0719a86800d40b10070910b0320845452400b019a8151130007000c1c2d040d448000301e81e84440c445030725070900010180c80360b020f1640000042210b04100c0c4400007036840100c01043c00100902c1101c014000c905401d541d51541c81801c400016810030003441d11200a41003401c0f20300d120f56054055541c4d00c8603200a02c040400c04001d981d81081070700300280c0c2c040f6000510029008520152000144181c1c070040b1844c608490f00041031401501c40780e1202e5411808164a0901c1035048510410001e540500d060102d80d000507c16005003245c41e901030052128007025a5a1661540104003004040344000c803401c62581050310405134440980c0ca06a0729214 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 798406294 1250 798405044 798405079
    0x30a021b0a2d090c0e010e04020a20010605040c120e010923071701061e06050403120201141005093403020f070b01060810030507140409210905 63
    0x81800825510032a544001004168012a03080b001840c040d2018400c04a034580c00a00d007801c490300c07250101c1c8072440e5029060a0501c00d552076908140c03038200840c800d10300d0154007030701c81c10b00e4403a5030364803000081141d031140c0c041d1911089064890740d613200000301402e400e5807030781800e841190303241101080109120007801d0701d54905005030548000400130043d424560240c10040d54864034248910303c5000543c41541183d50310b00020007034040b01d110170200e42c40d440c4a0700b00010000d205c140081100c01d106490100d42c1400009007840b1141c60101705503a0031503804001c990f0f040c508028a0402071a40c5604c00d032610a50b00c50740f5a48000703803171420404200161852112907904000500950403600040c04031a0801d407122440e01d070100803003400340195400502c010001c5122140d100c1001c9060b2035003e8040c24650b4100b002d240400b0406076117095002d515051801c0114444031810026015050500801c0c0015500041c2c68040964482d030b01400e41000a400c1e00d2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 798407544 1250 798406294 798406319
    0xb28022b020c12090f0a0308040518010b190918050609090307121101061805010303231e0d090c0f050f010219140d0906090b04031a0414030a021b0a 65
    0x1c404a0900541358840e0601050b0000413942c01c09800441008001c8207000080c5c0142c0210b81c0c08039141c3d961404a8000d071088210b0030700c030b40c08000009016001d14415050448240d00c405440c0c0849002e40c0c1f1040b40d090030130491000c01256954109000c4d4500307102c06543e60040b441d400644c60102240d4520511101c005441c10410045042d4118030340020342011008140f2040d03c81000c02070840000001c042c00c0c40101e01048511282e0342c2c03e6200d584140320300442d9400c42c181842107902460b24030342d03a5000c20250a220422200c1d40798940c80c850b0101181c016900c080c000340c14500503600340810f640003184901750b00005500c050784d001a07520068491042a005400341c2481d00305822012a00b070180140107881d13070100515400b03201e070b800b212b0040c0c1d1041816690392081c40b041c0e2043e030201500402078400c0c080b0800d03080790280383d001407203503000561024500c5d01050942d0400c071402c200582100601d0380070a0500000c500e62098100c2c1c40c103442c6c0f03140101d1103201 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 798408794 1250 798407544 798407563
    0x71208120a060510030506030d02060106021515040e0c0a05042c030c0d0f0801050a030305030c03070e030f16090b06030112080c0601090c110a0b28022b020c 69
    0x4201603000001c014021541000e0014800500b0341e886600301d80e10050042c2100b21911402842a402c560644500c00500e0504079003154002e09142950003a5408004100801d40324003103400e00809082901e0b41c3c8504030380441088094403115501d442000066601c9500c02c40c81385080807461801d11214072200c5590314030818120080428202065046010310b00c01905507004105024520701c1c0c00c401070914109035543d82282e031340e032248100100071060380170140c0059030920004410702c64280042d5085000d40c2000d090003c01d00c0d0000e071a110403e07800c1d80c103a03007240b079400b501c0b42d0180e416400074019040051000d0340c25003022612901052050b074421200111101082c043c80c481290006a02042954000d40e115407101e030180c01a07940c0d40c00001c0e40003600d01c09110000c6000c0800a501171002c0e02035485040490001c0f0121404c1d800e0300400c00310007041c0036051480248000e014000c0048240d0001c007111000d6908182400c034003071401000f49071410b40011540e03500c1c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 798410044 1250 798408794 798408817
    0xc06020609070f050d06090f081308060928020d230a080f091302030c03070e010f0906180f0e0f10030507050402070c0504021c05100509060904052b02071208 69
    0x8415007040e402412800001500f00c140c623000340b9003408200c80081401c002e81d00301d0044055961075140d0742d1640c1c101c0d051200d0b9000b03030840d2203142045d0301074806000c07650724400040d001c05400082c440c0207011405c803102c0440c85601003010702085201440c1d03451600180030840201d44960843c0c2c49421307442602c00b44000741c0129140d0ba01801203100511420b41191a4945403035160ba641e8402d40305040400c542d05a0a41d2640c03044039030125148a95580f00c110301e00d0a0002d82d42880340440403000360203070700f00218841c44d2802c81d500051a1400801016042107440c9641a404c05890f41c40d110380014020301c00302d0000030b0160f00b22001601c2c010f94421160411895924264100c0713603000e400041e80060b03007104001f400c580c10207500300800c07440d00c50741041c030401451441030310740040503403001072640d1400180d0a64414015003e9a400c5441e0b002000300200d9000130030305840141844010281d079042100078050001139a9001081119403509500390049405900 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 798411294 1250 798410044 798410059
    0x20706020309043804052410090b07050a14150403050901020a0f030e040605060306150d0f23061909050709090606120e06060a2102030a0c06020609070f05 68
    0x249441c2400401c03600c0c001e007413010108624031012206a08000400f07210f442941001d0100e8002240c8403515605903500d885c034544464082c0c4c0522a5002d651810681800300e191400640d0100720002024030741d2054010300312045441c44e06522601010440c41c0c040c0d8000302e02d0f00c0850035200d130350581080d01800d0440c4c482c048840103d01c1e04d000e01700000d286c18503460721074041540003146282e131000103c40c1032085d0354944045c447d03580007c58682e0703401401c61060042500742d1400411803202c68440106100030a080c07148295811200039150130720a00110045a100302c10307110340c021004075031544050a20300360035240c00c443e074002d04600503a51404907105900a11015000b044034900074070407a03680780405800c0da440181400c0704d00b4240008d0b643d02c008041010351113210014026441305081010700b000c407007170302d00880701121001400c0e180507a80800c40030b80218402d0400040741803c1c080000e080281c0a0702801c0160b11248040c00b0140d0f203014020f007a18015202e80 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 798412544 1250 798411294 798411311
    0xa1217071101051b0706030f0e010b0a150210051e09010209131d060403050d0c090f0905041a150418110909070b0c060105011701030c050d0f06020c150702070602030904 74
    0x1074060142100d0500c252065290010320a50580c01903000d6589001040101c401d0349d4440700d081c1c0d43d02640240d0721002201007445004041e0060000c888445d2040b42c201085541c0d034141290001d5400c048918504201842c00324602a95503a2220320100290b080001101c0400c2c0420701c2807003a0480c0c0343ccc80302418803200150711107049400800070b044880a08048c240a000e030b90141d501c1d05240c605140d500443c40d801090f0003000c40c3c241819031001203180540d0f0000034540582b044800c101c04140704031a55290900241c007806401c100c1191442201d020002241c4020901c10440c202c01e0a0540200da0f0159001e9890501681c40c0001c41d03444c800d0742400d0110a410044c80d4800210740503d0200001580d681070342c2089c0c0310340001d90741144081503580000d00c0000c020003d50704d8148414100004400c152a100700c2148080e005583e4603101030341c010040311041c40c0e000c403c1200707a0820f010a096040840c074000752404a0030041e00070344a22941c03003001c1c082d94454440 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 798413794 1250 798412544 798412567
    0x4050a1e03240c0905011b0201050712021c05030105010f0c2111010c0c0b0a1103011712040b0307090906060207050f190b0c061b03040f020d020a121707110105 70
    0x841a159241d04003c120340c1104590242900005000741c6000a00c4105c40c451203d054140e0504455016101c0600b00303c3c055172400307825801c0811550441c0030780044100704090b20101280d046219859407900ea40c18080014143c20800c58000e0030000ca100c4003101007a48480c61300c401c4203428905041200418000b40c6507903a450360401d1003517181a9100c4035041e0b00c69215a01c461140714998001d8680c2e558540980b04410f880c00c14500c0d08000400c05424003c01c0c0e0b4403031841e0b000039a002100c0c851004082504643d22140200c603000041246096101c43c052000e00a406004c120107810424029a61000c1c0d00449009902810301c803001d9a0302c83c840c006405e499290320071480342d01d0b015264015084120060584e100b0240440e030705401040d5140601130b1110017181c11540c407a21006240050500240e8202440c3c10000000d03898454102010304202c018942101540d4600780385421034403030340b60300045c4d400d00c41400018100c002e5801d680300241f81094550130140f68 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 798415044 1250 798413794 798413843
    0x906051b071e030302071e0e1005090a0b190e1302242106030a150e06160e0103020304020d060207022710081b040c0908030f04050a1e03 60
    0x803182242242541002c00c518220302d603032060381e109034281d0326032a41d5101c840d800011054001c1c06100380703041080c0410190080040c3d4881d080750500489556500d021541041d820303034400b14900e48070240c2c2d800c0ca041c840d15112600121220804e4200c0c50451000d20000c0003410181c46044500c4204c825542c49010503c1c54010440034401990482c60035010309620081c1c0c95106081401228200038002c0d2418034410f00d005405050003006079903400e61134100d44400f102840d42c0e11180c000e07217040e080040030b00c20b504400750840c0c00e014000c4054905409030341483e040500400802c001600da20424000d100d60003a005038503541c043c80015646860a1466101005913100070014640350b40b6a25000c0c2c4c0c01005036104040d1608022500c886030540740303484860080d040d50b08181460740c0300c1ca1500340d85103400b806403604d401e0b60605560200c03c180300900c8000c5400d001c64070f0301aa000c4000c007040380017003100040400f02d0420040341072001074843c41d04221117181e890480d00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 798416294 1250 798415044 798415049
    0x9021f09180b2d120d0c290105090a0204140906041b020a1506050f0f240309010c020607021c0c02090f10080d020c040b12030403051c0906051b07 64
    0x1040707800d0b54404010243c1514881110b40080240348566034911810032581103281440e290010f8038012a501c43c0940725209507031801c6406042500e02040000d2040810310254400707100300c041554034040800032500340107030101044070300c104410407541c85842c0c22840c00d80d03025200c403036203a82e030300b00010000c1030800c9000f0030140001214008107680400c0c0e200090384076281103040320400d940807200f140c480b8090346401124002200c8182d140a003c040542e4000a0000348141d0410010502070403180041104420020092280400c070030302920300070b080a840206428030342400000d55890150701410510303030a200801780c0d1503100c0c3d92090400b64010b40403041d981400401c0b0200c02d8400c03034035400121210350380400c0007400803580d070600c0c0115078018080c03101c0510800c001044800030f0310342c1c419200a15500140401d0024100030360042c40038250100b42246003001001070343c0582801c003d1100c0d814002e190700101a0344015503507020101c280c0c4200e0a185180c078800d40c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 798417544 1250 798416294 798416299
    0x40b03010303020303010611030a0e1c1e02011d090106050a0302071e1511040b1804050c031602010c09090e15010f0503070602070f051912050109021f09180b 69
    0x110070b154002008504a07007981e0b6035010707282005105107840380180b008120024215580050003450055482d03207d501c100c01504600c078525545642040ca10480c503c0070300168000700034155a000b00745181047c0c03500c110122010348000002d1000c2d041400b0784800d0006c0841e6140207107100f5419103000c141e000d00446030544507810090392900d11044102c403150202504d08100d00c0c0c2c05c0c0140e00f807a500104145040c281080c100d020300ba048210402100514510003503101d90319402414055803c0c041c05641d6814014640c0d010310a92880c904203581c10056004815030740900c00300125280b00c200058220803048855042c941c00172501c00b900d5452100100385008008841003c6070300460840b07900d941d6599050762204c9551184000c0f081c0002c50410060804101d00300c02041414980e819031a11007a00e800400c0901e4000d480583d912400d100450030034504d0248072000c01130071018045198003008000044601070018418032000750710207125582d4008007400da800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 798418794 1250 798417544 798417547
    0x140f0108090a06060f0311041506031d121216170a1404110910140f04020705100e100b0d030f030e0a0f0b0c0c3304060c0908010e100e03040b 62
    0x700c4075204220717003842c007040da0f02a4900502c40704a241074030911800315075450b014408180f03048420790050080d0f0b09000d204900d100480202000140320002c0201d0100c030745182c48007200c3e40c0c0f0888641c0014005031054034200006030a03a500200309403071880441c41000000c1e50380204071800303004002c04180c482e110b42c001703100403c10341c0c601501e4244025602d0055035550f0800107502c0710898401d441440c071410709240198200810f65046d50800544050b142c05960b60703446281151113058960020f03543e00550f41c4000d070511420042c0b442c1d2900c00d008941c07034500020851000c46130002c092042c09002c000c505c40c0203421500b800c60b21482950718645250601c041c40340c94046007240c0445880e000030b20568040c0041d19a0185003038020200c284d00304c45132802049da100c40181d08071101d1480e414205003111403885c441c5104140101f01c06c1c40142c0043c2c54940c0c513400022041e41020003280200c14000f0306a8090150783c0001303d0602c3c40002c0765411841903070080e03902101c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 798420044 1250 798418794 798418799
    0x90e0703091b0f030f0f080f032406030f060406180b090906010806060607051203180c100e060f09030d03092a0608091606090807140f0108090a0606 65
    0x20580d10894419002d02500421200525401c0c014500140182c0303c106030b401e2801e00100700c000b40c0507011688100e1010425000da501d61003015004156100c2490400200f0014145059001c0190340c044550342440c658000383c5c009000ea000007072035841040b40c2d020006519a0b100d800c0840103140a03000344180c0310100c80d00038080c00d036081c6100c3c01b80454202240140c040003552504071001080503085644451302000a07960015109954501c40c6100c4564050712800017140a0381210000307404003d01d03641c04900b41010043d0540c840c0c220b0440c20f2840707941250710102c0e861801c40d801c50f07442c240681c400c038541c0501102c07540c162081003420100341d074240d480705030a41d015842e08d56003a031000c4020f80858202e034510941c004102c41d0104900e80c068042207402032041c04c140d45a01e90b00c080404402005036000d040096108401046504002d01a040290440900c0c0082c800300180115070440280b101d8607040240c40300c00283d03441c0080c8038010340260321400501c102076 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 798421294 1250 798420044 798420047
    0xc08090d030f0314060d080906210a2417011401090f140103032106030827030304080c1e090405070527040f0219031a0c0c1507090e07 59
    0x2155080c210b000300c1d04d0000c454800e654000c0049208000040c1010040d001c41d0713444a80d103400105c0041c1d040b00090041803101d4002c4030b500c41042650b0804884541380161040066495038058000144050f04c2c0f64100000d0610b0b809096a82200701000f4100d00c428141d80100120210b401d42448403600100d0310f0215500000702c0c400e11210180104204031001520444081c80001d01141041203e00329010141800180003021150000f90b15603030381c0c0351012030b54003411110301c0038540003401c419a2040002103401e440c1c400d40c000c42c1407074106501d0940c2d81861803100f611170b44041d088083d1841c4000701c1100d00b000b0291840340e9a08040c83c100f036440032a8082d0a00c02e0301004140c01d040c5d000840824065124403540098070b803140e8803401001880078805a0300110010501c1c4504050029000c0c01948583d45808103001d41403e6003064540103442e402e440350302041940700481000441c03001c1980e1050451201c0d440c0c0c1c0001b40c03200340c0d0650080466031000000c114090703 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 798422544 1250 798421294 798421307
    0x11d1008270345130e0607230d0917040f1703090a0909060b031914060603030a0f020a06180302011a10030e031c1e0c0f0c08090d03 58
    0x4520303100071850140c40201009a00c941402c5540c1180c0a100640d010280c20300c007003c1d07036500050103419240741541045021740d1504007541c03200d41c0c024410310510300e52001d071440444600052a0349040031264040410b44139007004410301c161034060b4101406105901c100d594552881260390f07456032403400e04101507040c418205c1e4161040d48140c4224004070448907280402000c541c0d030b203810288420014402c0004c240c0303185554502000250b00c0404c052404a800e203a26003150601b5803405009030510b05c2c044140300d800c90001e005103a203001042e15420320740f5041c80c40c060100c0e05412480c0c807654190141080e805d091100e15844c8612409404050107607009000d03400b8408029624101103c0803d078000603a42c0c0c0c40c2c10320a01c070b41d0006a28040e12000c3d0780c5449035002240550b20f04041c2c003410400e54840040900408806042030003450541081c80000b904141c09000858125004014840900000b80401001404483e54104018050003e1103240d080080c42d6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 798423794 1250 798422544 798422557
    0x20a05060706061d01051207150f031b0e0f180601230304060f060b090f06030903040e180105070f020d0f11060415050108030c06010312030608030406030209011d10082703 75
    0x7c0460f0540340d5410803011419005492a02118129400c43c0740c0080f0b0349510290084420150350b00510301c0c01800c1c005c15000b06119540d200461b15100000300403905400c00e4881d03100310070f40010101c54124514130254800001d08043c0c9040c80341800d801d803030089900555414950000401041040c1640f0551944882000030401103455150b440054459103412584c004040c02001a0500d4030000a41d4000444000c0e40d050940c0d03070110140000301030340d84440c0030641c150410050f00c024400d05601c03054a107040d241595040e48080e4035010074605800c20045e5440c0000c02ca68056038130602000f1801302200d030309141c10b0805040340c06644402c0c071300850821000050b005400410f45491801880251201d1703460b42d540c004c40351800c1c5000005254403501c00107070406091000d4802007031191409030341c400ba1400010914220031004225050300003d800d1580e80f20b640d0340c0d411381841410b01d512140c4402d4002d00d141c0248200c1c91122001c0c400da0912a1080400a0060f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 798425044 1250 798423794 798423799
    0x40614060d020f19050406060c05010b0a050a0e04080405090903030f06060406021e16081506090f040201030c1101020d060501140703021207030e030615090f04020a05060706061d0105 80
    0x215500c4000c10000e5120041401070f6000315000f404100510b8010b010301403c80200220500c80d42d96400402c0950ba03065100c500881c0030343c00c071101804000e01030203200c16011125a0300982c10070703001a44140c0640a02e036014008680003174204160501200c0182c00020040c80c0d16103040a10f050752940b003243c005141a06c540003003001c0b411310342d0039507060b1120b075009032180389882d05400d410700003501a441d40303a12a210011654146000e410005018110702800e40d21104201d00030000d00c0203450240140203250800102001303506010b500540e0918011604c1019800c04031112603a01c0d69031646540f00140500049441c1ea21442c22603000fa03e405030760001407c550700c0e003801100310181c0035030800b500305491204003034010412a8030a0030070340744a0320b03084046407618104803034a000710401c2110480580c0707008803901d0fa0044c01c070b03081c009042c030b003660225005003180e10401703000e25000b003500d504000d07682c2c0045000c0d044184c2c540020384141941d008000a003841040e0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 798426294 1250 798425044 798425081
    0x51605120f0c060a090b040303090f080304120201050c0a02041103011a0306061801140a02010c270501140904050a09120c0f03080403030e010c12060815011217030406 73
    0x1060500c0100350700400240403000b40640100d03074014080140c1c0092420001c2144100000c28201042c00141001d14060707a00d9881182c02d00d081501c04c0702e002e1300246510b0b070061004104003480b146198203c03a03420301e001c6d505e4140d108000e40c41c0c901c1b1500002d45c0142801c049403180c68034240614122180100050720031191010f81c0061071005443c5203070030100c01c00c80c100844000340c0d149000340e81c041c5041d40000700c0740032604416411020a11380181d46840c0500d0358a40d211080c895240904510003000d5010000e101d01e84061500c9502c1c1802000318a00c000c18404409030b0b4000407001d4410310041c9000854030000388002001120101415070748001c11900c18083c81e299198000b45e034038082b078080d0b1019500c035240100100e0816883c0c0808031341446081c000c0090b08980d039110703400000076615440094500d04d0700f000c600e0360702c8103104020740b4450401035070460303140d4924035040d00c0b064103200644141e141c1c242e914065000050008002d029071142400405a01016 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 798427544 1250 798426294 798426319
    0x16031d0406210203070506030c04080106051002100b0307080d021c140315040219030504111005090f1f0503010f1a07150906051e0109052e03051605 65
    0x40200c079920300a8075a4400c10403960586041a42c00180410340000c084588081e40e510008460798022141d11a08a00204080140030424007a200103010100c4140801c4051010000e54031440650703524051503c47e22241c01c41d48003403040e400584134141c29102c40d11128074000c0d54440c100c04070b82c1480c00301c60074031640a501c1034060803550100c9000451450b21901140c82810b000e8214055015500b00f2041005e9416090f034001c8002c09903e01180c01e240508150a02c49802d0600741c0c0103000660f1319550103940841290303039942048030041145230480020403a02011140f0840252141c080c0d0584c02135006800340d030403a00c5031070008030441e8898071003c500c010018000101004103101038000904100f0b00c00850004110001907002d207113407911410b0311019500c03242d450150b00d0480c448250014142c5000d090050418446410b007001690f840c5503011140c80f2034a1000910342e942c0c6001100382600031a080300c1101d884280441c0c42c0c0b20282160300c12544103280d2705044 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 798428794 1250 798427544 798427549
    0x40e1e0708010b06040b0307090b13030308060306070203040501140d06141009080d0305041110030f0e07030b071b0c080d0306051f12020c19030f020a0f120516031d 72
    0x480d0f49184001e00800d051a1502c0024003190304094101024406419404118003003104040c26480500d52405a055031030760502501c4402e0281685029410038820410340c036030004121800c4031000c0c64003508444101c107082d00b40e0b00420700752864007800c000780021709114a105a460750035044a60100c840c41c51441a91003115078400c3c1c101e41c0d013000800841c01c50103540300e1075220b400b601c12180d040341c00c1d0002030110701c404d44004001c6680d0761640803c1c84018400c80000403007080c000c200c05415500e562101c0c44d4003d000c20200100c080300c03061020341840b606203241d0f83c0422040c00300f0307071540000340e01d506e4103214a5001070314041000849203030083d03040380000420102960ac04000fa2022a1560101c811a8201a4007005540e8100c4800c000a650f81e5081c00442c01900d0380a140c01400035000600389001c551041d450070307010500135510702c0c2215602003801c02404480e0042034507640235060040c8a51184c5400c075030140b64014444607101d45100c02c000021f02111000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 798430044 1250 798428794 798428801
    0x605060312070506010315060315051605090603010905090309031c0e0a06050a0e0111030706020304150b0307090c0e09010b1b19170c0a0f150204051c02040e1e070801 73
    0x40940a541300d00f00400102c0c0004580920070583c3c200c0101d4a141ca039116002032120000341408400c2d078402c2004000c0404c103108014689861410900d04140c1c000099005d010601070010701c3c0303a6883c003241c1c40060030021180c0c200d20103400c0c0e0344030101c100c0168204207104840800400d4044800300468070b45110030368103aa01a44600c0d04125001c0411140030640d80d000a050209010850b40212805c201400e48284030341000742e0b481c58103140034541940d060103039940300c03800c081d01c20685a4002c030307a00059504446000564041030b160485010b11040712003508101c0c400f0000c26540b00c0400244010484c0d403940c0d0341c8103007844010664071500c14000d80d00200c1c12001c900300159030402042d101c1590700b40c0c2030f030820086040c1c09040c401c1c100002c940d500303a483c02d000104003140d010080c4401403643c8c11403c1030302c2c00010940400640c5040f240f00702c5031420a81c11940e0303139804050324101003c2200d05010aa0400365184209401d400b03915129182001510200500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 798431294 1250 798430044 798430057
    0xb0406082a0415051c0b01120527070b040501080c0d1401080c030a0c140a0317040501090806070210020306040e0d0203090a05120d050307020712150f090b010e0a0f090605060312 78
    0x8201d00f0880300300c09034860062402c06c01e82410405030440d4820052020700a4a014840180118a202000c600c105002009603260181e440d08030202c2004a00590b80130f45d001c03a0000e003408402540c4240c51200a84140d11001a14500e00140100032010340b0100c83c3c140c40c00507007140d44003400e1804141d07450b00c000500410f6100d1690341480f80c0000c00004008442d409000300d82003980b03981d5100300794840241c51541c14000070404000e0340d03a118014a00608400c4064011030400490081d2541165104009020f400201040203525154031070035100f10501c2c29207214040308003009440f80d0000c510140708418079040401c2900e064010221070001c0a4020058603a0b0800151801d8100401c19000c0d400790b00800a0780000420f0100181ca2240c04080303d000720f4075181a0464164002c03040125282c91071402c0028001c81c4018151680d039a810452a610080c40f14040c250941c04503034141d007081d000e4010804075400030344c002d240440035100039003010700707481c00240500b0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 798432544 1250 798431294 798431317
    0x11010305040f1104020f0c0114010f060801140f060d0902280312050403020d080a0201050c0315130b0a09020903010e060f070f03090c060c060e03040b0406082a041505 73
    0x142d02c1d00d00094020f4801c0b80c18100151016044c846904143c1c507440c5c100d45000b08580e5115008825a003806550303060140c401003807940c02c4a41482801421040d050080c520b00300084121008160794096a4118107240201042e5035510300c01400f00c06031481180403800750550141c0d40241c41034420f880ca03100e046042500c80900d10f507072144000c00c0d03020043c036000e102d0100001310141c0c80b60280d2040190150b80d050341d81d082c080f9002421283d00504a030071608043c0b0521107140e03842129901c03032040071264000140f1402000c5c03030003441469201e80d8408005800014103001c1900a420442c100b14000c1002e481c59660103074490100301c840b1810b01c160040010303a84d1b409010345013000d100c94607000a60152035520700c1c1600301143c10950204410401c02e60030090035000d021000c4150030040c40c02d140c6450107207c1c0c140914011842841204000269010100c19101c00301d01085500000c814490301d0800340c60740c0c85802410114000a044032800030701543c115407040805 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 798433794 1250 798432544 798432563
    0x2090414012a0c0215040b07050c090622270201032a0c080d090b160201060b300a06031709090a1d0f0607030608070e151201090605041101030504 64
    0x802e1030482d00e40d189018100e80c0701d5401d4070490b103011410005000940781240c0203907942c040c5818218944641e501c00ca034400c2001e43c00300009500c2e03201107081c200c1d04007000c981c0030f801d103407600304082d0806247c0c11b4070300700400d102030b5081c4d10b104084088450007a01d04001e408203156048290352001403030b0b070803010b200d00c10381900540b06a200d04800f0340250b01d040e007401c1d00110500256490300c101a51100c80300c0d814400d2541c515110b02d048410f290000b000454070704a0b42008074000d1041c040b5074600324105160100f0424a02e00800381404080c591540c40d06c004c408009000b41d000640c0e000c4901842402550402421510007110041407460b4070b6031501c0d6000054204404010126a1388158852028101f0001d1101c0b1034400340181895207003000005046030440e51003040e07246d000c803004000d0440000c0035560014145840040307925603043c00700d001c40c04982c080c0c02e902d628115541c4c06110003a0720140c0a103101c1e080400c0b0f80d40003440114241c2b4415075024044108 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 798435044 1250 798433794 798433871
    0xd12081b13141906020604030305160c030e01050403050708030703031103070903021c021809010b010f12020a170c03040b01050f1c0c1e090506040903080106030e07030209041401 78
    0xe00d03115401a004003c052140d070b43c41c402e0340044294429030041c000769100703d0a100826816020780d6600c540a000d100c90410000c801c01003040707807890340c06014400040c1c10340b5420791140c411900130316040822101d040342d80d0703805590b49501101d030a80000e4906005049105d03100340450b4021040c560310442c0503801c1d41c08000080d0301e4202e5180c440c0103082aa6401a1904200d402e03419441c492540c009181c4400d00c1425508607810582c10030414412100310a5004000c18803402a80a80143c644107801d009807110341101031305820845c2e09004010340d049001d070095200c2c1c1d100b01c281c01e1143c1d0342d44040c405c01201d202c060a500c4182c4142036000b201d0700c0682c01c01114050300d1055481565008600c02800941088018040094905201c05607540c01455000001604c0404c07040401c2e0302c0003081d520040c0143c3c810140c031a1084460001c08104e040051900100070703082d64201868242402402c800b608100365003014914191004145400c81c41d01110540105a050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 798436294 1250 798435044 798435059
    0x70f2a170f1e150a0504111f050708040e13140114010e091c02103c0f1803110d050a0e0402041805010806010b0412060b0d12081b13 58
    0x1400d030807003100796108040c424010545083d062074010381224000061900b4a400c00d085004100d400180c024040217443c12090320781e155440f19039100034a809500d4407032a2400704014403565212081c03c280c4202840012001450783c0340006101e40d030210501040480d401e82a11600070312102c444c4003920040080c15210715056a0103003404090300c1001064904814031680000c940f0001a400342c03075120403082c1d0a05c18030000300d0f91402d0051801d480c00d0846c003411080540002d500c1130044a00d200300c0111500300c1c0e82503ca49480c2800b4800c0100d46c076a04805d80400b0a030300090401c01d5501da09040495264020f02041d9155468841a8030041e2050b060400c08103802c01da08020001d4005200e50072450185600c0c100450b181d4035180c00341d841c284040c1c01c002400382d020482045650b101855003024150b000340007150101c0000c00050f02c1441c8182c02922240100201c080550b0f40440000d10039611000340340059035200000c1c0c0312900603d000449004070f028000d20225 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 798437544 1250 798436294 798436333
    0x6060e0f04110d0201111b04060e060f1c15090605130b0c03060f1302071b061205070309021f1101020a121a060c0c090c0708070f2a170f 60
    0x1640181040c04d01b0040820800745403411a0701d10448000d02d84941c1d210324070302401a40020156440007202030b0a1500018880701e121246d40c40c85012003015003010300c41c81c1140310302001d8102c40c0311800280c82000c40d0000d000c00a8040354421720308400220310800b01c900f4621181c0c4c00c00c0703441c2100da482c8140c42500d50b02c0a000503a01180000210b08266681072101d400e07003030310078005a142c211720300d4054060350000440c0c40903003074800c0b01445510323404004c840035840c2032038020425465401d402e40090212001c007a40141110300004c02e150f50000c1c6020b101022a84c44d030016000c1080a28202d02918043d40c002500c68140b00c0503540352604100b81d840014a50013811441c22000074266902c9001420540d400920f541d0f151441c0550443c1d5201085180161901c04113659190142c40b601400412400e2414022004d111078240035910340c0c525810701b44812190740c0145003028240303104621483e000d01e02210b485a00205001c41d0508083c0000e1100391031400a41245 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 798438794 1250 798437544 798437569
    0xb0901031a0a02160311070801061a130b0f0a02071e03020d0c150804030e03031c021303140c03010b0604080628141e0c04151106010306060e0f0411 65
    0x30b00382c082c8030740505203511500ca40c03450380c840d440c5c0c0d603825920901e2250428905900006990349000001c10408041e0010501130a80440c40c0b2030361001020340030601d050064220508803440800c10070801140c00004000411050b001c940c2c1241d680e40108410407a0900e80b070034010403841041006007801e4110842c403a208140c04491346484881c2c0b0b48040d0034403940d02c0d0004698505100c185a00404405425803042c1c02852409150300d00c0e015001e080c03150300c0f1400c60341c00a0034803050800548010b024542c400b440709403205850010540d0340c9038850030f00703109505e0140c500b01c4501d0802c1c11a03044603480c0015003025513a03c90b00c480c440c40c040a1103a50703020b01900354010a520781c4119041c110780c601181045082c100b0602440c511032400f5940c3c05d00440c02400070b844402d0007600c04648901803448103480c0200000c03210768120300303210003c4d072142100100802005802240594136410604540341c0e50ba2111103800600c1a1800703444410740c803900205900f0070411070fa05 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 798440044 1250 798438794 798438811
    0x230705011b110324010e040809010e01020109021503100806010810020a1404151725090503030d0609200a031d03070b040302010b01090305120702030f1006090b0901031a 74
    0x42010b01a0301080c1041280300001d031040f0880052036040e1402582014050304041c06000620300c0c25650303500803485084080e6060009480100449030300c04d4009559082c1c1c054400512074030b0044122819070015030348040d4400c443c1c02d020480c184005100d60403144884000c1a11645a41004c002903101b41500410008641d208100c404071410080000341551080e500046c0e00c0d11070000e05680d00003045140c109012410302124903900018800401d0410804442c0300e110800103481d10300c460b034042500340c0000f203101e9a01d55180d0b0311842c100c0d6000c85080c4406e01800544281441840c20040c222200c14012810720758030951050200385210802d01e0401c04151803101d07d0740d00b081c101103075000c0303086040004040d42800b83d0006180203080400d2014219039a0a0f258400868a240c4d0b10304003140c0c1c0025594100310300144c1c3c80c03800c0c003030342c41e01400308920320040d006078040d00442e1030824281d081c4501303048010f0f0341200c0d0403604400d00d442800400d5100d00401030074240 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 798441294 1250 798440044 798440063
    0x604120504051c1703040b1b04080f150c040509180109020a03051b1e0d230f0706081519031209060e0a0e19020c010504230705011b 58
    0x5003503c03620312040300da6010745125500c0d49150b1405600c407014a81800e94481d40502c18800003030206100907030020300e05502001030003408400ca0115000701c1d03202c60318904c42c1014024101d000800d44951750140c507107081d41c3d903a80750f03075a03070300a071045104440d000790b45140024401c20600100100b100381c400004035550259400080320100c641d042a10241c1045920b90b800d4010411507a01c0d03c103042e034200601d00c0c105c241100312000e10030b10113401240c4086000080140d007100d2000340250154103900c0d0800e2103804c4170b5480e0800c0f03802080c144554000450501d00410589102d502400740041c4003007608024099100310a09410384404080c28003c400190100c00d65140c2c848150740e008407162600078014040346080400c140182c500310070074010401d80c02002d82c0e110942001c0205070800902d0500028070444c145103841d075180005010400124010310001149521100b052f0582801c4007070391140c0c1503109003404a0101e0880d14890386a15942d040313082d00400010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 798442544 1250 798441294 798441299
    0x30c0d031206080d0815240c2d061f1a070606060302090406050402070b070f0c0f031d010527030307150b04111201060327030c110f030604120504 64
    0x4a18007040e40d411078021411071030400c03d0b80d10900498801b942001c44001c941c5c55405104d205082d000302c0003411259400080d503207046501000001500e1640051300c2c41c00500103000c0048a010340d07149240c00303001c0e01c00800d000720707441005400a524140742415800340342c140c00c01c40f402540002a541d031202800420b001c90350320700c104801072019071000750340da030044001c00003204c0554001e50b20583c81400441d0204680011181d8040c035030b810f021103008030103101034030724140d4010000d201002000c02d5004040d8818a043c84c0c1003884442400b204008500540d042c2c000c400070f0102c0810300130446c007519070940c60030003025040034041c0c2c1d1400b141c82d1100480c100f030119501c110039032180404400350a26125505452100403003c80c10720200c40c900d5031000c4010b01c41c1d0740c20151540c6c0c48002191411140d95400c41803c000380c0c007288101e160141040b00d83c1350003614600a90311075050715081a4541c0c00000c50010080c280d40d03a9196224940228500911800c00c0001e01c0301 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 798443794 1250 798442544 798442559
    0x40c090305160e0115140901051b0a120305130b06060d021303020306090a080f0a090510030f0b030106080a06051e07110615100f0e060301180b030c0d031206 69
    0x428005a1000810700407583c241442091000b8041c4d200240c540010040108055405040f00d0114030010b0890703680d031a02d0500486040c0241da030401d01d181504203202c1e59070754000a0704110a0702c6158800c0c0f212108190540494101325200d854811080c11150000303a40d000c8559448039004184a06200b203414000f82242c000d00d40d942201d50001030140158031341040069481081000107148400c8c07582d482d40c40a000d01101030580b41008199820380c907008030200710140c140134041030001e6030030031720087c00f91007180d100d0b41c0080e2a019041c0040d00303042c0954400c1d078903039031b000f0105040181e4481e0000c160060901d103116220b00707801a03c1600d10440c42d0b0280b2684d47d154032040000420417400c0030400f8100c1764140f40380700c0e08801a6115010300d100148070741d040040b144100001e041d02c204c90700ca250150720480010011540700324201490740c0620fa00c2404120800160081c1943c64005015030b035403000712807040b100040d200390807007106107011a4010611070307900ca12 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 798445044 1250 798443794 798443803
    0x6050703050c010f24090b031518010f1b030b0f130906020d061508070905280b0d0c0302040b041a1902010f140411040f0e03030907080c030a11040c090305 68
    0x1001a0307a0703c5030b1081705c904c8102c0040b42c81d001c1e04070480c0802a0003100c0001940d1851208000080d1a40d90400034035100b40c40440b60801d00d811200a01502480e640341c80300034400c1c4441d241002340b424582e841c10500c80e100c0e10ba01018050304401500b0b440340b0410400708450014100001e840d03035076039000141540041e100d03154124101042040c1440070410308405000688020080007000f04010a54401034250498030242c5502c0d40009100042154000c1191240c00388074030000300015088158800a10030b41c98040d000b003298508501084040c0d21482c803039610139810500051040b89000a244109107001000b29071034064180001071080c1019111000984d41d107000f084001e2400380551040c00c801074444a160b49420359922910610000d2030318003c55843c02c81e85039600340fa2340712681081c0c06e02c0441c0e45078a490540542d841c51540149001405101340128103424009131651006a02c60010180305c15180f0034800180790340c40034101042820f18001000c01e07810b02 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 798446294 1250 798445044 798445061
    0x804110a091406090106050705030412021c03020d020c061c0b03150c0a030510030b040b090f07141807020703110f0901170606010f021203131407080d020706050703050c010f 76
    0x411800545002820801c1c1e03040141e001d001808402c006c0c000000d09d0200c2113030162404188003c04a031401d0003c92441c0e40703682c0352845034603501c50800c414036400007900305481425900321880e40e4001000d1040b903006010b20f18400c101049040d902d00c40d40c54100c00740100020b03040300c14100040d856869518400e03030790741d400340300e0020702008919814025a0343c840c00c15007006ea240d9285542e406080c0b0f40007040a4003824122001c5090300c0b030300f4081c50840405042c212580c15458800c400011100041294030540510181410350b51002d84039500c01d21090700a45915440c54481c0c0d10300001c1c82c04071a0b40641400400d18007a601c0b505600e0280c20050b51600003001501c54881c60404041c000d64180184a42c103c01d03050f50019203910545500111141c803929026124482080f034011300400c1090280441c540b090000103001048802e000211012104d03c01d00580c0c40f4051809080000b40b0301b0040e22006c00e006400800b2803000c10400000c40c0d1780d092105004448110 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 798447544 1250 798446294 798446321
    0xf1204061d01092102280821060109030f03180807090614030106060e060a17010e01090c031a0d020f030a0506041a04081b03130f090c0305011d04141504031d010804110a09 75
    0xb980d00c03008c0660641c0c0096805402030900c2100c46042d81c451400100154900908121201402e00c44a542d0284031200416a030000c4601c3c207070b00c07035040d81c1c0500000e006038058441c0280d00080103140500401040301c0450b103d02242c86105006d01c4029488803007070509021102036068002c1208905244c02894100c88122155060400d80c1c4140c40d005c1a40390101400c02a050b210700014042c0003014a004590b101c61046051010072844051a031842d6498051045803800b80000400c54a114911501200c211000e000400503101c2ca41a1000b4180b040c046c40301103414062004101c4010098000b2241060343c02c810341c1c03c2c0c0c010f0303942200e44002c00207401008000c0b02030085243c0d85a16003421700403981041614078030b040202c8540b00780380100381c000c90240510000000d0f2645450019501030008003032400980200941341180050700105070032140b9100c00c2e02450005074165142c60458695880b180000900b10030400d0380100120000140d4003042d12554035640b904 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 798448794 1250 798447544 798447577
    0x2a0e06070f1b060315090c020f0f06060120060705030a0603050105090a0b0109020c06060f01180b0310140612040507050a0305060a0c02030f1204061d010921022808 72
    0x150042034980b54501d6009030140360504101041c4208450f403e1016201700b15000a500080aa0108e20300030701480303c200c2602900e0103d6025110110314684282001c2e00c03030707400360245840b00544840e403019120105400840105100e00e20400046404c0420500b010072015101d454031400c482c400c1d549618194010300c6d00000300442e11103051b00401d44010110b042005203050b046c0c075190020310291041c420f400d60074000360f0103807001841002060541d0385030b44d911642000010783c4280d54110f00b000114a0002c1c181d00500000d081c40c10010304110700b80504070000310440b000c0a0800c0303a880c080c500000c00c00b07455100480c4000c0d800356004252a0500f001d04200311152a400c000445d042002103407403070311000c821501090003036a110446030360b6130300700b41004044040500c2d0702d02c440280044124041508418081d81c0604803551b680c219280301c5038082d44180440f03501503049040481410041d0042c0e01034010b903100841300f0f10b24500d64801200f035000a1100350074000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 798450044 1250 798448794 798448823
    0x11d041508100b01020d0c0b04082a0f070b0f0310080d05071a010e041203201b06041104090c030204110c070605072d05070f06032a0e06070f 62
    0x100b03002d00f000405080c009070801503070780040205024128003010704460845800f150070080d6004c01c9900c1c514003206504c0e809030386041041a1b000c00452542100e02c05c1100b1619600d00205050040341d02802d0710a240518505000c0b0311a0401030950441409135040041c1c504800c0c42090400081c0d581da6030703645c000c503150520f680d01c44403651250000e1894018031259002e4a900d681058000c0c0a8a00c01401d840d0201d0103882c2ca1983d50340007414103501c6403803540901d000350070354001d10007000c2d110001c600d00b180d549003421107001e00071102d080950100e13800e140e441302c000c0502980101105c15103d802190030f40e5040c240b40c020300301c000111701c030305600d0500c031160241403035190040c42c11905480383d8501280d1014172010700500e800001048000070125910f5040c1d01a06a888180e6030700513110502c8524803c0c000803d040040c26030f075030001801c0c500c0060420081c0c0c52002d850100049644404032034001d50010710030008800800d104000001d01d1512807194001c0c00712 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 798451294 1250 798450044 798450073
    0x7052a1501090f020702060d11040305070e0a0e011b030b0406050d0807120206010e0a3303030f02010e10091a04080703020705010c0203060403080c04090204171b011d041508 76
    0x3020308080f2022544117001070b40050b07650401315480c040d607607030020400b00c1501603240001d1180e90b00081c030b60700ca00c0700c0000d586150850098807403c0340380c0342040594104100c1c0707802c0e00e50541c28403009080c03a140c1c09130384030b009610280e480c910140c40080c14584600c007054103101496011b4803010804124807041000b040c031000c00e402c0c0c030780c40a016507524004c0404510f8a001d0900381c2c14130f0326003080d403503441d0881005500c407042020407511300e440d00a42541c494441c0e070000764006008004056009c0e401405050b00400900c1e00074032000300b5040c00c0400900b020703a003c0701c50031104814003000c00d0041903028040e40c0246281c964a000c2c51134040c0c80c1c542140c0c00b05061041141400d000769070041403c0354403130f40509103001c1980e02c13020003d0b254400d9400900784580b020501090348896142240c030006144011a26102c6054400141e403514580140e40018204540d441103d1440183c2d440100780150010885e90724404245080c191650000c425503130082c0c03400302c0b500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 798452544 1250 798451294 798451301
    0x30c0818071a19020102040303020d030e010209040207080a0917030927040318060807090504090606030b07031a0909060115092c07031a0d031b031106090607052a150109 74
    0x140f2090008500e410f20b50b0380c010351241e040d0100e100074590b1741d80082440070420b40480746260f00c0140304550380d088625100380c90f5004510b00e040000d6840700081b91185054080c0b4500300f03201c00055041c014030204020001c504241e8410211a505640c807210080000300c0902841c40b0f41c4580204003140d038200b46030710340c0300d074030000400c82200184001560000648000d83c3d5040e40c012840315414181080545820340c001013400c4031480c10071200e5945a070101038814580d0100c0008140c58108101c141207040d00d50b030100f034000c00010402c0c2d060700c01c5240601c00303107030030282030241e17030340c08041c080101002c0304051a640610b000d8942d811409802ca81c0040c003030404104030003501c601105254149a4190f000c5c2a0300c10090050600403030302c020700701c445450a14041c030040d19009200150b4003159a100380f140c9400304405c0c1d403000c00d06a12074010b030355906003058005c1720b181c07065444c010181d0380b2a00c480e84c0c00b03041c80c03001800386080300307143e14056044a5140c4200310085 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 798453794 1250 798452544 798452587
    0xc25030c050d0f0903030302090612240906060a050a1413030303060e04350315030601060206091005130614060909120d0f021605011a01030c0818071a 66
    0x400800038880f00c43c00ba0440f01d00400e03242c1500d0010f03102c414030800708810344500d05000d00c0790380300e40b02044114070240401c49144100740907035a0030380c990b04040c001000700c141d0b45958041c40034418802c034180320328041c0040f1415458035440c0600c0c041c0c00240f050b800f480104040c1148501b0a00515400d4001d42c0300620300d4120307616040c82c2946444803680038050914075201c0ca2039041060a0b021420f5440408060401c1c176541ca08058640403e0300340011503d9009000700c4000082c0940013003491441021a00017604503041102c0e0008000e1074010726420079503074540c41d407001146c418821171030244a050450805070600400f00b005420006112400c903034000d14500b098000031200382c0740d032810907903400b04402441414010190041d4140100e000901c00400c41c1404015000380c8a6078400c550390a0050482500440a40306a10b95290101e005034011400280d100503200301f1036903000701030700c9804d51124200300d14004000d500f100311010119101c2c0207a05982e141002 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 798455044 1250 798453794 798453797
    0xb0a320f01050102100f020c03040902130b0702060418020706020a1d090c0a110a1e030327020105160803130b181515060a0f030e070305060c25030c050d 67
    0x2041d6140200003550340d1007180d09407845035150500c6032450502d5405030b0f0500340c1d6041c180c0792200e441d003403e64000d4002c00420001c0072000b00f8002640390003001241c440c0c07a000342c6003030301e400e041c290f203601010b03c110f106c00d008039802c01c17941c004143c0600c0544500c0f4403a43e0351400102c0d070010182007002201c00c0d00c611410860040c0140c6924075000c0301d0000219040c68030034000018016414246242006000c1c01d0310000e465031032500492201c070b0100c0c03007510100145240c0084d4004040f4030124582d2308144580762580240d030080c00030304000c8000c0001c07910b845040d640c4814441d0425a015000c0302e0111031050b0400c2941540c0c43d500c503051602e4111117812030142d450fa240d10305150702044030115400700b58181050690410400c5d8090f103510395480c01c0d40802480c00594200d03540019280a90407170031918003140210032a5084401802d498540071319091003503100c1320395420710041000705040c02d480200700070182c1c82d006c0d807034083c007004040c20302c1c50501000611140 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 798456294 1250 798455044 798455071
    0xf0b09060406060806100c02150717030103080405090a18050714060f030610052713140406110909040f050115030308010303050703091805061005070309030b0a32 71
    0x1003d542d000803425400782c0c003120891100f41e0040310070381e68034240c6017020b17421905800304880f0b85080754004090491051460603e9010381005440043c0000e02006000000c00c00c010822440d00d00e5460350084009240003e0309044040c0007414a0356014044881c1d0304034444c10401016040c119210710322099440e2480c2803060884094130780300003803a551007000d103408021200c5210303000382c1c0c5e01031100e003070101c401524101d100140d030110041160321130701c103203001c040c18864940104c0c0300b00411903144060940b51503680d58003400c250b0820025008040c0600c44190b9a401c85140c00f85d0b0041807480811020b0342009400d5600740416000b41a202c001e04200190b8451842811645c0516085442e00c0e000e1900b10742d640320380d510540702079540003a00f50380b1401d1070b0b012078000c08003141c0d100c807003600010065810703005054024001c0b0328011410001726500782e130140d40c8281034840002c0c8510b126607080040c541c1807a882740303c4076400c2501c40c5440c0d0070f50301070982080c0d1800c0b141 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 798457544 1250 798456294 798456299
    0xc0c0506120118020417030702030c120d120b130603021e03030d0b04110304110f010f051c0e0a08071416050409020f090106021f0c080103080705100f0b09060406 71
    0x70303102650103114250424001ca5039002c50085942d0540d4054003080d205a4000c0c2c614100442d942d400401040e40b2a01403941d003000d4924015000e00d542c400044040c05000c000070300103076440d4915190104415440b00c072003c0d019a1280c040598410902d030b00002c0140c15401840302d8a41d020f00340b03024100401d128407006507000410b84030707100030040002c00d04007145404078014000c1d500810b20320320b001005120800000811580d508581038811704001c185101c011501e8400440d03442c03000c101c0820881c44c4041d0b104202c20215881c99001107491500e20035524501031030840c00baa0302c0200801e0341c008010000442201241e0014014003206152011826040b125841101d10480c2c0c0c0309505400c641351584803034001c26000f0105445580c0d5400065100c9000038001c114000c2040c1042031320900c0e52041055843c4141d40b010502d03800c2d5035031620107034000d80b81650f85102d080f0040400f140d103401220905401d940d0081140d03034480085c822a207101415043c400c509002d400e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 798458794 1250 798457544 798457567
    0x21f0c140114180312150a030f02010f080c030105040924020a180b1c0f05010303110d0201090506041e0c08011a0603090c040f021324170412050c0d0c0c0506 69
    0x641d00700034035170205031501c0d458980640c40e00d54002d0813070503003110b01b0010000c1401460503070b44045600030703224041000b4002e4000c40c1c0001d01190358090003c4140018015400e240c2d06c28000c59204d009999045001118016030811401259240c1d050300080d2160369030340e001c8612101d12090003095105181403a42c80c4400d4000c0c0355440d0780b50032a04580b444030a0b52078000603070b00302c0e240c0400c000d5540c41303040040070702e60080300e0314026204841168100c41d20500c2290750301500000a05400e80b100e5032401129800c840346c1c0203035100e010554002180740200c0340d80041041100000f0084544225000081021a42c145c0f0030342d414070401150203000b1408411003e81107400082c0540300300c00080090050381c0700d800c1580d6650030082100c1c90784002c0d030040314401241030b414080340c00c641103070350385021a00611440300342000320700024a05098004074542a08202d410484410340540c501030085d4103c60020310700e529004148001b00c0c51580203804195401450100c10104 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 798460044 1250 798458794 798458797
    0x1110a03080c0a140c0606030d050408060c09030a15060509180d0e031c050301050913030c12020a06180b100f050f270f0601050403021f0c1401141803 66
    0x140c403500040054a400700c1d611a481c0d01907000071119103d600c5c0c03801c2c10305403956100100c3c2c04a020780315004441c0c80c0c1e81c3c041d8041d1012104a5001400541d40340102c1800e5a0400003049800d4070603081c040c0c001500d81c8841ea40240300300070300060000d25102c1000044000502105019003030701909078540c00c000704034400c0c40403240c04c0c482e20301290307500800d142442000320b4200d09074070301c1c030b031600c1103070b4050019412628111894a12500d80218820400348901b00060201307458003058000104076010070383c6003074046d006454070310b9802d07112501030300c1c0e074107010007003802ca1508a0002c104443c9012a0401d0310846800b9183d81000c900a000480f14082ca503c6112200a400c501e0381e15103019058444612010b114110140001c00d0508501074510440342044040040c40300e5100d2406d0358202da400038101c004c6011b000745501107942208200b4010400f020340c1c00d10101d0121034401e404014004000541c41c0d511a05048001c0d9014081581c902100c0c1072250700d0410010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 798461294 1250 798460044 798460051
    0x305060619091814150634080d2a050f0c0f061008010203060904030e06070b070e030c0307050d03141c02090f0105030613200c06010501110a0308 64
    0x21595000c0c042032480555803000c09030712481400181c1c1d642c603e074610241c4c002054021550030ba0b02c20a4850703000d001c00307011003aa150b81c0c03c81c00038400e043d11421304409020b19244400741501420440d08091003404911541c03d4a00c64000500f004808240781701e060040d020f101d5241f400503030f4000080768008241001202000004184091185800b17800c64400b2080311049441c11402c01200d2510b4142c02c469042500d1101200000e6500d8103000f124450348000307118000981d2155426030300c544ca401d030b60540200090000c4800905480300b0b15019200303c0d2540c51000a659040502d003500e030469050080d0410351040100c2e03101e10080115007581418680d004215030850803804e80640c1000c52a4a112507520358902d54440d80200300101064600034000707403042c001900d1900c02a1006a080b007524020080d8082103a4440066038a44000d85504040f03540e902d0f107220381042c000802641c00510040100f5a0406461040a00524003030f0080912135100a07040c0c00005 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 798462544 1250 798461294 798461317
    0xa06020a0e030102181503090613030c080c0a020f06070b0a05070c0507181407360e0f15060f07021c06090311011506050c010b18040302010c03050606 66
    0x46000c40360180186108000d507940035008540b40c0034901504503580740c81c1c540050150140114091511b040d840840e8406c03100100202030329104d800c00c5143d0907424441c140d04200500e644040082e841800401c00080f03194001d100400c200d004101000f40308074011b500c80e480402c006800110200060f5600180d070700000500c0d6070f1031213400c0e90300c59001c0000900e2401000c0c00802c41006501c213810b02e076641840100080c00050b042e1306032651068882030007040c03654107220100301c40004400841800c0901061600034001d20306600c041454209074050710100081103000ca02001c0c0075948058000010015200d038800841e14510070f0f40c503542d502d002c000511600390340381c0c2c2081440f41040701544c0d014070b031400e0504030014a8003403022000541800c14010605005004061400300c21b80c48840f2060300e059002e85490744003c11800a40d500e0311164200d50342c4051041d089000e02e4071350800d25140c180780007401c6549440d009003d1601c0e0030240002034544100380e90790b42485 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 798463794 1250 798462544 798462547
    0xb0c0d1107060804020f090705031e15060313061503060e0304030812151e040c030603030e040e0c0901030501060608100303080604050612101b0e03030a030c090f03080711060c0a0602 80
    0x1580081040c0c4650003c1b400c5c1c11400c04000e1010f01075200009500c40c1202421281d102c45d084252101110300a88120180540e8020070408134580b0720000d541198841840182d2582d2581d1040c0c2070310f904244c80c41c42d800c0048002c009015140c01340c01840d114203c085d500d01429540e8840150084141c3e82458902a0380020005003421840e550b11050041c540003106454484410a807046080e4044c015814103041076801030080c081c0c0b800352030389074803094000780b140e03401d11000340711008592445210744001003286480f003c001d107000e14014400450780500f003020150000304003030440d80001c410a103007000440da100b0045500000b00301c1c3c01003440c5c0c88000020310000a82a114151405207411186a5a62070f5001a11003089480852052950044280c035030440900d4880d4150f0000c00808071040e00ca6800028610100d0408910550b2145084080000f00360000c60b28010006071040030701010b0491240700d40011290540340122086e0503075110107000e08001c0c03120380c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 798465044 1250 798463794 798463801
    0x151513140d140303010923060f03010b0d0807021203030c090613180e0d0201020c1504051903030608011a010f0c02040f020d0f0c03020307090e0c0f040b0c0d11070608 73
    0x54038401c9080c100d40108060031036403585040d01e500c1e58000c0c4035101086192a1107850641020300000e4403010400740c4600243d0346010611000d00b801540e086d0b819540c03030f002840da070f541c1d403031200c1b04081c003c0340016280d4480d441403040d03042030a00710382c031154414800c004007120000c044402e00b6105803010303510b809500070051800c503440c2d0401c240705902e0f06000e81e41321074a0761200810500d44004c880d01500c03100011380c00c0341f00301144a500c07900701d0321032441c81560008945030860311410454140041a03401c240580c4203c02c821000a0786500b02040120000d010700c000950032039550350700c2c008003640003800100b61040700c0024481d1104500e0f0030355455901c110319440c4216802d654888801c03000c1802442d090081d104154503100141c0002c6100380f080d83e205a165448200ca02ca0900c0c00f100030411005054004100701080b1195446a02e4405440106042c00c809900c40c030701220714508000c3c144c4800c1003040040340c20b000b1074500004100c2c0803a05a0b003807800407503d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 798466294 1250 798465044 798465049
    0xc0d080423031e030604060902030709031b0906260c0f130f1a09090d0c0b18120304020f0909032a0102070c0f06030209060702090601031415151314 65
    0x22115502240c00c040c8807003d580700c901c1001144911400c4600b00803940d110310040c005c80c0000d50304180000c0501d881403000030311007800ca4001c0d4050046201c0c1c1e8035510462901540c4040e003040ca4042c0801d190024007141e40c9410100316032000005d0304040000c9404a09202d0341100c4a5110344641c8a49400702c0e017569020200300d2000c0e00041c030141d0f8241020a00400b04214058000c3c04104002241e8890100303a200d560b90007075640e086441c08036141c55045d42c0c00138180500c20044004000e0b143d070800c02c016642180c151755400c0e1640f1b414010082220400d0034464002c103000c2c403c0080c800d102008560300c43d1500e450014101d454021902071400400c1300c1c4081542c8002120700900c202c005001c001c4480014180c0714158075408114140d000d200710321070b0005401d120b07250040c0703059084541d02000601d030006680d01040c5042e55070440079600ba00e250181c10403041800d0418084030098500a504602e18008151800d40050740320b42c032803501c4401c9101812049036 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 798467544 1250 798466294 798466297
    0x6051813030c1a070e0109061b11060d180c080c100f0c080d0e160b0d0504030e041401080d1b110d150501090c0f211d01020c0d08042303 60
    0x2c0302c440710710094510301540c0140c1604c1800c402030b804112030000000d070f00303441100401c1c030840001d480b08140713000ca070390ad81c80070310000ca4005074450814001c0102110451148852018041d1000c0c251406182024248040c1030380200c2c083c1d070441c02c200395461315079803205180401a071525013000c4954410465096549080c0141080301c0040e900556800681000424110900950f1100140115240740d0045030f840340f001198001c0c0580801e03021a0b90140781e00a000c0e041070701040f10b004000408980d43c004101c02c003450458010b000504081050b80394180311800c041300882144486034130041030f9244018510712444d8407040c0d80d6214441c40c60002d40c2e1104160030098070140da200c1c05032900f40145d55442d03103801011203003644101e1020b00c00b00410340710510850368a42400c0b0080340450041c03828261070301d040035004440959014588000320740010703110045030000b94201b081030a100b1040080c4c030400c0c000801c041c044800034100c10051100d08030390710f00f0f4045045 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 798468794 1250 798467544 798467573
    0x5030a080a1e15060c0215070302011104121101021902091b0318012307030b030a050709090b0c030903160311070f080c031b06070305090a060306051813030c 69
    0x400000c6003072114041800e41000403464a40a041021551104c40c100c0300103a01c984082e6100c0c0403c0310800168400d04001c09119000f4030001c903142c0c0c05800d90700311aa202e64880701c0900304a10846050040715420754607081c00910240c0209440c01756050751000e80c2000c00b078803c12410004c50601e0b075456540b8034800000d00f4805449241c0362800a41803c0540b0201c003565082442d07160184201d40220500549040c400440c5504c500c18210001d20240305003640501c940d429a101103401002403030020503c1442c0890140c1182c03520310141d103009855801c0e04141071091110600006c002e0b1026207404001713900d416032a0717080855244104844248090141e003401081d10b020341d10620342503800c1c04003101d8039856800c0230f060352050030420219450848108910072498000300606ca00ca000340b41244c1040007050014030f84282c20b5000c4c20100303a032120100018241820100c250444400d003035416443c0ca80e100450700c0703140c21002403c0040c2c00520600300a0180c099908 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 798470044 1250 798468794 798468821
    0x200a05070f0b0928030302182101060b040803191b1506080c01020d0e03070503060906060109120f060b0d06020d060503101a0d060204030512220305030a080a 69
    0x2100c9941008461a10183ca010385140142c1c80640718403141c403c02c3d4002250b008244c0d039900300c0c543d02c01310003d402c10503251407694141486840c403541d41100d60300c1c9a0594026400d0130702c1c0c0d2404248d003152080d9110500c804014003080200d40c0d0044180c0d50300d403a06950b15800c0d1178210904582454a030007021030404111002c4500780501030310360004d0440002d408201c082e440700344d501c0e0365480e510700d0030380141c0c000c45000e02050301c100700001c4480c4002d0111030700e80742c84400090030404221040300c0c481c1d018104103e02503920448210003000300d0382c1d40c0441d03e201501c601050301104040a0b00c0d05858011349129910390510344d451a5800c0704c402c54580510b07406810203016603125140c841c0c42020540c2c0c0134400148940d142420040b200c900c2405002000d03c004405000410b660542c1d00740000070105400b40710303031014011000c2e80e0710b82e500e009031001e98030340312090a511042da5200200f440083d03000011600d0001e0981801c181d00d60300d0344085005030102040706074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 798471294 1250 798470044 798470063
    0x3040302151c0207020405062d120a050c030c0d120e0d1a040c0b1314040f0c0816091508040c0519090b090423030d090305030103060c0201200a0507 65
    0x25840706964064031039107100306c4090025444407801c00860003207542c0030b4030405640e80d0044000900302e20340d2071010354020744165048a01c42d080c0504012420070700755043d40000c005451036103010302242000c444111450000da10315a120f861040b03420310503560130f00c800c110b001c41c02c0fa655080d924000c150b0080401c501542c4d071181d40b005692003500d003101d403101411004210880d41500b5a00c4440b1a030703005055240c41d0603040b00381d0424000025400c680d0b2098400851040781c003d03580c3c2440141c5509069040c01e9504040b1100d8502c04a420480303805018070800260f200d440c1000c2c105440c1030929601c4504082c900001d5545c0030300d43c0161320300c0e5031542d407460142800045075a03541c0e040100b0540d00041c001048422100280700f01d80e0003c0d1440c2c1040c078442d0100c0d09034503100071a410401d8814006040301c44070b141c1a00400d5010004004020700d5008000d8940c2c2ca0344000d21403041c1080110000303c0d8902460b0013203040209081075600d21403402c0c0d808040c3c010f820301e0b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 798472544 1250 798471294 798471337
    0xf03060f0b07030813050d03110d020403050a03140c100c020c0306010905150303120129030a0516030b090601080615040f06030c0221070c0e150f040e0304030215 71
    0x1c403507405040114041010980010050b04244800c0000c0e5900035021700702030400e8060440040031443c817809480c000a0000c009040722500c06400070b58407032801840041000d00f806407400101c54541000100200010700c0e01042c040b54000c0d842c45034500205403e0144001039007000c01c02c2d40c540d60140300360000000d1410070342e0030050291104100c83d840c0d406094003807680381d01c51088020030611101d80108a107440c4444801462224940001d00018560600070169070041c1ea110040c2c60711141444104281240810700710900c1d810308011041208000c44c00b040d0000380b880381400342c01000112191161015004035445000c04c0690b1680c80c2c83c1402c1004c2140e009190010b460b0015880c50705000140034203030030420080034003c140080c80c0c02486980511000c0b04c440d4000715001030340e002ca184006004508410b9202480da103800c0c2801542c0ea51542d005201e81e04007083c3c82103104011017242d05480c0c05450303505404102e00045d030101d02c60081664000d50040a80 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 798473794 1250 798472544 798472559
    0x602030712050919120c0515090705040516030906021b1501150813020d0b09060a151a03040c1a03040516060518010c120309050708070e070f03060f 65
    0x9044110752140d041240c0c3d1104000a036407404012a0a13213001e1082c903549000c62041c070030030707003072241180f5000441c15419034a560410341d102d83e45e0500c0324014020711a1602061042d00302800041d1001c2105c2d141c404124034640100e02030131002d040d41c0b4424602804405c4e01201c1c8492132802008a4185070b00c4e0361a9552840c015128100c0410540041444074002c1c65840d010100756440d105240c503074115102041070300060880e40101d0f190082e100207444c0e2040b01e0b100d00403080290a00e231900c1041c18059500c40d00c2c69a95085242c1d100b4030000c2080117a0044407600614819202d82d01c0d460071242110380c3d81c200a41081d88540c44091081000000b584180d100d03006590381300403044070070710281e0b04c0c500480d400b164042c00020000b00c04c2d19100c040d50101450030344010189616540000500b8481400009845001c4007007400000c021010080440c000200601ca10307102c940560b103000545020208040e020301994142e200307030800000303411031414980041d55a03560 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 798475044 1250 798473794 798473807
    0x7171b040f03020111060403171009050c0c0c0a050631090204030219140d1a0901020c0c06030f18030c070605180d050a02150c1c0810120809060706020307 68
    0x1c121300085042800130000ea0000c60761900582d4140c0320341101401c0200082e0000da0014005051500c0c010740008840010f4051140140c424610648c0e0383c14a4042c560708010901c030b6079034041c800030343c01080079454120807910403015170889042c0d15801d000b40d01d1504180ba904030b40d0250092940450100344680c024001c491088070110107d55901500d030312134011510807024200540850840075080c8800744c806070318030844034400f455002e0700440050031010b81d084070050307602248544182c4020072441d00ea4000488041d81185072100d041800084018101990802422144000800c0800948241c3c265110650300460f03110f5000603c50b0304060f20f01d440b00c2c40045103224450420314000b00181d6009000307003a01a106170244445094449400d200280041103112507404081c040c103210f14a10351000c500c2c55a009030010500c2002402c01072108002c400c2c10400e44240111040341c2d40d500c500125100e41000001854600a220014103071038000801c016146500c0305 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 798476294 1250 798475044 798475049
    0x10602060601120b063711060f040602160c050f012a06060b04030b040c0f080c3f0d09060813080f030a0e070e090d320403050c040507171b040f 63
    0x42181d540807008282c04c445141c03020741f10100039000a0b001c6038030310000802080e4800d018600142c50b00044401c0c1015890f41c0341c2003a56808103800041c4240d00d00101ced03185200c80c0c24602103103c1070200680300380c1f2510368120b100ca8104180c0e1984108407650304800002d2014107a4292607580d2070402c104031207001c8400b2a074145200c2400703c0d11042c220740c1c51040e1002407009002401041c030500c040c007000c1800d840c100c10b10012401051805840740c0101f606d0700f50071101c2c030945000800a103400c01c104001428004814824854103500145255101c554070704030031200b80031810a440584500c0504000300703280002003001c1d480d01034006042161015046560380c40d50b60b1441c069040007918024500c0d0010907003c180c480c840c1040c03c0b1101401c41c0c040c17122200c141e400702c01100741c4400d028907101c80810108180242031000600400040d00d0500041c6020800240440c4408442007140b01c0d550010030201c024900480000b000d6141c551560345441d000658000031051 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 798477544 1250 798476294 798476377
    0x32102010e1501060c111003061410020a0209071e03020c0d030603030206130629091003080d0f021309022203110603040f050d03050f010602060601120b06 68
    0x454901d1110000007994010401d500c01a400d40b43d080c41d004031114140a0025186130405190100c5140d0340c10b0611076081040d40c80004a0500d8611101101040680880d110340303100040105000d40114400500d2030341110780c803c45070744100c415070359881c0383c1d440326020b8803840c602c0c051810f4040e070091a02103035503c00c4540e40c80d01030350304809a60a50000078010b070450b0000c101c002c0310b003215440390644100300c081034002c9210084000140c880c1a801040e0f521036041c0400380c10705501040d08080182c81c225441400d40d1034070a518070821000050603642c07800942082c0c6410781c103aa1031038000c803000240e4996560920001394021070fa409980e05c40b6514444820200d80382060b046035417150344482c26211013001c208040d00001d100b641c4071000c2c4011040040d0782030110300580a00b03910001103d040c116074504503500c050f0003070340555021205006450781c00001100a000c8000700124110800a01040300c078001c05280c5103c0c0384a1402290032006642c214020b1803041 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 798478794 1250 798477544 798477551
    0x5061c0c0c1703161b0213090204061706010308070c09090c0602010f15030809030102040f120b100e040204051519140405010501091a07080f030403080714160c03210201 74
    0x10042d0404148010740c2d1000410880b0b0a20025050050344c0d02c1441c015610390344105c200d5240c0101707200100000e1300502c0559a404404118038052042c00d01404040e114140e001005104140d0360380e40600020345900000304181d401c2202c1c24204c0c2c800f42c001d55200b80440c00c11864a002440b69a020f0100554241140e06d081c1410a104803510210750204003e03c0307928607140c074005a40803524141e0555000c00c004681c10071280090707001082c10100c000d8148841e82009020188090480b10084031250010426030104100068109404880c0041d05840c1e03035480301e0481c03030180c001f41d4000780e03030501c00300d210000c010700e00085900000c018801d1050705000c0008940e001d004250128000c003009100b000d01c104040004c1c20391113240c0301d14040c490b403a051584e130030505160301800d00000801c004c055100c80c059400000500700061810020001c0090303030b00621000f481c0c0c140c8a019260140100203146034021500466507002490790f60300038a0034901c0c1701c144c1c0c0c8095802c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 798480044 1250 798478794 798478823
    0x2010912050c0a15021e07031826070305013204050d180e0423070b030c070f0b09030c0601060509010914041b020105010614120105061c0c0c 62
    0x74400c440105010314040c05200303106a44051a4600c01401d80d8040e540c288441010401880b1003642880b4a10401c20f8540f00c0320300c0c0080c518001000354009420b03803c2001c000c40320008007070744c24408002c55000303175040c0b906d6092843e02c0d24542c400b41c07003582002103101c05444802540b104e036a00c40084a0200c11454500c44000303071007a9001440d96100034801c00183e880355140a000d10000307000c0840d041c3d0303104400c0001e0b02068074141d4815803c6910080054103021214100385941005007400c2480c1403c2d807506404010000400d031000010514100400703241e150103400d0707211003110290b090000600c2e689402c0410022003600c0760390000300b001d034002c005a6520030816541e0080d89801c01d030b041800916801c03c0b4640141d107074001c0e21988250540c5c040085612603000080c95032405e88014400044091040c0000200704041032040102104940c1902c10035aa078a90b10703001d03441d541c03100d0f0500c50178010120f403500b20341c440340d19440444082031a0064806103280759 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 798481294 1250 798480044 798480047
    0x31902130302060906070506010e0f1e07120609050c03010314070b09010f0c1217060d0c050f0307120501020315010f020c010e06090301060603020c010608030c070e0406110a02010912 80
    0x8680080030050205510007080145480001400304a40140071681001c55a69445140030300a80050244282d60700c10440f0042052615691003059184005c0c5800140c1820010311311001e0203d004000c0001ea1600b461045c9400044c0100301d01c0e03204024030300d007058005050f0f400030b0104a41c1c0b207201c0b50320b403500b004000941000390b81c41e2607502440c008a10006462a002a0b01c00c80c2c14440d02c0208500480c910740244d07020041c0c1c940322241c09608a40380d010499100825407031244240306034041c04151a8a400c406844c0c0a50320010308420340384c0000e03c6d001c215800391000e01025004c41c1304000c0107401450241049000080001550f0001981c481d089070b44100016400549640200d43c41160303900d03615400030701140c2c82c054048000c03078256600c5410002c007194002580e4500441e00340b281c980200880c80c091414039600003100c0303850f046141300f03100c6640007602c00300b01441920380c0000380c0c2610b1940c40507a240345603c4041d002e4a064903050f00c807420242182d00816 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 798482544 1250 798481294 798481297
    0x1b0c0a15020306130b030a0209041202060601210914030a020a030e0409171810030606080108030a020a17090a12020913053003100e01090c08150111070605031902 71
    0xc83e0001e00a92900851804000040c802143d103164103104800c1194090b84a0ba414140254003e10b0110340908407080d0191804d140540364504202ca040001c090302095540a2600710034000d0703002c51000345e030341040c002000031012000100d0000240926030207400107003d181c80c84c8240c9410021801c65000c1000b1241e040301c0103002507081e040307000201241e000040104030003d902c5402000800c101182140000307031024008640e07078400a010702034110941c14010030021000318545200040000c0d160038811000038640380b034200e000400c00c1c10100a94200035006070090304101d41c0d480b010500304162075030a0f030103601e100340803407a69224601a1100710380c04c10001c0c000d141404400210011648a200c220315080c40045a811f07005000114010114034960665660038903205a078010f10680c0160f11039450010010784240d040241d403544101c40b40702000c3d4031029500180c030b010399036000311401c038000c005001c10415000380103036001e6661110030f00101007800c05240101d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 798483794 1250 798482544 798482551
    0x7090501140c0c220c18050f03030919031205040303030b060307091707050a0f03050106060219060b0d0f06050a0f110403062003070906080f01031a1b0c0a150203 71
    0x35000350300e101d041030802c0354541c469120030a2030002c155103204d102c8030840340d150360f9141c00108004180221031b02e6001c004005407800312120400c4600282c0040c1d81c0c2d00c03426803007a002e81420420100200c5018810b80700642c1c12980f810b4540111940041c950b507c24081180407c0c64002e0209141c282002034920801180e215840c200d401c2c00c5404000001c1e0040e80442c610640c3d401007a25200c000b001c600810b0a040e0340c000039401e5180c41400d403021500a8811036121222281c01403d20144dc6510a900074400140801d21140441e4903003410b4a401740800c001c0c100c030b04082014075400316100b801c40d17000400402020103032660a484882c0070050800b10144400c0c030200d005540100703286400029521030018207000000301c2d0350002c40707511000c21000e03281001826005488298020000304031201c0540c1180e6800c2508403000c84662001070b031081c002100648500110f000e030061300d51a298844c4900004c0e00c2d0f079515144002c0f60058a80c9030078100d1000d150003901d00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 798485044 1250 798483794 798483817
    0x2030c010f090803072f070f0503030717030402060409050f04020909031603031e090507081212041e14010902011209080306090406090c1229010b1305090709050114 72
    0x2e10345460f5170454180c0514001c0c0310112000305001c80c0411000d1103804181d40c040c5025000c01480d0001d94045640e0390b030b003c01d000740c104000c40000110490301c0c4d4454980c104c0e041035229283c1c1e0000c684140a2500925421850541485400b0340e940c4030303240c80342e4803ca0740030701035940740c01105480e4050500904e07600c0e4101440703040041d000b03070050310400f103942c034910b60030700c2c40c1ea403003041551081d00041e203031030f004a0020720413448240151001c00c040e048003145440040c1810b8224003100034406407009101000f1010042100e00380707504140d0f040004400070002c2042114000e01000c98100d02140742c919801e0101c50403801190320440d080082c482c00d40d9628000d104516000138011039407d5a80c14030b101c00110700e03004c03040103010703420034007209401949025004034071144000055020b1400402c10140c0c00c1035001ca041d50065480300d81c8482011201380b00041c82500015441640c91080290255001311000100c0d00240d90f100081151803900f5001403140d020303210b1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 798486294 1250 798485044 798485047
    0x4030b06040618090311030a050a11120d020a020a020d050f0708240709080d0305060109090e0d0e0d17030a0b100c12051207030c09140901030204091106030702030c010f0908 76
    0x10000700c80ba80c80134042e54000d05002c10f0103000c0411843c2954022030146010840c08600311005950114940e4080026000180398595a103c900020350246024980c41140c00168103c1554801d000d0380c24403a601904134100c0c080180b0300a034440603c000c8200f080e12600d10001440c0f03200240d220201c03148108131200206821100400c400c03001010081884805500051009420006414801c04035a800103045c28100001001c0005551100c10410b0400020354081c0307001080e40940314010707050685a0010030408143c086030700003000b402040c1240025290051082c000b180301d05480c2d8800c00481904c10200b286290300e011540000940900c402800211884408c4c071000c1d8841c01c020f810714502980d00203074000200c0700180081d07110003071500d003660854480ca0290049071844007203031400c00c01090401605120103849a0b849416180a026043c0406c000c00300d0f014000784e0392481c101102a41c0c0e42d011a003580890f40c40e06049806171611480f55002c081d500c03101c0716 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 798487544 1250 798486294 798486329
    0x100b04090b0604051b030a061505040b03270111030f0f010305030f2a010b011e1b06020c0a1b14090a021317070306151a0a03110f04030b060406 63
    0x1c4c500100130f000d030b07000c01040a401ca200f90b880954030540d10300f00080380290034441440303051900c22100c4014032070144828050645c42c1030a507548a8160f89181d84200160078041d0b000c101e800c020b41c5c04d1540ba00d040103030300c402c880009610a140d04240045103449000ea03056243c07009100c083c02325003061081d0b02c1c00021150043c540525800c12034280038034602c0130281d0151400d4542240c582d558204038009503001005d40c40300340b6416000d010568000310000d450f003d9041c1103650071840764000341c07040205079030540b542d5a18a0046452210306403400000c0151240005c07101e5505582000940d00c0510f003228204149c00762107c0903e4403450380c00f03000394103e92940148510071100100f50070302c82202040980305030400405015203942400011520490480303440f10b841c3d05000e009062406024040001d00983d0403030740c880c1140070490003042c031000c0310484031500040011003022000d000c0e10a481c05000510150303240d46082201700c980e180f244a104c000d02c150003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 798488794 1250 798487544 798487549
    0x6030c01020c062b02030919030e0d02030708011d061008070302060f07061505011404080d1112030708010911070b010303050f0c06010305030a0905121504080c030a02100b04090b06 79
    0x15003e01c0301ca01501103014070119036804550780d1004066413206a001c0204045031104000c048040303100d101180d00e14004a0f14004c10f4480d080481c9401010000d5a000c00c47d00d04002d14002000342d00001c2144040f040d000b801d00f4903441c039004c00644101c1c0040f070381c0030420184140403a100304008080c003034a5039080c401943c10802c0c800000040038400000400d0702d60058081000811151010301400c040024007409884402001c40c003201703100500c0101c0300007642e19102c0c061410b007610b100070b01d403010f17914140303080c610f0040080000c814002e005400c1115079050b22540b440a0090008004105180e0302680758042c052100030f07030040010078040c1004085401d191a0410700d4021081425031920b0421780c02110310340c0c03001441c282e01948c030000c840041d0070215040000c05142c06880c6680700d54295074091180400b4001c2010001500c080392001e0401409503030b25240a058069103401039040c541035018108404040c0341e01d41441600c422903400500807a09071584400d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 798490044 1250 798488794 798488797
    0x40c0905090724050405270c04050d061d0a0b010305120f27042c060115050d020405120a050d2a0c1a0712020d0c03030218060309070e06030c01020c06 66
    0x1511050090401c008940c580b681d00969080c030400c8018002c014111903840540410300411236902800d041c00140200e59900e00400710346500038001042003280222112510310b0640d002d88018410900074200b0042d0f003210701d0781228001c02c26601081004080750180b4429049180350f9490100f2150b48040c4078041d031a0060044c220389415a10116408201100d86081418000c01d1061800c4803104003441c56440d0045e020703901801d465450520042103907a903080005080c094003140c0c42c0804841c40c0d0658004040041025143e6080d14108540f9a50b4002c015185c3e805180700c00700d9103d001d000c04046118144221300b1080b401c3c0141f0341c01c0d1000000048814907045a000910210400c9140c4907a0104401042d07407041c003403501e078a26401405151042d500050b4100c05955007000c2171410304c80e0542805641d030144403807003601c002c2190103000d0b4001404010300843c807000013608015075210a8080c0340340d480c1c3d001050b540707017000c200040c01a40064425104c9082000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 798491294 1250 798490044 798490109
    0x1050328030908030f0408011b05121e0a0c02010c0e0a05010e0307170319020a0c05041a0d110111011103060409050f03030c0717090d0803090f06040c09050907 70
    0x40c0c001d070402d45644215081d0351000342c260b05e6240000c90284407038102032081190703a15008111700030442120f6806882d40c0505002d0309105407034800040d2004240e14992002c032101d100c5980135511f80506004020440340c0c05000c0150320384000c80f0036075401790806031080c0c000141000241c91034a8011207541080001c01509801110700000d5080700341c86a00b800e1840800c083d68036140551200415028003100a104540c0200b0410000c01c8001d400801951802d85010449541c400c0c10050406000008160060145801d85050000700354610140c24803d90b544ca081100401c0a1030a980c000d8201c540c000c5020804500b5902c0d240c0c2c00000340390b2040c02030b81c00043c0e2006503241160005c5507084015100012400100030600c0b800e40980740907040390904140d10540820001d4403800c50040200c140000801d4201804000e11f120700f910900844d0728034a840d180c281582c0e01c6501c620a030642c00d04c0089000c40c5404110f480580380c1c800d243d40c8032080100b00c8070b0803114000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 798492544 1250 798491294 798491297
    0x91e0b0d110403061b23090f03101e02041404050402030a05070b0406031104062019060b030f010b100518060c15012103050903010f0e06010e0105032803 67
    0x318600500103181c0c0707001d04000d60081c0c4002500401070841c081038075401410180c2080100b40c20306034082e010381c02042e41045100c0e10307a92280b00c0800490454880704080c1989841240c201c106d01c0c2815800c005400401520482160b41080550105078001c50140c0c00180002d8490310003141401d6106ea40c0c4640014215103038600070303072110f034285003031904903c14580000070144146905405a1080b2071001a0761924140c41c040c0001c1a00700c0711101701c000b10422030086c8980420070821074600100d09800900154181c2c40d01c2c400070110407859130300900518198103621030b0f042c4100c8002d1034018004281c884600d142c1210303140d0186441440200b150380040c1c903d6210b05026102c42d2072403100400d00320512050f01d00003040e0503070240d48541c02c4210004503100000d403501004941c1801d28030f845d44024000240504052040581c100d4580084005103075000981c01b4100d0360740c61199030700d990301d440c1451789412810703092510054018000b1840424007441011a0313600a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 798493794 1250 798492544 798492551
    0x616080d02070b130b06010c03080114130f021b120912010608100b04050f0603030406050d0b06030702011b0302040b0301030b15030a051e031903020c0712080a091e0b0d 74
    0xc0b0340e20f540d2115400e4860202864102145500300456020615003140d02401c01c0302d0b149040b954000c000210501942446c2e4084005a40b025103a034415040701007001c00083c4040c1040700c03400c1000f07412181c0d44090300103040c60444032409001c620341c1084a2000e0381617180908240a1080011030405590710310f6688250005031281c0a10402510000070000891400503010400044c2c807005051004599810000d00401e035900000301d80445103641000d0f91038a4044000000a014910019810240020401c101d0342d0781075120141a00c07544d41c0c07500c0c5029a5180c210700300d020700e0051079a072083c200014004290b451102642c004840303044001d04108030b60220b030402178a40c200703d505601941c562505000154641020854000f00075800c00d544008002c9240c803201082106140d4005003402c21080c050080034080c00318814134031401c920900d0700140680c0301c401e40c4ca00051924070f0201d4483c01082240410b402c83c0101c041c8642c1c20a21030590a0740304070700c03002c030580c0d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 798495044 1250 798493794 798493807
    0x60426030c070603050105010e030d091a31060f0c031d0d0309050a06030b0114160b1303021c0e040b0402130b030910020306130515150a020c0616080d02 67
    0x20030041d02025000c3c695010070554548400034003400105d8160601c00d8014000300ba24035603103d48140f00b19002c4034141c0300c0c40042041d09148910990340e09201c00900b9190008001c0c1c1d0004490080c00c0355454011207103582c070002200c8401c074003900100042d140c108602c0102e0701c43c0e5100003a0b801c80d0040070400c4078415000601a03104218200c0c0032a030303840420001485d01d00c88031b030b00408035814180144143301c00000c00c2d0707540c0040407a0041c84045002e00c0b42e50300340c154101c280b0780d0080d010031a074107000b034055480c1e00c941201100144950400d28640d6800600c0302c00c29400d15440d400c2400c40341070200700150101c140d080b0b401c107909128404039880a0b5041d40000c1c40d01c803050326a242414035a9a00b4001b10554052003c0d00400c180042d6803118403a082044a000308000360b9038840c4019201d00c0784100b040c1036030104060381a0031000340140003d20908615808a94814440c4003d000941c040c0004501c0e404110030703080c00100d002640145a082c2405500500e40344 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 798496294 1250 798495044 798495067
    0x10f0c05161202010906030e0705010c140106030b04060c0e01080a0509150c0405041a0d08070302070306021c050711030a0509010c020409050d1206080c010c060b10031a06042603 78
    0x81d0562040e0744003502a91814195604400301c4806015103250910080000700d00c030903070311400c6114030350420403484440300c24024080c00031001429240024403045e87e40c1d0501d14602c144c1030718240c03806450050410381c0c0a010b014403a43c5590180c44070080d943c1c40404840041400800c1424640103c082e00d004402d01c00202c01c3c07190a07440412070b156410907050004a40c031284116110107520b100e84080f40d035418510f03020079648541c40c80c0c0e0364083c91504a05081e0180e000038190750022410000c030302a03140c0c020480f521012004c104550b20706008480e40030803050703401841d4008201000c0b00901c00c0000301495801810024103050441e0f0110381103400007402581c16410a881c004007095101149d04080c0d22038110512803a410062002d4542154030440b03414005141d41304010040c1c16040182c21441c000d11017100c4500d081d101802030400d4034000d860718003460341c1801e09403510509480a460000340300c41440200b4100c42c0e021141c0041c00b0500a1209200c0720030b411 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 798497544 1250 798496294 798496333
    0x103140d1205190c050307090e0f04020d14010f02040515122d011503050c031005010e040b0402030405100c0203341415070e06030708060118030308090c040902010f0c05 74
    0x244d215502d8581d64a40380c04020400001e136003144c501c0702c0340c1e2000e1210601050342e0700380d0480d404440480d948902458907202000024002d0380e244e50070010403808003d02c1d98047c204890703050760b1188150101010010492160f42c00c1c010310b0107210408100e0400e0315181480700c04050101140c5441c62220305425404000d912881124084800e9804916414003d6a802480035030000341075041c601c00e0001003208a004150412450205081d442c5d80d598201001c00c1c400640115528146401c1103520b40d03c80e400048074050900a907541800e20000807640c81e0452054951100c603c0941801c00203184045001c900c0d400d645040c6005c00d800c2d80c094a00296a58020f00e038800801e00e110800380002022070341888119806001300b03864080131254405114544890035644e40c200599107400440c4006c00422842c00d0b0100c20076411441e03650090303050008981032403140104000030b580412100030b0004504910404100f4021120640c419102c2c070141c0340410407001080c03490 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 798498794 1250 798497544 798497561
    0x405150a15090203240d03030f020f070303020919120b060409060c020624010f030c0c060c050c1015170c1e0108070305040302070b090604080102120103140d120519 72
    0x30158000144682d030042580025503a200c11740d96204c501d00b1810016280340070300312004c0c00f0705d51215032000310401d490b4101c039060050201c8a90302c824540c1801030081d0091602c0c20300504160203850000d01604851310125030000c04607043c1400695241c4030001f1014191942081d110030310000001d030b860186640031892940101002c2c03814141c00448841c41e103c16103568194a0401105640d005001e160341d88058180170034520901c0c0c80c112b90b10345810401805180c034003046c806c2200c1d0700030010021801443c0890350f82101c400c407800120780c04040442084006541c0030804000380b040034803000100391081e0b40c01a600705000c1104450310051003c401c4441c1c0c89048220342c1c001c09040c2e00700303060b45001c10951606030740207562641c2500480da00d44d000800d000455a880300204c07005800548025512000754100703000c42004e00b804201e03500111501c441c0d260410002d2120900340c1150750798100800c404a1107402000050710a903c80610362036900403292860003603441 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 798500044 1250 798498794 798498809
    0x2811060105130b01031512150905030a0309030e0904060e010605010e030d11070b03011509240318021203030609130b071d030a030207031401061d0907080f010609140405150a15 77
    0x160508d040e082054a41d822050382620303000c0d0316030124000000355020a211410000303138a020504090f00d10b038901c40c640a60221a403000c2104100b100d8002680800c4084000d010349034903640103550a0320805044c58069000300b00c44045503104240d61040c020074841503808164680c1d82e2103030558002d0300528400b0030394000703040341c0a9100c0b0340280100640c3c0000980c01402d641001c012020280d0341c034040540714203408030010603002002c1c0c1c0184c2e0080115050840d0006050780340d03042110054400d48000c0e0020f1315041c254480501c455610140303074415503940300340698281203140c0c202e048c108503041c01c00c0003684007000303880f00f4503020384c005001040c59850f0204a08c07181070b100341d40c241d041000401815411094501000102c042d4140040e904c145100f03142002e1580420407074880c041300903140b64010751002d400d03200914414400c122846e0300320041408142e500a249500240c0514495801c960340c0341d410620303502012803c180d600c140e154040c10b0a03000040c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 798501294 1250 798500044 798500069
    0x4080604060219052d04121a0702240a0908041d06040e0c12010e0105010e0702070501030911040b0a0911130509010503030304080304082811060105130b010315 70
    0x90b0703092050b40e10b2841902d285002441c242c04c2005155a8814100d0304061071340170500040c0305c0707a59801c04d40d0040d080c0000401850f40081c02d000e103640310790119074650751121001292002d480414945c000c0c00c120103284a030300001c1c1000d80701804004140f1101c1c3d55688080d00c0c0011010001330000780420a4011b03515049141c1d405000300000d0205803041c1c0c80d244842d00b6165010039a000402000c554800d414001d0240107805401c5c10380c0c403551503500e00302c0042508460701440d24000c44242d405c456104d912200107508030340b050f0102504000303c2d8000501c0a150942192808100141c07015022580d5080c020040e265202d00140c00e24038007240750070540721481c0c035400080408941038120b651614001c26102d10000e0800b0f000640700100080074842458200d51350400c81d44185602814480382c101011203111050343c1c0060000045850540000031326141603c800600c0b415800d4000038004005140c3d041107503051540f00e00400501c2d034800980301004042640c000b0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 798502544 1250 798501294 798501307
    0x120a0203071203031a0a05040f0f020c0307050607050a090306111e18010201140604090221060a14070801050f010323070f020622020a050918010b240d02040806040602 73
    0x907003680d9528100e591701c41100c00f005056a600c4041400480d5000d84000075070110344210640984851407410074142c4c000a03100c02c3e0a88000000c04905000786c0641c1d445840d00c4c801203419204907150440004d0006030240b01250240d40005101c900110303556140600c0c040302108003e100700f6040102c440d0101e07902190850110100fa030303040c0c091008002c20901c14101c80c0301c407000504654021940d030203002085484442400329444a001481400c3d4040300c1c200f40c0e91b03007004035400046075042181d290840c2c4880d1800c1b07801b0380c407581c40d410707850ba09140c01d01c40782455808003241019256801d038121800c0300c1c6030440384004840c00d041c1091a051034050500e00702c00b03030300764219801071080002c0700102c0441c102c04600c43c0c400503034195070f071030002600054050300800c1e4031100c45003c1c8002d00c090021070018020004000344078030400c2904010070502c0420001c3d10300300000241d451840c052030700904002031501e10050030180c403801c1c105e00d440700480f0200c41060340013410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 798503794 1250 798502544 798502547
    0xb0f07120509030f15090c1f02070b0d0c0e09091005091207290c040b0309011e090b010b0406020a02220c0c05010f06050604060c0c09110414030d0509120a0203071203 73
    0x12168019604001040c0725202400480d01c2c248408e60340010320b60001040d541154400d0202900034000c080095841d0019144040028001280d8441c00320b2403888004d601ca041c0b4404451050351541302400e00c08103c11031090240600600068041c001c818104031500044d602401c0c40c2e50003003400750065000341c00c030711410085608299000b04124810098141007000496050324022000d0a4030f03902c900c000705e405404880135128115002a080a0050710541e0000051a004100303c100c240da0f240083ea07600d202c6e500951005810020003080503003003c01403c003000d6106025145520707c811901030458100c22950000500c0560524051040c24021084c000c002d64030100415440d00340003070854400c5221b14000d01c825034501d071007404401c0414000400d00d680742808240d03c034001101d4564458047c000f144001031106070001e04000031404a900c3c155281e56160002207020003030040d02d40c05a4144510443c0345440c01a141404540010601040101c0d86100ea5240 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 798505044 1250 798503794 798503833
    0x30603080c0a1728090e01030803150a030206090120060f0414012a02010f0e070f1d0402010c021f0f0e0907121e1509060b0f07120509030f 61
    0x3d0343c4440002030041001041d074000c40c6008000646030340d02e1031020070200076940e43d6103d034041d40b080c1c0b009400000501040c1401184104004034420341c80602010412400420b507000194200100b40f0021038154001c00e10080002d082002e01d00ac008070010039540b400300b084a00e000b010814005200410155103007083c02c540c4072070001c1c810000903660702c0031804140e07041c0540000768680200e511600070340c80a10b8410f02a20140701c21030300540b10b9651160140f194082d40b0040e83d00000d0000e542d9000742c00001289d0407054019145c5400441d000723940134405907404030f48521040700071074120504c1d10300e5882d2522402d066110f1075001500350b4a2035402c042c0680d4401042018880c2d000b4020402c420320034000141d4101c680d48030410941084516031902d40c6001c1e80c6500e006420701c1d2030012511460b00c1409000d032a180d490761603000d1005280c0f00741101f4466400080d02c109005640d11076586011070400040c1000030b49010314000854146070811070501900418911 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 798506294 1250 798505044 798505073
    0x5011a120d050f071209080f0a170903070b13051306050f01030509030c12030f150a03061a06070f060f0e120c070506120702012004030f03030603080c0a 67
    0x681140110100421264650094501d41c03001c00c10002104000d2141ca1000d5031209070f0000c140b40070070b51402c0b00290144519010b001054030803001e09481210300040d56010300c0342d01c11003400c0b480400e114150b01f55008138800c1503243c001c00b1000f00320040140d020b04144680341000300d407200d16010030b001180406900c1021714500301002400280c89014245540540030302e40090f05503203070095a401c50003548035014150280c0c8400b115441a048082c5029410345800ca40381500c602d080ea0304076800c29100f09820514800c2c040010a11035401000005134201160203810307508400610641d201c0f0408071103119014031014240041c0d0321560078282001e00080140c641001005665003c3c0300303648842500000991081c3d40d0002d02c1300a0044ca0007502e4180c54004440b2041241c0908071081001980303481c42086041d022042c006506100c0c103601d0358506411610b40030030301d44044005a0034140c0b100f17400800105140300078000007840d100039020000c001d281008000002c2d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 798507544 1250 798506294 798506299
    0x3030a020d0f0201140402130603080c1f061d130803181903090512010207050106091b030b0f130b0901030c170724110d0504031a100b09010c0204020705011a 69
    0x265151090000040180c010780c04070b408c060b0740d8400012080143c02c55800042a0a02c04110400001000200000c9200d44c0c0422018500c102c0003049080783e01c240f03d42140c0300501d220710f04488204000c00340c0c1042003001c41d030300020709585550700f0356031045e1204004204c01c6004031218003020b0103803201200b080011202c01c0d000c0e50b1001400b1031028014688108103400000862034800d50480e9034590348600280b291a13550480c02004105070a118012800510083c0030002e20900c65440920001880c100e00512100700b800109000100c4c1c48070040c1d550440c1031019511401d8080c02544a060007140142c18072070f07210b04c040ca001e201a40386030700684051041d07050f05a46407100c2c0312604001c6500e14a580d800316944040529104824042c658003a508141d000e401001503901a00a14088a03e40c0521040d80b44007141c104821040c610028072030300032203000a00c40600145040c0c410000740d90001030881c0d204040807a0240c0d51a05181e0a858460200040100c400c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 798508794 1250 798507544 798507551
    0x3070501060e07351509010e060405010b0a120504020f040504050c030d110c120705100e0306070c02060711031f05010905340311040e040323041403030903030a020d0f0201 75
    0x620b000303105605800d402181269040c180080c42c6100c50b02140c5c051000001c141c2e8a0741d507540c62020b280540150b555500880c1828008903039000340104a580106080d40d80d0013540a02c000300320010b14001e4030403a40101c17114640c50040e6503900a030350081e800b40d009400e4481b4007104062400e0f4010b070140087c840426020313480b050000c540c102c0180010380340007001c040461907041c03c001c000d402840d80240d410a40601c2981c1c01904580c0445041e01143d5194490305410760301040e02e80d40003503000c0d0080110b84005034013041c482c001d40c080074084030a00c1009138400d81100354070342c0100b07101a0356003004000f5680103000f01d50f008580211280d00d080c240d071410b441c2508110608803445441c0e0847c000040d031107503008940468a60341c130542c40d2600c50f0051070700100c050702d05900040d03201420828184003801180c0082180c0100342d49054949019a202cac3c0380c1000b2807991500050140c401d440d10240010090242c0d01c0e070203440710300003550380503001c1950200c00c8011a8034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 798510044 1250 798508794 798508847
    0x1c0809040e160302090406020415090815011a0724020d150303080106050711041a030c0a14100314070207060219020102120f0d0e071505070f0204020a0203070501060e07 74
    0x2080840c0c88283c030303016603c074207141d55181420f07030203481a0f500070b89290110180103407000754804490819540e06005550744c1f00b0340042001090a000c1c003603c81500030048501c0c441c040344000401c1c44910400c02464840441e8a03000b0742c103568400345001198000811604d5050319101d040366442c642c40c00307484000c0c2552801481c0d16014080d02c014010001445010710103808156250b00c0d500810074003403002051000e0508802200d0351900900c00c3c0654600a450030382c040000340d9031520340b9a081501d0841c2004070b82259009030301c003410354a80c00e0a00001c1c40c0c1c040107115003080d40040a43c246803c40081c50002c0709040007a10b00c025000a00050b07a000c5042e20030a0980b0b060301d80c0300d10b0000c44a080394843d4100d81c40c0c080749003c04031004800049221012126000880308900e0b11000040c3c50314480c0f81e600400d2030030111100e200500c0c0550113014600d44500c1147c2c10004295145421600390350000c1340c802c01c00d9405c1200c51944186400c0451038036084902107201d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 798511294 1250 798510044 798510073
    0x1514041404020904050715020304030c06020f10020a03090f200108091002030406060b030a05090d020318121501090603021e0f09040311030708040915061704021c0809040e 75
    0x40340500003e106100b080040350602c01c040081c603014000084207103d00c45042c50019540360b0140c0702c11075800c1c26807100007030b8490000c02e08010401c10040907054020340c80ca440d400941c8000d4604042c15500c2403114040340082056448051052801100c0b02d220516501c90f1401b1604c0d0f0030381004400000c00a501d4408100040500844040035843e030700e4900c0d02c0c40151000e9005007160300703800300400c030200c60540c001f070303000e4142001914218400c114089031244900c0711403808060103100c14003a50708003100020b002d1040e003001d40c1c0450000c034060060449083e448086040c0c1c58610600079454900844003040800001040f0944022804610104241008680700754580c40009d07060600409080001d5406401565600c0c440c52402c00c0c0309400a002e20545903142400340201c1000c140d03e0300003603442544400c60b40c100e1030b8075a070703c42490081040341c10682d2100504451b60402d82c1e031414032441240c2c104d4031882900140412100035105100840d40035040940340c80 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 798512544 1250 798511294 798511331
    0x13020304031704080405090a0c1106070507140f2401080c09040605070c080f0d06050628110a0f150b0f04020708070203070801091e050c040b010210151404 68
    0x400320140102c01c030b683e1410f00c0005401940d000c42e410901d00d40402240301e4440e400003051940310f03101c1505000c0480709051b41c455046840c54007180302044240003042c80f0245800d84000900100c408481c10142c0c41810f08a41c4208070410318146e0f00302c02c601d004140c0e170b00c90240206400400c00c829006002510022001c0c001501990783c600110700124422003503c0c3c038182d080000c4d26510b2131002104069948044a15116549460008541c524217a000c5800c1c41070003800c282640d0054440703079403418201c8468035050024804284203082e00600007200c5580c00303040a11142c800320709225000e24140500c05580e42e182c100c0100d03007a6201000c0b82e500c100165070060b00c80341180f8202c402481000000380d410307c0340d080d00280300c0005401900c04944581c2d241c0850002a0752114003141030801c00520315080200031307210782d00317040d4410b104107a8144119080ba41c00d1381034580482e4518080a0061402d040b030500101d842401801c0349900213480c02c01c5031040145655110 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 798513794 1250 798512544 798512567
    0xc0e031e0c0f030a06060308040f0f051e030f120a110118110a120f11030d050a08041a0f0109061703030a0b0103021308010c120b011704060e0f06061302030403 70
    0x642ea40d60882d02964804000c60010250310810030000c2c15181c2c101030019400901c10003088001c10710f0041410302c440b21445044400c0604142d8010500403404a01103499107000c503050310032540700441511303041101203040c40124650310f49d2050041d500400c440403031070480c107040c4e05029a901d010340e5206003410420340c000030890040701c900c0300003a50f0309085e036005254006c914070350441804402400c980a45200d55400da041c01c010405140e01e4210103003002001c0b80080c8800380c03450740116900d55000f4400c0c0c078908200244144034040d0100c00b03036201e071250076440006100c91944d91098501911100f000388000b483c03915007480d564480140f4402c0d445480c0c1c0400c92669001e9015202c2009016540401c00c5440390000c2313008200074986640000e0300524045084002885801481c5030180d490961001c04075400310540c1c1c201030400c0b12010ba5400301ca00b5242c2c0140711402d80f03d40359002416581c249007081000b0101010000000380f0b01c1002800300094200740f00484 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 798515044 1250 798513794 798513799
    0x12102040e010f020a021005150105030a0c0c021002010203040b1008031b0c06041514040b040306021b190b180c0d030504080703030801170705151803010c0e031e0c 72
    0x1080602196418050900c0c1c182c031015044c0040340c1c00c07800030340106070514154001a010092542c44200082903081b81c8014a0b000c40c03020004510b15a0264200c0711141000b4140001118801d5001c100e80c0607074106d030440140d50100903c07007084401350701c440e0005806100c80700075a051101064581c03048040040f0000704100400c08440d405000600079040d006145030748496903058200315454080c0301c040006941044960030b1391328424103581c00d9511003054507081a0a65680741c00a510122106010360035100380d100040e20100510300d04021801594041c0701340030714103000011000341100759401c51068003200942c000080600000030221550384403d8900d0406551510403a08440d2842c0120407010090540100c506412605000f80e00711840030301a8001d5110440c82c05119402204030b013982e4030300403c0d8009008810401c8000d42d05e910280c50000707003195070610480c0040713450210140e0342d40c034013403002c007010034044031060400203036550410343c9842c0409c48207403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 798516294 1250 798515044 798515051
    0x100c0201140706090b0106020106080d14040306053312010e0613031403041128051011010e01090302010b030d210f050f0108010c0908060c070204151d01210204 70
    0xd0030f100250704103c02aa03002000640907586984009010f44214041c2145a100d180142403149204000e418518071a51303038410b04160035507803000301900000c1c158a65000700e100300c40e40c09855007074040c016103110054001c40c44840409000303807058000ea6090950345401640d10003003401007078090707001400202041c0c00c0000780ca001c0d1000490304901e2801244040100003c01c0b0202c610105904030803078034103080203803024000380000703450105822100d000740405c1000741016481500554018100400710401e501419400c48024002c0380d401070391100342240a04d83c081c0700701d075010201500600b04800d00da00020740b03e402401c0d140d9035411050a1020880c1e14030b50321001221808040500560506202c3d00b07081034000c0c0121802540303040d0361001c845000700b4598003211810780103044d40d940c402c1003131929034110341d105903001a200c1c200748500c000900355000140c13819006402440101c007a0760700d06084160820300080514200c0c9a00780c2c40003656080119034101c6010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 798517544 1250 798516294 798516307
    0xa09090903050f030403030204051906020d030b01050c010212040b0c031b09041d0a03090e150603180f0a1e03050d090f060e031b033c04090209100c020114 68
    0x125998070424003c0400c29002000340b004266142c0c004100b2124100c800301d1059102c0000800b01b219980301d00d90150f4844c210074501c0341d0103500110326590050501c0d078249024401c0d440c3c203903800551000c810b00110b0082004021f48509442c0d00019524902815441c0146000c80001d0543d4040e6200440100c1c0590b810b9440ba044500d09008051140c4d05c41c800e181c0c406680d0b02d496a40c21400b01c0e012800100b0450000810b640c030942071100a810030000c26000d00255a1026140ca5281c410b8800b03010200e0b4020005a490b80e010344008083d032071220306045c4052030101140149800c03812125802080d0300c003080c0c03603590550b0340e0300098984051500c0d0140240500d0001c091750309042c2070b100402e0001c00500461a0707003332007043c400d0b030000000e96140c2c4101e200007010000c41d008040301c404504654444030561798804804081c40301c5c0400c444540003030f8020464a83c00113a26800c1d0305009103282c1c8480050304082c1441c84c8180d001030036081c0600c494650803680401c1c003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 798518794 1250 798517544 798517547
    0x4020d020d151b0e090601120c0e04060b0c07081203070e04090b100801140610050906070506090c040605181b090d0b220c0e0a0e160e0106050a09090903 67
    0x101000e411801c2000c11400c2ca200c00c6140d8141d04000703c8001241240c03540700c1e41820a00d031202d10400059540803406054408850b004081c0150b0304c0d401c2010341c2c6217286042d1564491760700542010040991982c0050b4409d6280003000c1d000346010303400241254140d807480324240d0b03801c21043d0500e8110241e652000c00e0091542c00005401c007071440060090148002c5016000c1d5007000c0024080c0b5614000d03d003070076400c20b0303804a8024407149529504a0b1007500508440c040040500c2d260080a4484c0e0386448816241d05480e908551081c040030701d010710a11004041c141c1d20362010760358000c1c03800c0c03821030000c04407000d203032000c10244002070440b011070b1032030310009000311501003041c10415280d2108560092510042c100e5174401418820200034640b40c0c45009940d0751400c0c489405000031002d0130030700d14985c0b40c03413000c94801d0040c88214203540860350301850321407038141c12011024040e40850284102003214040c03283c1d2007220782054880045001c030304041c071443e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 798520044 1250 798518794 798518813
    0x180405090d050a030c05070f0b15010306050d0602070302011503030801050307060908100507030209130227060f070c0302090103030507050d050c0c062808010906081c200d021e010504020d020d 84
    0x40040c013060132300c2600410070010903040750080e040c00030160540d43d0071364015001c8403464040c03d540110308901d480002611a0000c0007014071a20011500c242940c3c02e280c550780050700300f14082080480144890b09007081004018130652508140f203a1030f091003e82c4a43d04448100c020944400000e401140242c045a10101c0040d240c1e11240030161030240080d0040050080e0600d00380501211121000d06400505c180040000e1300d4405201c1c1c1625444d8000d4400316121062000d001000d0307035403c90624002c5004c1c2d140e00341da900c503501d45a03041c800d81003200c4050000a00c001501100005140c261490742910800d5941000000d1030b1070384071856244d100c4030b00e4a1940c000b55203501c0b88420341242c031100c80512006031070340381c081c1e110351484500361040700c180081c0d02c200d684101d002c5100c01240210140100b02e401c0b510502f006641d030720032005680b050914018409058040d02864915030008010381c0c1000d9000400c8140141e401034800c00a0700d58032000d00580e602c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 798521294 1250 798520044 798520057
    0xe0102130611121305011202070507060c0c050d0b011d0103050607110f01060b090319030e09060f0a140a050a0e070311160c0302090a02130504020f0f180405090d050a030c05 76
    0x9411131302c44a20344806401c40d103071802024005441c4180080280209000f81d411455003c0054003510381460000c841d0f40f130052a040d1004601c83c000010151200c0078030200060207a0300065540d0f05000c24960403405d20103059107210111801000450008100660003505514100e526418075401c140e2500e0780440c4600043d5113410800583c10000100070681a003041d829942210307000000c442400280901c041c000c0b8030804000786041c549502c401c1d80c040802000d00c0c000e0304501020070003c40d00c54020490004050507860814034091680740c00502c0200c80c064411801d007003640044180103403a15003419102c001640b00c1c141c214003030700c1d05011094009050030400381822500c00f0400d00c42a801480404042402103810b4001c5039140f170041c2c119800c07802d01d030100b804002e62161102e0a213100091240c0c0341e0b851749440040c054070345503030746c0e46110800940420080314000703041c5060311340c0441c50700700c0380c00d40102c181c80042c841800c00140c420000a01a507807849100d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 798522544 1250 798521294 798521323
    0x9180506280516090506190e04090b04060b0f0409050304051c050f03041a03010b0712111002030a050108010513110315130c090606090e0c0f04030b01090e0102130611 73
    0x140c1045005030103c40d68240c041c80070b6407186000d9030344200b0710030300e48142c00108210303541e2101e254183c1800345034204080078000c1c00c0014035003010703101c082c1e0805040d03904881c2c0e981c40756035030030607860410724502c0400d0003102c0400c512403442d0b0b5420359034412485858022004411072000d00c0d842c0c29a02810a83c20806442444038000340d116100c3c0d0042c011000080788481079440c80b803000106803416100d1510711307103140800949030f401941c540f40841808100480034415800c03441801583c02c81c0109541c056102d0138007500220503510160005e00850b8580f804000c13401590840181d01242c0000f481c0b40701c0d1071030f071010906102662401580003840c0b94103000440d4204020345c90b546019480c42c89a0f0b45e1078045176810f807440c501c9030400240602c50140310548200560390303000f443d040080ba103002c240105091190700302d54001d6586d02e007500010010000075000341030305050808000c41c5441c030542241c6200c84903900564040210307030300020300ca8070020800f41d0b542c01c000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 798523794 1250 798522544 798522551
    0x6051b0408030403120c170903161215050c0a140904060b030a050604050702120a0e090903120c030c19170406050a0b030723130f060918050628 63
    0x454210030b550341c1c0b191008a0b0000da120301c10501d0284100380d102d00306a0301010300c00da00000070144002980040c0c8215a240c00744440002e0031000000001c0300a01c4050200075408466007400004540928000031400e410401000301c45090b010854588410364180005240301c100c50a00e034a0141940141e0024a0325038081040c0d01084080c1d440780156840c288081d584a400b4007041c3c038810703291800503030300000c04000004400406800050002d1030003104070b05000c03001a080e190262500310203134000284500754401404003987d40403401d50411455801d249070050100c0c8039107400204400c100c001e0228003584a504110b032640c1061000b0031450400382401350040c803046c3c0304240d62600d49031501c079060802146010442e540e0140c50f401000b180781402c14614001da107050f61011000410f2806695507210351801e030b0641400028140781090350a00071100d009014660301440500008005078000652541c0a42c5204200010045c001104184030140000c1c2d000b84608 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 798525044 1250 798523794 798523799
    0xf04080604060e0109020d0206090409020a120605010b130504020a031404060510080a02150c011401080a0507050607080715200d050a0c0507030c050a1a06010e03031606051b04 77
    0x100003400900450140204010622408108600303c0340381e04802500f09a20302007400140c075044020f84600310000d400803400c1125507000520020a03604401c94034407100c2314003c01e00c401446081d014180a21a032451300503100403840e0740b0801031151078400c075000207880e911140720340c210201065400c5010751440c03c15207407142c0a02000c40d0745505a003440303200051900710005518030701a4000c2c0080b2411300010108215961007a20204920340d01ca400030340502c2000c46680c1d000b00b41ea0400342032028030750f1400909062480c0d11461060200780815004548140c04035500300b5807101c60070030b41c0707080c136007001e0041c1442c40001c0d42d0024152182000c002901c00003000c8415803204108610b540e82d001103070440b10306010383c4c2c000038401e000020004c1d0042e0040140721340648122502218a55541407880900700381d68028820401c060050a50700481c02d40f0f80c842044005c0c1d03080c40341070f103050f150186249401a02c40c0e0b4907400420141500380c000061b4603812003207107666554 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 798526294 1250 798525044 798525059
    0x303100b0a0314180115051302030903120702030c01390e2d0d031b030c050610150c03020303072a0311190c05100e10090609051807140f04 61
    0x112400312134a01d03542071044800d564a0302614003819588004c1c40912080800003150000350401003401d1040d100c20070002c2d81d040404500b0301d200792210381c02103555800b6042b8841c00d407080c0f22079148203002886c0c1038014200b9003a5801045c911000056404400d88600846075908806907190300710201c0190740920305148120507841d40607a07002c507038905040c01d0502002d200040b001400040013844c005d140000900f0458400c58042c0c50715030411445510b8250a100054954135000034552004018820405100481004440c1090500c0007402d8901a459210080074482000b05000c040912562040b071605001e401c40d0060504000755854080d11010740c01c85201003d200c4c600100e400e0750503082691942c80d600800d80c071900d1703103044248600c40090700b2001c004d03c000340c4036140d40b507244c3d10039044e034010b0035690300c50542d841c098001e40101c050340c00c540d021b484080003e5518042020a140d005840d0b85820a589604142c514000b405030072222405084005800281c42 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 798527544 1250 798526294 798526321
    0x40e160e010603150b0306010c080d1107150e0607081b03010f0f08210a0e040504210309050c0d030e060706020c060c07020906010c020a08070306050a0e0303100b0a0314 74
    0x1c0d1034549040010303000c080b001e11004c0d401c0b0b01c11510b45041c10800038003554480c0490b66000c502c141e00403410a0f54800c001d20130f482c0d09141c20f10010b440840c03c1000c1c008024610b08201c4186a4204000c46030386040a4071344400618800a102a64000c19500300900d840c21070300402c101401070f107a503100c001c81642c00855110742000600c844001090760a000f1a031014011070060b1641e0355031440898840068200c40781e80d0007440a030844041702c0c0c3d110390058238070552040200301105080701903040d009442c5403144100701450b203250754000480008003501020740032583c545039804589011580c5031003800c1600d40001c1e000c03c40d80100101900584142c5d0360b182c0640700d21b6030f9603e0b948080c1f070040c40d001039402030031000410300550241004443c00d50001d0300c00b51540b511000050710304181c071380c070841c3d00325500d10400030302c900948954059121510091499424000b10500040269008103c04c1110020761850314501036404000d201b20610700c00492807404040b5441d44 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 798528794 1250 798527544 798527549
    0x120804020f033c03040e04050c0904030e090702030a050702150c1507020708030306060f3604050112020a2d090c0806090c0409020a0201060b070f021507050a02040e160e01 75
    0xc1d10480d0b80c0341000758500d0001e210f0000c1c80c0a000f982842d01d0b180391041c03402ca02900582d520700502002800549a80303c1d00ea110f10b000752203001c0719202c0542404003442c00204060215081840080710040d030042c01c44100d142c04580120520058541041c0350b88244d16070462a0b01c01c1120b0f000d002040e01d55558400c2c1c01c60b80a50300e41d41d41c2c030200b96417648801c0f80c0c0940d003c2c00400482281c24a0ba801402030500f407604042c0c0f00c008004401c01c480c0c03501500c1940c0d004048108500c2510342800303031901400c0542e00444d04004a81e01003503004840d40200d0780d0451b0000100e0800e60048208490301d01490301c0d59582e07103652022001d0040100c02c42000001d03c043d00094007900340f001081c1c0c0101d100240d1149480e107010b120100035003100071030320215500e600780047c0c4200c0702000340c60014054441152030351054810044d92f05038144c9194254241171180202044001c81c0301364507180c05403000304445040da4401ca04000c081226010301c40625031010030420310101140c0e06 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 798530044 1250 798528794 798528853
    0x10020307080615030618040f1a1902071112030d0501140a05120d110a0c0306020327032a031b1216170705030c0606150304120804020f03 60
    0x40030104550351142c520080301c14a0708601031440c0c6c039114100211010307601a02030414a00340402d83e644036080c207003c003620002c81131020003d01101c01d1401c040070486a00f400c004615110340d55441140381280607001e1841400c049084a0700d0340d0041c0125802014280703010000d541c0c45040740d8107081411040c45024480803203020034142031032582d0000c1e00b024080140340032350090900700c0301d10948059850140c05104550000a8102400c12000d90320841000d030301c134074041405d403495003030801940301040000160192445400300c02c446011201d07240030750130200126400b02a107844128032048900c4001440004110746110880088566009030b03500110050400f40f0280201500165500f16100000c00004c020307404c1e08080d09550300e0100e01300301c440d4540a082d078104003004015a000401000032514080490941441d078410a4a080d401c00d611040d16544030b82d4208401d00c1171040c0803500750354131700d004402d4103440281125944400c040001450f090408088603 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 798531294 1250 798530044 798530059
    0x1060b1902060703021612050d0c0905041401180509011b021f11040b091521010e1009020a030e0d02011e0b0906210a030905180c031503100203070806 66
    0x10748841c031074001c6500400c41061b2076403040321661100481202d0030f0048100303000381008001d00580c49801003050922103030700c4480c1c40c1d901c0c12040c807007640c40d20000f6415a02c030b00c500502014581d400c0040d0004511640042c040d41c4a012446c012b2656440c12018000ba03a5410700b01c0d1603000070007030f80100c81b00c2c00302d14164144e41411400d0300d20940c0030703401c2094144000c0c041e00c0c0c04400031705407002000300000e81d03620303c40780e0a0045520084440b440034000940019a185440b204580100b00b0013098580d5440d101c1502200701074240900303c0c107290002102040c00d1b03c2600828000c604642c1039a40d000c58981c4040d0003072607240721001c54608444a0f5a6010440740303d03245c15140041c00000d51550b0b444100303e142c1501b51081a40f140d041c855400b40c09004109100f1024401d441d20449941441d0401c01c8000d061250f40c0c009040b980d00b0060030100e20802d498010b00181c80c15040342e226500083d042601c010001c100851020040251140c2c2c86903006006d040203440c2d20 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 798532544 1250 798531294 798531301
    0x1107060e121b07240210150b0703031e0b0907080601120b1207081b040b0303070611070605012319030201050307111c09240e060f031503101e0203040501060b190206 72
    0x6c03010348000c4130280d11400500304c410405c94000340011b000040c400c0c58000f540540980c04003910b00c0c80034035500d945940d1042d01c2140d508201c003204d9004501c5050020071843c14400080ca00d4920140804e241510b541e000240750300e40403410307010006000143c440441c0c0b00c3c850710382d03202e20164103a55865006002c0490a08151003450340c031141c040c000c1c514024880e180c08003d05403c4240b900c1c6600108802c0010a9141c0310302030103001c0802d40000c180004020000c5e0700e20744904020320403c80c4940e10314241c0e09840c00c06007240e42c282006912665590015540741405080d83c1c402030251300103605240c5003040c00620034011646544405a4840318041c0e8050200c10070345c80e00b0041d000c8140d2f04607000d0303d5110300c010001805c46142140b82c1d100b40303210790016180100c041201040c075145070325050040504034250341d0001c01451a9103e4080e092205040000d083d0320b600002040c00e0000039002030001d07200342c034001a9940c5841042c814500700140d00c950041c0140303c040f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 798533794 1250 798532544 798532573
    0x605060a12050601140f060a030b01080a0209092a0705010603020a1a0406110102041d0613110904090807020a0803030f1509060f03010f1107060e121b072402 69
    0x1091465604440201820785c2442a002c082c5400000c4403075003e8410807550440303580300c0700206800800e5942c0800c01c68070b07180001d45030b100301600a01c0c00764010700612105844010586034403d4581768800ca0350000c0c0468401e80e01e0f00d0310717180d90140c3c0c0300090403001d0040c150044c5045910a03100310700341d01e9a65550949034090030030341a800001c104000c00a0074400c007952030000048500062800359100000038100c050700c0300151440040c0c008200140c0b0381803c80c8510000703402024400026052819450f500c500c2400d54480d55580c080001800100410341d007215602801e441381ea00d4480d00510390725002120300c44402211900010324070800e56004695590014252082c2901c07110200b0a500400410350740d0599a10140c015a43d01c003802141420f404000c0d42070b5590103e4181407041e910302ca00d0569107a03101182454400802c90300726a8511140d090326400701d51a01501410220194409000c12014044021003600c200c604425500c01d01e401316904c40310308840 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 798535044 1250 798533794 798533819
    0x1090b120a080702121f060501020f120f0a05090907090e0c1e0f1225030204080303011e09020706050708131a191d0c091510090b070605060a 62
    0x40106a501c0512400f40103013010319035071000c00d902c1e005868000b04250070f00c40022201e40814040c5685643c82040700e540c040c8107400c410308001026200002821031400c20728840c22a6680d000c0200081807014144100141c0740791009c0106480c03160709000c0b03c0104112100d0051a03200f0490801096488036010111410005101c60350341a61824841a40e12900701e9040c40c08600740030040c114124008843c01d510a00c00c502c2c0c403190104004d9400e00702800441482014035204010074803001c800042503038112080052442d0340e5901c801601c003490f000c0f030341c040c10081e400030543c3ca0411000d60000b510a01d0150340390310b8190b9868080f441d5040a00300003500320090448004686d4145464080c0d100e000611080000c0c03481d559094111035080040c20744001400c07029030446001413005800301c480465100c07445050581040703a601c48072440d042c2c801d00c01903510884070760050707480b10010504140d443d0740b03c0d041d50400102800c012a240c5105001058000c10680c50511 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 798536294 1250 798535044 798535063
    0x30312010f0608040c0909060b1c050f0a110d0302011515080a0203010510030c05040f080a1202010b0625170304020f1210051f1203030c0518130b040501090b12 70
    0x18000901c00e17180850031b50040c0fa100030700341c98060b100d10ba50012034868840c40c4032043c10819102108916904140b401d1980c42481000c69400501c038039008601202124840224200c8003140e010740a8501640141030840e40004c03600c1e40c40c4000500b044d43c041020001c001c0680703500500d80d8661351820203e200900a950f4032070904445030f601d0038401c0d403000a048201303007000c41c64161a503030002900c000f2584003c100354410b11000e000c0005420003140c0901182c0000c2c000c003003520000079554021081d1080c0750000e4404640485c0e40c1c951028641c940e08240c100f41b4220707130284520318503482182e003030740511031a060514081c145000d29514041d54140901601990003140e00082d1030040c040c26401f00c001aa100040380c2c05202050040c00ca94103236001c0000a4034028056810343c5000005000c014849441d100f03100140701c03118524100e980c0c05500000501403801070083c0320344980c00524040020414800580c48a0031030401240c8154601c11855026036651900b0b2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 798537544 1250 798536294 798536303
    0x9060902040e0f04170d0b01120e0618070905072a0b0126030a020a021f08071214041b050a0320180f07080105010e092202030312010f060804 62
    0x4070024551000580f4915005442030310301800210401d91703002c4c425040207507000076840c7d54001c070015540c1c20151000d4592a003280611480440004207500d44100414240c040702c3d000c07e22011320202880008080c110079a8100b14504010ba0024444402100080c900d680e40c1c090024808048403060058281c1c0200d03400d1160782040205403506034010300c2c40d00d59061a04c032000322454140081d0550480c0340e8000c10700e01003c0e00410003050880041d4003003092440c50f00700d2616500c41c141640c01485400d1402e03d40c034400144030024007440500304909890b4900303000802c941185091080c0a000c444031040c41d031101c04102100d061031000a0050566035500c15089412000c000c4500c1c2c8002c00e200d03040c3d403003228074540484c07040714183d440d1540e01c000c0000140e00203800701e0161400703103488060100c1ca8401302e01401800f510003d444030300785000684048401c00010300550340582520b456226813004c2110120080c02030016002034850040303500c81c0b18140f010f1085800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 798538794 1250 798537544 798537569
    0x24060f120d030b0d081c060f0f0905070c23160605030126160e0a0903020c010c05070b070507030c17030d05090109080414010f0e0a14031014010906090204 68
    0x11040580090403e510243e80002242104c0d02c040340702140074001d5605811b180d950803917042c4071841c0440e105a002400403909548052040e502c00507005010b035181c007480001c040e183c1c4202550390081100005000070981c40c80340180c103800344003010000d0103000455000c8040000032481c1c001d200e0190b400003507014030041000038a03d0b102c0d6500340700c41100c05508046160340041c00d000b6a419009042028088200b00090a40020980c0034076408420003804030b60b80d40080d02c90806605040c100728210f104d01e02801424802d000040104070790072070b59440e2615060351548d42c030f88402e4421100307647c1c001034650407d14050440740c0130f00020f185481c0d12294508028000584042e4881d0340c1e5108410005891000070300c0540703070300004401c80040510005002480600100082004207041020240c481c5041c060585d113554074902c03901180c40740842c1c40c11210420340c2c5100c5040040034031f003013902e107510709050380c0340300c081071110a4540d01c0c22000d0303119a120310042c1960 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 798540044 1250 798538794 798538813
    0x602040b18100e100c02060d02130303090b16260c01290612041104020d021909051f0201090f06061508090703030e010201090210050904150503071724060f12 69
    0x201e54505c001e000d1005005904003004400361600326084200118013140840310140305045d00030904c0b20080040c3c01c052889e02e981c441d9110b10000c0c0001d07000381608681004c1240d81086900c0510381c9400028126442e0907001240c18041d064110020031079502c401da0803070f0781011004030012002c01c0139062038504100c0401d108200c04000700251899181d012450f011075883c0e000415400e0002000540c0315440303001d28819101003001020144039286004000385e86405001105510142d81007410000f0503a130181e02600c20f0060040203484c54040c010b00300701e0254014010b94074011210707454800480d0007500c1c00766065800c64030076404404c04100103841503503050401c103018800400c55000660106001070076005034000030035800700e46039043c0c1c03d0074829941402c48403150011421b1610011a86a901500454841c4000341b1500360840404000010a090100c0003403901030f04101c41a01012205aa26600ca0441905034001900d002400c1e004030300c100c0c9016040300c8a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 798541294 1250 798540044 798540047
    0x108071505040e010b040f060f0804020123120a0e06151c050f011a010c0314030403180801020d060b0a0f08040309050315060a0f0602060c070602040b18100e10 70
    0x9140400c007006020480456030a000718040d5000380685580c80d900c541c03d0401002c00e02d0802d030002d004108070140000c0e0001d502500c60754001d502070030301002c038268103c19003640c0c648016500c0000000047d01c0d084104418000d0791251483c04801c104100c0c02c40c0c00d0307685590040c1c911080c00c1c0c52005400c8498500b00600342c424482501c01e4041400850351202d050141c01600302c4143d0f5900c410310400c80340e074441000381a600900c1c00c9102d1415030343c0e02030700a030320101d414017440d000480094109801400030130040406920740502c015076030003605002c0d600c1380e074070140100c0c1050b01c0050303002c15102c2541c8100c500d54840c0e001c94200c0003c101c1c0d01c40c600030310580030000c0306240002da0791400d00c1200d180d00400f1010307043c0791400c18140940c0029550019404248880c401c01c20140d0110308190007200024480b42e0319206820700c01c001c1d000d40d0b000f21011210000d040e0794142001c030314800d1141001d0300c05a00116541c0c100390380c000200e42c0199003100000c400c120315107 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 798542544 1250 798541294 798541319
    0xc03050d02090a0e0403030f240e09100905030c1020072a080105090303040323130f0905100302031b060f0a0c0510020f0415020a05061617010807 64
    0xc0b028180c8049240d0355200380341681019103081d80425075400141d1030b0302c03105000305001031020184440386042034600a10b52100075210b08a0144802000701d404d41c00144180001410ba00301c06004c001d100d07050090f240d9014121500741c42c8030320b6006007110b00c528004d846c400e03403007250300d03a1a060018180036001c1d80044404c413041c0741c0046018030444041c66603a003072210a82c294050035030410805500b150005415950b0b203500074070070000001c1c0e1001c02c0d072840b5140e884110329140d0b150314800c0914090302101c1c1c8110b0741020f10119280c0303e480c002a0884010072402d0206840b544942c0e2401e42150002075015040782134030700da4040385a010040d92500103042da0307142c108086d4586080d5002000d0b01d1000481c104081740034010708001c10744241010603411440c0c90b10400446000f071017a8410445183c03860200c203203480d80240012041c440e04007094403200e103080954020a14a02504030f40864078bc40d8071032003100f48a116040c10385100d0070003001c82074101404103445 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 798543794 1250 798542544 798542557
    0x10c06090203070308180f090703200f07060b010c03020c040c090506030901020903010b1206150604030b1f0f060203400905070503090606090603010e0706050408010c0c03050d02 78
    0x22540351086940140c60420254001358003981003117403245a24000e01200d46280402c0c94850800300c180c882c003e40d00da1020310b410400c5401d00195030303c1c807400c007100c100352416491112107002160f00e075440101d4000410f100e6205030320401142030300701c0040d02d07008001c45000c0c0c0103a00c1040b080d00b01d8101980080d90035280c034142000101e5417000040d60f44d0303004403250521650041201d1207241000d02481c130725188221650884a1000d500c41a55188000c280302103040103800b9403801901c6240c1120b0103141c0199140101e0700c4d002030380d03031004401c85111005905d800d010024103a50705c464120195140c2e0b502a51030300e003a01d00b4440c03190100c0068078800390070803001102c0050980244080351010491503038802881d124283c001c6807402000201400001c1040220b004c1010520030390090086402c56502d44444000c68014295010b003401c40b48540b20700410910380050191045920900084c0402e1400c40b80032140110440303070003008900f0038828942065a6a00a85603 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 798545044 1250 798543794 798543803
    0x6220507030f020a0c02030708010507140a12020f190e01051206060c012d200705010b03030c010e0606030706140f0c0d0c060f050f011802071406070801170309010c 72
    0x245510818441c000f207038000710503070001c40c020800032400c50600340305080090200b90020841807404000140c48421001e0724180084400140c0b401c41d54020500d070010460b0340c50003151154159029800303141d00c80c241460381c40100328904e50300369100301003c0b00c0b03262040e91010f090551807140e1051800703000d08080da02c800305000c038441c408024800da0440d110b0046900c0c4480a800c124440d000300000d0f1680c0e9082c0c1006820207240c80c85c070b22100030070701c03900c01800c2c0c2d54041403c24500624007aa0740691602000a4061843c5015081f400e010354034002aa62141c40f580205940c07207442e0700ca002e0208000b00c80d00b00c5143c0705e503005001c0b200001500c551900034007905150401e040000300c40c01080c8903100e1241400118440e414070781341c2289081149080c6814031001100f0144034018409000c95201c4018444d640c040e915015440271031801c02c48100c0c000307280c440d03100f22480c800181c0c4e140000201d180000006c07400c510603150166107049081001100d040301006810388 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 798546294 1250 798545044 798545051
    0x3090204090b0708071e09050d0201022119050c07090b01050706020a0314060303160b0c04120804031109010e041b080d2304080c12010b0a060503040303050622050703 73
    0x200b001a04018403804070391340c5540c1a450186805004116441c0c91510305004000d4084402a08034045c070090302c80032115403842a8240c80100c0c50711210f0520030080c8161044420a5482ca071409080300600109035a40414141841220240070380441c03101d09501000e0200556082980300170481681032502da2b1402d900c0f5211103041c1e0b440307280a80006035070340c030b1411031610030000041c3d0007074021000b8501e03100b00481003602307136074511030051319030300d0808042504441c038202150004c003030306481180c1040c070030308002103290004c0c072042d00c8000c000030009807185020350b03066042c0d0b050300034114000c0c0c0302c41e140c0400034805c1900e003c0c20795170b900b10003068440040002140e004a2551110340c0085502c800c441319002c510444459504140018460040007107241124002c05588242c4050580b00480740501915542d4075004041410040b409581c402e000b113105030301a407000d11054860324107015503420022076a06603013250381410302000013a604440c0c0c20112a01c0e010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 798547544 1250 798546294 798546311
    0x31906050319020301060e0c0304030315090f02030f1f0303050904140901050910050702150a110c0a03110303160f03090c0f03060e191b1508091b0102030a03090204 72
    0x28070346554034400c00ba08541e184800811440c09006a002a0140200d54501b50030603550043d5030b408044c0c4010103060b22409000d031a02c4c00e2081d0740000386100c00c4184580752401a40100035402a18803401916040002440e14180805000d41129940b58200445461074034101e509070400c3d03d00f40d030300c191103c41c64181c0d410311060300c900a003840c2c800016141010800c80d45800b000b01141c828450901d0100043d854010603800d4a02c00320068440142c1d883c101c00400401012000040101c1d020520040e41d00b4001502401c40b07200e5141e8001d2290320400981d600c2c0000c0340d04098a461a0060030102403049140d01000000350602042110440e81c41e00401c08441e0806040507e0801041045c0300321401082c00c10a000409001c16941c820020200520074007001b8108858103142d603945508529464401013902014002c074042420b080100240303400d842001d41072040c0b40c1090010510307550031003011030b8160000d5150910a820030350141002c028166402591040318 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 798548794 1250 798547544 798547549
    0x2250501180f09051801092105040f060203133305090d08031504050411010e0d0503040b040504110c06040201201902100903080d020706180c030201030c0c0803190605 73
    0x2c4000b4120040c40418289406080d4000c456402c00010740d41e07038100390101d808a01e41c0101c2c0c034810710122078004400c50714040155454441d95014954500d4a204001002580071000d003e440b0004509604103035690440c854928a07010000090514840e00412040c41140603030740103c4814240b6604114010303000900103c0664401d65441c9000010406080b803c4012810718000c211010003039402c058440071049118007409905008800c000189a6941c9070f560070305842d4030108a964650b110000400c046c0c11074840d50780101d0404101008445550b8140c81c3c1007400040200300f00e6460341c0045485030703858011020001078908849120b80401d0010341203442e008410016001003a10621645034000d510360410466031301d0003440040d00c10070071640501c500b51800341e1141441e0602c0e00c0102990f0068211004581004000704080041d0340c00c1101d000342c07020801c15003441004d031940104140d004116078000c1000480d011804040c8000451a1302c3c4000740003520b0343c01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 798550044 1250 798548794 798548819
    0xf040303030b010f390f031b050a140c0a060906090605210a0b060729100b221404050f270c0604061805010309080f0a0e150a0225050118 60
    0x6050306c121807400000011300d90400c071083c542051071130105541007065121203445600c042c1c1700a08400303062410a0702580c0c10003407000c01d40b4000b080000c0c0300e542e0b020090102c1c8076510410000c507842410008506000c1c00555450007550740784400c5041e5081860700744070000030140202159030303001000240c2c98400180501c1d62107624005940c00045071880e0108500c8942070459420a50411910114280100003100c02201d460741e07c0f11000c3d514000b4441c24101590b000f228400400102024850940c1c640c003c415681080710740c0f2104c0200303aa0282c00c403501c111981c0d004104038130080442011001e6981d49134280c1b40a5010f01d4000350480c0d04c29030185001640007001601da94501240d804024142401c042210748403a40c1c9416980c01504031412040c0c601042800b010703070203590410342002005241c13118140d2408000142d40d04111072500c010301c81e5101c00c035040107880d034441d46407541407006007140915140045520700420007034118816610900044d001e840c109 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 798551294 1250 798550044 798550157
    0xf06090f06020406050d1b090501210c1d010804051c09030c0e0106110c03060105042a031a33190507120206100312020a0203030f040303030b010f 64
    0x10748496448030440c1c40c1d03c00f0f41e040450088007c907405052401c0c09074000d0740700e00417a402803c01b05220b44042180c070702480c2040700c44e044400d0810000e180d00301d621445116159004544503030300080c0f18001150404000c90340184640e20400650580c40442c000d81d4180200c01e2800b003482540301d980c1c1c1d81c201c4840d41d106d043d5126000c8014804150000340240c1e126204100400d460000c2070f00007952110180b1039580615540c03040e001c0700400707000355118102a1203800c0441445208030060082c00703817514041140454898010b1946000750740c0005002ca40300348414403081803c202c101c0841d1030304514240f0ba00070000700040345181c0c4e10080520410b43c540c02e846222500305269003444600079001103411072810000b85c44010044c200030340c0c0c0c10074400b000313800c81e0300300c00d0385060009100030b54503200220b280e40f4040d01030001401901c2c4640c2d400d1011086500040d50451884071544000c510380718001d80030014080102c3e01c030450045589070b612804a545161140f1803c0d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 798552544 1250 798551294 798551297
    0x50601260a053003070c02040906090b0f15130f02040e090309032b0c05030d0207110a0605030126120406020f0d020f0a080c01090204060b0d0b030a0f06090f06020406 73
    0x42d854090b01034a603e0001552448101d106002c51041c14100000d440000d00500078003a89040503015501c40c3e0748140301c55540511304018540721400c1010001c1c40c00c880010f0070411100004004102e02c4081ca6900ba2001c0e20115442100c0c0040340003030901800c4440e5000d50030b00000408800c2d244840d8094000c4c0005150354264900505040200f44490820300d00c8080c016950132a2400ca6400c0507000c2500c4d04904041c200d144c071604500c29103011b851130303900100340c000c01d12001c481c9101c3c41c0740080350380410480d038a510948040c0002d1007100600360b00318014650f0120048940c001900044090325a04180c014060840e03812a40010300181d200d5640849003040c1000b14114400043c00180b400b03081c01c580d03440da0b0748401e14000f030480d20301181400c0d014200350002c102c0560300501c00c0c00717625100d13458800755402104611005900f04007960006040105443e464550007a50795030140c1115120040900001201150810340055002c00416600c3c4040c0c0080c0465 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 798553794 1250 798552544 798552553
    0x6020f04060e041b0507060615030c1b030507080f090402070b0a0f050c041806050a08010207020a0e0601090312050c01050711070f0f0312020703050a060c1407050601260a05 76
    0x14120020b04454094282074002c62518003000e660580004120820310403034540141d41d03174007500d0008040c0ca000e900c002440215810801502d9030117402c00e80140005903120380c41c0c2c200e41e000742c4c030890b080f003080500070910402119000c224000000c011030b50f02010040d281c0405840030804036440b9507000e40d07402d803050043c090000f14901071059800d0300c01500b4052801c01581881b814822403141040e120100328045403107029603001400101401000880340540e1040707030902030751080408904c50901000042071100d0401c00240c0240c0069481460f118195a10602d2000e800400e80082c05428000107555404c00d0044d54480c945565031008000008503a0a1415000b81c000c0e48000034007100910814503110411012243c2201900d09408e10282c41642420646c1c1c00151840c00b0780c82001c0e0030b204c4160425102c242c110354075070401c0c0d035880c0c0041f41c450151141c01410381d0880c01c0104030414036414101c3e020603040843c2d00054925070001d6141080002044403607400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 798555044 1250 798553794 798553799
    0x30c080307080a11070309051e04051510090810090602071b1a07030e0f010c0203070b1323241201330c0c0902120a05090f0a020402030a0906020f04 65
    0x694090001c84c1d03040d4000a5042142a03a030181100038036000303440c09040c0407138407143c51140391000c1d410718100c080c1c02080103003048120320000311400c1070301ca030240503203096403102940301c1c0e0b40f05802c6800403005891a203000300103c1010300201e80c0240d0f6219001d014409c00f22384d018102605400c560420191018a494012405d0b100f140b09401086a0284100c002107500310400030715007103007111802903101207140103850030900240045e40621030400040307540c6d82094000d2613500c081320070548000e1340d54041400b030713081e01749008503ca850700c001c603005a00b020a0103003164000707514040ca80a0081321006200d820001c4d030702000c1b100c050010000c00062005000c05820140007040610705908101c10008054039019004c000100942405002030750344080050840d9040655071100468030b0200e59400c06d07110b001185180002160188034000f2f1701c5000810b1004c00b601030541d49808000007504004d0000d501d2944a400d260001a4030344020b114159242e070415850300d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 798556294 1250 798555044 798555061
    0x6020105151f0503040206041208070b0609071b11090c040501090b040b19030e03130302091807150302040f0e011d0609130303090b07091505030f060904030c08030708 73
    0xc00c0004524000d5a85a940c250680d10118290031000090f04042ea44ea8580d480482c90038407440d032143c00c902644400c03250820903008001d1106a026540c2d80c6442c0d00e4403070402072160815030701399010032a8002c038180c0303001e1210356858249000380c80b1080d03100b20320000710b03150220441c2e0108940500080a100c10343c1c000440c10302921540c5851810141084200f00282c400d000a5030510250710680c01000c610039000054000c0e4400b00762511178001c0d001d18a82c22107140400c81c815080f11002a0182001301041941e84050b1001050714628180c0c0c921130031007815800004064081102180c240580512803000702129000d440a40d89030402e8405040200541e0040120070102030110030351703031400e845402c040c5507561045a81c40b0351070180c00504c11080014a001d480a042000540d00030b02007004071411035250110701c40c018034084030742c1e01c0200c071509007640340300c4041619030420070a881d41c4148241400035221a40340c41d100c5498208841d06000950110104050403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 798557544 1250 798556294 798556321
    0x7030c0305060303030a021e0403150506100815010e0a030516170a081606090c0e0711100507021e0304090b0604150e13110306090f040c03140102040f06020105 70
    0x20495180070045401c04000080d101d01c00035101050680c1c0100d103c0c04001c02c0184495800008c81e060265250f03528681154403042902c40f1002c2c43c0e24100c001a490704241c80e60003420b00159854000503580c0c41204266080340007000d5041003c80c00032490207403501b001e02800703540118024018031071070b11414170418055410001e44049640b00c0002c0b203810010f6174412440c0d22203881501c0e11301c1014001084144074074040c4c00301e401c1030240000d102d0128016015100804060041c0d5030703aa0ba8152503100040000304090350003010514540c4400380c1c4201d070060f559106880781c422940008907025100034400c803400d03400004d4100080c110901c0390501e0010700707507000d44c10300e480c02590000c2e0741440c16900081c001e410580441c0b0740d03501c1640c40c420103a4a201080b00c0302c44000c800c42c291300100d40340d03070140381c0840c00b0a1545044145061141d0b1740040c4090fa507905594031240b5040314012030342c00342d41d000c2c0004607201642c00d05c80ba01920b03055000150b9403400c280a100c24 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 798558794 1250 798557544 798557561
    0xf121f1d070501090e04031b140c0907091a0417030309010b01020705091603092a171903030f1404020f090c0301050d150606032c150a0b0411030703 65
    0x554009601003182d07980110540e000c80780080205007495607a41401c1e1055280200920030106e0000682c204200f031700f0f000c0c00201d02c04441290003986c4400c05100620714165104000304480d0f0328100b110200d8503400d4180d80b9440541ca6081c10b03951042c03075010160303146080703102c0e800100030000225000d00c66841c01c1c0000744003c0c640f06203040c021821001026102d000505400004a00c2d66402500813000e82c50b03004112516800341e02c203007101025502c0c480c0045082b05400005003232040b686c01c10405a02c150060045094141c2c6040c80503001054100c0c20f050f1144001d140f064660720408003c02c2d000301c0c030501c4a11345481000244442046101d20800c401030900a150540360b05890540b401910051481407aa09200301207031200300141841d03c0c10000085452540b64212178000409003100003042c0180400d00f950022001041c0203c41e401800590b0b0060a103031192900004a400300203140c403448404942501c100400076280b8103000018003512544c0342c40380198 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 798560044 1250 798558794 798558851
    0x607080f04032603060d02011101090c0803190201090804090507020a24050708042003031309020c070f03050a17070b1302030c0a0e0c030402151b1009020f121f 70
    0x344d4600038001421403500c03510003a04008204a08c45e82081d025444001e6050700580c5040c0c03019622a80302e0303a01d43c041c200c0180b0300301c1035402c004807070b0f401400741031481c513401000c17203040c81e00340b8512000610006004900314031580400e0404240d1162818024460801800f5444228002250103072100509607404000388401008086403440401c01c0e44540c50f80f034131584040140d40041d1a41c0240800c1d102c0d07840c0b07001400945511260f009124400000050350403290362440e01034540f44081c400600143c00640610700000c408981e50307469103000200d03540c2040c04544511014417000c0f54040a0051078202da0020351908202c00007907030400326501458036040000501007080094800d070204c82010000c01d04664640c600c02080c0d040100c40c240d110b00401244941014506016856074015404904414062802048580742d0050041271001441c4818010030050713a500002d894000c07401c0c29a01024542ca0b60f1719030820707002010440f41d00401900401d0b0707400560420 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 798561151 1107 798560044 798560047
    0x4151a0415030c060c050a08091c1b09110f0d240e0a11091c12030b0f03060103021503040302101404141b0607080f040326 54
    0xe0031240124400f141c1071341c2d202010f6500d40141c09000e011600000f0000300414001c40040c400014090454200c9040914030358410301c0082000302c2e01d07100000011008281c1d0b80180340c01800340d00b8401c120440807994400300a01c1184407518141c400030551800040040c5d020807001000245810101c141202c0c401041c4100b6006a034141e01411002c01c202803510300c50b4100001441c1880c61410300b00c3c004100082850300da07900c481911380300c00030740040c03001041d0b025607074002d48020900144000800c5440350002c10410300030342c400001007015a0f1100301c1c01e1160110003041036680e45550030201d0400c0f803ca0b6102c11405c0c10800c02c00c1140f501c01c8c803a184a6402200c0c14100e0031202040a52907480c030410030408011148080c000303603d800303002815018880c902891400c00d001c8840b12045c2c00561041e2401c10340c0000076030031241c00c0b5502d034804035042801c4a = true := by decide +kernel

theorem cover : BRFrame.Cov 798381294 798561151 := by
  have h0 := BRFrame.cov_init 798381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 798381294 ≤ n) (h2 : n < 798561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
