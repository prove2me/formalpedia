-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0148
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:07:04.184651+00:00
-- url     : https://prove2.me/submissions/addf259b-89c0-44d5-91f9-f9e61454bdae

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 26438854 ≤ n < 26618710 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 26440104 1250 26438854 26438857
    0x90405060f0d0302100e16050118030f08071202011a060f0c0709020309151e040c0506030702010501240c0b09070512010209030d0311031324020904110c03120c040506 73
    0xb03000341e005000040c06042c6170b4003140e504c1e902844598200410202d410041c0d440c020084410a10744110113200040c00c01014101580000b050b040030040428140b00c24140506022402009200c2c0382d0404204241e08031241d54003144c01d54020280303c00018030b0401d016140c42d080301c0801034038121981501508052060300a0814a039010050144d00b50040013910b42070044d4003d07003070b11820140c00d41c0e400c0c0142d4802c4003008211b400000343c1000004028600180300103803e040e124181560064040c200c2401000a24407103010034a040c04880080100400e4081d200d0503001801c0c0d441ea104803950080003c44148201c0400203115120744d10343d4003280d040c034000140c48401c180c04041c02e00040340201c104250a202980f0300c240c11040459402190400e0407940700040c0d0314000c0010800f000740d00000503030640016944408640050130b1040c0110741c00c0040c00c0402a50b40d03c47c1c082d0350380c29800c0b50b00600245407000003004125801170101c00d6a141016941c0b0700140a9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 26441354 1250 26440104 26440129
    0xc010c050708030c070906090c081b0f070f050c0306061518031c0908030a120b0301060801050705210403091511030a0c0510060302130b04110a08010e07020d05090405060f 75
    0x300c5c0d01044041215803201d110b088040e0100190501c042c9000d044000c0c41c2607c003400c50300d030f08403d80d0901c02d400000101141d043e46241e0300c1403911207205040c00c4224078000780303080ea100d0240e4105884d840ca0301145540c0300b170200900f030342c2d0309009011400c1c10541164400d402000da030f004043c3c3c4035036010070101440c20440e0504101394442d40c0030041c590b81c043ea003d0340480c1d0003813054a00c43e5030003040168000d0320350000010300314191b10010b8007411240d842045c0d2540382409000720b07154010010038440841d0300280c4130410b640e20071480c24400449010340003030160481806081c0030303060031451b8045a03203401b10644020b07103d0b0364256401041e1101c0883c8040c3c14480810000340324080c0c00d104d10000c1000b03442d246402158400881c8030460b10500d58910103031400d030ba10b55000284030217141c200d890703d170903880d0b00141c2146000e00500e660b90000d00300090540384001440045021507544d118141001c11b02030001428010700b000340c0c00007001c1c24200d026100c03010300002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 26442604 1250 26441354 26441377
    0x1e0a0606150f03050c07300509030706050301030803161701120c05010305070e0108060102030418060306050f070c02010f0507050129030d0504050f040b030303070302031e0105030c010c05070803 85
    0x4081014040503060080400b0800d003414245401c01003a803583c04281c4100710380081d164048940c02c1c01d40c0c60711000c40d90303140d644250030225010302d1103540100604045003040d01140c41a5407200b0b015030b0940400d01c00144102030801c001003202e80003000b9001d0780403480c14039542a140480c880700424109801504c132b030541c9242448244000146d80400406081c00c1c1000b560030304841c01414480a401d41c1e60501c1075400120303859900c00c00884000700f894000101e068081e20403000064019844281c92442c01c10300410410303807401c901c00b4003c0740386844001480400d6401580d04d040c4d0440c0440500c141800740501003042805959110b040c3c400c0c0083d10102d000d900460f00d6841c1d003a80e240039500112180b06051303004801c8074240d400844140d0400501c041c001006040d1080381035405020200c00d0000c1c3c40c0e0150091401102c5000d10b01500c04010030303142e90094024070502d6071590000d00c0c2403c0300d5025880390070445000b032003540d21198445a01314a1584041c09003030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 26443854 1250 26442604 26442629
    0x5010e030d0e0c0a03120c0507051c0210031e0902040b0405040b060306151e0604030f030918090b0a09030e030d09030c0905040c17150a022205031e0a0606 68
    0xb403480d1400d201c810501042100c15001141c10b40c4c8640d00448400f00f110340a0040c2c21f4504414080c040080070000c210040000b50b82042e000c962440f0600c132104128001d4440c1c080c01848a1b02074001e04000b0030680b4407086050020486003000342000000030b0360007d5079088d00007120740365401000d125501540800400c0c0c00d25200b4140740281c01000c41108034200b041004040d501d50200550f401c030380424150550100b000051524400c650005100500109401d010150010f0400c1c0441d080d0030f103c0c1a04c40c0201d80948150b410514000f80004003c0c0300013051418240d0081c44d03980c0c0245004c242803d9100c0210741f0b0300550642807404201880420420048011104006402903050500c041d0600da03807841100c95003801002041c04c110381c1006039408003000a200361001c1907c840040d41010b40c0e10000075803005034080030101c0d000d040c10b800e64082090b07050448a000d0700400ca0350b40418000040440304c46041c4801c4d00035081440c4c0482c501d8052900075061400c07105 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 26445104 1250 26443854 26443871
    0x3050403110306010506030606090103110406110f01020301120b28050a0e0f100b0303070b0a0606030509030703020c100e13020406020c120c0906060f0d0f060b160f05010e030d 77
    0x300d5405141c1c0c211030b40300350301150041c0301c0fa48030507054036000903081e90050303140c4500c1c100690281500b4042c0403a81e482c04140042c800f9071003090b0400f109990002d60b0080d04408140707509074402400350050820800b01104009856039820a40c8100c5c0c4012414200c15884c400c840d002c1d1050201152240d1281c0c188000484644600d9242003031100c000d1902086010a058550310380290f001841d80e92001480807586082c0110764050341c0c080d02182182c0781c8944028011702c10750045d003001901e040c0000d15000000000c4030052501a0020030321031000c042084540364800e518041000000890340416407101c0844140480d6150009030b29a0b051110081c6808554417107079100d4040c400d00c210f55050042007800480c501500c03841e2480ea42c1501150316031041c0501d001c0074420020740d402c0d600240f5030240c1010308030b05c4000c0c888250760303009559940c0500d50303c0d00380c401c2c031543d44003001608403008081214480c00001c1080d514115505003550003100e01008419100e1400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 26446354 1250 26445104 26445113
    0x903020c031612080903070305060906090601060903081c0204080d020714010c02060406030c1b1a0f07020d21020c03031503060115030b0307031e05011406090402010c030908060403050403 82
    0x1070b4114869a4904811441c5002c50008840400400113032020b000051440f0440d202408140b01071500034049500340d042c0310038407594886003250318042a020b00000412030034032950085003100d03005a909130a00c02c0d48210880003000811283c0ca101d5802c12000403d007800f40304100320240c454003c1c0059901d046211a0440020125035040084402105005992701c0090700c0940782c00e464002402c029454090340c90019241441d41c510300081580800c0103107001744540e02010224058019441e4080c0201c2115400d5560301d026810035065110883e100e2080e0b40d11090211004550000d1101c2c0083c04030391100010040540001041140024988101028003401a03000b00110b40c544094201c40500c07003c241401c05803a02c0a800c5150b404100c0344018680025900c1e520a0a10141c20a800702c1200100c0f503550802c00d10f90102c00714084810310072803001d40760508a0361130360b0044074000d100303403030880034003201507008580240c04104040c400c601c0f0f600c80070390300c90a6040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 26447604 1250 26446354 26446363
    0x6060503010c090b0c0a0204020d0203160c03020304060c15050c040e1503031608071a1501030e0607140f03010e04020a14030c010509030c120a0c0e16120209040903020c03 75
    0x450080e814091102c5090b40d228800c202100d40c1d08003020340700d81000190314241480c0c058040e611900101c0c1120080c3c0e040d03402035008003200717140c550030400740e01c0094805201c81800030f0090b800c1071204001550155190a84403845101040c42c552602a48401120019204018501c03404a000e00401c146d0200c69500992040701c40d420b8520050002a1390f8420324600505210242003140300b0020075109841e4100d6003ca4440401341c41c081c2e80d0704554004903040344440e44920746d0561154024801c41c1c42842528024011540c1c52030350644660944058801ca628010400889906c080c6c80240d8042c041c4114049500e0900f0b0041201058182d000f25183c0403540000200b03954001230001c02c2c01100b820701ea074441c1c40c0a0000b03824080d1100308503030800c08504444402100c041030142c0002d02c64507003202c0e03403510740e9644070019104440b014540e1215201c005640c900030800b0101107000880058603086003d00400e0540c5e107403c0d002ca0140c0d000f4060b840c02442e0910 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 26448854 1250 26447604 26447609
    0x6020f0f120906070c210c1e020103061d0c09030307080409090302070b0406080a09030302040b0403050601050405090105090706080411040606110d03110403020424030c0314070501080c0306011707020a0606 90
    0x58140005c408548074121500ca1a0105602e000a0200154401070099510651458000f07207009400c4507402419095048940c6049001a00d007030400308100d0105940d01120340c10301c00a11405541c1c2316600600f80d400b020315545d0521082c080540000c12110003403024103082c043c089101c50340c510300030385170803d542c00150340b50380144001d005c015400320f00d4a61000880364081032001e03131800d056009216542128031044000140441840000a4014102d4205680070043c0d0342e1000304050890701c003526440724941000300d0400c00244251080342d00036010f500d000b451900c1743720000e0100ea96a601010125416400c0072000300720031700000344030100390b080a0207a2610a11070f806580f04030f01009100b96551030450060311903468418040100b0751444244150b120f0400c500121010300c01161005544c038113030080c10f48046003031011a14181c48905464580e900c400d80d4641008250380d040045d2012030074a0701026650007806114540c000d00281d001a09051060320301c80d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 26450104 1250 26448854 26448857
    0x6131802090d0b10150905030f0307080906130902030403031a0108070e190b0a0206060310020f03070815150309150103080d02070302100e0c0108011d010306020f0f12090607 76
    0x180080d0101d5141c800c00c9080141e8801e4041081e0b0782c035080310740541310180c0c11100c14801c900c0c01060030660008808410765070118101c03540e0800c154050707a0f691181da44010701400d0f0074424101c0034100b8001034100750b0000ea000c0c45080d03880d4942501243c00440303043e00060b44030a40c01d850401580001c0140302d100307107130194542c9442d60000d000c072800013030281c5c05282d60010010f40c0c0c510485a60300603001400d0b0160b42c1c1c41c11440300139514403068681900c41c0c02105100b0b010344d5464800c440f528007100075614115504c818065030452402001104032014900e48240e20b540c500c42c01c0c29001e05914445901c034246150b03001d00e80181e1a11400140b02150014004610940705450550603034884c090f80d101541d2030202d003400c0ca036a00f200d02c250300703015070064100404031700c2c80700c0a80d0a0fa03600d54180ea86004a140c005900c0d20910410300000e0014008583c3c01d80040c050712030140d40385032801d049501d846103180c0c001460080c2842c104018402c0481003440410b8115055 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 26451354 1250 26450104 26450107
    0x302090708100311040b0301090507050f0d030914010c08071506080307050304050d030905120a0312020316030b030313090608010b0103090209070f09030b010b0c0c090c070f0c0506131802 82
    0xb050080c42003500c9800040e0081401c000c02d404150346540002040d0f9001600034450754803e46440e6a5030500c5010741031045050040e591101e041141e04032200301c1c0c05075180c50780c0b686004099005041510500b50401c0700502c051000b0452000003000700c180b159920090340007014044004860035a04100380711341042054002007607000ac04d560a44100b141c100d45412418641aa807048580e4030441c0c02c480142201168040b001c20079200c0180a915001d64002c1d10840c08412848201e40401100c40032105100d8220300c251b0046004050280480740751050b5800070b10489842544840066130f00e8003424001d0080a01a40c617060b01d080c00d05004132045540003d440d408014914420040b110100190381c601c10003628000355005003280540e540c40b101581740540c0f115012445500c1440d1002a40f410041c5600d4486d4a001a6160901c2007a41d20300525004c0e03008190380200c4248004100b954521300103026103e401c05409207890b00d45441071a03940e1f1000000e1001620 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 26452604 1250 26451354 26451361
    0x30209030a1e050105131109010608130c0801020313140a0206090d060605040606110d08070519090b0301080a0201080106181403010e01050a02090f190e06060d02070c0302090708 78
    0x2000202810440e42c410341c61a48011100b4220301100010140074181d0743c01c00c01480b106541d448140c08125001c0e0300710140b142201c805000c8140020310403900050700315400246018081001545480c0c071403064160313020f0f40c0780b40850a9070805d0300d031041c23150343c0e1407118410004a039039404000100e80c030103018a5843c54000a4440c018103030118000c141000400d000c1143c1584003101402c0000d004000c02ea031a80c1c0d00030103c0043c17141c110003921403c6061900140182c0d4840d10400140e51600d1911000011907004c042c204c00028080c03145c103810110740c41c0032000145010f0321040004102580484c00010004101a44400140580d58228041e4006806002c0003910100703107210251a820101181c01000c052038150202e510340414804501c40b281c0040ca1048422561260100070110410030030701941c19441c0b141e205902400c000c101030f12501680e00c004010901f90501e00704005800070b0b6130103c90304072117222541001303004515015180700e07001034603031500020300d02c1d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 26453854 1250 26452604 26452609
    0x11a04020a0207030803131a15190306051914010b0906090a0504020a1223060d03030e0613060f020703020c09040c051203091509030a170d1119030209 66
    0x14110440180255000580750614600801002c00110b41c0285402e0352071402c01c142002c504034280048480d01c4c000040d5140b0304003000c116038060310340041c107140008401c0701048030071030b001c608001802561020010104480d4450948100c2c0008540701c094201ca50709001101c44402c25a43c5500304c50b80180b00c0444040305031014000c00707540d10b540d0390805030002a81580c0c4c99212541c02400040d0407040e0359800812001d00182401b02809441010b0110059250b0780340c00c000c815422200c0000c100e458000241070b0214007034100040c103e18200c42031400c04000301d0f0300300c09040342c0106920400400d0b10942e5415041d0075421800c05034107607802900c1e142040d045900c15401c0704040382c00e001900d0800320080600800b1075110091040300076481c5d0f001003a81c0b40c820644020007078014401c0000701c99484100401400d0340c45141c3d900c0e48807190940541e00e040220a02c00038610f0401403003082d00c010f0403006140c0e120b045824946c513106442020680c10180140f05892854 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 26455104 1250 26453854 26453891
    0xc05041d070314070e01110705030a030804060e0d02060906060a0506070209040c0b040f05040f110f030403020a0f2307060203040b0d110d020306030d03090c090203090109060e061801 80
    0x10140c04503444859260705400301c0c007500b5a0040d0228203401c140030710403c140c01c44020008003c0a0305c820008600c0311032001c1d101c2d07850780b0545402d60003a808c0c410000b80b16005e82c40d4480c1c0718540014510503070b880081d28106040c000113015911820a02150413402c00c803a0390303c8441168088000c90a00c004200e80f03002c0c4500090007000c461b400701702001410502c0da009003071000d60301911113036161044030600c8483e01c1514010b82c500390002c091020311703001e035444000302110140e103403526200300403039140d000500a030114054201a80006110894401441130242100a0800d0142c1d100c5001180c0d0700b00440e2103644c4000c6041040503004400c0c1d0381100c101c1048103894025050003e4040c1c0180c09864080e20000506011400060303806540515402d9048410802030120700380c04560101c840504182400c030030412a20040b41c000b5079011f80d061001140c000c0c403641c0e41c1030035280b81c901d81010b1f5400c12000c00801000544c1e040c0030f0003007400000e01003d0424003a99080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 26456354 1250 26455104 26455139
    0x12010507020c1017040506060a080102030609130305070602130e07030203060102060406050604180605040c050a03080405131d0a030206060102030a081609030218010807092d0b0a0b040302040c0504 86
    0x140b45000b4070f503c6840c080c10458200e11005200c08049140c50700d0405d0700c0704000c8075920700c10f04500101241d00314051090700d109040160403d00c0a07202c45400070507088031070b20110b040043c03c001800000f81e260000e000302c080070340c0a82081a040020f4458404001041101010b1040c410041c42317031ba00088171904550810000202c680318140410003038081d00b0300c2c191650349501060f000f00211640f04520407401071001c184025262410054009a5440003404001041c0800e20840c680354841c810a800340707035400908160519038450700010403038a0b007006500071280310350a054050005d03952000e8240301541ca031412442000d02a19405400c45602c160050948600e05e4000d2501c2d10255800403c0c42c0711407240b43d4041c2613028030900a44125005030302c000a00e8003403900814603904032110200d162040003400b6002c0900001451112041d04d481020b0981e480c1c52040718003909081800d070750b64600b503005000c02d03941d14100c00f00130030404100c100200c1008084407000d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 26457604 1250 26456354 26456359
    0xf0306010e03010f0c020f0d080105010206010603050702071208070501060b03010b07060213030501020708041505030417090f0406141504050a030b041104020a0924120c020304090e060612010507020c 87
    0x880c00c907103002107401040d203481c81d4a43c4a1131708a045034907070b40003d00d648003480c81000f1141c0c0b5600341c1c40111a042001c0c03140c1409a80044018031419021ba00880c0d4007141a104039142d0a507a41105082c2e400b041034281d4450100040c00f1050043c21f0043d800540142104507145514011000b2411702c2180c00283c003542c0e01103036024030300f81e00796800c03001103030454001d40d01d609141c01c140781d643d40581b003409aa00001038600e40b5040c080c2090780d103c0c81c0c0110759410000c032581c24807001036028412040d44007081e0704205107140d0380ea02c101805440b03000c0c5400394160400050101402c0c50840c0c003003807400c0502042001f561040c0c2441c055960004a18959403500d29100307400f580c0070002160712900108900d101242c0c420380e1901200c8a85d920808418582000e51a0154900389a9000290f0758000c001c444122500035110074001481100d00e410b40d00e964900443e0360b4000b0300c59030303a001078007440601c0c507040301410000c5804030000c000380d080451005c0e41c0d850f00505020b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 26458854 1250 26457604 26457617
    0x1506030604020a11060f0906090c030c04050915070206010906080703050d0309260304031e080105010815130203060307080d09030605130219150507050c0d02030715020303010f0b0f030601 82
    0x803a030a128104084480043d1000c84089040c1b03030062100c0990100c0f040442d0740318410000d82c03060310020b00700c8064540940036002016030202408090700009180c01554860409080509680c580741d0340d126254590140c215941000307401801e544040c4d00c0941160700044d402c1c008110701103070414450321907043c0040c40700200d10f88100d281d05c010520804a180b1003061540210305000158462440f941c0d509400c188500c2000c2036841441c8107000008810100610103075004001042d0410100c600c0442c03204813807000680300c00910510041c0d8150040144840c2d42401c1010324050050503000c1c0589030900782c4018400c0c0342610019140640703801c04541c00212f2500d514280350707006080758140305010101068003070b02ea0302c07443c95014245d074034032501c1611a030240d90186a000014040010a0108020001088513402d9906000341000003644031070742204200402c0c12500030f50744942c90050303d15a00801540b02040c0500204a960345507122107045913804507003424180d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 26460104 1250 26458854 26458867
    0x503040e0a060503070f0905010e010e04110301020903030f0711060406020d030b0a050a0b0c060c0f04120204020c01180b060301050412030e16080c09010f060207060f0302090306070f0305150603060402 88
    0x1c001510840c1d0040c2e030140030380d08010074650641030210040c0c684481081c4620399882d50700688000c1d0911841e0841c0810704041030004440011040c09a4801800903040404400c002400c55100303540c40b960001d400074130801004100140309807640720841e030315414a807071320001a441e007514000050805690f8440300c105981d13003004180140101602c4c81020f261913400d600240c0d444032071300711002c1c8a01c40000707042d01c10341000c50706e078551081c2e1035508151030b1030003000480030388840803a40603400303024a4000310000d200e03043c503101414a4052584009051042004001624041c0a0f904140c200808564918824004049146030008011100c5150369003401c40c0100307800345980020b5000a01c1c5d0303e0003e95100102411500d010890b40d0f01c0c0706241003803100707101d250b0140c0c02c028410000b5500400c2c54407031342c5003142005844e048400001030300f0554200e41c42c8012440f4801d0f110002c0340d2511a079944aa56017009400814101c000036205000090003c4d01ca1038000440 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 26461354 1250 26460104 26460121
    0xe0102120c0d091e050118030905010e0120060f07110312090a06060306150506090d020904020a03080403031707030203040c0b0310030c09050a20030c0d0605060a030509190503040e 79
    0x4041501c0e004203940f41c1070004c041401140b000081c80c2500c181d800c20244000103180000c1310303882039900da141c1e40d1140f4900705c01564204514108581480840e1609205034094001040d01586c2624060503503480e1001103030f03034925030103080d80c070402c00c1004252000c0c0700700008559046d8500410200a030760340852044c54041e0748070008103054100040002041035603003045032030782081218901d0482e2030300309100e00d60141441680e481482101000b000d41009034590b0340050016100080b990340326114030000b9405580114001040303030091100b0041c1c0c044d403c9070840801d142c15891030400c1d4544a0784581c1a01514003c05800000704d000404004201d100959003c040c81400c030b84e0300d001020040904a07114503400341009082004040400f00181500380301c0404a419500c44548400898002c842564000c694644012030f0307507580c0c2d40c098501e03500c0c940c2d0007007418900543c1560400724000c224a04508103686088005180881590161405030360303480c2855031002d56 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 26462604 1250 26461354 26461361
    0x102130608010f09090206071e02010201200d051005060406050304050105060607050d0f11010c09080c0307080d05030703090f0b0a11040b070807020301020702040905060406060602070f03020f130f060305010e0102120c0d 96
    0x401005c8c3d8032000d11080481c03900c09e1407050704034001d8008003c1e03000303806441d440c0e01107100e0742ca0048174020450b10341651540c0c0c0c002030304541c89180d00c000c5691214041041c1e0352250700302e4400300710080100800c005c000d02481e40c1c401c4003984c600342401415603407940d0340c00d490072080e0180700301010b1a80010348111804c42c070002a0344000e1094120781600070b002a01c017801400c110f4000c00403800d280f410700160260448a202d00100302400f11200102c4058101601400806444a03111004a050f80ca403014103940521039050070350400c51000400c881c1c0d0b0808030301c40300005020421112021800340c403507440d004007015030b584102e480060700910070348400a61080c541a0004148600090f05a1045100320303020000c0d2602e400d020b070ba03216010b1088502d0054200d000348014141410203d031082c0003c3c00c2c3d1203495080980e10350a44500040c203480b1195546c50820510009001c0d42070300c1c0c0100c000031860b107244880901210701008100e901442d60002d24500008410761 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 26463854 1250 26462604 26462617
    0x90f0b040203011401090b1305120304030203120a0806040b060307121d0105011a18010c02060712120c05031003020103050c07050f010203070801170a15020c0f0102130608010f09090206 81
    0x184110340da50303101c41c040c2198800c004113242c00120380a00c040f40c0026614122048004000c0303100c107110b4942020401031145038032071400240410b00000006803402c02a41e50480342c49402143c55144c100001065030ba40246081d10681c01c0048000c06500d905044070b801c90107500e0400000340300d2010800181c60500c010004010944606450044041d400107058402c207040c8110070488282a0720003602070202c94108000307461150410660048030000255840038113040d041c21401d890300c0441d032101855407000301d00708410311041c076000c1d849804c1c002c90031400e01c0c80c154103004081540b200c1d00743c08000e041c07607a54000b04281e20207075400d4450305603000e001c50b0a01e8846002081c041e4005a84582c0416014000402c0080e01e035003100880408160081190000544450415184910341202043e60810031740a90801c144503400d004c5102ca800580c1d14248524900c41c0a074040d48410f04210307074900184071000c01200000c0031105150804034000005000050740e920038003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 26465104 1250 26463854 26463859
    0xd050627070507050a050f01140103050309040216080a030606080105030d142b0c080a0509030307030b06041707051807020303040f0215041e0e0610120b03062e03020604090f0b 77
    0x210411360801c03800003000241c7c081c60800a200c0c00500703007150410105c0c2070000070a140c02c1840340e00c0c00d07402c00e0350141014000c00e0800f2920b800d0207071075604e40e0768012802c039000680c5502081c42600d800040035070050034147c00824905090f141e0040c00b191051942a55000d80058201c104290210400720f440300c98240c03000b4440c911009180040c6460707088000843c104400082185c00c2070700c24503101d1080c0c0e001561559440480031002040d000144940c850424400032403030009030100707084118a904018034040b0b00b00300030403004002e1007801084810114041041160b40881500e0f00164044800320300724000384001214040e071410b48201c0c8240c007050006014092041401d606103d26410146c0c035038890031085d050301030071a01c89400c000000078069000d4899000000d8074152401c00084910b400740c0040d0a1210645d9000d007079000c18044034034140c42d080000740d0710341074489500c42e8092656012505034065803280d00c07a2580d8560315a4030058290b0413414040b07000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 26466354 1250 26465104 26465113
    0x8180c1c080f04060206060105040b070f06060e1005040506030a0201140a020304150c02040c0306061b050c03070b130e04030801090203040503090409030207080c04050f06040b2101020d05062707050705 88
    0x1032060b01d81681d0003900c102c100500c00d850110780c0d40c0d402002103030243c664071080750b40f60080702d489903041025000c104441c82517480b080060b2041c0c0001c6283d0051403107009100605280004000946601030210340c0b29401c10701c003120050780c0201c60a819100b510541c1a02c0e40c0c035031141641907010341d41c48103596803090a42c3d4800aa84103400f8000c481c0b080317404200c070300d91040c011401c0321254011300010401c085000b1107401c1072400c15001035480303007040390520240b020229040c444113900c0650710f039101241c028807503640d00b290107000c4c044441e070758821340c41c0a440080c246481813040a14207580000400c00b8410140121840120040c205210f041c9040c40c00039605c0e209031041c4c450078020521150f00506d0280560f03806409803030701c1090b0726215102048010039600d10105d0348440040c114040020407041540d044030181d00c00142c03250708000900c002d940c0014090762184050405258041400020804103106441c580300003a0b40e44060555652081d0040602580315 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 26467604 1250 26466354 26466367
    0x100f120e0c09070c15050c070204060e010f0506070302030a050d020c0d020a020306010603020c1b040207150f0506040204051c140313080705040203041e051f090308180c1c08 76
    0x8151076003560a503000c00d041d40e03910302d003210b034000c0c1214020500300c0001d030580a80d916035085250007a40e40ca10b0540b40c800036078006000c583c0e01d644050b043c0380c0c80a004010000c40e00c4d80c488014107080e0381e4070346001004e55009449210f96121042809004154030708007040e03c1d4180c0b0b400c5c0d200f0380200c56502c400c4c040040c0d035500700964100c0c420300c6070070000300780d061103402078a02040c0400000d140c0c0c0c039004080580002c00b0a51000d82240c2d09100083c045014600383c1c0700c9491030700100040e83c2ca8002000001e489008044500450041100304032585504114140724992084414407203031076490001016417101c90710140610000c991100401d031100801000c4410110071100307034591756002e0105030b01007194098a04025203182031118452411a000f03414405d405a80741189802c8410102d2055480c08600301ca9a81d4085810560415600342d009000038840030702c202091000c2c560303107170326032241039004000d8041ea0341e011134000c4403609080d550016060f031b182c60 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 26468854 1250 26467604 26467631
    0x5070f0303020d1d010b120a02092a0705010c020105040f061e050703021201080f03041503020d0501030303021804090b010911070206070302010b10080601050d050903070f0b0a0f0b100f12 82
    0x5144c0e080d148140d500e03084080c0c00a142104000a81c1001180a00f040c642590200541803170000c1c4210701e00007484c1c00b0200171003c0e1f401001000e1152805807030305d07542c40d420300c3c42c01c42e2031b01c1005030103583c076050500000c00e078a52a4a558140c1c000c201255108080c00d15480c80c80300ba0b005110351604220501c40b1990301034014246c2207a4a03400d44190703a0b17a03020460745e600e02c150400c00f07550f0000c0005104d03407032540412035660095814003600d080c1070401e00d5801c541090303006030b00181d4041403003603602000396080348019070102c03020b000496030327501c41028509d410700c1100b40d0340742d8a1090041c0c2a40e50400d440042d0b40080c0100e8485481e403d001c1d002c1c00f45180303100e00c501640100310903640d0040c140c0e01c0c05450103941c1d480c100040e4019010040a01801d4447c3c648018401c103000101c140040ba14810b204909904982c108030b6041401e035858a40d50710701043c02c24824000341d4a941440f40004402442c02c004400c00c1701505070f400e04001d41e6254840703402c0a00801169 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 26470104 1250 26468854 26468891
    0x30c010515040f0612021207080601030c030b09010507020706050d180f120f050702090403090503030d0e010c0203090f09060411070503040f060c050c040c052b0b0f0105070f0303020d 80
    0x1600c1540c0c14420040440c0c07008044500310b01802c01324254540108015040c10410300046080f1f05040f526015107034500c06180042c00d80c01200e0906160b002801004004455140c02003008030090110b410a081c2c042c0d100d00f6a03001c3d02c0200000850128504c080580017119680d601c00e03218a584400d03410107150001c92307040c5c12303240b2040b0602d0f08203502c0d1051540c07044168441d503d81d07081086540c00c100314141c024100303408100c00c2010204580c0d50a100034649040e98001c0015803429928901d0700359280320642c042990014001e07503600b51120003501001100848002c00141e0303c07034001400519400c034009070001030100703669040040000050095403040c11080301304a60350f11048076001400c5000801d160060b070083d200a0030300347c01814402146003001800d1a803050600945580790351150510345e0320740f40501c0c4140c5454401d400c240001a2860327001e030105040060402d102c2c0d0340b00180543d1103100d0443c00d1601c258103407810075a00007424071410b610030b494020f14 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 26471354 1250 26470104 26470141
    0x406090e070f082406030709020406050706050105040b06090d080f030103080406090504050601050910020f060c04031a01030f080a050c030f030601030c080609130501020d05070201060303020708010c0503060f03030c0105 96
    0x202c030304a20214010307400081105400030b071010810014a00420320342d0740118007811840d010300c11403030007003090682c50001d80040c22040c4d44081c2c4640e064180501940c1044c3d0040c2d00952914110403c03030744074a812101c05140c01c1e903040c09030307410601d4108a14071640405030741c06000480088204a000c40082045401660740d59200e940c680c030070001200e40689880780487c604201c4040b56041c50100c20416254500513581148a03c0110380c1c00c0480c111b480e030722039000000703040c010040d202e0481c4c85503400d044065109581942d94011411200b40d00241202c0d1001c034500c40700500c508129240d00c1e81550030f480e100c02010f800c02c0810b810945945001c641090808002d061050407007c0c41020300501498290711003c0e0100210b501050041d03a180d5020001e569207020140240c1d80141e00e1540009500c0d851404d0090800740c5540000b140b030307410b00c50801a451780c0202600d800c03400440381500e1010800d00002e00c1c500c1a44054521542007008101e0038002110000e9103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 26472604 1250 26471354 26471369
    0x1704080919060503070e010507020409061e0615030207021f0201050703050a05041703150604030f020405070203120402010305060d060f0b010e010c03080c0a0306050306040510140402011b020406090e07 88
    0x18052208003041c445440e18040c42c80010014800108118070440340c2100d0fa0006051061401c0c0b129000f003019200801030a4a00030384a1001d55442501c04d54171550140710300004101d000d0030039810207015855030001104054000c1030035825541c0d210000355900c402a461488808003002029001e00421505140464604000900d441c0c100b8010359100f1548401031201e420790704442d0000941014110000004210301a4017040d112140140302440c0a55500c4243c000a8410482a604002c01044c119041406940d100b8021a1040c9400980c2424081410b13601c0340082009a40d5605006d4116418003801c040380b12021b510440043c02c082e81c9135102d1451000041d60f214031407500c001c0c00218440300080810007200058249580e00346000324a0326520800030b440d25030305540c2035130b540c0c110905040c45058603104200e0178603080314107100b0902e856000641801c0d01140c0d40501d1214401c41d0004555032a0711590203808540000c110400b000000c80c2c0d92002a40184603 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 26473854 1250 26472604 26472619
    0x210c0f0a0b060a05030a0201080703060506070303020c0d17010306050702010b040207060b010906050412080c0c031e0c0d0b0c0d141315090c0b07050c0d060c17150607020117040809 79
    0x102c8504002c0031800650707a000c2d009000c24102a0300440702c0f24002002c40d002c05a07504d0011405a50701e50040034014026500943c5890401c5e00080c28948658042c10903c80031408808040003044a43c60440c2e401c10340000d0765541d00f13081a070140441422a0f80c0c070a1001601c0e8003003107a0351307100500d05034080c0c0c0c40d442402e48903001990681718502030501030512141014000800762002001000780c4402511187e11610700880d10304003810420301c5151600959100d0648410801c001403080c0031070344200e5100c420b032212641c0b1080506284003103680001c1040039810207400c0f01c424164850b9040b941880c05504405028030308030821030303140c1c0400180322240c2d41ca034052000c40d1a048580954420300e04602019254407640c804c0340d240c000c4008035185550755800d110300083c09810040384068400200a0a184560720320029221804050050703d40d082c1c008807201001c00da907003035591b00341400180d610003803030ba18451a84100200700420820204040d0000e501b0a55410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 26475104 1250 26473854 26473861
    0xe07030605010206151c0302030406080a0204030f0b041112030310090902030c04090221060105120109050d0518060c1e0316020907050d050f01050f010f02210c0f0a0b 73
    0x11015a40c052003030070b00507480040400e82a0422400501c400c40c801040c1c991102c0c2c0145208820390110b880c1540507800c0440c04002c003580060400343c1c4a10129011450705003160355101d46101d51904c09001d40d200d440001d010001080404001410010102d00c2000035140140c0d030b03641c0c4111000c604a005441d00000ca86640b4003a14040c4c0d5401005044c54800e20024000100551390050360f00110084002c60741c8081e440d042e00d1001d550030701030205581480c0034884c031401d40ba180c0e1107107a071601851b5004034501140c420755101d914900540d40d1a8056050002100d07811070711980800c002a00080c090000581460f40c1c0301241030046801c040040000d44a0149205000c0e0000d603588204005180101c0c800e5884086403c0c824142072100d1524001c83c0e90440e01c181107064950018440c3d407802c00035120001c0f200b4a4020307011001107400a49600c0011084007503124a80140c0c510302c480320051300c0313040311110210b902102d030300d543d050350b40c1c40e170b41d00305445001c14a800f1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 26476354 1250 26475104 26475107
    0x30503070314041e033f02011404050102040f0b07080304060507030609020a03060e0f0c07080304030c0614090616090605090a030609030512060a03030801030b0703060e010b040807090c09030f0609020306010f0e07 93
    0x22091180f461041052454903442d0581b0500401da005d001155a0381802c2e0030920a0848428040c0340504001038403503050502d85034640702d0b150071040c810441070101d40300142a03a0116035005606c0400421241c8803110160090f0a0344d07041f081a5500126071150710641c50341c02101160f6001c99035103015280d14000d030768a11400c0e55a0802000c0400508003c103580e03800071034201c0d00c6071810508010f1251145402c50702e00c02c4000c007042c1818400e02814880070822107400140c081907410404a6104014207016041c0c41020144080810203003403d940c0c200b1008011504901c007032200e05401c2c513008000b94400640341000e40740910205100303080441500c0103903607064581103640e0b400c5844401250700b0040100c410075444440100ba2009101c0c241c60007082d58100c02030f110350500c4403150a045440d0811108a40b401d884510840d40c0002c6c50710449400c04910b143c881c1d82801d104015214001000c0c1d01841074800001e4001c04040c5600111000713008110026140c4500 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 26477604 1250 26476354 26476403
    0x7080303190501120807030c11090c0307020c030c01020c010309150504110901090b0904031b0f0c18020306030a080306010207080f060610020a05060a050c04030204060e070f09030503070314041e03 86
    0x2000d441008184401800030303019801440240d03000798105038609c0300142c0081d9000c0700859203018031407408014010340d107404010400342c50101b01c01a0501a85410000f5030707480d103460b0001c4c1019281d01e260424801c1f40c001c100101d001644044c0442d103042d0800c801069a0409058020b81c407800c00040d500a4511644c8a0603000400c4800e4988036600c04807035810302c0d003030b0340340c0320006c03142010000591264100442c00e00c00d40010ba1020b2802100380b50740055070030094001401081041001d40c1c000c95440c8034964008100d503106c0d10780c240100c0c075051440d04046558459040d01c1d418407000014010320450b8222441c09030005010b030100e8032803014950041080d40308402041885035160096544a9442c02da01e078201a43d82d00000c040e21002e900071046c19a10000303014007503501c80789212812016041584a031803840d44d03510365034411882c024003000300b00300100301c00100e07200131100103190b00d089030301000c00d080d4142c00d21500144400ca410b090301d030400c03507078007004800f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 26478854 1250 26477604 26477639
    0xc0901170403050706021e0a08040b060a050d12030902060c060906101508071e05070b0603150f040303060e2805090c13090206030106081902040e070e0307080303190501 74
    0x20340f07a605001040e95110040e41005000f4100c401000c0004050282e418001e0070380200982d8403844541401e04004103e008050402800760403001d07c2403255850740e03070700e555000b43c1c4480a40440201c101e021001010240d0009502c00c40c0044da40844842c001002401481454140d8085403501d0101c07206011441c0b1a00102c1ca41640c1070400700e600601c003040e44000c290070712400024a02e0b240006980c1001c00c4c0a0110704085030318002e100c54440c40036070004055009041c500320b201340801d40c18070002c16551003246d42c0d01c0000e04040c441d070058002090344480d165a2401e00801b42400709808580302c541c0c60031000200806441c0d90b0107404c2c01921501d001e807403a440148103002c21025801410750001da19200d81d04e0058075140c0055000341210360312040c1070708040d41d20311007503961002210410b500601c020710002a1420007203401c62483d0602001c51744000340401d080080c80c0e440440c0901001c000c00c10111b195040890765650364420420031682c84000c01c034070310015076 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 26480104 1250 26478854 26478857
    0x6020d09060e0f030303010603061e050d0209041b12020910051528030516050f040902031e15120f030a111006090902040507020109151d01050c0901170403 68
    0x84400c01450b409681074646059024040b03d104507411004a440c5500070707801200040d036590300411a84c15980d109001c40c03004424001c203041d1402c2c001410803500708a0103481503070b5840100c0c0c20042130810146840c908c044c1d0743e04009540c0ca0240c14103101054040c4d00807246030000444000c44481c029050743c000800254900300c040400901c190010500448a0345101004c5500220616402140c20085580124252030403010b201c4100211404001c18020b052002c1110360380068151070030341e000c00e9001a2203540f400c140188520781c1c55120740806482d0744c10300c403080144030384000102030242c0300b41245074440f1580c0f5649000f440000c44e00c5800c24003441c030540d84503810301c00c000c0c91554100c6404c0c1600106070402c8552503400461503680d40c074499001c5003054020164019000d00082040105a482e07044450380e05407010032085540741640c904c80304040c0d00c2c1d10081c12510008201c0d510703103410380f071040b50300034140d0a02185c01c5030040c1c14586480d000383c502c9551325 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 26481354 1250 26480104 26480117
    0xc090509061801090206030a050106090506030c16062a0e0d020303040302040f2307020607050c1c1206030c1d06010c0816140d08150307050d08120f0702010606020d 72
    0x4030100c40c0082e034403003510102903548840e0070344050b0f61007101450041610201c0000d40f035161650244c41e02d605940054090401402040741911a0780180d0308100042c0c6052465429030349080c000510115085022818100c007505d005551103040501070040e054591850b8119000b007004481c43c2d00310002541a40104400c0c0014102a0130091004a007200e01003a00c40c0e5028924030558442e070071040d0790340300c0c0c4802c0103c0c4507410041903400129a0405500d05400402c1c0d0b44c0d202d1109091544001040402c031600052040b100e1020b0203594a104000322922407074494806401d9120300f80345886200c3c104402d210040c40c81c1c6004a4058442034130750303040399683c0d581075084404802440d1592350215004549400d0039005520003002c090411100041405070403174401419900c48482049140092520001190f000f6240d040301d042c04540c00034501039500c1c1c401c2e101031071104225081030013a4072002a010341d00502e410780090001c0c2c2e8895000720b90300c000b0034a0500000d003a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 26482604 1250 26481354 26481361
    0x40b09040f020c0a020f0a030501020406111c0f050304020307090e0f010f05100302090a0209030318040c09030507300317090c0d08090d0203010e030d0c180603050c0d060b070c09050906 81
    0xa00860740040e00c48040d2187e0195940c0b03440d030710f0032030704590b00c00000b04005110004603018107000d40800d180641c3da5810503a14500c600410103065481110203014000002c00c00b50340c0c003085400700429003080184070304070007840d510b0f40310840b900c9918450343c03c1441610280c00305008041c0f10707408202d9205085803564003045805d8002501c4c60800c2ea501300018442500e00303100500840c494030361042c48200b5880148402c44098180700020046040c8040c8005100483c0300400c0f0344801c0d08140e0402c0740c4100c1c0300d501740302c03c000e4210015095200798003050303008128400442e070003203000d004a680706884281c9521060407444c1c2e000d5420580900043c4112000e89810710f806020500e4601090307020070f003111030598034503d690384041a80a60a0b11f86d0040c00072481c0317985007481c0b0f00d19003080825211a100c0c06040140f43d00c900016059001900c16201313041031543c000d015241e5030740b6001842c1d070710004080c0e03414003541d900440e00c1d800c2c5019060141c148a40284100e03034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 26483854 1250 26482604 26482609
    0x80408121801050406020307120b01020c060f0424020601080706080105041e05040b01080c060414090603010b031603030210020703020307020909100906050105040c0c030f0809030708040b09040f020c0a02 89
    0x40000340701941c8020703080d03040306809609100d5144198450f21700140d80c2d00304043c000c0c023205a4090386903801400c000d4014205c0c1d9002c688007084a10544009803910000000c201060241d50004903103c3c140903e104040754218000c003c180000350280c3d83d103a40c03141100d5858150f540580340c0854201c0700108180e0520f42c1c0f050f0340a00d500c52108400d2101b590004007664810b48094a20b54685c60050090030810301070050590812107280c0e02d484c3c40d145401103400880ba840e1481a114400003500070344080d0400503c2200003002d5914039191990074040c100c40350300096006200314201e68131200ca142c401c403441103406400850038840d141d07080004c081001003100210b401b408413100600038a0703005520880e440342a0104056041c60240011109410311520420025201a0021940019401c4074010207407820060f90703915083d60518603c43d20000901c13019000500043c0031403108042e040480381101c0c180300d0200045130160a80c0607068822903150804540e110051 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 26485104 1250 26483854 26483887
    0x4060e0c0a0c0c060c02030c0a051503090709060b0d06090b01080a0c0207050a0603060303031401051f0c02030303070804020103050f010e01090c0908030403060606080a02030f0a05150a06030e0706080408 89
    0x124890b24000d00c030408540d40791032100d2282d42c080c2c00811084c1c00081d04500c2c041c040b00780000800c0c0d80180c0d550307180c00f00003104116005a011985c02d00000030907640c240234032054020b4041040107010f02a030386c090039503103907000303810340d070812454000d0203d00c100e07031401010703007050050b5104c58003074880d02055002898101e4811040d4490440c0c0000c064444ca2000300081620703031000507146103142409803d0307032040010203002103c80e000500140d503c01010000b01c00c0c0c15240700120b020312510a482240071444040e42c103110110402c0601c0d5840100188107502c01e0742c003400151107082c043d00c490002801001c14030b41c0140014001000f40b980011207052103032902048959540260500755032051300140c5800c1e495400a1200c180c10022054204070600c10441c80c1d443c00c055694005000940134421254a603400f24084101c4e0000300c18691000800d0303a0046a42d400c00078004180d40345009015015410703000400038040d80e0841c1c07146420031042840d0011400011500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 26486354 1250 26485104 26485117
    0x10050105030403050c1c020c0307081614010203040905010e01030c0504050603150a0603150515120d03090c170f120a0225081203070e04020405010203120414030a0c020f04060e0c 78
    0x601c5000d1030080008848943d21b010002c0781e401400b40708102d4010b050400c42a40c001c9240759202c400c0d0500c604021648400c200c0700845003020b038800c0c5800040341144100d5105400c5030341441c0020a1035000b10007050304880c442c60940c40607664640c18070050b1982104e5095058102490300c4c070b5019281140d20361700880446000820a80300ea9401c031105010034601580c1070f42c4d9004200d0503c40c01c02040d4080300302201c00d00c40b890b4418070520794809814401c00101030b00e500c2036408111282c003402002d8051201b5034002800801c04941d900e10340c08410303109030300c00c6003c03007070711210048101da00b00c04580d4090483d00030081c009400088800083c1032031030341603043c0000c03203031002e01050300c806a01c5102c4170341d64108440b0042c010443e0900292080c1d20400040007a6a00042100d4070302c098440704450598890070701105801e0794107220030250000140299009a202d403803106140d200300c446007080c0340141c05110484600780100c0d90806030031004105500000c2019244 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 26487604 1250 26486354 26486377
    0x30605150a03050604021615061a0307030c0207150c02010e010f0903020402030414010504031701060509090117010e0708010b0a0e0f0403140c1605030f0114070c0203030d1407081005010503040305 86
    0x80c1c210900c1447d244a440c0c01e10a84030415804400d842d50441d9010744402024080e110f10200740c1c1c240116416840040c080d141815540c040001640f4000d10481c8018100074801d01e80300703080c001d0702400006114204900262a443c00f0017030643c01171002d42c001200c203503221101d00341550f090000940c0b01900035aa005021100420003500900856118620135030343d6800c44640c80b41c0f29180707090b041e086030b000e00400b40141d9126480f103041c5641103800c080a01a56505101d03240c9004280445c5940c0690189403008940c4880540000c569a01c054400e040d40c1690b038404004544000d541e8400e181c126003020402282c820000032000c03000c09020b0381e00d071154a2080514010b016555840351200c0030300100114a030a000c0c40700301d00300c844028444243c003070001000d0b03008002d180c0c0007801b05507188102036440800030b0703c008030b01000c001c00070401403400340000d0800c126040340015140b4000109641d89000c0c18004071901a10b885044d0b803101e0307400740c6450300312000514 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 26488854 1250 26487604 26487607
    0x90303151201150f0602060121030309020a0b0c0d020105040206070b1f14010801080604020a0302011110021c051803070b0c070501020d0504030f05090f09040203070b030a060501030605150a0305060402 88
    0x650140c428481c1c19909407000c40e86a03d030500e000319260240100c1d030b104405540000004003c48047c61800345510780d1850000700020002d494103400800503400041d4114030940408a0032402c0c0703400412211440508442c03031000c6031441282a5402240c00035086134007403041200242080040300d4202c010410030056500a0030046621901641c1c0030a018a8515404190b1940c0100c085405132000030702030011440d090300801c14500a610000781001150130f4a5905540203101c0380325001f442c01d40c159038641078200820008194004140038491401012031042003200b00c4155581521901542c10041291192160420002c1480c0c070040003c000d00400a50284020040d00b000340c6800a00c5060506000301003140080c820001d000c5d0422104002e55070301107050907003040480b03250701c60b5643c2d0b10220b8105850350b400071058203800b106200742c1e0540d0790031a8040c1c860030798040242c00d640c1c20401c88440603480041214400401415416912079040301d5400b030030181025 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 26490104 1250 26488854 26488879
    0x2060c0304120503071101050304020f0f0303090d06090501050601050703020a0809040f091208070801080a0807020f06040e04050c060a0e010507030c0203030f1e090603010b030a090b0c0a031409030315 88
    0x20a82e080a0b0072079464000007030950070407a5890900303210040a29103a03080d490140c0c0030410b410380301010988108138213907419401d980d0030800c41c0e92410014003c643ca400c000d00d81070000d000401811101c1d5400c05000034100c0d40304505542c0019019802014441c209454030780c840d50101c1c49070354009450303c08410b8401a40d0213440d402c1841207041441181688500070501d00c0f025051408114041004020407807000810f024480d030400d03181c07651503650b84009405107403141c001c40d4004c40d0208000a86d0a4140d041c7d621490290058800310940a01000010f22560004401064038000d140c2c034554855030191009500c60304210f40c50800700d0f00003070300c4c540091000c000c0c074800001d2100800450071907110b00448031110303640d0910114000080650105000e0401c0740d640110010743d5891441d00a035282e1a0440030000d418240000c2411030f40d40407414010210381000c201d01801c04091900f648030340044006903041d40ca603411005400e13101c190140d036000c0e8406414 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 26491354 1250 26490104 26490119
    0x603010b040315060602071e030213060302010f0305060d12021510060906050f04120812010b0306010e03161a070c08030c0708070e070804020a121208101202060c0304 73
    0x4501800103945410345a9207545030240e40c00801182600d9607500b080803c100003a00000c41c1d03406c1d11109003808489801d03000e20840350702a01d0344041d50080700500c00c003100d8140e66000d00300b035a000f03984071075181c2003040082d0103a850a40d89140c0010301c090000c00810105013032002c19030b0b0984180ca850f031403001d011512000c400e641d20812003c861504001840d000100350300101000e04100f070400d102d10341c0c159000d00491041c84e01c2c0106981c0204108084c040403115024110f44110202d5615102c6041042e00115030140c0418090580c0b8070480c07800189510085100c1c1e0b01c43ca00380343c20203800a02d00a450016014156024010b10700001e840d00d0420000c3e2030007500958503102d101c58190714000310341d8401030307058201c81001d00030300c19241034060340030815041102c03c0c1e840d13910214080c202d03181e01156070b0448142e4000e0404c945030709511a1459283d4988586481e0758402d56400011841039046040380301d80030000506000000e00703a125031f460b0a480c2070950b210325 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 26492604 1250 26491354 26491357
    0x10909020a200a02090a02090d0f0606050a0b0301030b18101805060c0705030a0503041a010b070605091603020103110408061017120a03090501061a070507140603040201050c0c06 78
    0x156001048079541000410040912505001550309004000f0302e48541c000c11203000c40905850341c000d03000100c01419440d40748408481592102103001d0440160601200a185078010940b00c0d690301100016546e00e032005030b80c16640c20000340b4415031601c61168002c00343c80586480d040c01190000d084d15143ca2103031100303021800c8001d044010f11854110f091640c01045100e8074a002d010000224400000381c42864116040c801d40e2a15a4180170000416003d444101785001500103e400440080503140540c4140c02c00d100319251156419140c0300201d4021040c00c90741103041025602c2500440c0235002c0e40b4001a01e420388480055080040444180d030404000120400c0382100201008058001060242c0311070080c1c3e4021840b00e01c50f9801c00b104250b182c061100c02d01400303600a83c0104105583c800303491360410156240ca81000805450501075090000b506200703034500f00003119802030030305245507603660054596401400b00704895215a94035075a072a12003c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 26493854 1250 26492604 26492617
    0x30a09061e050f0708070c110d0c0e06030703260403020604080a2108071115091b04090b070c080403050a1b050d0312050a0209040207150608060403090b070201090902 73
    0x1815580442a40040303000740c4401522540d2504240f0040213040c5030b01110680d004500351030803080280c2035041100384068100c1c441c903800340441d0303459010400c40c2a0888100c030880840c207400d9545660400d41c980341e01e844003414058512401e9205481400780106034041c46010050405403242c020801e0b50b00143c020403541e512007481300c010701203080544925400481400c0c0c5645509200060003503e011300f10200303000c1e04030811008082c0c00d100000c8525168412540c003450b051404543e10342d51800c14003503d41c0a540341c01580d0805015240d01190803410f10b04803505c0c2c860040302c0340305038003000340ea501e4001c1c840840000c0c0709100b100a0503010300300080c111010285c8c2c41c91001c0c042d500542c402c50400314000e0001c4d42180c404912944402800201c1e50344520b10100613200340d280f17003940144001050030811442c5c54072001108090ba50411015407546091079444605880203000706403103040030407209600320000c148103403040c90f00d1302c10300e5650340300c141c01d17600004c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 26495104 1250 26493854 26493881
    0x1012050a060317070303061a07060902120105090705010809072405090a0303030902010905041803080c1e0403060501060206010501120b01120203040303021b03031608040609020d0b040501050c0915030a0906 90
    0x510b0704e060541c10b015000240485400b80e00c018070000203020385d94822600300401d642d0711016480c0c10f65031218107030006501988003c6c007640c98030583c41c42d255a25030040c180484c1000010900020703002650f00280c40d08041d000c8500c070750240d1400c0281c081880a8001c0107010040304c90581c59048001c001184262404212070312540300141c450305883e00103900440c50062101208241d00c080121031a0b0107051002090f280d0028041e820b1207005031038508541000c0f4811081003914005004480c007900d01000540d03200c40f412612104280319860000350618000c02100c2c0f1030b03602012482e18141090100445c030301450b14143d03002154283c01090b40460b60f5a00e006d8103400240411245402461840c6803040b8500001112041040c0030882d410000900704282c50703000046c142c0d0010f112040e0b144003460501071a1204440c1103405d0350030709021840e13540d00c10080c0d4000c0b50005010f61004040011301200391f40005189a0030151505810008140244505c1c240704001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 26496354 1250 26495104 26495107
    0x1207030f03050a09240b03030a02210306010207051908070b0a11010903021e010204080303090a050d020c0102060a0903030f050c0a0e06032a0708030a02030f061012050a060317 77
    0x640000307001c03900d0050060440c0d03814031800b0800a11720603070807054107520788110381540d1201a0b0000040036400340b01509440001895401280c0016040d49403440303401c03c0d43c03840e0300c00080034500b0b408151480350159100810902c42d600e410b00b5030b62410070b0340820103e04541c1c0c80c0c106610700b0030650b200344509640045e0905074598441e04402c00b85489200910000d0a55500250748002c0040f03012103a81260800c02000003084d01154010180101240d4071717420101340103034071407082d45000c68042c4955011440707a18008102000171450507000b078070450340d0345070034003018100e106011410155100c1080302c200c2550311071940180e01e140c0549482e201103410203004d030f6440005203489a8014810030018031540d022401401540d01e9215064101e0540000081c1c02030300c41c000c0265102004220701200305501451180b542c04a5400700e50301c8003420b020003000503980746000180361400404079040250020380e04501481c200068a65403a200c070500301a60b1100b507000f100b030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 26497604 1250 26496354 26496377
    0x6030a08030103031d0d0b16030905100501060917100902010c0506040b0601030f02040f17011413050606040204060203070b060a08030406020304081b010f0e040f02030a090506010e10060e03120703 86
    0x803145e103400096004e40d0406290300003601c4c0c144c1c640c24000c00c2211444034191411110302c1c8641c1022464a83c410101d500c3c4408044c4014043c00c0c1c01d0040710300040c07520000045a1013440060000401d4000c050212510350702d001e1005000207007810f9041c406007038200000510304000151013180243c1c1e0046860511034001019180c014124000403401400144010311034404194100c0d5008031603612020000e00900c0c1c0580218100342980c446244100702d90100358070195402c441c801c0090740c400d40d940c501040124040c6004880042c0e000b4001240001d4000d1201e9802880060100d01515660701c1010702c1c40e403103600002c005030400700301000141d0b4204521054060b102410420100320140000c010681510001c001c10204000903502625140c0c001c8252100258096549107801810f26024040401e0121040d101d10000050b00042440455008240e5508180a018602001101c0300340c0c02081041e454080c8281c0e0120004a20009249032440b03900ea40c2c40030711 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 26498854 1250 26497604 26497637
    0x80a0c06051501020d08131208150a030c03060506030703020306070201020703030e0106051c1b0f0806060102011104150302040b070f050d020c0a0e180a06050108010b0111070303050306030a0803010303 88
    0xc002a1480c00e2074018209464070b00d80c1c000c0380e09100b80f00780e40340140e41070769892030b0309880000b03103078001d03142c60303022591106600c2d40503180c58031889144d0500c200c040814410b01041b004079210181c0361201c0744900384001543c0c0d410180c0c01860042c1201c04450b2a500003d04010090303d031480940c0d400514a010160180503c0b9401c02c51f103c001c10105c0c1c501400710b58904441c03583c5802d00855041d00200304860070741c00d0307a107c0700ca0012042d441922500001c41d54003140c0203103030161103810009601917205015a24807109065141c0c0c1c20a85890a40407042c0301c051010400e054080c800499481451000b62000e03501a104040c0401c4c007900b0100c7c2080c20214165046400003154541a03440e0700c04180c0c100d800d1810400c01980d109604800004292000c452550003142e040e10700380109900058181c4e11141c008000c00452840103651103d1010b802c1085a0450b000400100c0c0c0964095644000040c080c3d07480c11000e980c4244441c3e00907001140031990207805003c118 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 26500104 1250 26498854 26498861
    0xe01022a0f0402070c0509040309030f08030106110607020a12090503030d0b0a05100206060607020a0305060a0f0e01021305060c1203010b07031202030402010509040506031f02041502010204050901060e010c080a0c06 94
    0x1080c042e82c08514003811521000d08014003070103014041c03581e543c04102014840d20f1540015074002541f846c00d0001807400346a0f0358000c0c0320307041c0001c286a1f03c1642e0460b0108a45025004940040400070495070340c0d285410f201005010030b000c072100c400112a02c0c02d000400019411a800240703c040c02c0081141c2049244c10640c040e56030b0800144001d50001100794001c40121000c580710a02840050001c84480d003004009000d0401030004036280c58002d0320220b8202030003800306c460301d0b0002030b080340a2091140054200c10400304000d092200042427080030107401c1e41e400b140c0421107224560300070307400780d10b41400c009084002e069019001c030403039101e818025448c50034a0b8000034100d0044d800031620899544010589581d020400b004c0c44840002a04604802c400b5800000350802d10511400b0803030305480c0c00900b80f0600c215820b0b107200400b01459039003440c808941740c0c80210f4020341403040e544c0c1c07400c0200d085079001c1e2081c3d080944c1e811184100500d00078069 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 26501354 1250 26500104 26500129
    0x30115050301050a0303030b13020f03040c05040506060d050901061710180c050405070c05010e030a08090316140307020a090b030d030e10020c16090e16030c060e01022a 74
    0x20003030140014080c0e0b903510f110100889803d8540070030b06030000c00c006061400d0f20301140091603c005488803036000128051403041d4050550052000e9442c011f0100740c807421914150b0080c03003000816503004050340260b03001000c0900004a041c1c4800340d0b500412020210200158051200c41c030100415010341511001001090010b410150b50758040d0f080460040902c1a6260800566a1480381d4900d5203950f412000034840101d0385c401d440e4696200950400000c0c0c6502c00260a1000010031548a01503040d0007490460396511042c440c10075120741d413075050000308a4040580d0300c00d04400003603c030480303002940c2c07500c0d14205407900041c3e0603083c0505003418250b054009001c0388a40506030103100140c0d0311951410b09500742004600440300e0000042000b04032464640e006d280180d0307802c421101181c1100d0f00d203241520343c91000038a1b000d0003440a00c4810300c40d4124190340c1c0e0042c01200c2c0c952601040d0101d21003a1042c0d02400600c1e2501100e031030b4608880d60100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 26502604 1250 26501354 26501357
    0x91118040c0f05090601050703030207052505030105060306040204180b0403030f0507022a010903020a090209040c1806030b010c050607020c040506040c020c19030206030106050406020d09080a3203030115 89
    0x226070f4608000b24100c0e040040c006810300401043c0300003898081c1d011140c01303070762103029907014280318030035001800c40307410038080e60507402d12000c5990f007014880c0c0350107940c00800501c0d840d6655400c1001610000c4c0c050308081c014a50001c1c001400300000d80c1c011031203514042110a4007404c4001152001081303e821588a41d2030500035203100740d41410021170f620640c042c609102c90041e44c0282041c0d1009400c01d41860001a221500d913001d001070350001c64060100964690049500c2901040450146520301c402041501e00035403001250070340605181c08500003030388542d8103084046a460340940c1000480c0f000c64a05441780a038804402c0750704000c0003c6c5400000c2d076641c051148140100d0b8040c1542031840c3c80c10490350005e5034020f017441d41d40c0da1215002800c0e6013080c428074016101e88141e0b02d866900680c603003420340348600020444035405898403500c0e440d6030901003019215094680c0c0c82410405850448885a500190750b01d5251142c0b010006450380320600 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 26503854 1250 26502604 26502629
    0x21005010605030412020304050a0909020307051503010b070c0e16080124081807030f0c0b040e06040917161104230702010e0601030f110904030210091118040c 70
    0x51550001c041d20f8115412845c0041080802ea1060307141d07218680000f580034640d402c1c000b41426540e00b0002e0503500c00e400391080c0942d151309116001e5554482d0b0603070444240018020001c1c0500a03290040c000c0200701c10ba15070704d20018080000c02d88a03001c440841d60258500c0581020465004192034070003154004403140d00e42154040241030f09040009400204010700b8490540c5503030b02c2c6814064503540c0f80e4a01c1e200d00b410380c0340c101c21516941840b5000030585401019982110004140540c0640d01c8108202c014000a0007c036030303c212811807a0304104800300604143c69401036448280c100c1410509058003999440c14440c5040c40d0703a0000b0080c120400d8003601c003c00c0d400003500d0311009403c0c1d014002c501081d107800e108034000042440103441d03c105055000b4a510000d030f200c6481888410b5800f140c0c0034015a001c440f02e84994106607019171040d074040c070b54907071514031031800042d00c150b035042101007042442828442440313642800000144000c1d038050 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 26505104 1250 26503854 26503859
    0x618060b0a03021f030e19050f03070f0807150609050907050402070c06030903090306020f0a030b04090308010308090105130f0e100f030809150307020714030c0603040206130b07030309020102100501 87
    0xf8070380030031440c00751340c10510b900c1305441980c000c0c0c00200f5a070785000d00380e4000301940d040340321200350b01c000d00343c842e48502050383e400b0050100444500b550481c1381e0200e440c200351aa4001907000384022100a07a40e681501c010b030801e40308040c09010b0601c0007040504220760001c0c134250560b0401031003a84108110b10004480e2000380088842c1e030304001c076040c92a0709041c1e400d103220360f1000d01500d00000e248005c3e402000300401d102500c6031000c10200b1401270030b1004070b0f6055a4010003168200c0014004112258003610003580305260003443c10514101c1032000e050703c0d9000f074083c06880c24050000d04416083c0f540d02c43c11300d0f9a20f80b181403419240e00c00394852340c8000350603103100003400403154407000e8240c102e110000804c2980e07400c20360303402551605144603c610b002c041c0d6007a20018a03000c9484806100000c1110342103458640801070b0a511401201c0404a4107100000d5000300c004040d240a0f8002c1d140050034108500019062404640d00402c0592401006 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 26506354 1250 26505104 26505109
    0xc0e0105030a0b030111070501020301090c0f201c0203190c051005060402190206090c010201050114040b130501080304090605030705060d0507020f1b040608060f07050a0306030618060b0a0302 84
    0x140c942c01400924080380382c61564011074018401d00b02421000c0030006444010b12a05400460407a20a140700708442c403803000e404c40e081d00c92140c060340002c2c41d003003502042d8109031261080038182007055406044a02d401c1300c0c4105810083c03c409a00041400f251000300b25100018084590400541902ea10758a00340c6541d44a00c0d00440702e0703982c2c0041f0340680c5480d81503a0b150354a001c10f6062000c10420080d507100c00451b03001c02588203c00e10b00f02194418003e10303040b00c4541d81000c203054071080800002d004071840c060f42010098900c210340f8000d80c021a8000d2080c00c000d1a95682803050300002d0b01d0058008034006c0c0c2c030007101000316440300030403690083d807040000541901c8000c0202d0400350101030b01011803094507204020590490080194030b101101d0402110340d941c2c95054803030b9405c950105002d1a0f400c002030905004400800c1c0e4084185800210f25032a40d039a00c017281c408074030343c0032032068038040b15040050720312486400d00002c0f04c034401040d146600 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 26507604 1250 26506354 26506357
    0x7050607050705060c0102070c030b240603011a0708030a2004080a02010509040b090106031b0318020f120106080d14030f010504020d0902030601080303061c05030301050603150301020310090c0e0105 87
    0x142d04d000b9100060507046081c030030350590304200d81c0044400c50a581c0e90401030440d003000d4601c0400c2c1d0031403da0a00c40f000400c08143e130780004c003030300d03da085a00e0030910000000404450b179243c00f508029420014005500079031141248080009a00301000100d008124255a201e1606081080103001510001030201c41050382447e159984407c042c0105014002020400b1b0300005c1800000c520710703815420200c6c60216030b640c90542811080f00450076680d20071200301d00040000001c00144c1407842e400c803c0d05030003a103610003280414110324212a0964000d403516041058400250355014142c403000d000150034481c2141030076445075011403810b10a480c4141da0016040000d00c4058008280558004081d180b507980e454458540340c2e40202d46451140d910a00415040d010060541b640c1642008c0103500f16820076081c0040d46d440a014101100c40c2c034112040540d6090005622030119808580c09a40c038242c02d100a03a22001e4488052100c044e80d00402a43e2010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 26508854 1250 26507604 26507609
    0x30907060206090607090b0d02040801021b01050a1503020f152701050301080d030504050f030d09060f060b03070507061508030703030501090513020f0a030c0b0304050f06060f01030207050c09090f070506070507 92
    0x47c58590703030080e8201c002c0c000c2c800d40d40804000c2d4008140c81c03803000407103460800002c801400a1186036208005502180c00c1500a4903140c04003010500150401c8500603950302405804080c611001d001c65035403541211f010650780000d038002024503c0c1c1182200e03015500c0a080076400c65041c00b060b60780304d80e0700030000030070599120002024000b00308103002036200718209807961080c100002e600a0300411400f900c4242c203180117100140d1b0940b10705403c40e40443d014605603140c0080880c4c182d0f003c008190f80f03590b240c80d6a198600c03080003104000f01900402950f90704003034074001d810760744140c3c00305034075030f19260800400c482400505034071140d04407114848891684001204030940b6080030340100417220b408140707241010010b50107207000301c04031101c40e0108004669603450031541103030800d000f26010121540a0380207803c03403c1c0700f402500c010020841c00706001d07140490340380f55640e00c04480c0c102000c105200100290005a440500d405450b8498581c0da14079032 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 26510104 1250 26508854 26508869
    0x122e0e07090308040f080705030d02151503100b01080901092001030906020309030301030302120403020a05090c09030a03030c030b0102010513080715050403030b04060b09010c0b0a090803090706020609060709 91
    0x440004240e40d1040301850091036001d4903071901e8a4544c00c007500c4d01c030b40d540100c02c0710340324500022070149000940b200c5440e00d6a401000d2911040d04078010f825406013015038603c080308110742c07a035902030020103055205140c00040052080c030005040d640d001d065640a42d01d4140309074007084144031b2200d54401c1e0740190030a907005910040f80105580403001c0c2c110b51000c02032040d01c10f0080010750481c0d00950881d801142110440c485500c1548002503014480c0b01041109062844116a200510074406070400c0310000202c1e04014040c6411800240d0701c0445026a0b03405100348920a0020b20080240d8a0504081006c001c0008005440f8400c0400c0201c100b1007020307214840401d08003c140180c1c2841e14000d000351000c0303402d241c410760500002164450a80042c1d81030b13210143d40c8d602014801c0d89882c05101070141000e2522030300c2d0ba400358086103680700114000c681603070041000501e048402410a18017420790b1895821400502c003180e40d01002450a51b141c6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 26511354 1250 26510104 26510129
    0x71704080c0c041a03070b040602060118020f0d0c081003020105070605090f070b04090507030c051e09030d120e03040506030411032404050601090c020a0b06040f02122e 74
    0x140781d0351498090542071803a4001d0800c84a280300c44240e92030210004400d6089803102500d4201c45180390080780030b46401a8040801005003900528040040070411000146000901d0441c12840c1e4030042c13400b5010f94807601d0081013a64001b01042d40910440e0f010707844030341150300080044c8143c500182189844001080c42c0c40403e0201c01c006211450840c4c103240d540b40000300064105118003104640381c00001028a03001c0d0064007521001940da503440c1c0503a120300100c00000e8081c1059880200340900981d070303101081102d481d01b45540b90300c20155541c4c0c6400007990444000e844107600705201c20400303500d4030400c0c2d0740c006501c064400480650034022900c1c19a400d60035000305541014600c100c82000340c14240103902403010b560072607803141204401d842c078210303d200c0142d0210200401080d800180c20340c01040042000c1a003a07000e8007008140e80080d05112f507041c01590500103141c51000308220414080216002c8030300d0040d0302d400034040d8520900d08007000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 26512604 1250 26511354 26511367
    0x61803070b040f1a0405100801080c01031b0c0c0308131701060317071103011422050606010309060b060301060504080f1603020904030201021b030306030118170f1608090907170408 79
    0xd0030050324046d2070041e05140c0701083e00c0500400002d002c0c4140fa03814010640c40e4542e55210380940c1c10200020700450044085401d001c50350b02c2c44075481610180101c0401200003502035006011034225590305007181d500f89542001c2c10180041e98442c1a031500b0070070070000314000c83c85001090060b900c65280c024500f0200b100f061000101c40e810f52800e80407003089922060000e0242c2c00e981415a07000c113141a54601402c052500605250b21420004c0c4c01503110b5008140b115114210219142060b480826001d40083c3c10940202e44042004d01c440b0304c0421010300f1018040e40108085070301e84214565149070703400702070f00038030071000012f09240c000d404032440e600c16022011545103105007502d80341d80003600d1941c8a035085c0400c00c81c0350821610507115640d002a00300f901d120032002a10050350200006440c858000d0200c80c040103248024854681c1c0503811195440b42e141c02085030300200184000c052000300c044030403521500750031103039119602c011503e40d04c0300b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 26513854 1250 26512604 26512649
    0xb030c0d05090703030e06030702060109020c01020918010306050f010e0a0b0f1c14010b01050d020a02010e0d03050702010506120d08072304170a081603050405061803070b040f 77
    0x3044140c19a88a400c1c841480000300c0005032003411039000342d03100c032090790328070042100314841503550f200146e0000c0c00601c0040920780c000d0a503504018001490f00e202d08000c0303040b8100402000e14007400c502c00400074019540243d84e4030000e0f01d50b00d410198103142d940b40d94101c01410f802d041540d9610302c0021074139003a8817560b0b03005001304a01c80512100360310140a080c907017000c452201d040e04810b501c0c11014080c04102c450161600c1d428a0414603d5038000d42180656604540d00d0305030070755031850248030f4035061180d02d680110b82464450000303401e64101402981c0070b800400580c0070306002c082811003145029180040040e2240201103c491101c48005082c9030f10440303144a1000e2884000d00c02c65450028140e01803107040e11064481800040c007800d0500104034200f00c0b031091002c1070001902c2810010f080c6500da002040f45500b0010700c0303110245455645060703d01e410803040c401003040c1d002030345c0b51504000d00c001640025114010900d10303410001c90b0380c41c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 26515104 1250 26513854 26513857
    0x60f070806030a0c080a020102010b0a0503100e030f0403030c1e0308010b21090312090c06040e0c0c030a0314130305190507021201060f170303010302011209050106080f0d05070c0b030c 81
    0x80e50410302c00c4ca60301da19003e16503294011808101e000d98a09100c400c094100a00d010301110740007000b80c103000c540c50003d031380644001c004024417070000f0007a90100b540058080d00245020350348041404006203014035107031200c2c103aa081045a08850000009ea0022049041d6582030000300e4071513000c0d4451b00b8148004642803034803005048200b0110900000c0030302510340000926440d2502c0341c189854640300e541014541002080005100d08400814881d8108080008007131608036410881803c58024070712110001c0d84407440c05401c2034081c5001a0040c1070038030f04409585240e603000d0824407601c400b44003048502e01c644010703580504261817407603801404005c103a50840c0b507040e00a0480e4020818411100100490308400102401c0d8031056440011859a403d40c0c0056545006103a00340364160748402140000a00a0040000600f0040000c000311004070403418100003a56000900700602071010a01240322890f141040b5036034041035694a86800c10b102c0a507 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 26516354 1250 26515104 26515123
    0xf0108120a0e090702030a090b0c0616050c100f0501090e0c01080a14012d080d03050408090d0f02090705070b13140a0308061918110c010606110d02060f07080603 71
    0x40f098032010003298540100085c81400e40c01d5854001c0640c940340f01402c41d0088d006004007541c00f18000602d1080d01da104031460303040070b09045050440d20311648e4600000c0500c0c039040151a50f10300c01d0300c807482d07000d02805088102028002d5a80000040c1e603140c1401000504100c40000420b20305025680034800a034080c4035002d6280d81c407103020142141d4404201c4100300b202c0003504c00c409014a61f4201690580e1005d0211103800c800100c0140c0005003040d54968420884800d00d507580c114001c0742c1c40d100700b00c80107103c80f00c0d004020030070400500c51000d20134100484000100400c015590000e0302c60800e24048809003861440031040d1050b4034460f00c52020f02005046c2c0001c10107105420480302c821640e41c103943c035140d007001184104400c100b08014005144250b40d000a03c440d480254200c1c1426000880340e82911aa40e10003004a010852182e11441c001d0220314038100d21800104900e0400300c0000c0508600207120f07008100c8480049142c659003440740141 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 26517604 1250 26516354 26516359
    0x50313110607060e070f0e0f150915030c010201110409050406090204020a020304080c060a0c12030e012306060906090d03020309040c080106020c030f190c03020402070b0f0f0108120a0e 81
    0x841c1d090502c3e1000040000c540c055030745114004000505040030401c2c44180d4411700480101c54581441642c1d859030b01030044003032904400628502e40d01ca105105110303075405050030b0806c00c0c444090508000c4c80311089411a41802900b84003403420390120390498040c0503000640f590b56090907002840c400c00f0003584540001000414582d001002e0802e881c40c88068a03581c0c03050108200c164401c00083c480031400481040020806038207010198000c641070104d50300d81044e00960071500b400c160f5242485d13090541c542118000c3c11040d030300240035030705540340c251044005890b41c01440c0c001d5110300000140c010030184207100360f80301c0c110040c1040c4291a181000540b440c60709020b0b41c40180316100368001c0f00c1c0340008800d070104002002424519003140c541144845c0203071805d842c180301c421070000060300c43d0300c0146141d500030054151142848400009401c034080c04040c0300449050051200c80000b00300340c000b20740d401060342e9a4075103401e001e880243c0030591495 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 26518854 1250 26517604 26517607
    0x2040207020a0f03120504060e0402220308030115110a0611070c090504140d1205060a0e0f070f020d020303060f0f18040b071b0b10030c06020106051806010503131106 73
    0x546101605000004c0d00d2040d80032056441c00d4004c203c4040c0074a2068a00154450f0030614082c2060750060840004190003601c405000c401c9020601072140c0c41115007600c00001000943d41030034000125140e540b5081405414040303a031075848200f0000600f15550717491959600c914041c040b80c102c240e03c4802c0001c460340d1035100c40c0080c1021241a41d20700c40c420040300303004001088101c0c0344206070310380300740640c422403074400201001441c0e690004000400441c11000d101d00542c480c81b810800364030645040c040048c1440e04003100d06c800d6510044850500c59004000e4a50040080c0e6841c0c01802000c0005280d081c007186c0820b4001b0288408501c1e02c401c3c41c0074040c45907000f000120455103552404072a5403d52851045620201c00b2001000805041074550050305582014480a44030385507007050320038940c030860240c2e55802c0100b00904040c5154000844040316001440c9080c0002804500c4010584581c107100010960100101d840000141c00000f81115 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 26520104 1250 26518854 26518859
    0x306240d031e030203040b040b04110301020f0405180f04110402130305010e0105070509030309120f070e04030210020f0901030b040e0f0307030905090106020703030c061410030b0a06050a1202040207020a 89
    0x2802c04082a0404200480310400c00030301d035806802100d000342d40c0308a010810b540d6a0302c4607080b070746c03000e082207820510490681565079800d0024281e0840c251402681e110310301750070461700d085241e0304a1b528080080401c005590071081d000d030b0054100011085001c05000002c0c021f21400c1030b280a80507d41201005200c41503020741c0e0400044030082041c0d4540601c00d03a45030064050499040d0b208001d400300508181d03040d5890b03c03180b841142c141d0303444403241e103081200503000022407158040c01c00007416410843360000200000003103203001801c80d65405c00d4821001154141170300e0300040f10032034540da0b10401c2e000346000c045c1c96034030203110341050312944850350540c0000e400c80000324603480e104070034a040b030b901e80d00104032641c0b07542e5040d502801c00d503509031440340d910341000030120704548042d40301d9941820b03203d084604601d010207c90401034404042d50f880d291081c803642d102c1c0e035414425558001d800c2105540301d0710000e0082e2003075134002034010a242100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 26521354 1250 26520104 26520107
    0x30903050a0c091401050a05100329030d05090604031205070c080d0f0311190c0819080a020a0806060f0c030f04060f050c070b0f0c010e0d090503010b0306240d03 71
    0xa9030954031043e50901c40048101440002c503e020300549901000c2c2050802592425178140390310340d005030030081101d40c1d081042080707807166900c140d0b400305105042510301e45014001480d14400b1420550f00b0200220046903150180d40030080c13610740511011071641c0e000301c05581c200b69100d4101002603895280581d220810446040b003c030741d85c480c030040c0f40f500a0103401c01140510126034109104481c003840015074a402e4a81070002400c0c041c00490503000050052951103402003d0254408100500c2c07c82c005240c82c45451041c003d80071a00c1d44518050b0f08a070301143d5558840841e000c0e0a071131480382e001e8007a40392200203443c0e00b488508901034003c440a0b500c429a0050440a0a0f10780f446050049000c94028460600031440c0c154064003195071004030060034240b92042d55800c50745078555080071544049032100c0d070154004030030390261030258003e00c104a44800880d03503480713002c1d2600032a291a030130000c1803800b011340c1e19a0100d00c01003d403101040c69080 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 26522604 1250 26521354 26521373
    0x1c02060304060c08090a0206070809060f0f0403030206010504110313110d0c030b0c0309030a080a02070c03030201020702040506041a0108130606060f120b0a0303030209120304060908011401030302030304020904030903050a 97
    0x660100f6903840004082d401d0100e080039446c2e4016061b1403426120381e81e40041c1e40d000c0c011040e4007000074003107024020a80381c060310300030f03c00201240c0c0d02c9046040103858504142d0003d4072903414454800302907070300102036a400400318000285010450310706241200307070341d40d0264340010304840900c051000c1000d11030101c074000e941e808100c1d11080030700105031000700c0b0014299801081080385d1944540b00050703201c0c1b9508001401c3c400c960751402e0302c2c020654400d500503074001c500d40041d8a4a40301d00f5800c0b06c41218101b000b01d10500c0f1420200c2d00a98071141404600400607080c5900e14110748152984a001000002c0e103940000c2c2507010001310540005404200c800001000f074030801190010003450846507900d5940d00314003a501c24201190040040d4402120130a8100017600290400c0c2c0c403056401801c102c817140c00c582d09010002c0c20303000c4000040004c40c3c1c010007100e4019405075010301141c1d803542404e4071102029440101244a4490901d060042c20344 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 26523854 1250 26522604 26522621
    0x915061805061c0f0504020303030103020904080705100e0d02150c0906091c030f180e0402040e06091b0f0d03110307120e0f010804030e01030c02010e0303100311060403111c0206030406 81
    0x5082113450f9045030f0140c00c654040301c0007505540300300700600141c03078071901940e401441070240501d000007541e03c6505103c080c4003a5078050b80c840a1500c0014814400c80550081d240700400031000540000c0c454500c0c05800d2000003200020b14410301d0300d0b108211280860041e000a08119030108104030113100d0300c00c01d60001d04505503070390b40b65111f5040440880d12041c6103d101e20300b060101c1109034030107041268016510200070b12400018005030707100740300d4007024000782051a00000c403411319000c41c0520480040081d40090f5a0301c0b03080d801407540525041c18805268990070389588100a005000b0301c00207404482c20a501056815800c5001d071403000b0039400031001950600b005480050229a03c90901400c1d940711f50f000714240800c40c8000b180c0000c441804170300b940d00c2500c3c1d0310b842403d02c4a0610620aa80d9880c40b00003000b070782e105251900d0740d1240364802c3c145c80380b06c42c861080c51803860f6411880417140b615154000b00f841d55a400d261610b8802860510b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 26525104 1250 26523854 26523907
    0x11d03031b1806160b0f0108070f0602190302011503081804050105010206040609021f11011506090909030c2003010e0316062003040516091506180506 66
    0x3111800e4641c02a18107440c441c80c481410541d09819181c1048050f411a0b030b02c3d0305550403070b007403c40085030281a003503000c1c9110000c0070046504041206050a00350342012511001140e400c01c030456002550f80d01c5140d80500081240d0114030b4100d0140907140002c0002c0c50700c424003c800c0c020410b00030b0500b061564880c180c006c88607402d01c41950824807030a40540c000b2000200854900d40100115620081c00301a0740c0c030003410080d681d0590200003c001480e090300112051f8424800c007445e80590088060070b2901d00140103206003003d02410140da51141c01c0740041602600300f40c00041c0e4400c0319030b00c8603040c041c840102400309040c0b10340301c3d40c20000c0b203000f2070b080441154045a403001d42110450060780f20760014003000444070108a0744c0300c0001c055419480041d602407071041001c0c0071241c3d0100c2681da00d501c1d481d00010500c0d407804000c0c00344400c80c0c038806001c8505605106015212045075060102001c0e80145d401550004076400500c81141340030100c006107 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 26526354 1250 26525104 26525131
    0xa0902040e0123010e10030908040b0c010e03032701150b030405010c030c090603020c07050d0b04031806020703030809030d050108070f0b040b0306040e0a050a0309030c062f011d0303 80
    0x640c0b0403c4030a61480e4001d030b01003603070141404050b080c4145000b55802a506002c0345800c001d40c7c80e021654001c1d8060f0b25110310100c0c801c00d0050080c0105c04c0c461098600550a60505c030800c52140c0f107890240050420b50343c101700721190401e4020700840c015880c00303460b40c5039444203103604a07441290704490a51900b003050316414000d128080c85004541d80300d003402410500e0035002588040d030300e55900d104c1d03d00009001d5a40d50006848107100d0180e8001c0390601d481c01824099090305800c444004100e000c0c000254001440d41c11680c152411842c00d880d024500c60442c03160340c1055a81d00e080400102c0c0850000030303030701d00b1204400c3c124801107580d4001c02e502030050f4020390206880800214840d49000c0c0c02c03810840004c8c100751400902070755203003842c0c0300f0152401c902040d90590108148801d000c8d00100401c46801c0038005c4006580f00b108900c140c91b03080f45d401c0110310b0040c0c0804802540158416140305002150600880d2070f841e55a03003046910b000600718 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 26527604 1250 26526354 26526389
    0x60203040c0311040c08011413050112030e031207030804030e031e0609070503030403110307050603040c030b010e0c07060504110a0303020601031202010b0109090207240c09140a060305060a0902040e01 88
    0x3030031701c034a0031052031581c0c561001d6400c02c50190a081844001c20740e000c001310281c03192400d400c1c4142c500801c501103080d50401283d00c1c0c0074007102e8482c031110388280c1042d030300d010041c0c04075402c503044242c0c1403506440503945c5142c2a44c030000c1c40700e10f40d03400d880303484030505000f0180c03401e05580500d00b104840c015a51107002c20b07036814250003025012340040c8001c20002e08001800c03001448001c1c103179030b0031540f20320114440c0e410895041d9a51004904204280070a81401902500725028490040d1500032034112840c404e03240001d000da5030710400181070003009c503030981d040c2c800180484042c569a06000359588428001921011100d42c10a80310b280148160020190306850301811341c0d1402035018000e4000c4042902c04403426418101c9844c0300003281c1d403841d0380080c000030703c000002400074031258054000050280c44002e0982c06030341c4010111040301c00d070389404610765440030b010503080c0703005501c4204454008075011440c48403030b00c0078030b0503196005100c91401c1d8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 26528854 1250 26527604 26527609
    0x7050309130612080d1d070f05040203011203080402040f020307030b01090806040b01060c11030102040b0d0f090201080a092303030412020309060a05031f0602030c010c0e09160c060203040c0311 85
    0x803400e03c42d14900c281d18150720800030303480d0006000072405c01c0d500018803040c0503d01c003122088003084128a60084007051006050044e0104007414060710300714115030401107921004101d0080c044c0c10f0003102c000003000c651300d90f0001c543e0360805034011764807400c0043c00035010349454100207003c11a40d00b000b260f80c5c0ca00090f254841c40d000311030142c999207041429032301c070029100113440c01e5400035a0f40400303481c240020001092911091035950052142003001c6401d00420040070f0b074100303061400940e9105090580107001c0e00b070001007140d06c2e03241404258070890030009012030f2079803896802c3c00c0081302951041d409410210011202c4030000c030307107910030f060507181d2105040c4407a00400784180045c541c0b00c0a01d680b01d4107c9a03040d002000600495484800160310000d0b0700c2411301428082c805100e0700c1802c00740c1a1106a0000507500e11000348400641030781549140031080c8583c20603000030b500150115640c0c101801c02c0700001d001404142c8040000d0751070b000070360 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 26530104 1250 26528854 26528861
    0x4050f030604050d0e03100c0503040c060509010903030f03020909010f1d01030308040b0703091505040c0503030a020a021e1807020c06030c180a051509040606030608070b030a0609020705030913 85
    0x45503c0b070003a080c03408010f1002e85e2200b0400b404107070148130301d8010001e8401030307210724485131669845040e2685082d00e032501e160790498000300c08210092003c1411030341c20602e100d003500d6040c10a103079010310401c3c00310024001d1210040d27010240703000000703d00c4109000e00c1c0a40d0131002a0100080000e094480204800e11006000074003d000050100c3c0b00002040c0c1c06c5030244c6070100b01c100607900c03801700074030045500b0210303960b5403003e0004000240303040c1c100511040d070240d8104541c950019407503489948000c1c2c02034201440c10036141180c8902980640802849007072032920390b0242c6c070702c6035200f1034a11015104035040c05146e071411005407846000114490b07460070300c00d4415401d00000e6042c0d61500541c4c40d0300082101d03030341c070b03045d15050b81102824191118149010401910360540c010800e1603c0c00800340034032100850104181c60004045a5903900d404134014000c1005034400d01e041403011a40d0010404040014881a00e0448a8510642c4010b2800089 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 26531354 1250 26530104 26530111
    0x60503041a160309080d0504050102030711072105150108030c0f0705210c0402030717010509040807030f14040909050115050916020a02060a1713030806060d02070204060b04050f0306 80
    0x4041c050340c0500c207081c8681c020b8032100d485034442c1741c2481d4043c06224240c07541504c0844080e500402045003403544a0304241c40c03180d00e0310040c008903241461811542c2581e040129841004260703407018030408102c1454030311150b100003400e03981d41e0000c0304e459800c0f1004240c1d15010b4800080000c90340000c2c3d000c25240b0040540b0103842559290710040281c0e1000244140640c00419206a5907407025610882c0355440e165083c1020b81b81800201c50140c0090f40305491050a100100c2c03801c0080d186c0e400d40c1802e2500080c0000b00043d100d181d207854103d062850001800300d84205d1640110450620800c001d116881060001840014441c042d8541084032500080c00c490004032950881900c2c50050310701680450300482c4242c0d0281c4040c00100780002c40c0c5a54034101d1655866108038a0703407602c884070303049a0f0000c0500d20080d001078030603000865a08030040c81d13641107404c0ca0340d005004010300c1d80d40c2c0c2c1c00000660094403525103d043c0801c0c0400e120708011039100e11 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 26532604 1250 26531354 26531371
    0x150d1b0801051519110a0b0103140c0301050906150d1407090f0209030a1101050f040312140f0304030815030d080708070201060302090105150403080c0304080c040902030c090405030d06060503041a 86
    0x1d04c400c00c01240d800c441e40032280064400c2401040101d0407200c451130285004017442c0d006102c07001310251400c0e622a241c18002c2e0300d0700c0c040040d8074001042558225504a0311007104121503000103001169200300a484020601070307802c0e0b100000a00c04045406600d0240040110240050304034051745d144a80c25400520740e0f2800182c0a01f40c001c000041414624108107410481074041e4100350811218100000181c210a58012a40881d8480c04408861800c1039a0404032900d0101900007820300c040c0001141130807814080344d20b29004080c04858000c0e12006005210b9141a100c40e030108a90a022681491040c0150740580323402a00b00622070b4645801e0019598494000e00c403011028000440060341e000000c1208484a600542e183e07410322100508000200300e0007842989001d44510050310042a14400c06404a0f40cec141d91b561181001d41c154400c04070359186151070710402140c4260001c0255000724081c142d108022011010b07450480c040c1991500f0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 26533854 1250 26532604 26532637
    0x40b040b0d0b090f010c0306180203010501120e070b030717010807060207031103030c01090b04031205010f0302040209010c060e0a0507050a03030e0607050a0c030b0103031106010302150d1b08010515 87
    0x40100724029680e82d042681d01d0300b140d103040e28040f000741c01c40b1b2a00c6004400240c40e44010020703d80c00070503502140d41d03022421461545080001307010500c101405a00c100c1d11942161040602404944010711b5000100390f0ba902e00900c006003140c00020380203084d03040d01c4002051000300040d0900684046400400440e0b085443e8481102505003e040d8584030411030f0600c210028041e100200d441540065070354103240c600541000009209032045a103000010042e0000e1094600212901a140141e4511080004862600130040c02905d403d0810718410354242d00003407400329850240d0261800346845508200b4400d0903440040c0008202c0d20f050300700741c07410800512361503200740111541080300d0303034681c1e02d201110b034810b45140c540c6900400038550004034956080c03519002400b465810750303000448800f400c04e60310007040c0740071603441c00d0640e86034081035442100040170004846c50000c024140d6a09029031400780c560350b100c2000c02d4106200355034490050340c0c02c41 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 26535104 1250 26533854 26533879
    0x6030d080702120d060512030a0207091a01030b01021e071a0304050303060111070e09010f0b01020102090a091e05090309040c09150c02040207061803031b02060f04020609090a0b040b040b 82
    0x100100e030403509004e000166500b00c0010135503a1284022816500390000c0d41d151009400080d09207807042c0e120445523800c111520610407142014040c00e80000d09000a03d001c062004074645142000000c0e650440028078032800d250015411084848044243c101070f9400400c0c2e0320103000030344005200d0390003440403610543c01071035102d0703929600c04201d50381150f1b580510141c020381541c401045135591801002000c440e070142c10340004082c0029448c100034000070130152500c40c429180ea56682e444441204100b58a0f260365242c8141401e02090030202052502c96000504041c840c43c40c20700114451800792015404640d0070030f146085000000d141603d0b0308841503001c0742d000d54200207500020704a4403030341d1078140003503030ad903661110700740380180844038035460b8051810850b403011260940d0010b0b842c1d40c42200c001a0034030700d440e1071001c11003e01130310f015240d1009a480401c80b060b44d80d50301101000c0011138041c8540182141072108807a800f0b004940c0101201502 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 26536354 1250 26535104 26535133
    0x10804060207050307020d060203010504110a02030712020709060803091810060f18090e060703150902070204140c03100b0a0e010c020a0f080c031005010609120c15050306030d080702 80
    0x1d02a09070143c41901d1421016500042c29202004012600320394080010300860a281c4544e104440301c5a1b421440c2c1011400f0280d5603010380d00000303040c103001340030216855200b80130b50380007069440030038404581c0f604c02032038403900041045030040c000b2075098003814550508d00c6d4010456034140703848043c02d041c81101e00d600e80189200910080811082c000315900c02a01e00500d04c4500c0010201d14240f0381504207032001e00804109410600c035a41e511988001000880b07038103d0300140e0300d60342c510115001d010780c680e9101004040300c1c1001102e10000c0020b510600c0c06603070101215484445030b44c55070090880c100b001907107109403030303c081d40601d0600203003034001810900080d40d1034040c510040d50642040d22103812a0320118a281000c1040d101c2c0060640d0003401951304256009000085901c903620300e062020340420140b1039040c0000001c0c03c140c2c8051b107418613002101400560096440328000c1c4140303503007481018072a00c0f03c607000d0009a03010b840384803203000c403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 26537604 1250 26536354 26536357
    0x90c0712020a08040e041a04020609010c020a0305010c05040501231c14090309040c170403140f04080307020a140d02040e0f070305010e01060608041101081806070914010203090108040602 82
    0x455005511603541c41030b020901e600301500050140e06061801c901c0c00f8580f915801ca08106c5014801d9011000d210040e0b8410054460481e021718203500c010f0104d000045406040d54409041c0c0e51801e55101d0406a00400410035030b01d084c0c9403000b0880c41100c0c2c00420f911803003c03103403e02c4401d1040b0310910303071440c490032390300080c1c400e0210340e6a4200020000c1002e05440142150b400000d9802950805004907119807501c0d003481d000c800c00061a25910010048c0f00030f0400103005005a4207240144c203840310000344281c8151615281d6024a030380f43d0048005a1080b05140c00006010302d010209090400b0040c0407144502481e500740405030042100c0740c542030080744c1a10342c2840d810402e800042d8000c000100b06140072820150231201c00390050800c00110504200100f2010425000d89040a00c1c0491440ea03800d103540404e084c4016910000e03000d0074050029040e8462040020b5842d03541c414200c001c1c2d40c20040e03a0780d100d00841e050203e10364038000f81c00f00f10703160b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 26538854 1250 26537604 26537633
    0x7090b0607021801030606050d02180406091a01050312180d030201060b0d06050a0807030506070f020c0a120c0f080c12010e01020a0c0b06030303010302060f030601030e060907080c090c07 82
    0xa214504281e4240d00040b41110140d0480080304918001002072145034016140100405d85d28003041c03610640108801001c402d81015111004038042820065241c0c0301050840e080301502d85180b1a4140d00300900d90207118840c03192041d81240400c0300e88040444030000c907044041d01040030048140060070342c0b8032000341c055540c1e400d000a07601c90f040f801010400c00413880000e865003810204620b55072144c00c002d0050744800d80500006100041c81600220f03e400c10508408101208034035000e50032441641101d07002000207050702091f801d41207810f1040400c80c625580310031111a4029003032103101e24039440480c0325061401c100f100400c4120160002250200300c01d4081800c0e44c0c00001c0c0707100003440e80a900400d00202010894220304201e0181d07146500d50380000e582405072100b0714600d50300010129986a010764000929558032500780da0340b1b4505141384984826044c0304410160142035040c09041c07611b10085c2e0300c10400c5c10001810a5801d886440907010802c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 26540104 1250 26538854 26538859
    0x30a0801080d1e0e04050702030a030509010b030303011a160c15020109020306010b090a030803091c020c0a0605030603010f1d010c08040804030b18060c04060f02060f0f340e0303040807090b 83
    0x79400144a891707600840d03105001a40003141e444031007540080803504000c184e01941e9241075041146940d010040740d04403141c120f40140e101d44c28a0b2400c034603104003460484d4809400100604020000b0440c1c4201c48a01000707031a950764280d001d84c00d072059000000e40c1900100010312460306018080c1000307480150405401c01c0e2a83d4407181c1d140e00030340300355580b68008441c00b58000c00d06020394010100d24406031a50030b000c003000c5504c0c210f0b5400b030b020901c840440000c0c283e450951010294501491081c4101081e50b4400341401c45069960f21b00c0e0f50808003181070043c001c1c0304150140d80d200800c580740a00d10b803550800582c0180c10100200703442c1c07419081011007041054005d0140719041c0e0354951a10078050003c01c5044456801d540200080082240d02044000d510048240c2c94042d182c0c0d4840c1400742c500c10381c0d20780d04c0d2480f048a1126508102012013190458003549965560364881b408042d40d07800355206071502548003907002c5c0201d16460700080f1148601 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 26541354 1250 26540104 26540117
    0xe010905010510050a05011103030c180d0318050d03090b03060a1e0e070305130f03030b06040605090a0501050301151101090f060f0f05010506070303050c09040905030a0801080d1e 79
    0x99034919081d9031083d681d00c00070b100c0d8544288030518250a40c40000d1601f420400c0c600d5100e412259120b01000300600349180300461002951006c0a0801300c8802005044142d01c45c00c910300505031804c58450340c014088110300110b86410180e209205807074250f1a41c043c1c407480d09814580c5584014211038000164120000d00d00c119613903013030400704501e44622000350816201c000d8403180207041c1c01c101800c04c018400e020b10681c2c6482d1205404c075541c091000b007503050580c040c0c4115070f6441d0b0030040000c1c0000f4890362102c00b038008d04104a0384040401e40e01d000440c1e050100380500340b40c511240c40c03102d0703101d4013800030b42c1c0070904100d0001c200189a925000b41d00303d403020b0155041502c406981908521500c00d2103004000c40000b003101c0e5041c0804104035002d80000101031555071000702d110320b000c01055039240c0070002d0051113800d0007442d101d80c07650020420b603004900640004101000081240258424140e0b034803000d41e5420a5500000300350110781005003d030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 26542604 1250 26541354 26541371
    0x405090406090f0b0708090a020901030b040f080a020106030501060905070503060111070306140405100c0509010518030106080304050a0b03151309050f011a01110601031101051b0a0b0f0412030e01 86
    0x8141500f000c1d40c5009160030851031901e460003134180756004059042c543c10103045440180d0b81c151446054170f03041803003545c030350351103203007034800790180c1c9001078000f84000c2126a450369054002200390f034802c9009110040d0340350002c1c000c1e903d042d02d4035004144184001201540b01d00d00886010f808003040b5851107a40c0d880d000103d80c00a4411103440c0a0b500402c030600104009456020010b15010007901010502c0103241e409004001d41c108080001e00001a1200448840c00b0680081c000c210f510307900e166081d6079901a10426001d10b42a0b0000100004520705070f901c64001160210660f415110400480c0c5c8441074401003140e43e03e544040228008001d011543c0c02030000000340720703800300c08034a00322001d91000750400c03881038140c20005501050fa281120380c030045032500e079500c7c440141c4441c010040368001c0035031030f0035582c1900d000c00104120300d10700400882800703464800c04039400210403036010f460406c43c6283c0c581a24480d501210000f00c2c4800009007044 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 26543854 1250 26542604 26542613
    0x105090109030c14120a03020d0302031503010e03030f070504060e2b03030b0a140d02060c071d100909031b020402090d0503120c0a02071403030d0e010f110c03040509040609 76
    0xc2071a08524005250a0f0284d951400d00003015851003200c4c800400c10b03003c00350380c002d41d5119480e82c940105500403012990211100c03050190f0707218002c0084c800c02c80d2130542155179800840341c110f00541c0346400b051243d80600200c0702075940554640c0e00000740d020601c6a030401602e0080d030f041052020f03101c030345903c50300310213a241d2103070340d002c600310030060304001e928042900001062140044801c0e86903541d01412a44958155080b90f21600710034223003810076103d50700203040340300c006862000082c003da40440c400d079071003d00d0000345600c490383c0004840c042030340100454400c1c2c051003030780710010404845241c802000035241c04aa200410b0701e89120341c8048681c2d60000c180f50101044105806610000710710505003880710740c3d94001d5841c0b241d841001c0030013200343e0003203910341c030f05004503200425011014400c1304072040703050b4006c1c04107007024941d0344d20b0200c2d941c0088606404031103001e07602c8001582818200010820701c1b50700a44101c3c0c0c00e44c2d032111641c0004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 26545104 1250 26543854 26543873
    0x302071505131e17070c0609051804060204080106030503070c0812040b030901110a020706020c0d0b04020d0303140c040e060108010302100e060405030d0503091506031c11011b090e0f0105010509010903 88
    0x650309401e0652615924900b1803186c40d15600f000d414440c00030410301c070742c1e01d46420001c003d000341286001c054940f810164020311481c1c00c41580b65081401c040300b8400004010440c003803090007550142c90f0f49420841c0c55940e45007103d880c8080c2048200964140c541c0555040202c0c0780001507003c02c224a0006143e2001c0d4036880036030003a810800800750140800c519901003502e00b01c09843e1a69590000548010002842140c0d60710001e402d061083e0b000c0804000c3e01e011104160070407841c0c0100c0d030b030001d100303041016080d400050300552003070000c64101c82d8054120a610381004500f40d0f01c0980401040b50007074030900000030a641c081104450000094603201d5803410800e5249080c00490b510100b08a00c40c1024090680c40010315240304075960002d500740c0c482d01e000202e6820313035030044007031082d0700b0021212070410070148002400c44068a551400301e54a045555980d5002c440454001d0b62001c010801540034a00606c80c004051522a26641d142d44d5040400e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 26546354 1250 26545104 26545133
    0x2030f0105071206170303040210090b0409090605010503032701140403080c150103081e0f0c06251704080408070f091508030a0c030306150302071505131e 68
    0xf4841200c80f0310850b0b0f1512405000e0400c070500b9000c4000400c42003507991001400090090055161094407035100e540c000d00602858000650384070350343c0100e0000b4080086040d5082d134078002c00007030203160000803500d110181d40341c21018440d6504040780003401208903541804030000b00052000340c2040140051481a010562900e00103004280340240d000342c2528043d20080050010807092400e5807044440079031544142940e260340000075000d041c0c00140038803004100b1084404002c07414911130001803901c005018002c04134420014a01ba68210125012042d00480982c0c07004101d0b90140c00b40030030515069540b100a40380c03080d268407142c0c4681c0c08940a01c80003695000e60380d0840984c1000201d414202644240c50388a21828002480340115140c000c1500a4100b94002d04c2000300460111602d80c201902a510a0380216025180740c80b80c00c6805646128042c050101061404c64280301366844150080303a01054000300790468009200090a65441c8030a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 26547604 1250 26546354 26546357
    0xe010309060b1c0507050d0c090207081306030b0301050606030c070f082a0f03030f07030f060b0406030b0406050406030503120705070b011202010806010306151202090a060201060e0f010305030304060902030f010507 94
    0x10003d01800c004d42080419040140300c0d0411216500118254114074402d0700e243d030b07800582c1c5400d1785c904041e80d4844d1900180802c4955000011341c01d4269002101907007040d0002d000f5a03980d0820080d80b4807048034041e52602e41441080701090100b00d220100303c0c03003a6101c92420394010220f1020b1010b804816041c041c1c802c1d03240840c110188210000c0d00e00c204000d60543c00c0c0441c2c1c9882c0154018440b9081640d0396404c0010402d0b5500510000d0643c030040344d548a846120003001783c510030b070b01c10f0b000d281484400100c5041034460302e02125005000f5504222040b581c40c3c07030645000d0007207405c1000500420b00481e0f03001910074000d007945175000d40d543c43c181c0b001602c0c1650051030385050601d081030400422041030b400c000c41c44240d01d402400c0c4111405403c0007801040141900286160340201e0762540542c441410f07036040d44000b480a9440040b2034034990000d0100030103940050002c10009101d0b50881c1c40000d200038103403245004a07602035421070f0001c40d40e000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 26548854 1250 26547604 26547649
    0x102041e0b0403030c060b030a021207060201060f050d0b1e0c090f01020303090a030806030f03030a0c0206060d12050702010e130f0506010509030a0b060111060a090302010606050a0e010309060b 85
    0x5580c00c0c10404020051010415040c10b2514544000c0c003801ea00300c402405142d00d130004c1c5109030342d0502c10100400e500800421800c00101c5207a592010140501c6000d58640074001c1104840000313040102c501c000e0018510b922143d5641c110803801410030b01e940f08140792851810a00040750078482d04c40e25404030346036070069040048140c05021801d045d90010402d11080d014080f4140c95003a8050404070031a0b01c0b00c101180c0b62009440c01460316020102c140f102ca050590440c4092041c260300321181902c89004000e11165032100040c003856100d1005105640a1000b411405005040c1240e0345401c03400072030042c0e050613486034050380e079545001e40e2944c00c600c50320703400410038a8024100300c0c3c0340340403030780c0c500c0da004001c1c0004a142e80000c07500c0e0303ca0819a10322000e90304c04d40300300c0d0400360400000340400803030031405542454008510b0714403030701c01d848010440d44e4600e03030001e051000650040c50080c2003501c203e61500070700006520b4103491004141c9107104181c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 26550104 1250 26548854 26548889
    0x2031605150106031119090504020a0503100e060d030f0e040204080d0f050f1c09020406030506010812030f010504050709030c0b04050a09020306010c080c07091104050910050303030114030a05010204 87
    0x1001100160072010505180607810a0703a0340d19030098980c64a81e1806e0001b0b61080646c00351841c45441d84a240c1c07003030000821502a0f07901801550082c00300c0b000c11030071030b902d074903a000702d0345800c0350085d400500c220200c1011038481c11140943d146541040009400c140001c1400d81c1c0c040d80000303003190b100300c140c451281c1d8040340f4147c10029620f419801c12074a95540d1100780310f0301000841c44d04494500003080f040541c0301c000444d90013041084915524540b0b561070b0f510034404c45415028503a104c0910740b06040c1128444c01c4205649901760f801c1030200401002e010b00460104a825600031001440341800301003d4104400740c00d440368a0b0004004840045800c0040150300500500a040c0d03000b0700d00c0041954400702da40d403103001d1000c915180401662000341c01d581001000c1d11041b070740500803c2511001e0742d8100459617840180d0843e01014440c031034041e4010401044800c2d5206c03900c0c850704c00700405031100d80ca00c68030341c10300fa41c0264025104140103800d29 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 26551354 1250 26550104 26550133
    0x60403031407020606010e013005010609080303190e0319090816080303060108191e0f0e120c07171b0d0c060806060d0509060f010f030f1202031605 65
    0x8681c4a40107200130302c0b01d0f242400c00244940c0200c0851818020704c00c40c250448014000d5010049000080b46c15a000412640f600689000e200748000f1400c03049000ca202000441124441c14040c0045250f0380600701a0000900110805480500080c401c21a0610000c20207001c01a000d60b00e003514681405941810078120300921010758666000c2081a40c101100f5281d02c01000d0034166569522071206c8400101e2900d6207200346031074000c00360303007034454801c280b0b8411180b00300810501200004090840f01d010500140540c05140102c02d42442c50000305031210484040e10180c0b550b803100b02c203c14040c150300a03801e0300516610380451004041091609a04030743d08100d03402c0940350f0200e2642d0398000c22007000355820002d100da444520440c3c02d0610342450800144c50702805a0703803a44005c0c0d4001c00c4510b480c2c40005010818040712205813030f0040c9284032108034650b55000da030f658800c3c014082d40030500501c0040010000c0c100c00e400d00903030103041d259541440 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 26552604 1250 26551354 26551391
    0xd0606120b010906050a0305100e01020702060d0e1605030a0f02060d020d0b030606030a2105040513200903100504020a03050a030818030313020105090f060412050606030102040303020309100e0306040303 89
    0x3038000c00711b8010030400b0620006074010110000040001d00580b04003887d0701910030060080d41021000480c1c6014032407903407001c5501c980101c00e40e26404200300a2600c0c2803001d118850303160b0b00c00440b51004c10010482025044c1c40201403a10b856100c0740358900303a81150f688451002c2d9180000c20715030400380301d0380741d00280c1103018050346811640d0341c004607403101190b038000440150b50320700101d00070f50440f405400000c11054828330028280806071078040c1034900700c510780000078940380c0182e20a0b00c5004000034086e22905100d0191303c3d0007000014010703a841604800700001103902400710103c0b60b8025501d80050b4038080024410102c994031104016900400c10085010300c0da201c0e941c60154240313012580e6202180000d07041c1e00c0c8070f6468a5100100080010350340c0000c010b000c001a01c03580507640c071561484c0c2054203e008901c000740268004000d094101e1600501424420820342006601090144082898400115002c030003290350384210707607202c091009 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 26553854 1250 26552604 26552609
    0x403020906270709030209042a030213090305040b04080f0d050403030f0c0201030e01050906070e03010501080307020616050307110109120201091701200904110f090d0606120b010906 80
    0x50320035040c1c0104003200c60380c201c40d0741140b1585440314404604a00d1145030004002c0d50003c2101c602402e090819118441c0078010114205040c603440340d14821a000c401c07412030b82c005000001040c4409600c1c0c0c007034071407000c0031810007400300004150740f26040081c00103412250001c180381004a81d03018944980071142809011060004000003030381f000d1000f40403a10b620341070008410900c0141c002c1c04904410501c0341d404c1c8404c100000c44006012480303585130b40e45101c0e500108005040c01c17210f00f80241c500a410412045c00981071040c0107021141d140401d80c0608006c0351249401e5030002401113403140d4103604403241940e8440303540c501401e01c1d00085079800740603500192107840b0750310655030044488205515003a07400e41c040544001d03645030b1011b412019010410f140d9005040b001d100354680078080c280c0881035030540e4442e201000440345040c03025410090340050912084802a03180d03200815820012495021940c1c411856942654103002608050311040d8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 26555104 1250 26553854 26553859
    0x1080103050309012a030c0c050a0e0f0916030f02011d060319150f03020306010f080a03050702030304051c060c0e0105070303020706090206030412080702030a050f03060102150c0403020906 83
    0x44018400315501104484042509091186603115040384080707090300303810595551020890850003e26420003040c80720980f140d540700c3c580545803400c000c0180824080d00d240c1481240000b608079048018003900410032404680840d81031640a1785000d005800848402c1c102450400855800000f41c2551106030348040c0b4000e20000e001c5039890000420381c0c2410748240c60002c3c079400c41580010900c194200d4601005500c41040e01d000788203501c001c80c001c0c4221800010f04501e040c2c07503502079801c0c90b80076020300c0d9441d03201212180c0211600b42c2e0300d40070400c000509a994444501d00d15000d003040c66003c21124207100c0c048230071f80c80003132090020b11894100306a90241c2294034050707041c10b00507111a524240f10004118400e0025085580003080c0001c4c004c114080c0749402d02e45a46031025903072401012a00c90041c422030f8000b058090002d0f030211000c01020703540c8040184105c0d4450040b843c2103551108080d61030042c00c0746c00150500c10350503c0044c00380c1c041c005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 26556354 1250 26555104 26555117
    0x2b080601090605030a0504030c0602161103010603030c0201051b07090501031203050f13060905010e0a0b09070b0403020103050403020313090209010e0103060f120326060405090c0d030e01030609090b06010e01 91
    0x10b000002d00144001440001d4141c2d0780d000260405006004c03856010360059400c648a44e560300b0384007048031070004241c5680084800d03480f01031405005510540343d05999500528909500550f29500320481d500e50b11040c8035040100444100a480001c194800d07010403d54914200802402000d1009804041c2042c0401880e4151401d01c65040300003aa11001642401d0078010020301c16508000c0040d424030740c0c0340261000c0041c00003c001d0052160224540b01c0602e19645c5040c1407203072004c01e09040c00100301540c000e82c412640180a030060300e1801c5c3c4540003407014188250821203014ad800300b80144a540d1001282d142c030003007802c0c208001414001c40c484180350921070300c62401c610b000f82400b00340c841c20316407058405807525020402c080076407c030405036080307581c81e010301e103414005083d03040005144071403041c1c06001c001005005890072224280b0420780300c2d0501d510341400003440c10240c4a00803009004010100450600c0c00005001540c000511410041e9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 26557604 1250 26556354 26556359
    0x131203140601021c050c0102120a05010f081c0302070606120312110408030301030204090204090f03030e010c0306030803060f01020f0f15010602060403120f06030f0b090d0503070f08092b08060109 86
    0x38041c075107078104d1242d0706005480d250030b03452641c064440e41552404103001d44040c448990a60303000503041c1c0300c4021000da41541c4600d01d1a60300da1000d4000c440e80c400d01100d140c14a0700035070040410600464011881c1078907184c2901103054104401c4000890684164820f06d021f84502e4850740c8040e1190340c50245458181c03541c9020602029104176910300c5600b08540d42c0390720074420568045900351a130103140c140a8010100004059071315400d0003138184c441c078401d20684050780da02105060a5413504000c0c0120100c419645a0651003842c4240d00b030f400041126290002d000c0d001042c1c4081255443c014440701070b4080c00641d84284280000aa0001e2000d1120444054005810010b09120f00081c008503400a0300304c65240f0f0014061205029031f0034820600203048510300d01c040034044401d44000c070382c0000041c460a80c84032000c0d20030110550440030314411503031f010740c0c8403410707014403540100001c1401381314074500010560050741d169070049003420401c1c0000c0c03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 26558854 1250 26557604 26557633
    0x2060907030201120906050106050a0906050910050711060c01020901030b0d02030705010507170a0309060506090105010e12030f0d020a09080d05041401050c01090302101109061213120314060102 85
    0x103035010003410b0081d0003115420240080c2d1203007020541200f4140703d10350f950200980180d0010110300002a6201004100396005404980100101905c0c264448034040b00449031600004001c0f81c41c4005442103c81507a41c1501400a020310342000603036814020b4001340449980e81255800781d80c041d0344450159501140003070840e1070a090035039440721300d46482a1420052107000200758030106800403115459881040d01702d114000800890319410304202e005042440745a002444529890040b4189128183c0c030344405042142c0c1030040700380360785845801800240c0309260b8082520350b409a031009142c0014030040000d00800c0422150007815846103004a1202c0c01c0240008003141c4d10510440d510300014000821100e0381d24078009450f41c141100c80b0140c18100281d900200c0700420895011903801040e04e1302e404c2c503a07811a0380c0024018007a64004504500c10700104040a46500e40601a0307a4009098803150041c1c8100c401d000d0b25003811580b09501c00507040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 26560104 1250 26558854 26558863
    0x2701050412030e03190c0308010b0309100f0b0303031504060f032a050619020706030c02031e090909060a0c0305060f010809070503030703030605090106050f04030b0a060f14010807020609 82
    0x10885160224810303110340c0f07809240d4407071480001840503614941c0310105500c1014950491300c00c2c0c2c2c03011000c0c1d9a13446c42c50050301003035407901c2d01c1c0d811007400e000030300400703034402c20f824600c41801180406201000a0440d0000c80c0e0300c0d03030355040604020000e460140700e1200030301544404101342030700319180c100b2500088180400601c901d840c07000102211050b44c10018030009105a41e200c070700d001640840c00d02100c3e05c60151003402c2011034076600900035022481c43e940d0081d0f04080d61903a10540c120f401d012810722141c000c01401499440300c03144144240c2040380100014208012010200d40201c2080002c1526080c10700c8240d80c0d4032542c41010301824602a486034690800300c904280050340226414400000c2107405c0641542211041360710840d03681044d6030341c91005691500c00c1c480c00d02c4200808000a0000440001d040f0b60040c40501001410b00e4480902400140c510b411030007401c80b0341c900400966030301081c066404440c07803002d4580e904219100f250354 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 26561354 1250 26560104 26560133
    0x50417070804030b090c090a09060f060812030a06081c0906030903090314010e0d020f01050c0307020a120c0503040905011503090507050f040e01050f040c08070303170c0c0627010504 80
    0x401075184017050081104101d4410b00500081200c2c07400e01341510003100804208008903003060030440c0d008002035a9220360011503d010000e032043c5106a20020709540c002031901c9000c5d0b07554040410007603020400020040b9280781c42e19144020088043c4c44a003ca50180b404c05041090340000130323034051074000441c0e0f84120900340d02c03250031900c0c9000d0401e107600c0c01903d10558005545813640005c4240481c51500000c000c0c0d030320b0321030340c1d00d06c071307220403111078001da80404901030010300d1a095170707244651036207001c2000d42c2299948a0a40d8026403040d03000c0303621040107000d2002c1c0074005080c25542820300b08542d109981d91280c8070f00c480e100301c51141200e900c403031120361280d4000c80402d9070444005c114130b103401000103034440019036056400305006030b0302154610000410100790b980546551140c01200380542e0300200300141504000b1006002c0b000034103404020840c060f00100390240105030b079000f1049069580024a00116814001440003044502c441c0c04403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 26562604 1250 26561354 26561363
    0x110a09021603030f090b0709140402030c03061c05160611010c020a03050307021002030414060105030613110f19080f0313090b0607020d050a0b10030b0f0612010e0105041707080403 79
    0x40c49140f90207040020401d8550190420f032030802000107041d40548d0380f5080d01d0800c500d540341d0740000c8003480101e0100700c42890348204100081207403441c1c01005001d122010b4104080003424540c5c42070b0a128506295130320100103007100703102c80c5822201140c28075901030000c00401c042024001e65422041002506008000001c160114400d0041f2a980013a8500030746d40c074140380c078107802001d8041100f041c42d40100380010800c1c0c0341c0440c04600400540c81d82016000e05520341d010048110401c0651103604e019808a058541d20100c41400c08040c0304024441d14080070181032041104083d409600204614101c0c414032404000070b86c0d160300030000715503d9101c00b01d10355200c2c141011f580b04420000160821200046135000544100810b0a003602e40b40707803401499a6034040144010203010000c6e40340c1000661072940080010040b541e41907009503140d00b1601170740b20b0f20f5201e0b51944104014080c0803200003801000203800c50b480c01c94036454405d0341e409540002070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 26563854 1250 26562604 26562611
    0x10f1707030b03010603050a051002040308040902030907120506040501060515180609120d031a0a03030309020f040509070303081308031b0d020d020901170c0405010e060c0a110a0902160303 83
    0xc51061181c0d00446141c0c101400821003151641000ca54541c0d0144040711584280e042e003103552030060081e50102c0b5440f003006400e080c00c00800c030000c3e41004100d00340c82c1c0329003480043d03060340e001840501c0c280500c000d0190350400d420601d007510442d4102c2c900501c00030008a200001c554101d41c08034450180440680d0044400240306104030500c0c41d42c80568009210174140d80464082564000c5860070132603d244220340340e0000c1000c03099940c2c04151001c0410209000f5000038214607c000d18000b010000c0b40005421110151212001e961161a0600130150407000a680000c0c40e99654008407c00e540d494019100041600c6a00e4040034154902d035540304003905c0d1550644c0d00309648601c0002a44e1009402c03800750b040c001411b00724000500300031525218000c0d03a420456034641400c1600642c1d07001c03d004050f0340c000c1c00400900803544000d2000f00701c801d224500b201040301c0340c901001076041356504119426481045243c1e290460543d800650a90604021 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 26565104 1250 26563854 26563861
    0x90c090e0c07050a020d0503220b0706180b010e190902030c12030706020f12070c02010801030201080c0405030105040803040b06010531090c0807020106080a02060414031216050606010f17 82
    0x15030905441c44c0009401040b207a00e80c004009022003d001c0000c26030a880710542a60404406442510b00c10700c540014108a2140400c04542000c030000e4205030502c0d862030a155035800384500300741c2c4100a8a600141030044100009040003002c08110304d0901c100c0080c0d400090b11640c00301d042030b01c03401c140400c12880b90801e005642495401c5181107403a80c0603196841c40690020b24481290350380e6900052030a0b004203850186150180c0d1007914681c00c0d03038015919414083c010703071070a070011310002803030b47d4090040600c00c0e8460b45a16440303080c54541400101405400e040c14002d090010000c00d400808104441c8024406245040910a12400340440168100300400d60a0080781c44442d500503113010302070780f000e42c02089220307596401241c807440c8a90000398025000c1108100c8031558482602d03100f034000f015075034803000009103d070a95000501c841118100d0000000034041d060000700e600407020f007001c07101d911410030b00078004118400702032420040c52012 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 26566354 1250 26565104 26565113
    0x3021c03030b0910060320030a0f021b070e0a091e02010c060501060314010503010203010807090203060f030d021e060106080412120c0203041a04060f050c011113090c090e0c07 77
    0x1004500001810307640e550b0070210401c8041c3e032405d00522001c642400f81e039940222100034400c4460f00703081c0c4024110b44410b130741c10018009170640459001d4007407265852000c00e00342c2940001110b40000c0032281c0c07504064407403202c4000c0c0100041c52501001001003030803a1454445045582d15030741a005e41440142c030341480e4024042e0046141c0b00000c540b0b01e405070300040754034010003030382e0b511681d0b01e800300360a070312003402051150340207548100028040d94010310741140e401801c400d0034403840c101081c9410380b44540e44005078050492202080f41c04c00da040001200340c00030f001b65605001c0d000c0c005c5040500010034070000180d412280d144035501c0c2c5400300054500610000500078402542c07a0810300a03070302c00102c0700c111864018040000c460441d00240c4480011400c1d58005541c142c0004032040c10554880c034001c5100007503240100b10041c0b0121508484a0518002004031174603914094188042c40c1010f10901c401e8100f001d81c800b44100d01d042d981d0720540760 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 26567604 1250 26566354 26566361
    0x1603020a080f0901110109031e120c0f0f031a060708070c08060105030c0102060417031b0412110d0f2312030a0e070b040603050703060503060702010902090108030403021c0303 77
    0x80182103880007003090710780507040301d0003000603102c00d90780c40172003c00c0c12620368200d0f1801c1c00011b01044e80d0b00342010705440e405003801c00254440c100306102c6000343e03944d1001d40d44480021302c001390045018541184d003200c8401100c1c082c07468100130120f680c0d0b40d00d540d034446c1c114a9a06c242804a0144100002d01c012107620b0b66000e0702454515694a0b4100e551320b6080c011244640210200144154800100c0c2c5109507044288400809001091043d081d8000344c01c0541a40f07641c030b500441341c4117810003440140300d83c20480704900b0703da040c101c2d400500c092985100f140d449d0810008152004082c0d4403080d0041e14192440c1c0a0444112081c080103941480b02c2c000c0719108540700e0780000255224541c030490034014070142802040e00d898484c01852a000d400303101c10b002041c420751140d503001320302d81030004003182c9035400240780040031100200141c3d1120316000c214100090b205004081c403100850a26003158000780e142e844a640c0304903000c1e203403404030050612a41 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 26568854 1250 26567604 26567623
    0x2130305010c020a111c110d20090601031a010809010618060f090b0d1e140a020102070f06020a030309080f0f03090c06070b0604090c05030d0201022101050105160302 73
    0x5000300020030303140401039121420a10141c5e503245481c2c0002e034103802c0c440994000740c0707400f149820003d40c50755250070f510090f40c0350726a00000451035480c00643c078041d02000601c4d140308140c00ca4115001004445900101100e042608208180c0803040c0b1a100b0b5801442090070100051b81e20400789a0042500d03a01600940200900240103d60710354019400d964620b440203c2c2e042e01c45aa402c00d03141d604408507040121800705c5000b1a600031000341c40300810b080c482c2c95000d0151100d2030303040e00ca12400c900c16007118103c4d0317046680401500c0000c0400e000f42c060b64038505007000e916100e202e4405024941c8600070102084440b178115041c84c203100c1c20903511422040300085094004a8101c2c100d0f11400030502864039040381074500c1e80358000c490f50000d641e8001440050803902c40e089070900f81180303001c00c250741d09003d4001000e8030780d13000503100c98020380d10409445001c01d101d041340e01402e00610181e6440802c403001d80302c2d050501c41c41044d81d490120b1a0483c0c07031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 26570104 1250 26568854 26568863
    0xc0c0105010510172a09010206010b1603080a0905072409050a06050a050705030406030605030d03090c030305090d0b010306020a1b0c05060f190504090c02030a0e130b1207030501060b120109021303 86
    0x21801400c0d09485c1000c1c0090031020fa003198420381e2228559029442603806154011115810600010341708003100f50b40210304020200712841b850746d40e1032900c20790707400000103094503103441d8902a000b0400ea5521702200e281114100d450000401d03020040c82c0505c1041000000e045101c1c03a004c0e03002c640c17889510204032541da039502c580080042c2014001c040c4203000d00032005496500c64002e00c0c101c1500078203a0102a803a40c0c1d419111684050307202d940200c504c2a2110200d01d08860880c000c5010384d0025a582d43c3c0400010044d0140c1d20b1039500d01800804550041201e9400502c25114203546141c0d6030030808007483d03250300a001452603001014000d020030203900c00084c00448902081c14043c0b0113039071009907102e014200f900f0b030000d110034015200d54600800c080006100d503520010f000c040c20404542c0350015043d00c030b501c03a44003507020002c0200900c1840003d11852002c2420024043c2440740b40c0c4130184a20356130a9004101c421800d1154000a802147e20 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 26571354 1250 26570104 26570161
    0x51201090509060903030103120806040b1215010f030503040b030c070209090304090606050301080c040906020c1504140703020619090b070f110102070b0403020402210c0c010501051017 81
    0x10389900c0406484111810321481c0101c4010400080740001984c1c1a607602c800c28070004031032001c08803119070000b0504caa0080d2114048100d64850000c041c4d4106c9007000a024121071041d5840320242e0180e111700d604580c4081e0820220b840802514144d40200180e242c1d0fa84031113003040c00a0054540196121030440284400300c1c41c000014070440b00000d405108560b82c403601a07902c3e001c00d10031307000b45801c4041c10410600d010303840528031610400e03005050010307a44016140c81c1c4808810006110000d05210900054070351258441c2c1500c002084046d0030760340400e0f1580138144100e01075550f08441b0b4200c10b40200e03040c20282031403621598032510a42000d00881845160a17101849428113401c150751011501e503082d06d4001c049103283c2461942030100070340c04a0118180e0300c3c6407128141400d0360529105001d01c8569070266145d6059145103401c448060344000d11400040c1b0701d4510a50308100356001000c0210025002a074444108039058101d41c0710b8021714118 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 26572604 1250 26571354 26571359
    0x30803130c060207090e0307030e060903100c030b1906020a1b091a120c06032413060302010809031e0f0c01090302010204080d080903040b160807080304290109050601051201 76
    0xb4000303048402c98006440500131a5048060706e034803441801406000108560341c079005505000009150240000c1d003114a103102d001c80e41e6040399004101b81c0000303a2a4081c404807460008130565a4090318580d101c5510b00d0040c0103983c6020300b48c0010721414511502001c1c502c071150442008250241b002d021a103000c40e051140c6450000091f44500b030307411182c00000c4d00020340c2280c0340c1d9014000c3c030301d5504c0700c601218407203490b03c000c07030072041c1f0020404889403102e2401d80709400d104400031940909520005d811480d00410950144c0d0040c4000404c5503d0010042000500e030b0701d0550f80c03030340504c00c904164410141c141c5525803c20910b20205941540280308440d4480700366082c41040103011984500e0035542c6100c240d00900050040c145000e004004401c2c0c801d24070a00010f00c1d03980d911968105039415103060001104100070301208940611420300d0140b210014a41a1401055210010700815005d0781e5505c00007003803a40107204a8060078640d200861940d0b9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 26573854 1250 26572604 26572607
    0x6060609030c0b130501080604020c0f06060102060f09190602041e0821030a020a030e07030308090d030507020a03080603010b0d0602042102031507120207030816050a0207030803130c06 81
    0x1010361008440040368100e00055842450b400d540c61a0001c00f1021040340c507043c011031b405035000d040c03a5449a800c112102001004108503883d407201c600151045207407840c00079041401c0100607803450304040007044042c41d00441c55000c1458095000741d4138480703905008000740070301d8001c24802117100c0500d000c0241121003000c11640a58115a14202100380403060718a880344803000341d210900200340b00a080b40c000e040034800030310f0700081001d60f041144c3d16140d5030341c8c41a800f003502c0105001c141c500920525080c0c00a0342010721082c100501c000356224810a00a805c0143d480003040292b0f80a420480c802100200340008550b214144000250300c07502c1054540318511701600d10224100425520803500200542342003040203900c1640e6070300050840040091580b10102e000c1c5080c0f01408219001c0e6880da841460207002c1803250f50607099000051200070301c014403103d640040c180301503c0d481098142c51707031244409101915070680000b0f042091a04c0d004ca4041d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 26575104 1250 26573854 26573867
    0xe0f0307051011031c0b0a14010e0d02040906020304080a080a1b0f030e030a2d050708070606080303070305090c03070b03011e0801020c0c1c080f0307020a0c030506060f0a0f120201020a060606 84
    0x4110031103c2c0c7c0c09103583c6820201e461780c1c1220144d404200041c010034518544106481402030001c1c0010440700c0140c0c4d5500c080760300440e070844410402080009d2200ea02101d01680002c208904100151351020020030091522400c03600304030a482c1c2d1001468421741004d1134420300070045940302c2020200281084824a21008040f0f014501904680001000700031102d49140c803030501e400000d032030311140380e48110001d80d990341e221040081e1554007080110711811040d81c001805080c010401400c250212005030f01c40e61200c0001d201003c11581241d045411114212151302c04510b801802040168041013044d403010a40385201d1001040d0540303a1034003140c8880543c1c03410001d4089454200201801c08801845507240c0341f241c0344001d680004540c0101d039400b0b207080e46c450a1191107600201c0d580d801c500144541030400c00302c2800c1d544401c07207039503024a0074400e40a0303691210740f01e150310521903c3c00b0501564000d01145000d142c02c4541030010b95150140078080 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 26576354 1250 26575104 26575121
    0x1e06130605091005091309030512040303021305040b0907051b0a0609030e12100902010504090e0705040f09050a0f08040b03040602040608010b040501080f0a1b0e0f0307051011031c 79
    0x4466880d168030f8158030420450b501070713400500194211058610520003070288080480c02d2140030400454403404075000da0348650f1090390003607503500144210302000d000584c8164015810908060f03126942c80d03682300c2e4425001e1804d5074071044c3d07104030816290b991000b01c00b0b00340103c0c0c0c040000e000c0c080e0401d40c8080d00075221300d0000c0c4e40c480e00f8040740369000071142d403154000007020324181000c0c1d0402ca1042c0e0052600508040e2100d45400455004407400303001c950052004002c1400c15008101484244100802440a05466050b1186c180e8040200003406001906c2e0803c400c19080c2e030064800456025128138080c50714000950050040d0808181800000104500340c0c0044070161001a51030815940764821000c0c4800000b801540e82503846030704409200c8920300c03c0241080036540c0b03007001d048400051010950989100c14026082841c050145450f80703101086000510316000d0104241c0507680780c294080c030110071600c0002402d0801c1c4101240c1c2040e40e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 26577604 1250 26576354 26576359
    0x41206050610020a08070303090c0906120b0c0f12040203030d020c07030606050616080d061a070b010512190501020c0d0c030e0102010905060a020f0415050a09080303061e0613060509 80
    0x102030035001083e6510300c0c003040000d0245500300400000603201e900b014076200d104100c04020340c1d031211640b03015200c80760800c1036001a190003030030520441003801703038200c202158080d2400281e40c602038030521400c40c0305620505880045400c5480410803038400030744a46045417224030407a0a80c0d103444080c881560a5410101d0200b614074001c002c81d04619100d11340040503e0041c1d50b07060158010703c0c1e00110a90343c0d0382000800c01c84050104c6000003803202c00315694a418501900c041c403041e000030380140c8100346c51001c400000640da4810380d00010015080740e24a141c0140613102c0d05064004074080c084c0400b000a401032544a081403082d16440c941942d2034004a080306c1c0d0161015140360b2006010407000741d02680101101820700391440d01e415201c00140c0d034606109086c0b40700040c400284800500e81c00703d10702001d08400c0d0042d601c0d5050020003e4981c1200081c03110250f0740004910b0310700e65500044400b40400e021011203110754806000d00190490141d490 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 26578854 1250 26577604 26577619
    0x902040b070218070203030703050403030b10120f050408090405041b1d0a14070e0d020301060b0c0c03071a0d0603060f0c12020406080c0304030c20130203090a14030412060506 77
    0x2d03c4840b0003514401c4803140c4c021070655441c20380440160201420507400c0c15a500c080840c1902d0f20050180c0c1d00d22070b1b172039111622503035029000443e140718154004052a00c002d0100051425040764a0040d084802240503242c0f8140381008119802204001c1502c5600c00216101d121a1610342c4506140e0140c509540310400d010540c2c000c00015400080030b4800035001c240280900c80c03c0312000b4280c4030300300720705502003402c44230a0b41081900c80c0000c604540d40c01d1040210600464084d00508016440c0129441c480b02c4c181510000d480c9011030282c43c80c105ca0303070010005540000003030200c1d0360f201d0009002441040300044c00502c41c1c001e007121080d8203008407012114107030355800042c1d9649001070301941020300210204084c040174900130075496400c02a803001090303200c40c1010080000c0200b05d00c0d4074105260050700500070044400d4001c2500c0d510b16810045041202a4600080b815803007950402400d000500d82140c05101c2254451441000d00b0381e20300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 26580104 1250 26578854 26578879
    0x603140a050c07060c0302042d05180c030c070215030403090915060e060c0a3f0305060d02030d050a0809030301030b240411070210090e1803040902040b0702 69
    0xe80544004075521031101c08208030f000002103032648000305a0100d07280042c00d05844807100c4085c0b241d210349111030a00d01340b40d140c803a866440307100401003a0495480e048881074024003841d00c80020417a18502d04003200141003480c00804075510700340e004244880310411078803564842d4000750303400c0e40020400d030b9003c64281024400c08036441c3d44108003034256072806108a43c80b10118003580d40202d818040300603404e100b0828481100c1c4a0307014429110410105003015a400201801646103800d908207440b108400c1c2e448207a0186240100e80c0f81d81d1040460340b00b414441e0300039094070484d401868440d070b111002d4440001c0c0ca07600d100881d2a01c40e03600741c0d01d000c00c1c0009019440342030042003001ca650018400c0c0c90440c2095105045011000242180d0607000c0500e45d4403000240e080461a01000d070000c540c4150504401031401c0c1f01e0018580c4000400007030780454041d044400840c020020b481c010590440295035a54561032085250340012004900542c11903140 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 26581354 1250 26580104 26580121
    0x2010b090705090d0c0b0c0c010f0806010f1d12010609110408100510090c0503040215070b06090705070c09061502030301180203060f03030304110907020c060d0509120301060314 78
    0x10540180980e641d00c2d41000e00410030004260f039034800484030400303910700c0000c10a06040c09000c02d910120b010784126400356001401c3d516140194604102001c802c00501d42e03007010480015003082d152041041d0301c1891000c620880840d151a48074200a9481c03c580405400c80010b40754110414000452600811459401140100c0b11182c110710301000801c0f00d194042a8040221041c1003000d40d5140040011255941c9030040080d0000041005506060300c041c000c1c506c00503441840c0c402c454440805036440513107954403540440000c22802407040003940d4081d500324540c59407246e81d03403940bc401060640f00d80a141c100c0c420304207052900110a4134106d030302080c2010402c95a0528900c000d6000038117050340811101069041074400708051440386214441480c3c0c039071a107000700410403030300404040855001869560050311040c040e5050000740c1440810f8989484810600b082c0d01280103910360703076011000003007050345070308000d480c02d800e44448046170712000714 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 26582604 1250 26581354 26581369
    0x150f0212040c080c01050301030611070c1202010905010c050303040212011b080610030e03120405010603060e010c0809030a020304060c0609020d05060a1401050604051e060a0309020f0306010303081f03020306040308010602010b 99
    0xa085c04100107000402c0452000c5e08071402c49441000c3c0360780791842d0350b616000c4030f442940007183c0440800d03850100719604022000094102400c0c0114055456610030350f60b4840100002e00403501c80b500e20840031425001491102c1c02c0d50b2400803001c02c0040028442c10381251020300c19a000c00c040e00107103000c1e1159150310f1440320044c515010360601c6e6114154009803040300c0540d80c803140040031642e10b2180550801401002141c046402d01004140f640050428030041c0c20401070382810a800000300e90440300700d82020502042507082c15070041002c1c0b400a0b401c80fa1407501003041000115075039108a91402c8200301110101c0301540b41310b8024061103402c844c2c104428056403426500c00d1107002120700700d1098020703419001c00d0b0b054010b001d508012a8550700d00030304501c0c190301e032050003160940003400c0c95855910300500e2454054903950722038001c4001000300507421661075001d55005021543c490070140740040445809108030713001540307448640e401038501200c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 26583854 1250 26582604 26582623
    0x6050a180f020702091308040b030c0307110106080304120809040203040b01060809070f0608040206190201020a031a0a05010309050f03040303020c010806090906041b050301111210030b04150f0212040c08 89
    0x2d02c055040d585906c0726040709440d0310f0055802000c02e20000039450740c000700039849030f2001a0500d80382c0c00c00410180c58040b2217126142d05904042d801d010000d00042900d085400d2004803ea000c09d00d4209400c061140310203450308036000004203c28405c404003541e040310403503541c58100e80ea92884c102d448020354041d000f2030003441102044401c0c412203089411030300042c40c542c5172a4034000b0075502d00e001d9210040c00340c0d40100306004055014031a0071888110200c040f018140030400142c1c86150500540341495505c4480409000003040200051011001180e541d02e07141d0401135915074401c0c01460000f4602000203605041c503804044c014401c0d00002c001c1500c035691a441d51000c0790b4401628601e50b08000500b6540c240201c010340286020626a2003055100413120b15000400700c0c2e0070820583e00c10400107131078403911a0301541051035040c1e028130f0502994058660300f64000d03500d50003c0385441c41d040d641c650490060788962004800c841c0d464091a44070074611 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 26585104 1250 26583854 26583859
    0x51b0109030c12052109010804030e1e030d0c05060a02030711070b0310120209040210032d05070e100c0302010216060e010507030e0d0518060406090612020405060a0509010306050a180f020702 84
    0x240074000c0c0a5002d641241d2704203100341041c0c83d0400142d03001c513910f0100440c286d01c103101c806896144030304041c0405600e4980900d0070b0225a1001d03150190740b5103000c1c1a0107500c41d0f0000c0013500444c460f00003400c005003c2802d8608280e50303a00145070f01c0c1c2054500e100c01841c0031000040c2c00d0900180403405950240c140e00c9160355680811040d540c01000440038180c449983c484070301041d0b07684a04100300c004d1032104a03000c100c403035822124020030a105011040122001c5036554010542d8001c0703139850445081110f03171078200c0c0a4024108501e402ca100f0390460f1082000c0340c0c00115442d59404002c000360795510408a05803a0a07124000c2140c0024006001c03040c42a0b00410244074683d030240244482c62020885583c02a800311001910040302403003d180e01c0f440d031900041a003d001c0d41440c0c145400903d1b5071292044120500100090a0800764007a400034001010000c1070340e10300f140c1d212942c00b081408007889910362881c2001d00c1040428600c26200b09907000b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 26586354 1250 26585104 26585107
    0x70e09010f060509040f110405012303010911130f0c03051909030504050d06021b0102031603050601020c04020c011e0f0f05010311060702030f010e01020d0c0c051b0109030c120521 79
    0x1161100c92507444415801c4c1c442c1404041147c200b501c82d401118021315459034020820f440340300202d06d410170181002e0b07100b81d04105400d00864415841040d110300215aa000e005800c51802e00c0101605085c200368030b0b0512005141550701940090b102d00d803005103410521080700c0b81c4e441200d050090003000301d24140b20a02090a0851000300c1103071080000514000880910381018004021050300d180e4001080043c0388d8070020940040c4441814140500e040010000c1e488106000801b0301842d0b01099824801100350000104002a1122000388004041021001d8110481c40c203044c0c50400003114241c40315803062504807508104070004481412041001540c00303100309036410b00c05c15003100c0c3d1014080c8901000e00844400040e55135402400880c203480140400c2e00c01d001401d01004046000841c9000c46182c0360500d440e1481c1c0c5200040c1d0f140d288541024010120032107000c035000000003005000e150040f421101d40103a0440e161400701186010720022400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 26587604 1250 26586354 26586361
    0x906030c0909020c071205060604060b0a050f03060f0405040f020901060f09030206071b090207050d09150822030203040305070b070206040e0405030906120709050303030702030403020108090a05070e09010f060509 93
    0x2070b640e001d05207003203a14080c0c400256403520710b0106120f0f000c0c4162429000030003030108034a080e04c140e070010049001e180d800c01015400207030950150b00416284c282d0b00000007142941c1c0c1c0004031a08100040c002c022a0420f82400f00b00744041450403400307000c140001190f170741c2c096000100d1409565480e616028155800c2c032140c0d41095070700f2078419103a005426a001c0402042101601c1d0a041c010b03141d600c00c2c100b4a103404800040a810303c014500284250300b81c2002d0403a000c8810f0800d5005c5882c2c100182c50003110100594140311240c00540081650110040c021607010340200c5001c80c3d03c0e01e010300068809c0c0301d002540000104802c01c4144607000c0c03e02ea00030301500640b41000e02d4080030842581c05110721483d40c0101c5e40400540940003400c0c040a450309400071400d61404c2c50300603603640320340d000203070511001d40b00107501003c0401c465501254403405445110780e0700d414103151140c065500d10300d40e50038020200a0082c542c0304450444000a04e41c403800d49 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 26588854 1250 26587604 26587619
    0x60f0601180b0708070b01060c03120b01080a051009020f0d05010f08060f09030c0604121d06030c1303060e0f06090a03020d030b01020c030109050601051003110a0e060c0a0f030906030c09 82
    0x348201d0003111148000d004445c08944400c440f01d000340400d46a08045001d54a401090170090300440c1c0c1c0c00503c3c240c1500c504e039034040c103600d41c4401d00c0d0b00002007940b5008081254000d00d64800c1103141d00026100341d103080034801600405015803410b000503604c071000030182030b401c0d020303281031548000000b0740010f200c00300191b0842a012300303403440d08d070088080c241448001c5038151600f00c0103121a0104507030080d43c150b48210410b065101d5510010002000c501c0701404000d000e860120780c040481000d02c1c003900095600071420042a0480d0450035207a0001c803010180e01d025800015a50100c040382034058198581c0c05489000480340060b801442355608850451241c2c01c00f8142d140c400340314224985000e18000c01d920342c07400c070410540d682841030300000c2605081e4141c040312400d1065824144040c00d000b050503010f0700101344c440c0035100d43e0711034500c681c0c0c000d80d0511111102c0408002d02980e01c904900d078a4440c1a025140c080346841c000a015020402019 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 26590104 1250 26588854 26588857
    0x1018120f030c0c030c061e020d0c1103010b09040b01050319170d06170105150a03021503062202030103170702030307060c02030c010204030503030a061d010608130b09060f0601180b 79
    0xa4841e4524400d00750b101c0c2c4843d141c0201da60007110101d46006141440852000321f410590a101d00c01050804c540c6035008107003910410b801016900c2201540c0d000755000e4010524440014080b04906d141905159101034402c0c4181800380c000c901c91a10081490035491600d160051000f404225038103403980c40c158810366800f041d02d9511400030039401c0c14041500c421200c1c09001203071a04002543c001c01d04c20054095119650420003000103844840b0103114803141c104080d40c0740c0d510040890380d0900a424411414801110303524060304003580a14141d9000b104040407005c0420010029031149540c0650303d98824009140010b46a0300916054413080c41500d0a0650701900c55099070801d800440c0c007030b0008070821100c03035418450b110040c403403221009900001c0c48028004410180100303800c000c07a510002e009030820350018440f0b298400f00d01200c500c0c040303421035203450003500c0c03400b004040980803610640c070541203002d4082e400207410300300c3c918001803440a03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 26591354 1250 26590104 26590127
    0x10b0304230309030106080606010c0318050307030c0f080303040c0302090a110d020408010b0604060c14010b1306030201080601090f05010507030e03100603021203040e0112060b1018120f03 83
    0x24a40c0d0580090801041c00c80400c9944500000540d110901642010300f96020b542081d403072948040b041200300da0b03000b00c4289001e038150030400621040704400328030040d003d800454140c4141c090020070806d2410328001100e0000032008401d40d00e403044983c80340300030b4802038130ba110070b120244094640080c043c2c0d0000c05814002607003904802d50000c10350014038040410075408501040b0450707081c044c82600702c0c0112806031515081c040c015255000d903403000303050703403011620040610300254010030034030300010312107086800001c1000000d0609800102c0c000b03400c49000c28029400b55000405a030381d5040c0b42c50300d13903003001c00441e13403a0400300003a4104084000c2d8120142c030107004508543d6000030b80440d08600f0350050203c008000240030740c2c03a030310401040240e00d800303502c25815145195203150014019040c400040d1124448195100445041130348006402c00b1104141d0b81c1c1c85003000c01c5480e550301300c02c489200301c5400a4540c1940d480c0d03c000091054484500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 26592604 1250 26591354 26591363
    0x7050f130b0409030518010201050103020d060b010c0f060203040606080d02150705071e020126040f0c0b030907090c0e0d0206090402120106031413020d02090402060f0f0d0b0301090506010b0304 85
    0x780d11551000141c150b60b6034003000d50201d4000581066120300011139061807146c2070000303209551645d404165542d14030b03900034101c6075441e51019283d030712801c8590328881e00316180c4240d0040e43d041c050020b42c016101290316a203050b20000341542c0c0800c152381d11115035006070101c5002020b00f03041c50503000703024900b040700c100100c2001408420350501110341000c8221800c261a100240800d000035980e040f0a01c0004220054802003003c200e500075404644000f0f984070340e02c2d08002c219050341100011580103c200030310048006100001c0742c6802c4800d100080700c0040c01d0710041078000500760003080303031204200941015001400381c802c01410040c40c02030740c604900c0c2620000e0300650000b030740759840188c4040140d0800782d00821080400b9290402941c0014480381002200a0003a1601c2000405658803c41524020350804400b15a40d00116140001c968081d04800003641d03d41000c0403140c0c241403142c4140198800028015039081800701602034000500898 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 26593854 1250 26592604 26592611
    0x804050708070602071802040f03170d0c0c0201030b150f031302100c030206010605270409051006050102070807080705010c0c03050d0c020405062d0103060f0305030a02060907050f13 80
    0x141c400c800c0040c90020000342c0d020b000f10f00d06015100001034520400a84800c2c0140010701c056161000003c045035884440d681c4c0301da8401400401074020401c0801500e481c00d10740f00340d03150b044103102e54524400da800300881c0300d2040070044054002c185000050390103105803010740c0481002180c00c207400301d804900c6101e4980c0001c0d8000c0c409002000040c50f0030340b01204150f01000301c980903000e1420140d0804001e0050134075800d16109410000440d0004407040c3d9031a01e074004003005400c039058410402c14400b100d80074149a1040034010b2140b02400961410046800b03403c0d520302c00e0240c005645003200444240d245200c05031548944403034004000380e000c02030240450400e032a070b2101c1080c0303401040700320b400c020720031030251607481880074080c01244041090740400c40e0302100000740400040300100301d41d4000c540071108a44012050000001c050300e8031901550884100c1d55900888580b6000c2d1441155001f607040e00429215190142038011240300705070001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 26595104 1250 26593854 26593859
    0x17180405160c0203190807050f030903030d02071b080c0102070e0c0301030f030513150e270a0e030310030209060a12020f130c080106110a050a06020702060f040801050703060e01031208040507 84
    0x4030104d444030a41101c0d4881b00064010401109001c0501c0c203450b003202560070000740078046504c9205101c0d0a812840e40004c02004026164402500394499038450341c0c003944e00c0b000c100755600d4001045034094815014001480c150201060f80b02e440020180c40c1164039556036001c112503c08801c6040c0b00081c010a05890700c046100d2000300803040381a0111803481d0009000c0c1c04440380030038001e4000a012102500780003a07610107441d031a0051710416555911440010660406010000d003c00018007108090020121081d00c1c000c43c3c0326201e94641c001000f20305000c1c1d1094401142c008900f550245c503080b440560403400141074801003420311240441200c2043d1440c01c0407641d14801400505e51194444440d040800c00800c0a1000341c1c44030ba954812880008010580003c0e00c0411034450740300b5500e40031000c1c0c0c40030f5101c0d900c2c2c5d103516000c0c050860ba01d40c001707440c00000041200200c0c2010b0304990b0401ca5000f0740b1100d17800704444942c4014019110b500c0f507075600 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 26596354 1250 26595104 26595133
    0x20307110d0f080f01060c030f09080a1103010b090105030616030209040509010504050706050a021018020603010608041a150603090c0a12021306050603070c050a17180405160c0203 79
    0x30001003241e0b03075400d0301107803150401400440020b0421600190300600610205400c0501100d05e9038150504047c602c440c034404139072221032900460031030b00441c4c1541c01000380200c0d02c242401d10032002400001415428820300004c24403c1b903034036500c01d00110304448500c8a05400728180d5240142c50800300e40003040035140e058450164580d5030300c0810081c08801d000c518054403039898101d02d8102000c400950b540005004500010354941d011701240f2131449641c00d520b40d02030441034403517030360341005042c0400485044d0744d101100300c503018a0794180122140b0170844820010b021001120034415181c000400745402846820090ba14554031a80010020b0412503140400c40e0041e00c14440341c194200c5603c4d907440d082c00d6040c401a42c82c6410703030394010910310740108403c0c61400d0891508480800c05402d80a500710505400c0384103200400c0d0440313581904000c11130b1501c06020442e001201c4415540480c00741c0c0b0703074001d80f003170081c040d5007030004044441c9680100d04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 26597604 1250 26596354 26596363
    0xd1104030b06010206090109150c020703020a060908060709061b150e06090c0301060e060616060c03020301051005090a090f1418060f190203040305041215060b040302011202030711 79
    0xc15105a001da00810519603030400c4040c2d4031100c034400030b001046007555504804c00b584000755500540383d440014440b40b0820101000795001400170741e445640700400b4000c643c45001d03500560041c3c10018550f903005170100e500f25115a500c10104001c000720314010316000410844801c000c1c3c0c00c2440062025000d0071150121103005801c0c40c0c10030216451402c0500348040e8001d9041c4401080f011107c1c0c078070035900c6113040d981c0f26642c0e22200d41c010101c002942004141c0f500d410740e1146410341c16800f85050799419600304240c1c50846406644502074807020980c0070310403420600c40150035802c806800042c2d50800720ba58680400400a41c2104841484270401c2c031103003400c413089040100036000080540340c482c45040400c405201100c025203c400915000404281010301c40d000f160028100701102a458851500d02044501c00d030060120708107050071804942c040c0030800315405c8a60585815580e8031811f15020044d400c0203080006002641c214078201e48020301 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 26598854 1250 26597604 26597609
    0x30102131509030506160201020903030c0105160c0b06040f0216050c0414090601030f081209151b070303090c0504060e0417030103030c0809190b0c01050105190501050d1104 76
    0x18144648605010000118101d206500c80c100001080704001040c0e0100361141c0202030f150888491410510090f030181c8075140c0d0080d0580310025082c0c5030440306600841c020150f0081850307020220744022034184950440142c1a083c0c92000b05400c3e20381944141c0c0e0046c000e640260a044070944001035110700034006480c00d800c41049002d182c501445100c80340503118500e9601401c001c4c11071a034a00d0f050200815813a0392000c90410302440c4002c2c0ca00f8600701c1c0348688140d1620441c0030380c60b003214845003083c06a0120102c1d01384140248405503084000406e207081c2078007910304a0140a2482d825034100521000c0031505485a0155001602000d6441307101800c0910301004951894842c211b250701c000d000510000b4bd002090b0f154241c0c0103c4025202c1d600180012038800f4590103600c024059100000707107503045030014154112101008106e6682d94009100b04a42c001c03032141e505aa0900050110f98014000342c07400000c04032000844807100b00706401d080e0700c9034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 26600104 1250 26598854 26598877
    0xe01090f0f0906091109060a09080d03020415030b0906130e0303010902070c060807120203060423060f010201090213090c0e010b07020906030307150507050d140f010e070f1409030102 80
    0x900103210b12002d6002c0c62009040c840010041040b00e00303102031a6001c1d0004051241d100004e0181c103403446001b0780c1c4060031a540640e040280844805002075200d486500001d030902001f2a10081c000c1c81551243d42000c0e00364102070b502c150810449080c40c2d0f2584911555452004039100b4080014602808000c40300607a1080a0b0a00c10320304d0035560b11410030001c03540104940e180d0301009601003884a80f00250b240d031034500016001d040c4001c900c50b0340d40c00809800507106050007919026032003e0700c05204002c0d0030001242aa100003201941049201030b0310080d031038007035120340036150045401d102c10ba0f031250300502075a5403e9002240388840031844a080d4a052100d03d50800700450017549460002e545041050751244840d030802580c0354000f4060070b0241c0100d800c0c03a604050200901100e426510100c2441a0760001c440103203000041003504c49002424020b0a40d078a03001c12141086004503a041e040704007011012800703000e00000d94070300b4000f030003030010360 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 26601354 1250 26600104 26600129
    0xd030237020601080607090501050703170403030b0f04140f0402010c050f03070606060f0806010c0302030c010c0c0b090a02010c060e070f06020d0807021b01080603031303080c06150109060e01090f 86
    0x100d090003880c0ca081a0440c1003103030410001c0c042010b42112030030701202c00c2828143e4842c2c1c190704065035810b400002c040c90f409424070800c810942c0c035900100e02030a040315403100c1d0040c51400c2c08103c4404040044044841d6030208940301a03003041c1503482881403400910030f81056407407505007600788078484099440456491b00700442170140201400340c51170400d038118020179006041003030140035241844058903994007450300c00c0c000c881ca003e04100080c0f150484044004144135031548080e01c0011225000c03a68401c40400c4070702d10a0380503591030402841d01d458510040442c451210294403485c800020405e880c822040000c20482d00648084420301d18040c01410700200160210741200501c0000c045400d11100c0c0988000e10704078000c1c2d950440424a90320408201d0074040d01e4a10740042009144130040c510070307141e070058031510b2b21080121550030110500b014007080080005118140c80f5850f8045d990a0500d80f03028115078a2120300f030642c40c0d036003081c240d0700032 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 26602604 1250 26601354 26601457
    0xa18050607030c080403090b160c1503061d0711011e02030a0506010c021311040b030c0703020f01060f0b0d02120405012903030a050a0203070c091a040e0d0302 70
    0x415103d1000914544d0404100501e866580105444524040c29807480e001140449120302d07001d55250f02c855100c420070b140d8070b4903029407659154100500b000024241200030412400000040340c80d408644540181134580101c01e41d080040008160499036070340311006002952408502803031a1040001a524105001c0d04070986800805040c11300c6505000d000061326540210340f2280d02e201c6000030700d250162a0903800d0b1103030360b020118206000c418000d4901507040100040351094088400301c0f40780350419070990b0054499040d42840c016000c01c06406204020803030000009001450902c0c0140c080030898800d071001e40d1140e40d607110140d2008441c1e034600310200b02a03a00c103010000e416002954234422030400c4000c100001c500c01c1d004a00030400d8072601d40d440402d444150380c403024460010903840b2400c000f1b49000f01c221444609241c0703d0b40c2c003030b44089000380400f10b00310401507001e940b0558910300c110010001755100e81340d00c00c500040d5010250441030810700c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 26603854 1250 26602604 26602607
    0x309060906130605031e04020a03021903140c09011502060402131103041a0106021203061002070e01081f090f0b06060418020c070501020c01090603051e01080f0f0d170a18050607 78
    0x106c8408240c403d00e48030400380405a80d0f00b506400841c1c3d07044070424928110380d040102c040e1120382c80140b1a140303810030101000f0300410210b0f07600c01c0941d48581903a0b6500c511410130000442002d0241c2c200d8030100e8007504111004d4046125103410105044901181c0000550b104071020b44604c6c4d2490407403d080031040f0141801006684006c180c111014480502c482c4005400d16101e02d00180c41c5034440380c000e1080d0350040c20310032410002d5684d203410840c1c91b0a2060070803001602001a00c20051409208200c6a19003260240510721507580c2d80c80074000000d400983d1000d4107200005c2d008800c48500708071140d100c20051384a43c1d04140b21450018250030aa040d90070012440d0b01130799104004004a40c0e85145c00f00341502d400c15001c000e0950070f480c0380c100c201124008200100c00207180742884841c132040307070494400e074504181c0710042c0e01e0f52400003507081002030040789170070150709402c0f03005040006400c008049540980d03000d035010494160304044200680d0a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 26605104 1250 26603854 26603881
    0x30708030f04020114040b090d060b030a03021b0d23012405040608060c1e0702030d030b030c09070206070f090503100501050312120f0c1c0b1302040305030906090613060503 76
    0x31715000303003402c02e414440c2e0302845001e444882130298010000d810300303104058000009411014045d00c120b170110b0b0400944502c2410070020081c22058610b6405082c8828680e80f220740148400504a84056035070581b0b19190705144880c1d1340707034080242481485078401c41b0340c1d540f080c22208414504010f001c2565499030024178660440010040c1e140d02c10821a00d0603242c89600301c200720710600c1040e00034040c850f0007030b40500c0394003004041c458055104210f0180d00b101155031b811400820404203040840b012030040e0464804548610300680c00d03048190102c0c1807400031562110046407038134665855a800541d1120010042030405003e000e4501500485491411102c901240680031002d8000503074880d801c000210440c403404260b80201c0c41d801c5800d00030411008000010380b0041548078402c146064116004091500c00c0b070341141d17809000745080c60015002c200c0d41d601706400c007680001003004081450082c29110601030155504d96036181e050246094180 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 26606354 1250 26605104 26605127
    0x80d0f050c030a0e03030705060a05150301090314090103110309060a0e0a05030405010c08040e040c030b06041e051302091006020d0e0105180f06040303021b10090308090102030708030f040201 84
    0x90050401003020360601c003100b00c031249051810f100d0005851000400d1840c071580f8009403c9016110902500c0c0791240c01c0103000301c2c072180c8410000f20100033090301700c561002c0d008000c105020301e0902d07544020340103820250014100001c03051658400d01d0060b920848120a07282c00500c10820300848610a507401d2079820002401b2202450713031070310b540c0c0c030880c06030505025195084804010340e074001c0303a01510b80c5201c0f108040c2081e1600d002d9045860004442c03103810300d80011010304080c0705000003260809082036081c20385080901c02460054804c114001c9080007a1000d071704e8000c0418000d10b030000fa800e85540c50b1003c001c1c03c01d00d00201880c01c01426200018207070382e00009883d040724910084500e010409000180c0c0c0314107824500e03801900200b000010b0580100c1c40c00c2c2a0748105084241e4480e1550400960382030103c0c8bc0c00204204010a00c0818a500d014059030403040c0100c1340740c14110348038442e942e0012201640c5c4400e49070200401c650340603105d04503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 26607604 1250 26606354 26606357
    0x8010504021306050d03050c120d02070c140f040905030403050f030c120909010902131715010b0313030507050c030601120510060806060d032d1404050105040603020d090c080d0f 78
    0x40c05091800003140140381e50000b50070040302040100f4202420720505245003000820350ba5182500c8079108081c0d0441042a103700390f00310400101c0e0528034551b00308a6800406554540f10f615041100600c0c00403810f9655100c06e010210010381c00300010440d00181d42c0c001e40e180c0d08014000c174500040410b0410840c0014407012040c1d8481d280c006066410781000980c4894444442d0800062294000294403400540109c0303214404034411100e400403644406981c0e884d110740c0c1c1d2152009a0394208801069845040424454006031090510800c00e0724624450640040e1402d03800707070000d8000c403203502075460412400304905005080223042c184411864000b010381ca40a0003030002d4020f90046808808041c410100f8035401c8145086070142e4098003d008200c034041100b43c0408183c2100c00281034a83c0c00c8252422640140c0d035146c68030b13040050860180d0840354840c00c00c0c03600d421a481c0001c0303403070400b10003400503000217082400c0060001040d4804c2100c0860 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 26608854 1250 26607604 26607611
    0x306070314011203050a0c06150611010605010801030c0e0606040b07060203070314040b0106030b031501090e0c03150420040207300e0609010504080708060103150b22060906080105040213 82
    0x3c0020790010141c0d03030083c005003044410b003036960a02a0191034460216026030f2000d94001ca422070b0009505a07103052a0302c02044920b84030001590a50020300016000700d00b074030340c20008a0742c81000749a02030b2010b00294109551074440c0401c54000100454840b43c000c0204242036515120b084c80c2c5034070b070b40fa03003048a0811b5100c4000d62641070003010101500c0c0c1010070b480ea2410002828500728110501c0c0540d82e641070b0110040600c00e8940080740204903103061580350001c0c2c840d14480a001c0d0b40000754a03a1307902c642401031000e5600718001301100c06a581d0b036a880c40900001c5014003640100e81030001c500c558100204600081c003140c5100144905560003400040a07020a6800740e9031b60310040c00580e0705020f00d070700035a860321480300c02081080340420f255040360b00c5003c0f0307400c5401000760044140c0d200348000d40d4124a8100d00741d08a8031a41300090028003024000140081e110b011510980790f0541000e000c585d1507100307000071410141c2c10318000140030b04042 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 26610104 1250 26608854 26608889
    0x20c062509051c0303110a05030405010501060804030206160309020a031a0f1005040b0f1f080702030a0503130201030e1014090610050907031401141216061b02030607031401 76
    0x2203c204401d0410085010754490050415010754040c1c81201641a103960f00c03110380d90700081040d802120200c4195007002c0000800500a003503540c061545a000380251340c3d10400084501005100079404064072150401d000d0b880e070240c8107010b140602d01000c401c04480b00201c000d0712014002120490b40002004410300d04200c83d81c0684008a81c0801e000403800d0005801e9541c001950345c0c0020711110800b0b00708550301c07140658002e25142c06246964550003a030b168010b810390031340422410000280780e0741c1d51518004015105040c0040c0c002c1454240c24548044502204902070395030880d81e1145002d00c5445c0e41c4003014000400107071078403260b410315111281c41901d0242940f000803e403201c2c00b0360007040d400c1480e800854400e40e540c2061004281c5240441070099004141604800344049500c1c00150140c2500160481c54800308487c40c0f0204520301440382145115000181da05200c05400b6900b02da8000c46e0000c101d50340000c2c0f002d4181e1200c0e4605490340d491 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 26611354 1250 26610104 26610109
    0x50a0c0c0c09020702030705120606030d030b01120b011107030303021b19020105090a0e0408040504050c030601081801020d05010803090a0e040c0e0a0905030a080405060601092106020c06250905 85
    0x70405460b40340d50056164840c07880480c2c601034080c0c001d1a40410044802024450005012803151300c1c00c03012942d00082c3c40d00e040d022101c105503000d00058000000e265a24440c1c1c0103840348860602d84541d0040100c0300301d50400d00103070400c0300000d400142d49008564111602045010340780088c1600d80001807285644207200d402c002c1c140040402d4880700c9940300010400204501c9014000605c0d091805200c541e00500456104901d4407010810050f8100242c038421001030b1102c1135262a500c492a000490309034000002c2d40d020096185051b8150151500810f4004020343d2210340708400c0100034444d9820480c0200c4c2c02008100c08158040042012110403040040458840d543c00f100070300000c01c4c0151080c4000202e07001c40b1644818024882c070300a4040d22070540b1000c004481210f0503104141e14011100018a4070791010980742c1c103803074410b1f04c0051808510224180c1001d5048401600515281c20400400801240b0b25031146401c2d281000d040340c2001c00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 26612604 1250 26611354 26611373
    0x408030414030703080a03050105090a09150f0b0307030b0105030f010e100e030910020c0f0f0d11061306020304180228030b0301020d09060608010203070c120207050d06050a0c0c 78
    0x140d41c00848001030000c06620b0502c220030107103410603121540c1d40c40b0b200300940501028400c46018000d00300c0001d10200715031050f240c40c96401000e60303045c005003201c1a03003d04415420501740c40c1d41ca01c081d45142d83c0401004000303511400030050103624100c10181052400c112550f84c40c2d05015410050b10704c04160504d0180c3c1c00a80000c076a85a0124035140d8003a003100660001d945010006660340c0000d85c0f5040828116211000411020305200540032a90a055081404104c0c81b41c00074003465103d014065010301042d080a00d425802036482a07207503c0b000c0075030000203052000000c1109801d00d401030380300d415407403e40e80c0c50109050a040355101401c0001000017210054401d403c91060690014025506d60b40c007055803c000305001401190300340e00d090b000240c1c10006000390ba100e50300d1070b1107140385207115850751102c46038200719503421070040410101b010b640d00300c018481c0c5400741d000098545020174881003180e0021501c001030085030648070000540026 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 26613854 1250 26612604 26612609
    0x213090804120309050607150b1509061b0604030c02090a0c0c02010e0409060608010f061d010b09030f03030108010c111f0c02150c09030114040803150d140c03011104080304 76
    0x214010001155070401325121500c50304555400200042e11806200c41624031000c0d0b9007031010100310400d9420104021700e428100b02d008074150074003c48400b8585200a0b00c4924450004609204e0381c141c3e20600b8044204e5084002c1540303d5510019070801d410890762021070410704101c0c0c103050000250a8030031000e4020704110300c1d62024055500e43d60020714046611801c01d00010341c882d627071a4003800180712642c0085141910001d049034100b80355401c51081c14130240d101d030742808443d104c5503011154003600f62103501c22a0703101d550708000460007811083c1c00000c1c44e050740700004044280300401c2c1c1e8840e500104410a0009901ca0101440543c0000004629204000507810200310b0202600203c0c0b80c0010040c0c40c42680d00140002c11003103008202c0f48511100c0340103200e6050328068015001840000c4081c0c000019400e1103480c000c0440110700415034445040030402c100d00c000035004041e01e5490750800340500701c91004180b907002d05103030600d00d10302d50700e00403403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 26615104 1250 26613854 26613869
    0x60e0411060a0e270601020a0305090d05011803090302010912150f0e0106030305040e090115090f0605060304080c060105060f0d09020f0909030307020d0c08190e060c01090213090804 80
    0x5a1440c118040d05408030a43c0300504a6440c01040d4201142c01c50103d460f006a600d1041c07000940c0b962010440100095058842c2e80c101500d55051045090101c8011503140d03680303000c0507485542060641e001c0b1031081c1d5801e10006d045200060142c01c01b6030058041c3c1498200860014200181c4001110718400d40000c0022255072245c014005d4030b0b4035181c1c607520f4080080700340f5a2000082098609801c00741865445283d1a20300301c1d11900c52030805c00060328000d12440c04140c210401590300c241c404201c690320341c4001801d5501c00d66017290388060000b00301e000004144a0b103401014100c40a5041045c1144862071074402c990800d044159240c021900315030b80c0b0202c15001480281200e07101749411040307036135264010755503c4054855501c01c1c0341100c2c420f04440c000c041c0d00500e142e05000422104000407203d800311078060180b698258042501c1e13040103404840d20510001c14540720343d006003e4130b11040c41c91500e00604040703201d000b08501108980454120 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 26616354 1250 26615104 26615107
    0x305060109030206030112170c06010605031806010f081506091b04080709020307020609060601050901032a0302090a0b040e0f04050a050102030a1d1c080720010203040501060e041106 80
    0x4020040340c141809400095000c000400040b866081040b4204c88051187c3e844860782c4840c0d055aa03028081c107801101c0c2c551100c0014490180b03c1c00c050b54000f64a00e030180450000c0030440343c10000260864003691442c482e0801111350708001261500c40024203069031800c0c60404100e400b01c0c010070300c21600103c00795100b4291a04002c43d4010f24070741c2c05980c0c940741c661000740040d5005603036200040c8188004149403c10103c1c1950182c50161107991030508140019000b40c0381d110900ba555071041d0701c9030308825844c440301c0d104c00301469400582d204010b070f04104610903680c0120450003020705c4284420031210404a0704825441c071071206c143e68910b00640b9010440000604075400841400401925a000481d1103020702d04a000f6104d00d000b07101c0d40d68141890920450000080600446401307620850b8102a45240100c0081914408055120000206403645070750003c10003086c828284a1a405421251942140c604254540e140b42495031510b9911a080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 26617604 1250 26616354 26616361
    0x20114011502070b0c070302040905060403030e0304060c060b0a030614090d17010521070e0405070501030e03070605100b120a06090501060c030f030f050c070302010b04021314131514060414010305 86
    0x901b0001c200083d94014001d00030700306a031601c0e035156a8291400c402007402d10a00c0f00003158040300341c0e4103440240c1d039030019840305a02d80401030003a4035142608003c100d000403021440b1400b520009041241c0c424a1508009170b1503440d246550100c00104141c1c2040d0758070f40c4000c1c100e0541114001c440000180d059418004011048c81e00700102c01d00c0742900c0050080d41d142c2c1c01602c110300034400d4a402c10754070001541903400c4440039003241d070001c21440e40040d44541c055500b0400d0360b101940459102e11100a0f80e0b8880c10348522030303e00a4003003215003d210700a0a003d0301801c2030500c81940b5000c4094194042d030301c1c5c010203122280c5902c05580b44281d02c074101d01c00a0705024003241c10320004403135855010900c15001542040302c0780c5007904290003154203080e11075a4001059150840580c04070900003005540080f80c0c110280c05466a40180c00300d0140c001007000c82d880c9855038610070b00c04200100d41c09080140000c101c26003041c9042e0300404030a080128060340c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 26618710 1106 26617604 26617627
    0x501050412031b0501050903070219030309030201080c1e040503060601020a0c150903080307091d0402011202090d020d08090a060306140120010606020114011502070b 73
    0x380710300840000688984030f07040c1007070103106a5031a4141180e1343c0ca400d40e01c098070b20f0312150f4408500d000940ca0452605641c1402c120340c51a101c038510b07a800f03041902181309c00380c113004981e000a04040c0c04501204c10841c0b180301c0c40d010020300004811401e0704a400307218000d02c501000607209500019031904c020b41c0021060501340d240220003010710480c000114104815041b0000000d130007200a14055480d503110300801d141007134001c070700c00300550300c0c40c040c0181d40400340700140c0d0700115030407e00c4003901c40141c1e46420701b002054a82c800b0000003504112500510070501c08010040c12248000302d4040410b03a0744d42004030155032583c020400b00c0d1005c590b240740198020030300c40b10a200031610f00104006010b640130f01f184c4841d80303c200940d45810180501d503c0d481b00c0c640c05010130980404000c501160025958102801000c000c2074000a03001ea160 = true := by decide +kernel

theorem cover : BRFrame.Cov 26438854 26618710 := by
  have h0 := BRFrame.cov_init 26438854
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26438854 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 26438854 ≤ n) (h2 : n < 26618710) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
