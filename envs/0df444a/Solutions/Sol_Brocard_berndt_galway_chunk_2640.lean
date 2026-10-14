-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2640
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:18:47.777986+00:00
-- url     : https://prove2.me/submissions/a45afad3-7023-499e-a5e7-bb4b18dae556

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 474640287 ≤ n < 474820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 474641537 1250 474640287 474640307
    0x30509100305070e0108150325060f080f060604051503100506030c04092a020607081e010608060d0803070c0b010b030906070c030201060806011404051008070605070c1203110706 78
    0x1a440c4c03100b10040c007400664032031030020945954041011520303000d5850a100140c2800d00c0b00f803880c12845400b00302c0035429001c0b90081801c0100c0e41414100c0581d00400254000840c410405200e07110b100100d14a4451500015040b4010f080c005650006030340041d84120542401584500e03202d20401c00381d40310540d42400c035074200b44002e102e207045560100c40459002903010742c040d01491000c0b1041c62043c149070016800010810070032030340080401380c0c840f9001d060440c04000d40c0034690304034030b4180121340c1009107041c00240140c0750465502c1c0d120b50400510b60300d0785002000108480352803032045513140300c04000080c41c2a40607059901406070314015002c0c40d55044400c9850356141c0c0810740c02c542d00c0c1c2c800003e540d80300348491806800040c4080030584180010300082d0341d000382400104020350502000480300104164080c2c4106281c174a590341c0481c14001c102050f00c0c0c1100388001101640c1404040d00041d81049a513103482c15110340c40da4440d401d640398120 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 474642787 1250 474641537 474641551
    0x50a0506031f0b0a030303091506030503250c0305010515010c0206030a0c180b041a09010e09060a091d010c09030c031e140a050c0a060909051b07030509100305 70
    0x100500c041d5082c100b00c0340402500b0b40361500010030040c0c21000500f640c1041d8001c0e400320f903841142005024080041100000701e00c502407181c503145030342d13055891141e9807015054100310081e0421500e0f45100c2e88000c10303040100d94210360740f43d04059000380b074159003003001c1c548a50310240065019140306280c06400801503411640d9010044000e840b900c10403000f00710260350700c00c0e00c2120341d00402003d04064017000d92994207240070b4011004411441d01d003a0070090080000c640e034080030002807520f0580c1c004007140c40b2000402d40400c410340051840c10305280c031034040801c1c1b6107048200d103810800240310000d128001034440c1141808040c0880642030300030f0020540100c03104489460500c8012404912070710f810007181400c490925064010301c0341c400c01d0100070001215090382c02c0310030808142c6403a001401c0741c1304511400801e15129000203c5c0d40011003000d400c54054200060b0b610200c61600514642c0b100142601c99181403480304000c81c428890a4441c03c2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 474644037 1250 474642787 474642793
    0x705040b130e0705030607030603050105010e090319110312040204060f0317071a09150916090f3c0501060f0305150a0f0e0f0906060105160606030c03020301050a050603 74
    0x422081c06000381500081004040c0708030540003c8a45042000c2c500c218425500003840b40e056180003429100180e01241e800c03100074007407100180d0f0100481e00c1c03100e40019400708100000100b074a2400c42d04821040c24000454240c2c41d900e03000d00d03214402c51084404001e043d456128034109500180805410700705007000030455000300900403d9000d00841003a504c0c506a0303030040d10030700c1c0d04a8074508235401200e89008205d81540d40103030885510000383c0303070300124601140c0e00c4800320302c60b04601c0754584a2822020419a0005c03038245070f012568440403d00701041c900101304900e0b1000050b040341e180c2c20300d10080b48125410380c0d925a0b110242c9041c4480110b02514014101c4106a0300c2d00ca031008040d65140f01400042102c8145c1c2c81da42461b0444007140c0c04070007000c0005a40c180000c00900c9900490b44584c01602402c01035250280c4144441245a9603180204084c4c0750200c00b20a10140045050459208400034407441d40e94403042401c0d510103981d0550564 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 474645287 1250 474644037 474644059
    0x209181204120b19090c030303140606030a11160503030f01060f020303042003070311010f08040b010605070c0f120c06031b0813051005040201110718050403120e010e0705040b 77
    0x19941c81c0d01107804c41c2c04510340c0040f00c40740a4241080b240e0a200881714941c20141c00c100700342c2c05025404180001a0706951549400f0000c52060b00c030040120703481c0c135a0b030304254211b0074141042e04c502d00261440c4034094031040c44c0c010341d81d42c0180c1e00c010100e8a145e00005d422440b54106518844840d8069400c644442d9126518000d82d14210701f44d019011aa904d51745c0c80c1042604000c6000b80c20741b0464040000014101100455a007020414060200004070381001c006504441e0321b0716007ea03562810b410017202070303000c41e0401c1c405100d0103000021007130383d00c0041c04106400b654105220907958042a800c44400004150107400300e00e1140f0000d901030746c0087e621400488880c000124a550343c241450800e405101c0155900d1040c0030555a104a06480b4802401c0040c82114208011000c407001c07000c440e0950541c6803c000380401d8418121202d00d0228940c0a110402c4540841030191000c85500c102a07c00c0b208000f440307203058001c0c03120412001d0f050100300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 474646537 1250 474645287 474645293
    0x6060604180203100503150a051f050f19060c050d030e0d030e1f05010311090105030a1407090e0c13180609050c06040f0e010803180f010903020918120412 68
    0x1035000140f1304034028050741000105501c0601901502ca03600030500d4819190030b8501508581e00907110a140403580c9003040d141d900300d5600d1909840040714040d00792501100001d0000c010403a00820800310500c0005296400c5046080040d10403402d03100d000240756011011030307416000403525540f00c010b40350801c41c080e5202c400d803070310640c0c01d4840d40c0740085991500b03040f03400c16902e202944c8030010003c1c02496245624610001c0303600c1d080c1545400d00203036a41c03c1051000d0100a51941e030307500c40140402400004008245040c030030356a05c0a00b0b00c1d1904445076130a4061078401d2038200a4484920031980069542c070740700d8880720560303114040180381c1640111020304c52540d00301b54070766a40015000802c2002d5448804d1420900041d4000b035040c0c0c0400b07025403040c0302d2110010042d0010b10314010050314024030f58000140106c403e41e00c10782c00130b500135601000344402081044842c1101851041c1143c10006e482d500c180381504c1244105003690310405500400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 474647787 1250 474646537 474646541
    0xd0e0c0a14030a0602030c0d0b030102040602370b150904230a0b250c171c050906061008010e0705031824060301020702010914030a060e010603050606060418 69
    0x20381c0101400b1141d444600307a031160200ea200b9204222000740120340c00754190414010719050020503802542010300d0700002a540360b10380a00b071078010714460b22510400c0855280f5465180e861aa01072606043d41081616103405480041d1454030314680f15461741000c90340741e40143d80c02a5807000701010000c40308035070789900f07a60600324001d44108101103000d141d00303540140b410352050a070003d03004a501d5008082000500b092041a0041e800880d54084007040200b092050140c0d56140720048000300b00080319a0854517454003050040e80c82000601d02e103d5034007941e40c3e01000040701c41c03c2d15003000920516101c81c2d18a4001401c10307200d04099130704120b643c40b031505100700c400c1d40a0705004034018104501c00503214101c16180740300203600d8114209500071881c1420381c0d00000d10f024540d0092a0100074180403181d0142c508101b409421070f0040d008004d07081d82c098820340688007620058403d4032031100850300920700207048034115405c080740e0343c82c0343c1d405507500300c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 474649037 1250 474647787 474647819
    0xf0a1a0f040b1806010f080f19061203270506090d06020c060f0703113604060e0a0c02010522030e090a050f0106050a0c060b04090f05030d0e0c0a 64
    0x500700d5160280820140c0300e0102212000301643c003070480354a4a04001890351907001c860f00c04000d94201844601449108500e801954401840c1c09010ba0501080003034040c0c1c9d880f141c006140250b1a030f06160780800c2c011500301d003008a540500384040f80c0c20312074160b980500d85e1310040802c041d4417a4903005051f01d9980c0c3c0714101c00750420f0b03101e100c428182541110415000503040e020000341d160306100302d4601450034030105092010b0085078034001e8240a80d8402c044000d255080011429030009116580c4d004009011613901c1d07000281e614042901c05039006401c24000b02d16a5006004680c841c000003850f0715402001050b220b800101c0310b800c240c040c8011400c3c00c08484e101c4a919912417000c070080421a1304090504140b4844d059028104022082c4440c080c0c156002c20b11442c00384c0c01000c0491821007182c0010020484000028440440c8844d040c040100100240c982030300300c40703420841000e0494055840c1d17000d00302031984c089a07244051003210190003031a1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 474650287 1250 474649037 474649039
    0xf0209010603020d051014210307051b1e0108070908120901031112040b04061503081c0605130c27080616080406020a03020702190f0b091813050d080f0a1a0f 69
    0x1c0c064548032342181d0039a40845802d542c035070000760600003090ba089100c070701c00280070303950100360680149c1c03403035240b0600e0b502c0207041000340004110700900c507c1c90341010b880c01001b076400101c0800030b000d580c1c1d0b0000110a000c40e0504811071292010602583d0428102c60b104010759a03496840d141031141c018011203105503152285a0f11040706003042010350b12400c100d56450030f40b043e1031144d155085242e004c3e045e00b480003d00650715400b070000f0f50100c1000000c01c4410402c842507403050424152094007542c0078101d4107031608000340540c2101d0420080d0b401c036460386a081e0b070f081c00d02e0000e000b012030005008180003032210340c0108008046072400500301020b583c002003520038904880c0d141981d5130501402400c48842945000380214030216140c461110040340c10a08880c09001c02d84801d00f000034908a00c0301c5039080c680743e000c000d40d08100201c40c2e0150625100344d07211705c00801240c000649060f03851045854041d10312051210009030b22041020041805a0007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 474651537 1250 474650287 474650329
    0xc03060d032706031802030c0111010f2a08240406050607032102071a041e0b01031e03050d0507051b010e0f0d1b0f0209010603020d051014 61
    0x392094114400404208542c010318052182c0d15001c40201541e0280721013501482d041c084201c01070b6000266090405400c0c200003040e503030a403202074010640407201c0c1c3c010321b08010440800211003514203003007401e0b030b074038410543c9203105045404900841d44070740f185d025960f03a818070b0480d5100c8110081402000400c580d500c2d030700410b000e42c204440480108070420f641420070201c80301c826074868100c54046090140c95107481c9090110701c8985800303452440041000e20410012100d031840e82c807560440940003528050940003000d100542e52060079030508104612008281c07031443d070f0159545410650b40c2800c100041c200074004109204d82080600c0355046401c01c0103500c6551a400066813503880d00300b803402c0001101d4011a0342d00001384021120f078201e0300c040340300c504083c42686445000e00c3c0180c00800c0c140e102960049164000043c4140d054009150408170280148195110a00d44da070946105001c1c1c050020901081e440403401c00e80d0204020701516810 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 474652787 1250 474651537 474651557
    0x30209240d0f0203070f030c020705010509030c0603090a03030b01030c080a0213052805030606010503010b0d0b092707030302100b04020f0409060e0f0408030103060902040e060108061005090c03060d03 88
    0x700350110303800c8041040d907464011003044001034001d014803c1840086c1030520010030742050094984407a401510b041c0a07000c100540035817000c0042240f400800303081c40d60faa050010500e596a52030340d80440019080c04004815548030b40550010282c2c130f5103c4201d01d4540d1500c0c0c0000e0740010b0b2882c20603490303100700040d05a4804640000e00e0040c0010056221119901c104859640e5084540607900c40c070309009030750364410102d9045490b8000b2098807048814040c4000c4c240e400c420a170304c4600b1105100b0700d41d4040c2d45030503803100752840c43d03030585d010303014100d89031000c0d031202402580050560710850007044c0c004000c4040300a000510380300c00740f00c042c1c465410030b8100e011440e980d00ca09015001c201403802d07401c01e1102c2d01118240c6020356540a651005020080170162900300483c01c640307a940044130740100d8202501c005684580020359181c00480e41c202000c1c1d0724420000355803c000016900484488002c24955603450051003c02c02c0414002c5040007000c2807 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 474654037 1250 474652787 474652807
    0x3053907050f061810050c03040303020a020f16090c080702100c020c03070305030315010c0c0b0d0b090a09020907030c081515030f0718060206150111030a0302041503020924 76
    0x800c83e40b1030900d00d40c0898841c0c440801e1189044d94400705261154035010500c440c80320b140090320b600550514015035103e98442049051950b40c2648410350f1140c01d41009510b04401da90101341d90550404000c03616807032004551034a410390f0f8510160300200350740e000000c582e4024417080c0941d40129400c0c0404030307000c6032512410394400d80c0c040c2c1000c000d00034480003c1c1812b0780101004d2034651030055890300c6140402d000340c03054511004000403400c10b06030082c0c1003d021001c000380310110300e191504400000e848a075008138452024440002d122501910900d03c400e1b0351559002000d5880c80c490294648032080c04a80c440364010031940c11140980055115840210304c8a22a04100c0c0000c1c11440a47d4a0b40c2c2521083c44030600440d9070004e1040e9210000c180c40050b103080301d80050b500d064807298208030340d010001d00c0b045400c0c1c00d03400810407101048070034030310500003120880c02c0b0b000701702c80703d913100d8944030710320030706503415201038070450001d500b12032500c49484 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 474655287 1250 474654037 474654043
    0x601030902210f0606010c120f200309240702060309010906020324060a05180406170a0203120705070b0a020102160c0303110d050f0703020c1003053907050f 69
    0x8810011240c3c4281d000d07441840c420b201e216000b01082c02c20440c94034a03a641c40290600d8244581c040044c03001b512409180b103a44130300140c2081440c0c00b141001c511010303036202e51210100703501548001440d0804c1030058964850800002d06000c4c1c20700c0c3c0181e080100940c80a0081e445070b64844c170700080031450710702c015400780000d2064481c100341d403403070f1016030038461035400340c0b15031014008000c0041e000310468040820880b001114091024002801004642c01014000114860000c1900000100a803055000710200e178101c24401d4840781d0300e0710807104014510707008090700b04421358091020300127110301c0c2d00000d03042c04c8a031050005c0001001006070758110040c4820024950003070041e0a40d4503142000e040581214070002e81203100b42040009103510009003502454400c2c814811a40030040c144410000b907060010f003d0141500d400801d2092000038429820210b400e80001084052217000c4461010042c800030b5041010155018003401002502603070043c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 474656537 1250 474655287 474655339
    0x302091b0f07140102030f011509060509010e030a120210060803270d060504080306090a0c3603050c04061710090602070f03021b01050406020619061d1f0e0601030902 73
    0x6401c0010888d854100d00c0701070b40e2406228202440b64580301030021aa02a003100e4140f40b0030300b48145144188400300e45801c8040801603c050300d04004d03104d45c15070208403140d001c0d42c000e4041c03100c0c1d511116410385a02c160715003c1c0c43c02818241c8880088107000c0348600c0440000c04d580e10049858545105607442100e040b0b40e403a500108005441c500031032103a802980c001804c02c01401000703805004031408600b005a91018005549802400b0100c8195503a001604000600740d40b858196560842010803902c203d0030000d010a460003460752800402000c0001007901c10071040f000f0b0b00411b41c446080c3e5540d5000c00140c0702113842fa2800720381c6203100703038001c01071500301841003804021420106c0d41048006c02c42041059030000301543c2000030451406441650b0205080052100d54070192901c3c1c00c0c2c000d03c5d4624031000d00054881c8128105d500340d07401c40c148550843c1c2c4910b0040901c0c2c0200071010401d44d5100b070b8400d18043e4400341c010000a0080d00d6109220004d03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 474657787 1250 474656537 474656551
    0xc06040305120f070806120c0d050f0106140904110310090b040b06041b0e1201091419171c0204140f030d14210c040302091b0f0714010203 61
    0x1c0060054102010606095800700c2c6040700c02c0400d0404400080584801038071a600c18801518441c420302e01c24000981c480034000c08003909403041d8544144c4881d00c030019001c0c036507c0c184001480e0006400c0369031020b08020510000e80d62550b40e1100b41820107901c540d014412603440e0b0410360b0841c4100d0704003601a40480032549004d1402d00031080d0f0003401d0f50700513400d203249030740342e40807042c030340c0907031588900f0003203003440b001ca01186218140d4030a4030000c0d0b0a0261100a10143c1c20b100c911445140050780c801d9041d10700301518100354402c000b0b100381903140ca05000098000003614140c1e20340c00a003411100d0803150201641c00030341040b081e1940c045c1602c181407030300390441d40000c54282d002d00762421a69802a0200c0295100400c0316480001c8020340501091122425031014100311030707407405d180c0103a40081e0000d0000701c1c004c00f00070f40420410800700501c84070409500714528a03040755190b074007006810660040b5091401d5000b03850300c0010a00296102e411 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 474659037 1250 474657787 474657797
    0x904170c0a080f071e05190f08030c0c0706020c01200f010e0c190e01030204110f04060914010e090c13030b09010c0921060914010c030e010516020a0605040302030c060403 75
    0x1581400010842190f0740c650002c5c600014010004202007030241d1030107100c1e0500c0031402032070309040c0611481005d00030b01c0c4d03c2c8004208020310701c078000542203840c0c40004540d01c0c1c907140d54090740d80e040140c0460f030100350101c4035041c0b440c1c4481c03043e004d8407907e182610750b41c1503104465400c0d076101c12201c0346507812020482000381010000f08114040141e403a11205181601e081c0d05441c0601003c2d014a40b5403c0000252036543c0884207100050300c0076a07a81c503945d10300200704d141680140d600005a400540d01c0e550700c990035421221030014000e100030f4640a2559099a126002c180385021841c8000004510907908151040340d214002007104052503d00803c0c041d482c4c0c1100303000301490081201c4582003a0302c09848580d04c5400002c05c15903e043c14030301310303ccc0c020700c0b06425030070705a911301401d0b07254010910b0700c05044028840e030b480e00b1506070300d04150343c043c00005a100550041c007081042e001150864040e005607031a00c41003104160804c842141d054000c20 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 474660287 1250 474659037 474659047
    0x7050a0b0921120603190f0b070509060307030e0f03370207170c040606020a02010e090925080d0807090605030118091425050904170c0a080f 62
    0x980c051044002c00440118100d5207200c034408159150300a0b4030300410410144000603030b0b80d803410031840d0784001d04180c2a100042e80c03850650710b07442040f102140c01a202a0100701218000e006940300f6440060240b420741c0e0324044114004d04607074001c040580700d00b00713410040c12418002460719800200310075441006e81002204107603440451001d0600c4843e40c13071030a0035804251001913584000103103204a805480807490300081e01d001c560321030300c0d0102c0007030321a400040b00b441c1203100307803039810580445404001036007100711845205500301c030070030700a00740c40220180c009601c280c030003070021b0b80c50749000d52904152110a4011501250a11a82642106d41140285203c0c5015031840d070415004201c0d01903258600e02d1465150041c403420402e0416001403140140ea049032501a503440c400034210707841c41480364400408100128207410074450359031142d03070845e070341c40f0b100220b0b0100c45520350301c4055840e46501800180f01d0010703041d01d00a08081c0c84104a141e00e070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 474661537 1250 474660287 474660301
    0x507030b06131d130308070e03160e1807061407080a090618030f020d05010e011104060306050d0c0b0f04091404211403100e0112050c0a032607050a0b 66
    0x3c4840d07000d90301c100f801a04000007030307400740d0811501950529100d01c0d5038481b5201034075090404145268503000c0c0c008100300012255014904031442480c0d00e0307815482c3c030710781c82e03c082c412180e41a01d1500004410f201940c0a41c00900c00c240d8010314140c0b500700a511840c1035604a5503007400040c0382070004200c00c507801107801084a034400070641603686550340341d0031031003200c903c024050101c00d0b072100f0511001f90f2004030305051900007484010303114a0603500713a40c06400b6072000b0034507181d0041030b0b601302a08c42208865012044601c01424009118070503000300302c5190982c40100030100d8607003001d0094900000403003080b4401810b051030800384004803a8120b4006848200d082d5140e503a014060014001b5440c080c96501d40302c000554580140b190883d03504203c0f0040009003110100c018804054014008d44501200b4201001003203001031002038044480d42c184003070300c8920044051b046113041c109882c03501c2d20b1903850701c0c10320000e50350a50b4900600402c01000b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 474662787 1250 474661537 474661559
    0xd14091206010306060f0803070605060f1915051c0b03010b03070605130b070807020405101a190809030304060b01210e210a03020304020307080312010602010b03030702060d0507030b0613 82
    0x14041d40e000081d421b60410304a9980c034012400d0241065403144082012038448001901190001900d05403900185d0214640304440c1e6100e41040d0b2412030380940050741c03045040c0d1310b07040350b075101c10f41c1d040403520300c83c401401c8685001c3e9415540c4400207440307036800b000b100f4000c1420340c480645aa40481003040401d5260b80944604a000c2000342d000902140c02c0300e00140d81183c00041540720007100440e0001c07580c01003103040820024545000e0040005000f400c00d041c1e04c96000e102c03654900300c030400c90a072151809984144003103000610740d50012481020103140000c90f1110303004282064110080840340034036604d40c1f1401c5000340600c8a40c804e03c1c00490184030403256500745003018861019614101940400498119175052286400821500c404c483c1c03565107201070f04401800c03e1080402640c40c0142180a604010050320210381c0c0041c0040d00301701c0200011009450020081d804040e80c0350409011079941794040d00402c100079910000440c10070082a603 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 474664037 1250 474662787 474662789
    0x1031406130b01031e050102040f080c042a051201090204091a01080c07051603050102120702010b03060105121f0f0608060105150a090b03040f020a05010507050d1409120601030606 79
    0x7841d001d01030403440c0403031102207040d03045035480b440c0046a4140202501540c0b1031100c0010465400020000b0b0002c600512210540b049442500d00c8d10310721104020444091448100c1c04025411152100c001040045040183ca80c00c0c0300c1e05c0d02c901c0104c407403003d1800340c10001c00c10f5404282803158aa1620540c0300707980c0040d45001e50441c0c15000a040200010070035107007510001040810400b0a0002404e101c0a42d008a000c664980c64041d003c3c0d04820441d00031003030100300280b140752050240b49441031020380540141d9007070000744100c000903910003074080c1c401e4402880380560200a00d0203030103c0c0e05000214070620f850200d06032030081d440302da1651300890041c802036465220300300c500700b2070b40103083c1d440c54186c03020380b80503c00c1c3c0c0c418844114044204018010f1801c494031105200321441f86000d600c810040d209402800b10291582d4010b400ca111702071701236403031b455800701d140f4103060825020000040031800c03551a8554140c11001c01081000158000c0074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 474665287 1250 474664037 474664051
    0xf0a1b0512060a0e070909150e0a0c090c1707231804090204090506010e010504110a08040f0321090b0601050f0a0e0a2111030d05070b0c1201031406 65
    0x6444040e40c81e02503454002420012a0700d507140701c0500c0040b020040d490051031841c030140040c0b801c0d4184014000b492004582c1268200803400c9040200803035407048150303204010081c40c0e0308000c01c120003030403500100c00034050302091100c08007040160091103400035954414209000308030719031008002b0711030700e11508018441807003004105c500110120f10142c41c0059948081e00000f00a0074071500701030141d0041c5070021031811180c0c00024140c83c0c0584007480f0741c01059610444074402c3d5001800000e1880021400040c5604c2c070070352802d400b902e44618904603407088800350200c0c60003001c0e0000c2d5220110000c00c2590805942d000e002420040c0c145042002205003030720804280004010309032610024036910401ca41003d070080048451004142010342c204251080d10142c40591190000405c10302d4001a083d200c000d035651010300b0180d09a03102c42c1d1403200907000c2d031140d03072003806000f5008820040c0f1070700a601811104121710412030f241d50030020003038001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 474666537 1250 474665287 474665299
    0x10e040314130509040c210507050102071a0903072d05041103070c0606080105072c1e010c0b091501080601030f0b0702010b0a031220120306030f0a1b05 67
    0x1102c15844542c884200c403010780d002a01a0340724070b001034841283e0381000c031680d00540c8590f04049813040907011450304c5030080315105034a407001682c0d5510640300c1c0030703030900520a070508101e28070800f803e600c3d0005000c80340c143c2d49030101120111030b00ca92100d40d110041201201a0b401d4462950007480240da003007001c0f80b01581640302600c40249010180003003421110b003040400e91159004244000080004d0308000030b0040c401c04000740000c8002c0100c00038020204c3c007919405460301d0f0000c20380c0b03c5d003141904100c500b00c2e05d01581c45050110b04034041c4040b0303504408180c400c204280160620071b104044410b082a4180c02022240d4030260051000400c02002c61030307425005800b86c44a5540c50350100e001d80401c242c0581c01c508420000001c115402154034200892a140c0800e104070b0054400ea6049400200f80c81690000c554080c42e0740000000315005800942a5224140035441040ca4080b43c11003c988141d030065000c485503032006085000342c00e0880d82 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 474667787 1250 474666537 474666547
    0x120203010509040f05030712020703060f0c0c1202030c070f0f08150c161a010e0a0b2b080f040602060a09050606120709090305031012050a0809040f05010e040314 71
    0x803414020b8000d100608120b103541100b030a01c00100181c403503080d070003110640f1104000c030000752a42c6052000f220b07001d080c00940c0c4011201070164804034540b036036441000c03044030340303c00b01e040210910040540c00200f00c841c15031441404075501524031624404038603858221030050120140e40668600d40017811100c030031156141c0040d420015071032000c2d031600324501c095454103500f100001c1c5010210580d40e1001002c09406030304a400c041d9120100e40c1c2c85213002800d0352800c07078585a01c040040c0079540d0340f40340c0d202e40c44070441031b6a213040e18280c090303034995150754854051a015030401040c00c2000303135810082c42e913002c0511001402120140e5581d50703130302c0070061301d014400e0341c1c560032803060b1540c03c1058400074040c1c54000c1c421500c1e5810042d21640c0150b80000a40400c2c84012400c40d00b0a5119103180f580036008003500da80c17607118004a83c1002c00103030344c020f80794080c04001485600450f17010700340c01000c4074401d04061401401c3d05101300254518110140301c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 474669037 1250 474667787 474667789
    0x12090a050604050a0315140f0406061505072a06050717250501111602044a0706050309060f01050906010509060c0307260403080a052b0c1202030105 65
    0x20b840c0c0031268007100c081505088503803404003038001c42d41c1f0900c011000d103041260440784140f583c0e0085004080810845803070322007890300084101111804036508200d0180000c1400c82c0c1d40031102000d103584500f000d030034645291740d11041d030b00c004002400491210b0501c00c0c0c1050805601c08010510307071400d082080c840e460304d014488407941000302204c45005101d001e40201c0482040c65102e0b580e22221540b0071840c04650f214168050751401d031200b240d00130301c405204d40000c0d400544036954420b00c11420440c003441a0300e616007820112044146500c2000310a0107000c10b5101c5903168074003413030401e160190080c0511850140080100b0884d160500440d0300000c081ca0841d5541a1a001107806841540e002e2503e505c800601e101c24010610349003825082c0c0706030b50441c140445542c5034454025070101914406042056440090080b0024601030045040034107081500d406244c980c681c016001070801c94a400c1800f0109600003000d48031083e241da411411541410 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 474670287 1250 474669037 474669049
    0x31701170a1502070609080c0c0609090f04231507030b010c1106070f300815010e03010e0f0601050a0e040b070309050d0903020301050609090a0b071112090a05060405 73
    0x1560151071405030520380c514000603901211a0145c01c4101400f00010f10b140588403035114803205019401801620012490080c2c01c80301d050b48028440b45544d218003640c010302c0000904100c0780c118400c075050900007003505506a10005d0b4101514559409000c7d19040300002031082c130401d40b802c5140220744c1e801844103460f42d604411942055141c14010620310320810b4405041022180c82100c10070501028040070441014815210403144005294400200420110204202c0d0b000941240000c0ba40d40a2140c1c052502180c4040c4400201c0c5c21240200d04290058100200010154604210742c50040030150703428800c140c90405101c4050b01c024100802c4051440080b0b1701ea01c4c400d41095000d03a07009800d84291001c01000580280c0043c0300884c0254201000034000d8036201700d810f0f110700080009441c00c0060b6640e0f2000b41c0b000282000103000248132500042c07103003001070a01100c200c507100e940d00e8005404004160450b82c1c0401e200740320810051000b030303d0395 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 474671537 1250 474670287 474670303
    0x304031b150e03090a090b030c0121050907050619020105070f020307060e0709020a05072913140313080c09010303020d0503090a02061912061a090a080a03170117 71
    0x81c0c503000072403074542d0520030b045210f800c0480e5449030a100b40481c01840d41d40c4100207015044040303c0d040c3c0070260043d50210000501211109084000d04150a006801150340034480909444609407900005541c40e04030820f08201c01110250700703801a40c091151a40004944c1031801d6010042f81d8000e64034070030040c4c02002aa2109680b201c52501040014003500303403041d007591036001d00b030b0006099403c254400d6036000c2c550302101d40c00a518070415492140805d5800a131955040d05001d170207100d0480441d15650299034000000ca0140041e00c02e107180209802c1c40c481c03510800a1030255a41081842140d10200400019800081c510140c51041c10002d450703a403205404d500700001040c0180d0095400a17018407071341e0542041e00f2000c03016403544c404004001400d101120b2003800348484007803207004030f642c502c0c4d0050003404520710300030802d070411500ca03000706081010004044001c84d800302207030390440492003141401350a907441101c80661121000554800c54 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 474672787 1250 474671537 474671573
    0xc0305191103190b100c030212030c0a030c05090d0605010906050f0603010e06010c060501090212012106020306060906070804150c0f020f04020c010c0e010e300a0c0801020304031b 79
    0x142404148840b0f00e4112118010f00100341c0103551407a42d20182c03034840c41e10411001070058005210000107407005990154489018407030510300c210401342c00070a0a40700240a0040134000c102e002c2d03072040060b5081c035100342d034042115403408041c40b058a020382c0146100d10707241d0005510340d4a40000707590440d00096400001c0b030b19000700503220b00110407000307405c40381040d0000c19218480c1e001041d480d1441511080680e03a20101202138a0b0500a1590411854407103400424410303000345030401c00040080d8601401e28000590541c0100801c40c0c060b10701160402201403100c051000d6800036040c1441406140d80c3c41020002c60154000d1046200100700f203140c1d122a816940d810303900000810002005680182c0200d0310381d0b10741c0340003c2c40300811200d58280b20f00c40343d103107441440d11030030744044084107082112994000d1702000d12401490700082a10031041000400000000507543d00741420001c0c10841c8a5000c03841a08200381c2540028407131094034001164 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 474674037 1250 474672787 474672811
    0x3c090c03070309080304120806010f052b181203050105090112061b17071d0d0816080301030b010b07080a03020a090f080d1101060506030103030f02030d0c0305191103 73
    0x510000c080c2e004000c1404042c04001c000302c03c0204101d90700c0314114007e0816101c0c000d40340d0b540fa004488400c241e1144900140090101c0d01d001540c6c2040140d1000420340704480c0c801d81c1c0d04041c0c003200da000c07450040a1050150100900c036682e10044c652005510b4140815030400e400b003060750406228a024a0280e030f0002d0042c80681d61001a9820180c2200d010310340031040700030000804035012182da038019802280056002d5481100c2c225012069564100045010011013515401c01900e012000f003003844000c0380c1d100c0015031800d01c00c0c2d0b10592a94194104003420580582100d44124010031000c80407a50341e00940742d00c030803c1d2074096130b50840103604440302d00203030703003e80703103d6146890100750703400003103520110b030921076650ac1c4001211043e4203080c2c610b1441203c0d0040e00030401030022a1060601c50f074800c810780100c0c7e00d058400b40e200ca0486542c80800c800281d55241444403030242040c1a62510030801c00c180024800b1600d81009440060100c8140322 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 474675287 1250 474674037 474674041
    0x706050f150607151b20061303051207030e1c02060415021e0408010c020309150c1c200105061026040b090706090e010b0a0302093c090c03 61
    0x181e540c0101c40b00c00d100103112001800b01010364a50041c3e1078000403c0202d815060444102d02074407000c281400014021f9440d4681700b00a0164a58025800c003c0100215100600200c0d422802158940e6000032458508400141088854480c43e0403a401c03942949505960005059400c26080b002e076503104104400380000074492560340d0100460030442d05103203144200050b00031600c00800910904210b480103e89a115290a8540c0b19003217048009500021f6400341142d50ba40c207044031004001c401c0c402c41040003c0404d58002020304130074011101070300b100b80a62044a40090080c1d0409800107004025010f40c58000c00815000706140c018522015003440c3e2049980d220042c2010f007401c4c10600403c41794001244036030100002c3c02441800d50008860100c0307441c512903401d10455020b1350b84100d0060003056000e000801e5160b031104044214124500100e1402030711020303e4424141e505100c9480e00d550031180000e850b03c45c00310345503200011190280d925 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 474676537 1250 474675287 474675293
    0x3210f080a020d09060507091202090c0307020109151b0915030902010e18040b010e07081504020d05011d07110309041d06041b0807050d06051513020706050f150607 72
    0x1c0c0100054500110b080003c0744c000d20a10b948914010002035861100c02511003102c003460711045c91000390451b4401001520f00c0d04080d020755003003880d920000c03805c21130780c1c0c03144440010300401000d00c9960b81d00c4141101c840610446048068038100401c00a160242000004c03815813400001c1c96110485a011684608400385080d8401002055103101d550911a40d45008450444100c0311030f40001c141d8040400c502d80c0f044240d540d401c0f00640d542c68100c1c010081c4000301a0700141c00744001041c40c071050082c03502034505240c0064130441ea0111345010480041d00200901100c1031100515240c040111550300c0b800780c070045404540300340303460300922680000d031115005201c240304c00c00070300c00b000284080b6807600d0124200c1e110440d0307c2e00d54031603114442e44004812101c40000f4602c0d00080d1b800f02c0c00d09080b0700c0615000c40412115841c4403000c2413541d07070008154003002000e1061036081201a6403c13202483d00e20001c030300401489180c07510500e0089102010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 474677787 1250 474676537 474676541
    0x306050603070b0301080706080a021e07060b060d0203060319050606061c050708070909020a080123030d02250806131707080a0e040207031d06090306090703210f080a 73
    0x20075a0110711a13480d0380d03421240f9129602c1d03014244c005200303003021a0f0308801500940301170091445600307050008111135240c1c6640250021079840c0e07256a428000e07030380d030a40a4220740d00c0703002e00580c3e2407901c00100360601ca4400550400000c00841550109030002902075200c2d00179242e441d550f41807240e000729000c0150801120050070f180411501950154485000d8a102d4a862504d262520249401d03070180503850380000342440c004010320445c2e40c040c07500c40c1d0007090500042d01d01120100782003003100c1035000056884100180c05440c1c00c441c43d9501e83c544000780c081000e0516000c5034654101170208500140d1014451050000340b004a01c0400865240c05aa400c094613020241d504400c8405000c5010006404031600f00340c0203c880c0d6541c155a801c5038205034000d040c401269031082c00360041d006104800d1192020400a400388804100820740780c0e16500c1c000c0910281c02440e40f10601840d400610481c0e000540d4504401c41410402c074140d481e040d072040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 474679037 1250 474677787 474677789
    0x702030f0d1401081c080421020106170a0f060b010e0a03210503010521010f020703030e0c060a020d030c0219200301060803070b10120b091015030605060307 69
    0x15800034006400304045070150b00c14840031082c0c00c20707400b06a988010064495403840050044100f80c1e05400412030301c50b401850f03005200d41080c0316100a080020746041120501324030150f0b5407110240800000e00c01e00c451790070960801002c00034116030740c0c0e80403155403040080860340c0b6103040f0310040c1c1c001d101c1007a13101000350803c944240e03641440da0301c0b000080c112920101b00902c130f8202ca20b1044003181d044c0e420141001c803080d141c550b00c9441d00d0b0034a00d100d460a56a03110410010b9085000a02c1941e00030760740401d0040441190038240f0034954100351154400708904000f06402040d2003400a4450800042c084410b000513404c0c901100560105098071086100c100080341d050406100940c0031704040c2400c100052500700c415900412180b0303401800728500094103940150750020801150516103a59000b0040c0154001c490850720381498004003c0d00950400801040c0b00300003909000050715162075002c1d1142c280400790020740c548000400e141c50030020700d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 474680287 1250 474679037 474679057
    0x70606081f0506040603023d09061205150d05070b07030c05010c020d1b050c12071d07210b090a0c0207080703050d081803040605040501080105091b03070203 69
    0x181c0c4100781c04491400c00c0720100902a90740d8074140210303025040c05d2041106491b400f03804044007810041c0750855a92070903000e2040403818420700024180da0a580909114541d25051281c40c241480542a84014124209120b04d440c1c1000022640d000310003110270006d44100e0030341041810a103041030f150303410001d401c030740004145007010341c84042512464000c1d4000c01600701e00710b03c02c0343c882c4400151940095501000b20440d026000034000100d445003045841041c42c4c040468070500304803041544030303000a4810400b01c15103841d84141c07503600060300e10541c41d10a20103407409480440010100504500401c1040c1c159400800610001810303090b0524000302c0400142900c541040014041c80c00000b90400e00007440c8001d0300d0f03221000c0c25824140403800c98600b440140100d0f000c03106402c0c489110502400148003803c29075468035a100d04240025002d081c040e80603d000746004010440404281c1d491810640c4503e0400c5941c1d4845490480c9540202c031151 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 474681537 1250 474680287 474680293
    0x91e1e0f080c0a05040e06071803020d080a020f1626030324040c0804060f110c0d030b1e04050714130306060603020313030e01020a140c0405101a07060608 68
    0x7241034000000c60b40300b000350403540780505036110014002514002000c0d490107a10000100b20b0050040814080f0b98209402200800d51341303400084001050003400d45440800060503101c1da03a050007130440c3c3d0b040410050403090710112103270000ba8400d01c21101142c4044c00340c2e0600320741008203000404a940101c82d2a42055005031000b640390f01c0002c003000ca142002440641414003a84070f0803041511800700c0c40d6156256800034050340241c154503142e8541c40700301c0040c02175015048941c4808e000f86010b80850300054100c890b1041c0701842030240e404100146440e841030351800c00790542e80400c0d1a100d00c074043d180e0304030010300d618134190081900c001032003042c4203600450f40114028804d8940d2050207904a02c0141c98241d0400501d1800c8400f04c1d02941c6002c1c001c0d141071040760b9008801e40c07600c010b59030b50540354040c281c200d645103100c2d901d07150244a8000c04001401440c580c41c0c05c4441003050214103200103501e03c0030409106010203944040d005018338029 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 474682787 1250 474681537 474681539
    0x20103021c1d0c010918020d0501061d0904020607020d050c040c11071a04120f0203060c090123041809061104030c120b010506090301150602060601091e1e0f 69
    0xc01400b41000312020260701c440d015204420758030010311800c3c01e00c0c040c0c40d81d81003a400c00b1640c4e1001400002c08490281c1c08020791100c54007035100300341c02444a684d4480604004040d56952804440d40e4203101d8280d100900000d81d0b12601107030405036049a40c10500742c0d0503d440c0782405c03007280a0780c1c1d02910b04007900702016003214004610070442025500d089484111440d5940b4940003211140071091205100c00424080a41e0155024041040c00f000c171a50010b0b00c0d007001180d0404401801160b20a02941c10048000720780d400c2d00840300e405240d000200f03850b8003983c41341007400081002001c1c2040002c2e0302265025400100c103101e00e181403814410183e02600c02180c500c4650f0701c00082c030202104022036600d5002c07400707440591030401084800d400400b80c00703a040d56244019014528000c010070002c094503000b414452030f04600143c9a860a50700030010001a0019100582a4004008240c4518500f042400d01190700c010800c0752a50700564000c40c1000c070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 474684037 1250 474682787 474682837
    0xa050f0706090801050c040611120409092f04051803030c070b06012a2f0102010b1801090c0c020604060207082b12020f04061224060c02010302 63
    0x10326441500c0a0ba00c9141d070082c2e03510009402c075001107465500040c81440107101161083c01000040b0701d0600c112100c0602050b24105543d03c580d01c0703a110966100191420011880d05906032282038400750001812000802001040c5204407280b10311782e02c200245030b802d54444a511a0b036000701c1242c0e16441c0c03542152032030f50311a05080d0380203960040007032290344c854101c0300c11850004400e44c60340003241e452a00840a0000102c9003119a0301e45803082000790301c9000c00e850503501c0c40015103410304001900316191820314078060280340030304000100441c0189411200318090004031103081070003c6a00f03203503440c0d000390f1005000070005001d0381d0014a030303019a1030341c07005da414a0f850070f2072043d8810f030101501c0c1f4819002120903000e480c00f031404900c609900d224058580841c070885100940d01c2500400c1c04922107a04000c000351481c41928800c40c01c06019210301c000e10045030442c0c11051003480304000c200f960000459100750142d4100c102c1814100b025100151 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 474685287 1250 474684037 474684043
    0x3030309020a090b10080705090405070309020a051c080c0102160b07080705031006080612010f0926041206241701060b0f13030203150403140f0d0e0a050f 68
    0xd5010380c80740ba02c0000205044140348a00101e802c0c3c0201281c46401c00c200d000e66075141d00404450a201050052103070546840c000d40e80309950594001031840e05a1040111102d55a00003d008040e402c03043d0308078440013517144039000c2d0442817040d150501d007102c40d0301a10501d0f408014041510444c00e0400080c03040035030190303019844400c01552013004c112000d000855a0350803000030395104001342070140c66030f03907001380010b401d98642c91030300d190180c2550301c0081c80c2194543e0f07502c4942c045c80380003031201a6424031101c80030360b545d0306200540101d000301d010b0745110b0100c255040c01005129840360980311103150150b901e800000c180500485031600c244a00b0760414590740d14441410b108110689442d24a00d42c145081c94010000030742002c122040500700c00e00d00400582c0c1d04000c0140c0c0d442c038070014181346107450301c2c009001e0b56205091004a40060026080020400c3e0590340340015401c0d000640c0144c0344416071411400003030241c4070b8000c0e94001c00b01c20b0004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 474686537 1250 474685287 474685301
    0xc0c0316150c110d06180c0906170d08071b0c05010306080606011715030f060619060509011404150207030b070f02070b09060f0408010b130b090711070807030303 71
    0x80000074240000360740035120500c0c285001410200c4075001400780d4900b008000102038012440020940d07982c0b03103010603014007200140d400f00b200e80c00070004001c49000c0d2502410203108a4015040c03414065949ca0024904030b600b40480e8000080459120760550010704224000568402da02030030184401d80042c01aa40020b05206022540145c009841c50144c10107070744003012103118441040f00302901424000641024060b5451150303400c00c00c650b01c089480300540700e141000010041d9481e2114415610f100c40702004220141d00709082e074150602c2805e040d0320a083c00c0f00b0b00c103036034807550301315900f003044007a0540c0e4403545c00150001a244500c4096880d51600c1c84140c5482011030180300060344a64401e02c110300008000d4503482a000e81018100b0040d0b50034400c03260403a40044c4000ea646141c03543c0d00c0c3c90030650b441c0850080007020488103030540049a0445802403820f018030108140d041640c0c403042242400a20008041d44c0c030b81522072400030081e00003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 474687787 1250 474686537 474686549
    0xf040b0405090703090305030406051803070c050405010515030a020d090c08010207030201140c0d180b090f0d08010315020307090b040807030303051e040b0c07240c140f0c0c0316 78
    0x81c001036605004e4403a0420782d6426407a61415907947d41c0c1c0c0e0380080c0400400d004c1c0c3d100a0710b60030010340403041028191842c03042020000d05030600e0280400c0b5170341613204ca88914140b04204840d6450141100c7e0040100d480c0540d46650800003080602120440141000000080022000419030240000c14401c0d80240700365500d110641142030016584070700003e004108800080115900c4000100790f0211003051600d8140c40d900c1d050503080318100050703000b80c403900c06005018050071008403d0307401c01c0700f9294110f8486a02802e00c00420a2500d6400408181c505000303000d40070007042c251f0b06056a4640f1040350a407203141c544400c0300403d0034540404c9c0505452040402b08000c09190b020742c80d511a242d1401c01c0402802c503e45c000e10410135480416444105903d015403240c880000741e05423088180110b60b0a102c1103001c20541c0b8051007164003418007101d1038242c042140da61116841e003105424205403003403480e41445415070002144004460303040031621 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 474689037 1250 474687787 474687799
    0x50301030318050a090c02070e040f12020109120e060d0606050c160806060103110408060109050f0c0702031c0215010e1006080f060d0c030602070b10060201060501080f0a020f040b0405 81
    0xc01142c050801c095005241e800340349208240301c0701005030301c140c03e4603000348111600075a40e03060040004800342c038107030b41c203180c5000da00040c000c0500c6a81c3e8880c441d80f008000d4481c494a42100c908023440070f0804019044010525540d2510b00795509028203920802017a0303522000a0520390001081c100315019220a0354100d50301e4005803001c40b1047d030054106a030350040114002c0c44910181070300c9441c01d000214000748200112400303010103c80c0003a441c01c1195207000e0340000103001120f034050030410100143c0300865030800c000d5a14128412004444800340d050071034407058030380082c03210000010016920044907009121000c201c010081e15034004803031160049400984801d44400803070881d080c1041c01c0d440c0745001d803036007641d0581c582c1d4400c42030380c1c01001c00740d030700d200b507041800b9801e0703114242c0c03800414950000300012468000081c1a0341d00040c050012301c150040058110002c540448408140c4d2500c2c8542d51a00c0320000301554001e070050314040c103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 474690287 1250 474689037 474689057
    0x12040b06030d05040e09030717070302100b102a1a0709030c211e060e0d1d0d1a070f051201030204020703020f1e010b04051308070f0807030503010303 66
    0x1c2030110342080c41440340d43c0e4091803d41421160021000041d2501c0c2a511040041c070001c981c68028803001c0c1d80001250035910705103410020314181c1403030080c00c405803600b8004030032951401c10f02c0c0c404074140e00f040c050392501d15030f8040c2400c414041c1240c490841c02d91140070410b80d540030504401c0c0c5048400c1c03403511030070702c110749080301170000400c0006550010321446e41c42e15409078013282080d018085480c0303240da80b8102c0b42c0c01c0380150300c40d200e07001d9150381c10030000c0d0041e540484006c500500144030710700c0005160290885443d240c0441110850410f0b80300d98002003c2c058010305816811042800b10014512080380c1510018080070205194244190112011034104503025900c4d03034219001c00000f944981c00c01c80235841000500e170b185003c1407213120b1142140560010700221007045482c255502c45000c80d10952914040220000140c98280c4041c0c0d08400321949844e000d24007416200480c0710040d084e2030780403940e2002c0540c01f00045041e03a1007a40c40341500 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 474691537 1250 474690287 474690289
    0x60f060f091d1e071a0307030b010e06030a0b06090a1d10060c020f01030f05161209050d0e1c08032e1715040f030e060313060b0103020f12040b06 64
    0x40a440c00c4076009070b00b01e8141504160380a0f99110b00408280044d62034041c3d503584182e00514122201d480300400c007100300710341103426100b0544103020a09080250b03d40d000002a80c9200c01803e400d060750347c4030215010394980a09a07005050064104d51003a074403608110902e526040c444082d207a0420000f5081c0d81200070502d0480b2134035200c0a288010303544c00c01040c010011f0b2154100750b41d80000d0000660f0900a090080c00100c0c0601c211410142005019140301e403212110385040080c00c0f4002000000e2000f0240a58600711401c46100b50001e90041c0c800403442c081d921160f00140c09102481c40110700803e034542109003040300c0124543c0314203403000054021750b101304408101600c951a0750303c8040c04102e0076034820241c10440c144075803c040e00e040c1c8100600c44a09820540c104a03c1e140d906030460300c40e815498508011154445100001021183c40b801d4008580e4026016103da004401d140c5940b90812043d40304007100c41104c0503a20320200a0200e516 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 474692787 1250 474691537 474691571
    0x9020a0e0a1205190c03110f04140f0c0a050316180305151302090f18010606050d05070e090415020f0304030e18010506160218041b0f120f060f060f09 66
    0x113113034040061240d8600d15103e000c8914880740209420860004038141d0a5a6503c6180d1000301c070390680040a0800101c42e580c1d44030010904000080700b00428810541c003c0140e0703501c200c500030004800002c034602202d190750320010803d000c0c00001004001c001001c030b036580800d5a1100300c2c18081ea140c8032140c500c41c11468020750050300c0c941c0800c9008110451140d48030050000c0400c6610101c0c5600382100d03850740c0715800289001c50160b82c4400700b401095002a440e02d0140c010030070440c001020400041c01c02000b60048803003207021044a07030160768540c403034be96203281c40e490300d803c01400d04a40030b44407501c1040c0d560a0440c01885255a035416a0000340c0400e00f0000f003078028072800307501c400080e03038402da2005171820891143c030030083c0300301d10030341c55028500160400c23400006a950482d070301600300e9242c20b02030560704c0002480620740055050314440070900780880200007201784076184900380140491031a0344d0030f00fa00100c13501c0346c0c41002101d41195003030760 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 474694037 1250 474692787 474692833
    0x6020f031207120b031009051009050d1b0c06091d152b03031b09140d031704110f0402120a050907170a0c080a0c09020a0e0a1205 57
    0x101e1400c5600c0880c02640c81607080d4404503040803c001800288140082c0c505862520b038825920384079502c9404000c2e0600100403815a505030070701c5090420707910552510341560a20040202d1042c0f04805080d01c3c0640390030075170701308504072411519180e00519204841c0100c581034100002c004001c0080d4100c40c03482101d840e014000c0c04a00b00c1d0400803207451000d1a0018107130041010000d020f401c0100c0d54420388291000510503440c0d00c032079540e60b44008819010300007210b1041000070f0b001050704440d00d100b00c4089140b4602c51400359401e04100c0000e40c0409100c50800081041208100c2c80c40001125900e041c14800c104000aa20036801002000d10f0b105010510782c450315007046800120881c01d40d801035442c1c00034510030065440e9103003ca50720403c185018040941d1070b586c05044594090805448151100414201c0922a840c14030b58001200b10565201d101d150b600040c00909100f0010758070071641203100340d01403042c3d81d50f0080403122100007023800b014071 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 474695287 1250 474694037 474694057
    0x1050601090803071106090f1c1109070e01050307030906050f10090204230f06030c04051509030319030b0a06020109060e03040501090909050a02041b020d021f09110307030c06020f03 80
    0x300d07051710b05a05000e01d9400142446402c2121a4007200341e07503644448111044c6840c201c0c024009540d400d18407041e05181443d81d02500b03004e0280540c1b1071340088104644282801c0079681c80c0c80b0030a044004102003000136224a1400040c00b554200c000102c40c024010308500d00c501e162214100c90491003503200b0602c0640030041c078030b0010594404007654958000301403160760000100400c2d12a402210740c0000881c001500307111510f402079030740030140c3e08084058100180000880d0b43e078070600b4110410801d4100b55000168400d412481080302d0207402c01d01d28945d9103101038042d0022141c101c908a061003846900d0f00800815a0201c50701695142e441c40e18000200c2d005280b801d1094500d4051408040c0158480d401000704e00d501d000210340c40b54404c03250081c01d240051841000b15040760804550f090070180001a621920f80d8001640c41011b150040c840034800b41c0c0e01d138060188030800000e00c02c040c0c0440c011a02c3c903409450f2000140701c0080d44910442801c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 474696537 1250 474695287 474695303
    0x1213050108090f1204081002190804050115080d09150509010807050c06010f140103050420120d02071e0f2117091503130201230a020105060109080307 66
    0x4108a40c031500d80940c024200c20300350b500140006481a0400c080000d8101c80560002404c00c03444504010001c11303a85804004c500b004000441411952203451210f81001080c00c0802d0a00400b0360241206100001000143c15510f50b189034a0385840d65540010400001000a41c0420440c44c041182c055681e118640100340c0015900c0b001d0290001080040900118045c1c04041228501928103000400c0d102494070b2800481200d100300701a04060500303092100103661501110840c41c14412944082010007011401501004c00d800c580c51007445001307031074690085130140503166842c0d5039590440c0b06419104d0290010720800da101c41d0200804c10007480883d0006828030300b0445890b50740c91881c1c5420209071a10a002e0030710302c2001a0810362890a651004c2c8130241c0308034407504500e03018841451f540d02c00040030b4144828111a200713101442e429410300410a12003080e161720214074028002c1208603110350218044800205082d034000094503062a804141 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 474697787 1250 474696537 474696539
    0x6050910050d1b0b3004080c010207230607020303040b060108041a040317010501020f031e04050d060504050105010b190309080910051806070314030c070f0605091213 73
    0x140000702c102c070181a40c0001030200307510300000304074206400078524018100e4a404584a140f6015240801036030700f40030701d180400c2880031810094590181e041110315403104011800a40688991200103100742e16800d11601c030f82d0b4801e08040742d01d030a0513003154181d86d04c1031016030340d0340f0055a01402101c2048002401503214081c141ea001d80304000c507800794060300741040e00b0a40c040d00c2c101e000c200c40c443c1c0100001c041c4508140100401d200070301c10040445242034aa2040c50641d00010000c491035250340262482211300504029064525411041c200035008020a88048415500304800003c00c09000010b9030304200b050080340d201c4640c80081600100031002040760452028046014542e0760070f5000e010008141e03e409696444442050402c0c0d0001e60303405110f0a010311048001c260b00c109442c240c1c803e1b0064540e501e444070602d4034070300e01a1043c0100443ca96034001420060542c1001d4060700022040708e00c50303821400340c072900c2e0054030800c211a00c0102c4e4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 474699037 1250 474697787 474697789
    0xd0e0c0d0803060f0d080d051b070b0c0c1e0106050301050c1c060302031b011106072f030423090108030a0e0d060213080f070b0a0c0201030b040c09090605091005 71
    0x2d40d04054010110071000c2d140101103103010b1354440056500c0007011640301d200c004640203c55004130304000303001000d000581e01c41c08030301445001402a40000000444039802d20044504600d01441203501c0140b00031030900c01c50f0100581200b00d942007220024480c10140519402031090251440c105414169040d0710b48a400b000410301d00e44440c8000701686042c0448114983c3c0c40910032403011806001400d420401c20150440341d02420400c00300c0303036000802ca4003034101e000c1100d04070b140b00c051920241c40030b01c07030318030280c0400540007501c01c950709400c502404987c5080300701c3d811130a00300640304000348241019508200001d640b5680329110700080000014030402c00e00340c0e9900d440040340c0200c00d46441e81c0400380c0701840040401c124007859141a40c00821070f0904003c1880700d540500841042031040800030001168040c2d0031032926907001074002c12140e0f03e01440108070881e107201e025550761a1034000b19542c01c088030454401c1c1010690700d0b1640745004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 474700287 1250 474699037 474699053
    0x32407050d0213030602090301060b1602010513170703030e04020c0a0303050a0f06030501020a1e30020c010c08070c0803132906091012030f0207080d02030d0e0c0d 72
    0x1d648452140c0c00c003c556a0900d0140c1d1910286018010044c0c4400340d140a0608440454001c0341c00c0503402d101d05c40030032040f9554800e64a078203181c40c43e102c05080d0010203d9003035a13008440310190a90000188500000300780048a000b59908402c0c29020030511080788944048084e0507004000010080f80c0250885600981d0702c000000c0c2d80a950182402161503a41085903140d40019003c0782c1c0c180c2c46a03072810040720320075801c41e80c00b40e10000a0220305070f0402c00102040303425804840305100da90303030480e1010744071019959050030188644c000c0a416002c40c011502d98404039910302d02c03e108548120364498052483e6444010020341070050344e54084078508109280400783e84c00d94010039103800b45d407900340350032410a0000c118111708001c10700b0000c00c40030316040012001400400c00d0007905411b001904611502c000c03410304c112030708003200910440707181c01d6038103500000900c800c0c60200020085000600c146c03e8498402c101c6da1540111b84030503040c04035180c2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 474701537 1250 474700287 474700297
    0x50906161209061b03330504020f12100602100213050a060206010806060d0f080a020f03040617060301050411100302130306020306040e0a051e190b0603240705 70
    0x541010325000709041c280006442c0030768022a426901c85180030743c000d5100c00d104c0108a0303182010f11035091032203681c1c02100c00840c94120035101c40c120701250401c0250141e0040d05c0040c1003036644060103102c40900f42e02c0040d1520240d401c0308002154072011240000545009034082c01403201d2018031840a5000040b007181d01c150383d01f0700050181c1e1200f001e03500500c082c1c3c001e8805076141649040c20f000006049074020261100840000b40c5010814035045a01034034481d2034a000ea10704034a80010f20540d1703040c602c4001800f081850f0007035106e94520340d103802440c0c000d0341d40a05141c240e540036200204005801004002c640c9030403c009002c48001380b40050a105100d940781d0740307402940d0b10a807400743c0c2c000305002040c202401111110807c181c020180c041d880c0c0e0321550342d030104c4420502603401c0a03180d12000201030040412418880e28056051809400c00200708003050710032034070030f00c2400d074084909101c100c200351000301200310400d90340d91845401c1d00c141d484 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 474702787 1250 474701537 474701581
    0x606020c0607020a12031106090303060a0302011d0901030506090d1110050c070c0b030a2904020307032307030b03070806190f02030a0f0b22090611030c0319050906 72
    0x141c480040759070314001c1c00c17101402d800f0b80d13150311090408149907800c0c440083d0030a482d5410400401c0b106031900b02c002000c07a94203180c07c00c043d8075403407403862841d074410215a600094810000040c08400501c80b8041c010640558000980392a81038510b019101000d01458200c0700ea442c47e410700c240c3c0669803041500320900d161810541d2680032400030b64108000c112004001c0c442e694210348039009062105088009642064404000342520382c201c01a101d1900040083c0741070344a5005140e0222102c41485104000c041384118884402c540e00d9000a18241c60341341b01c0e1a0000b810350849040070080c0c42181c55101406014101c0380c101c1c00096070f10b1341d0440c600382d40780f440103621031a0361a1f0002210510724100030141c64038040c000f8800d8580d00c14211001a0f0340d0b038450300344000e1510010b902907052070010054844255030800e11070001c810000385100c40380080d440b481c900310302c00031050402c004030412a94251a80c00b42c42d440580007030440602c9407c00f10402c3c030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 474704037 1250 474702787 474702799
    0x50402030114130302070e0403200c1c060c03060b0a110312040302010902130527120f07060b241308060c070209150105251707050c01030606020c060702 67
    0x100701e0948201070074140d401203548100803c0c108140341d07051100c0c9001e0002e003040241c540c281510020a1180215501140407a14460300d900050041203040954000580400d2840b88507940441810000e000141c607181e091101c071102070b03446407090f0710030f036031401211508282491804070303041c1a00440f00e0580c5c0c40100081d00440f402100c600b4812440b9500110343d503880c600c11303c800540c01c1e8011000d55402c0200788582980d2481c40c41034049072103800e125104105010f45450300d004c0f400001d011000010b06c100b40717807080100800149020b007506000001d050310512240301031490a01c200e0305000751030b03011007103007507002091403120300780e100480340b6190070300c02c0c1c206071041e90420490380d07001a0010440c1011040b06500202030b03c240a000407100d40042d046101d441c00c0c04004013001300094020b51480800c00c200b05803c01100300c0c410b60382c140c960040d49d018880a440901c0380c1103c5101c1d96100b03004500075542958080d292888000b028000340d5001400c0c201e81c048 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 474705287 1250 474704037 474704051
    0x30a09060c081e030a140402131e0f02270d030c1a18240403050f040e0703060609120203120d060e0f060103320a06170f010b220504020301 61
    0x1044103d1a100e00030580680250340e401d00c0740ca0402101c4441d131102c0c038040112000c00015995042210895180700000818a8a03104a646c03003684654468010305510b0000a03103c950040d90103803840302462080440010a0079210700ba8101103112101d510801c40866000042d01c142586454948580090054501c00840f900b8142504031881030030360300c0c101e1384502ca843e010000403180368a8000c84080506102c400303180449801000541032140000d00c4030310460092044500604036240a0203c60030079460040181680b8402c80001a05001c80491084540c0c0e0041c041c80364000c0c010300000c0801100d600c115000f01014652007079030b40c0c1e80050103407100d04170603208042c43d03004003840d440c00e003002504450140b440c0342c41071081680c6015281d410321203c101c4840120810800310340d150b03940c413005011560441d22140c42000c010941074034000940a02800603c0c0091180d061000b0903c01070070321200c410a01d540101040d00134810f0a58801a0402e00103800407400b8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 474706537 1250 474705287 474705307
    0x924030e0f0606030606040207020a0902032e080d140307180803041217030112060b0d0611030601030606050c0c1306030b0106081008060708191d01020d0b03030a09060c08 75
    0x4010a556800c071142c10100c20800245405e00a1540c003250444045081484035004102101d0b000e015030f0f07a92a41c0040410010407c40040c040741d040380c014206d010095100c007000116405220714103080c49501d034040e0461f8002c010941164140030381040c01e5030342e11901140c0300501002a45c0b80702d001140081001003040c0010070103070000b950f008024444c54540001c14812044d00d10210321b0301400107104580c0b460040c0c4c4115504400045800b019400008100e441c1d802d0000300054505540d428040e601c21002d18401c4100340c908011051342c0d900256402c0c07040810b10381c05a08207070441e040c20301d042c00c20410003d40c07031071000920540341e0340c42d0700400300d007a0006000b145a0404000c5c14241c010781e040d0190401001130000d034100701e10098081034020b031202455420103039a24051090300c3d072000003103502e4110b80c080d08001c1c3c84e4805001f075001e01000c0f0a01801c0455601c1d80303050000444200302002e03510100752a18018086800c61050001250000c008009542803 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 474707787 1250 474706537 474706543
    0x309151e06081501381c0c120c0e0607050f122a0709091b180b0102010e0303042402030109060f050321030603150c1201060924030e 58
    0x14144030b00041c2985554039001c0020514168060b50303000c061810304078010b03644881841107101003d0121202c2c44001c494a00041c000d946c10411107845550700c003c3d01c40d2440c0c0010a0008040d214008001981d0340e950381900e800007000c401203440d24010307283c035080000060008c01d0080302515440e0f2004940300b0308007100c074854100e4400e004101218030809200c014450381c0c185803092080600750141454690711148601e0200301d89e070b15048018041e502540e400e00d9082513401c00503071903c4241041884040d180d00703811040c5849400c911a5005102d881c00c4200c0f407000440c1155203135604c030240c0f100c1d00c030b241120400c1c4410a134a8810454005103028100b40c55021503403508080c8100c44080c03403548002c0c46907020300100c0400d0361aa001c2e5056102c840c0d00f0042d620741d01c0300d011a01c2c1803064580c00d500202108204420307a208007015001e0400480c40000a59a0710103040342c1c01c00f050b010341141c2001007602c051500c2503000d104421040c0504020814502040075141 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 474709037 1250 474707787 474707789
    0x901050f031006080f10140112020a0329010813030306080d12050f010b180a0b04140901090606020d030507031b0c030e010f0e0402130e010f0e070309151e06 69
    0x1225030840c0000340803031034208403040d41c01aa541e494060714508a06e48444201580c07080740d110341e00c5582d1080d5107900c00c0094003500345001806542e2016a0344000b40201400c44400c81500594071501560303629001c0c000341d4041c0142c1d240ba07071548841c160700242444040040381450f03550900001c0c002402e104100c0d07070180359141d110042c0c101c00001c500740c03a030007021400501029070040c0407440f03001096460201d0980d07000a1400c402602052046003540c1000c2000c41740440c001440750800b02220164440c141d5487c40c1c03a0740d131101d414007620003d000d650050381001540b10700310f500c280d00c0164040c400b0302e070100b9004a000014104c04809241c00790010b80030f44802c205050704542000c208800030301e041c039076915100c0402840d00d40150841e501c07440c2c001964070f9269404901c0c080c0501101c2216a2440d65103c0e4400001c19507407054500c81400500001c2089010303100700e4502d10b400550201d5078543d0303041d041d0014544420150901e1024021244940f201032261724 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 474710287 1250 474709037 474709051
    0x100e0c07030f0804030c120309080c0c0301150605040b070c05060f0309190c0501390510110403021507051b01022e0216051605010e010804020904080901050f03 70
    0x954503191414014010603804440e042840416028000020341c06400c001015401c032000c51907060003080c084000d070a1305280031300f0442c404154155602c00200b1007a400c85400c800030080c0b882c1c0071041501d05401d074803032400031545c01c0c001000094010030042440c0b5122b030f45c001200c291a080042c409820002c81070f200c030784000c07042094200003008511004600032401682301c04855503600f40030740c81c034014107041065200081001c0c8489240a5081142e021803402060030404607800da884460b680550726403080c40d070050048102442030000c0c005900300714070710701401e40e000d00a07140d0f00b08000c002004801c02000003c510103100724219586a07800c141d2510300001c000914280d4416114428200030b607404000701468007160070103404500c40c2c05610b450030000112580600c1d404090454054400225044d0304070100010a4031030903214401007513000801147d030a0001c45000f50840600f20208001c201008080d140040c41407600720325105403588100d04d01c0d00b0030765201c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 474711537 1250 474710287 474710311
    0x16051905030a0b30071d0a06061d0f0d05030318160b09040f06030c03050303090d0306061704020609190e090115230907022d0a0209100e 60
    0x10080700001802026200501120303040c0000d032190303281c0d420581e071980ca4010000305010310b0b101300701001e20188004282c0d2010481d0340d004604051100648100c80c8022294901030001c200710340140c6000380000c485146009502150005125224483c0b44c109584001703030545250000e00d007000214400d4280004042c2c080001d4941c80b0b291503000c030030f140a001c1d0b84802c02d02c11009520140c41c0e65000890f00496002003050b0000020300c07158101a10044602d4070101c04d02c10000300450159068604840900c0640002141200d050b4020b4200080580f1515101c910a048020740c10500080c0501d02d8004220002000140c0c4612003e4112083301c0080082040710842258842c507914002d00001c02c4860f000000d80c600740c0070740c0d032200e0061210111880c2d0f650f4505511101c019200d8200350a01200285d681c0b101e8850040b85d00b0140003c00c40d0400304000080820900c020007014a021541e08000070040014844612540740f08000940c0c80744204250b40104a10252 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 474712787 1250 474711537 474711541
    0xf0f0c0307170307020c091f030b04120201050c0412030212130f12031b08040e04061406030c0603150d0507090207030f030509030d09050c19141203031605190503 71
    0x1011903061190801e203002ca071800e02c200300490b500840c07030781990345045a40d545c4035607411141403580702c43d07850b615003d0301c00000c020007003021405030300c2d000703a008452070814001203400490aa0300d0031a003d0102c1f200902c402c11101c4c5007080b060904512074015998170313030f24040005040d44c01001403040c441e450a0000c01c111111010b4000103003030443c83c01080d094040c0c1b0003418001032054042000e0414024603404e000c20a02681c01030403000400141c6030910b800e00c81c01411008039585400700180d0046a010b10740010f0001501001600c07050465a0349012805815030101000b40c100ba041c040590014209100311000fa2942c448016150422810010110010b0081e0802490b01e094188048000000705403000b81c507280201051b0421513160640c01c061204800d2074201808100c6030015400000d081426a0509594210b07401d003120204240645121000384541e042000424081001910766001c4c0c0302c2035003400c0b4500026141000000082c0c8189980004c4000c01 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 474714037 1250 474712787 474712793
    0x1b0317040614070206060a0b121f080102070609200907030f0e070815010509191806021801020607030b0d020d021c03051e0705060f15040c0302030114030109050d050f0f0c0307 77
    0x10110003070b040030161389060006202c0f08100311427001c2c0c9141401c41030240c560309a0091400c48002501c1d00c04020740d11014640b5181707018103480300301201c42d440c1c120103840d5010035101c1101c0c0704404c01000341174913454010065000301085c0080c1d184c0c550300c5004a2010100c05c01070017006080880017021010b922056080c8034a5040e0000f03481040705c0d005216007070380301030741c1034a07001116140002d0072a2043c450521058800c40d00400e0540041804400801022040c4407170580c2a003d40c1d410303a542c040103c0c111400302001c03070b83c000090111720340542032207040d4504091000e001066500451202c07030405180c4550210005080000d5520300d101c03404869076120f4086408103400c00304581d0f6510303180c607001840020300150b100000f68010050300d4620032400006001000f071401011401000380d4001d00071903903003d083d0340360040c007030070148a00418141c006010708805501c2c200121020b40c0b01c58065a10100180500e00d003c1031039100400036403103108011039403508145 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 474715287 1250 474714037 474714049
    0x80d0206090f010e12030c0d06170601060219171605030a090510173c0c090d02060a020c0406091b08010f120f0c06020d1b031704061407020606 63
    0x10b40410000d0341092000380754160009104505441181511501d03542d44099802240c041c03021011401400c1410008903603005900107035901803404140c1e21142e8880005a80d203402c442211a0911155104807020030009000211006441205645030a4400d1006c0c0c032044000c100965083d00002000070801d90000030710070040909551403030207030300c0d0810060403402c8509040034a180501c00055417640b181034003100e6015401d02005410144a01c40c981200554070a20310f02e500340d003001c1100c4080080655030100e100624a2a0048444d42800400c5d007203000c4190940c800d030315003403801c0d0707644d4010940600000440007815002c10007951080d5040d02c10031b4814071030200014031555400100c00b0080c0da07149074402c41410400d2520407003440700302402520781540b19501240c0d00e5400f007110803241076107940b401d0380303c0c00030f22102c00000c14200008003c502d031303a1031442e0086000707000107078072a010b03280002d103100041c85040119081100c0700001a0002801c00c00189042 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 474716537 1250 474715287 474715303
    0x10306030215250213020304031b05030a02070504020f09150d06090f06050603060d03110307080d05100501020712061509051005040e0109020307030f020607140a03030b150a1206080d020609 83
    0x5200030a10f426158004c9040c09440c0d10004a0140d0004001002e05004070520200d4808000f110501030134036050840d220340004d5150700042c042c840001960307140c20f00036107003110550190b6900d000414010080182d41000f0240d000c0d5105200c003034807041c91031003210010039500310042040c03050040c95004848003500580d1241005005009a546030908e1880d500c0b0340c9818440e08440c02d0100c03080c50750052410041c1905000182080903402c00d41200c1c0c010001840341a81c1517842c1e40c0107984550160184c0c4101c22a02e00040c0d000c5240b94100780081c1d000701d1604645151100302020a4070b01c01c540303203840c0d103411001c01c10142c01e0520030850090011402044030b0350031a80029240c3c6080c0c800034207203c4003a0107007015562a40c2c12503d040d03500c265050040d0350218007060702c0c1e41301c3e82011750200386001c48a80c4507040990020044031101a00e00349081c0c2c840e10151042c5000c1c44040f03941c0c507075403540412012070412480c14100c190b90001e00c2546804e0482030315000c40 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 474717787 1250 474716537 474716587
    0xb030105070c081e04090207030203090f181530060a0501050a0e0903090402041217030403080f07020c0405150a08010c050702010518090c0318010c02070b0702010306030215 76
    0x2e040c64000308481c4000d035075510344401080d000349058140c01e1049402282c11402e42c2c00e00c005409000c054001005140ca00c0b03007520b4a0003801c034080100810b0846945004400740ca01c0c3d4001689070120000c0259000d40c000c11400542d0942c858024041c008c608000804044c6240400c010070700401c103080d800105494184003030760519010038100d80d03281c40b6403010701250340f011941407030040c01038a4855001610454995583d0380680a018031801c000b03813400c1e4420450764111029030f00407280b0030383c4c05885880154454400400044000804000071405800f1208543d540d0300e0140d54083c408004001c155100c21104022541c6016070103203c05030301d8a02e005000d1600503095880c07084d02402d02c81e0315502034181d6041080c07020401e231603100303c0319400c100044e4000800345001d8a8a15000c01e803103484110030398201e50b0941c0c0701c0d2025078040d801c108011400840204000f503c113150108102d541c941c041201d9407040c01542429110102d58034110116071a038951405503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 474719037 1250 474717787 474717797
    0x4080c0906030d0c0309050d0b0105011b08070b1305060a0b2d01031e0513140f0a020909010f0e0d03110a0801060507080c0a120e03070f12050c090405010b03010507 72
    0xd054000a54aa45801a001c1400a00c8404c4800e140c000c60150009001c05000d050701e4240740c2c9440301a41c0802d01072140403e5540310030500c01c3c0301c0350f0030002c4a6540030317410a00d0203480385c0310000111390081c0711109101000446000152086c800ca60280b10f43c0140400c1080d56042000824001c50101070084403c0031181d8808404031b00d414060344401317090004401c28060542001c4908001007102d005081c0700511071014401902040064094008041070701e054001a0781c80d402880e8622507150701500e5503101500d046484140c000080900000e4940d0301e0028050507921626000319840d0802951455415010701482060880070400e0518211103a2400380103030310180a01c1e001c10101240440c100504607040743e003100314140c11116072a00034a000c0f0305100c21f101c82600000c44590b00500c003801d0008024040d240c030541140d00460400d043c2902042018809898600c110f061000a6861b011300140c0964040c500120382001c0c80c0040c90300f510005440502084 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 474720287 1250 474719037 474719041
    0x2010e01050a050409020f0c0a0b0702190b1915030c0f091b23181513120503120108060f01060504050d03110a120908061503060f130b0c04080c09 64
    0x3e034014202e0781502d180f50401600c6007485d610741c0351075010f6408900341910500e400002881881f10104d84200e055900b2036441d1802484045404c40701130500514902c2440c0114581c00300031003401c440071030310180008108141c580440b0302910700e40c1c0191502429918140078600c902034402028001a140034441d1001c912030a044040f418083e9000300001d40010305000310840910782c0c0013520040420761201380c0d080c8d42100c0c4da03030003d956500c541b0350070045003410340815040d202d00010352100180c1c01c03403030310451032560802c001c0200c44034002000700c804400a1501750078040d1404000502e4203140c10603880c8902941030300510144039060008010b6035a0f00c001d204400d55152506070400e83c8141d4034145041c1c0740031f50081c0f0240490050980c1d990703100c2d2010040b01e40102c01c0780c0c155260720f41d646800200c4403900365015003158000444c0e042080c00d0700340e0050b0510f6030001e010132446c0c480c0c940e40d1000392844900990002002c03c20000c0402c4500c402850840b080201c074 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 474721537 1250 474720287 474720307
    0xd110c06010519090c03020c010f0b0a051507120f080c12420a091401091112010311091f15030e010501030c2d12021c060902010e0105 59
    0x1500305104881c41840004801c0301580625101c100c000d0102d640c0a028001c1c03044009000394206002c10880796282420000e03156555000b61110660b0141000507207034141002e10000c44040031a00311281c00800613000003d040c47c0403000103c0c59a500d1028421800800800d03035040078180004592007817101c0403801c2c2010600c2da03000080f288118001d942506141080d07402c01440500b00140150004078824004059050030403100310381240d0721a40702c0329060100d4143d0000001c800c00194018403445005504c070440b0030003030040c0141030904d01802094403840c240c0040b56038500c00c10116800c1d0030b01c643d1090304400e66068071a0042c40600e455000000c071403060310411048447e29407030150095004484110094009105a6840f810680150900c0713201d0185000f4256084483d20b0a001004080c03401909426141d40c514201c60b0640d0300008080c180d0780f1130011420300d4490410091782804041c4a0140890911001d000141020150910f03041c18060100a080c0003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 474722787 1250 474721537 474721543
    0x60620030f0d2c0c040c090e0603010b03030309010606030f1103041209121406090309060a120b060318120405030c04052e0f0b21060d06110d110c 64
    0x100072001d5807042d01c4082d055490307405002c0b038581242200390850055109841e1580035008055040c070211443c2c14002002e1008071501c5940090004d81000014083c8000b112001c5812a100600204031181090b0000703041da8004d40d40c0034056955400700700318190700750051850b101f40701c1404000c0328018100460242c880204002c12160314645500361003406034a400014018234124980e4158842c40c14050b50744000d80780301454030844000802d1100004212aa500d2000e0700c018185007403214142d59904289041e41c010ba40c9501d9541000d4941d18081d5215501844c0800c01600102c1e248505118410400480e0481d04200502168500140039811a0003c3d1400103041d41c0d040e0303082d01c003c4d103034a0b1808000045d40380401070311081e4101503002e4403c4040e0b0480401d075651184503140c459905080305815140080c13040203600d441c600e55120703a0280c0091207000407590341d403040780c02c102c80740e52400f1000b0070f82c07140389420382c490900070020b005000c03440e00303114130903e60b9 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 474724037 1250 474722787 474722797
    0x3040e06100915030b1f09030b0c0c031c14220809100f0807020a0b0601110f071e061d061c050702030316020a0209162106062003 57
    0x40a14000d14280e901030344642107120041410f4224404041c20f400030040290444401c1c42c0c0c845c641d01140601005601c5010348001d50007600c8100e150741c5903907141103440790001c1c101103481900b4018000399080c00c9c0300800c800070b0506049401d0840d40212031044540a510600031086107a040003015a00c0300c03a00c1d107442c01c1400c4004001c00c00d51804c2403075441200310140c0c01280b00707072803a44a01d81041d1003205d00802c80c1c9540d02142e0314100203e03555610410090700eaa040728010502c2940941081344103d0540020344040010880380c00785094039a5010089000702e0580042c2d140c00d4007055000680441d14001e500643c2c2060965030025101083c5882404005004a4003242410b801d405448842106102501e003651003e9220307041200e08030180c01e40742e908a0011480414031010301c0e6070003402040e25440d2140030804030740b0000400c106005110340800d031134498a12024400c1981044080380c01c90400760020302c1c0e00103e10a14080424034213100c02c04c0600031040e96 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 474725287 1250 474724037 474724039
    0x9090606090f091d0a033501180e010908030f0c0309030f0310051f02060a020a0207050f04061505090901050621270a0c08060c190e04060b0d0c11101a04060b1b03040e06 74
    0x1c9192744452503c80080030f01c0c0704000d44a618044041c03042242d05809588a18212010210107a80d290b000d12070a01c021144101c25410802c10210340c40d1288024680012001d001490800e1722038010070b10301240070087c0c4550160841503280c2e250341c10800349070b001c041d02205500b40900e10b10041e6540b150360084c10301c1601e2503140c1c5441e5449580c0700800418a50703070b010019000c004400b901540c80040380c00c0c0550003803800401d8504200048690078210640c103c5070106149a46040346100a001454540e400104140d10300403103000002c2440784000140c01c80c95402c1c90040c01440c03c1d070f0f11200803a0400020401c42d60b11110a0711044000c10400784c240c8903e10b1000c81e04490f05180080d4494640076020500060b40c00c003810281500b20740801c28961101c030b042c0d6503a00d0908107050964010305a40c156101290800325255110904000408071201d001900340d52444c0c2210b80302c14004503842072b4907074200080340c00001e00312028514107801c0041c0d0030281c407001400c103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 474726537 1250 474725287 474725309
    0x1c15050f090c0708030f04060e0a120507060603230606031c1101110a090303030b010314130507080d031b08010501120506031c09090606090f091d0a033501 68
    0xa510700d5050307400c4a0f00290701031480781d0340380b50060410305501c60540e002e0f903013203242a500c600000d50000c0c05811007904a0030015080c5041e03041180d90368000501121440e849410000000f00190341103c890012440c1c41603000d02508449881d04000a0510b0700c25484180003101c011344501290300c282d130403031078115141000300c40b01a014120030b840c01040c50307200280300f88070158041700a50540344695024405506910011000c0e200f842100119080c55480419241c06400e200e4003040c62248042e07c403150b0303403102107505080c01304900e6408030752070b4600402c1030f51086840e800003031410b0600b58015410900020b0000300a100c070010100d90324404101c03e0303541088281071210103950b00d030109484001001b0702e0300003d0711400310403e0900e0f40200d003e601036620181038841a25078580018542004000900194500d8004068840141580040043c0520040c1902948640c0103030207404850410302104c4441c460451401e0054102400701580700e01811a400361603c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 474727787 1250 474726537 474726541
    0x9051503010f0521060114100203090108010501120b090c0702100c08030c0a1106040c030c06050f0915070b0f0108100e06070305091207150f1503030f050f1c15050f09 73
    0x1010f4050301d4940131020480c03182c4000021500c00f8072220000f030381c10540301c5071400c002181013a80d03071340620440d641c0800c0c071110062281e0b510490045111440003400824008540c0021805400d03041d030720210084000950402076040c25694103103403184624080c2d9103812561601190b5001c0a8200803440e0b00020b40c0d0002d50703100c0c11100288a2480c001c0ea070b881e00f00f5142a41e4484014030080b0b4212050010002e19075008001344d846110204103800c0c0b0b0a4400c500308203862080320320384800070b02c6c00d002080228181c03400b00352280c9802031003c2d6455061074090b84c604440c030030b500e003003060400e44200108107000c43c1141e08038900d810003040070f4a407c01514282403e00960540c400380200d00901806020390065060b000146802c000401016510a050f0340c26403101049081210b001000064807840e45c4000b50300182c030340582800c0d401d04032043e4076441941000380a0400e60749803480f40c000c030f11442442e40d18940c0c1d8034580c83e01d0600401c10f68101104128800d01d08000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 474729037 1250 474727787 474727819
    0x4140403090b1e0c030d0b0306010b1c0f020703020f010e010c0516240f0e0303011d0c070c120501180b16030212070c0c0e010315050705091009051503010f05 69
    0x144120140000b1200f5944440c1310001c1e2aa507500700d0440545010700300501109641004101075046e44c084a402500c0c042d155881a4224203850090001e019614034584411744014400340c116548a030f40640480c1408504460958416104401c02c592400d140d9000700c6804c00b04131782c0042c0869071007a032142c403181810140b108101c5000f050040b00c1e081c080329050b00c258403801c29000c8400c804c2007d40801a81c0315941e01090144180740101c1c008482e60710071150b0440c40d842000c500c9154640309081d51040300a4510b0342c00310703090844640e42801040340a0240c4400b030441c059009042c02000d89901030b0042d0003130010001090f00d031f0f07200d0b00c109219804581c01d0b80640c1010710814100f400c80240000c14201c2d040c1e0b40410342c0031011803404400c55030741d8100c03038014a140100385c03502ca044100034400a85101c1c24020304000d964016140d0082601404031151510b405e400d2800c0144450140300c003089401000741040140043c0f01c1000f40b80701903c0080c1c0311854507081041c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 474730287 1250 474729037 474729067
    0x80601030e0307120809120906032a0d1a09060f0405060f090c0d0b01180303030b0d1a0106020106091e02221518031101141c090204140403090b 63
    0x1002c044c04c43c288410f8104215a00906114025043c1a08458022030315641883c901e005111000b50b0050341040440d504114225000b4000c11403400c581d07101941e0b5005890103507015001400040783c648038120000c80300503c0c100380720401510401203615140700000c95007a401356100c2d20071079542d80410340390340301c44441400f258006031a80781ca0703003408103150313041e81c0000b100700d441c40e401e0010303c04c2e0552040b0349110305040000b085901041c110f95069002d4010020744d1038220205038540804601010310014251070300c540912025414041c1c002e080d81d81d00d810440c14941010b180c050411202c40c100070100c0c0c4100c00043c0c07a9440040400d080252841420f04142ca40000118480c5046030480e281c1d94903036110350398000b1480c801100616401d2102500102c890644000e855000b114032002d07141305901e210303282c0820f209000c2075084c2e5400e0580c8503660b079030718480304605040c45044211800e1a415218a2a181d50010301c0002c0d94026940c41010100b0240000c0c0040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 474731537 1250 474730287 474730297
    0x3030210050a0b030708210f07080a02010b090a0c02070b1603181706070801090b090a0504020f1e010e030625020106081f1d121804061d070906080601030e03 69
    0x1400c5e14001c83d580d40315107035682182c02504a01c440210f80c8100c5140d843c00448140380c0035245558205003441d213420300641c120741911001e55403038503002640c9a039000c44c07081c461b624100d00001c0100718140028644000ea4000301900041001800214405031181c81d2810303616180030b54020003015a001e5054043c7e90201080000780380401c40b4806021400612070402980c0356212680e840c0004012355550b0480c468002490310007041050901d90005a4040d00142c0996191058640480c0071200155046081c00302613201820503507900c00c4407694801c0d0118020701103400c10341d900889803210071815000c070300003a21341401d05e10300039042200140020b2099840120010840c900c00040350f00c0a0034240d8909030f03d908080680211a0528440e140b000b840d000c0300003072400069a0011210072000d81a10f07400c2c0110303550394002c0d07e02074980807400181d181e2003520b038059010000b038925001e000c0020028464140e010752507075402102403801092030403800401d54114820 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 474732787 1250 474731537 474731539
    0xb030c011220030f01080d18090c180e0a061202060438030f0115091a07060f0e062202131b0e011409180c16050a020901050a03030210050a0b 62
    0x80401009904c3e10462980c5040303c20700c409940181b0216802207454032038041600d40046459002800200d14991000d01251010306000010791052030f0000d020844a600c41c001041c040c600b0000c041c0000e014210080400781c0c100c1f58110402d60000d81076005900849a801c1e100e600490303807020070300114003112000b0f207090591307080b101c2c0c40c00174060303008903840f40b040e072240000000e140c2c24181c506010311210340c3e81d2007005804d000c080e0020811070038081e00d0001703080c030003440403d200c2d20415841d03000260001a165240e4140039090150080400c0d081b006610304040ca46800680c000c00342035170494402d00c03d424030ba03203010018000600c940103801c5058140c020318541100700445800026202d6403004d40f0802291401445807139185900408000c041d03d540244680c170441d041030607002c0050420007184958500210300302c905031141c1d80700c43e140310203605104003564003502041c0c8201b42a41e0942c0c070040e40d02e1403055043c0a04955880c0011481a09075015000d1500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 474734037 1250 474732787 474732851
    0xf030f0509061b0a0209100f060f210b030f030315010c0507030b09030f0a0809101122051906030506100914010309120906030f1401060c110913060b030c0112 69
    0x1e012408200310b441f070f402030000722220450089000c41c000c2c00c3c110803203074090b0b03103418403520302040c1a4080140903003400c0c0d8454940c1c00140d4980d1301441070180c1d403c5254001c0d5202d1514002e2103c0e0145107882c00d0b4140301c00303410031001141012a82d001603940002d444002a169541120f26500c5012305a0000c10780c0441c1154104c0ea1050205009a0001d000c4400301d0a0f0072440303004660190060a007003500c1040105c2d003107041d45e2071200700700740107110b610b00440c1c2e1880031848802c051078034520582401d0f1020f2090b56094410950841415580107030b420b0207a52028100d0f501d01e00a1045070f0850315850280703684079030030403c082a4070007801a00d50418100280403030030319001b11801b01b8181444070b100812140f0803013620320304a078025a0140d02c0c2c40f00c15503154054280035038a070f000403080b6a2164035440c0c00030303001d8050392100f8100968181002801c03501042d00c114400d41040300c44a560781e9100301c090300e2900302c03c000040c000030440d11109000034002c01d0001220 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 474735287 1250 474734037 474734041
    0x70305041509180923100914010204080721050303070318061e0c0203070b070c02010c050d0503100e06031f090c030b0403030c08160f03180f030f0509061b0a0209 71
    0x10f0300d0b81220f01181c0c411842131029a0038920f13103030b102c0040020054640c0d4405907891040301100e030880c0c109140951640004045030280072070981c1d029410070b141c1640022010040841d4003026448240c00c401d042c02da600c105540c800f0384038800504040101610343c00b04082c400c0b00401805001c0358480300c1005140c0124010f001d44881d0564035030709c1186400161200135001208642581e584441d0784030383c0750b940d03d40680d044031460308280d04000c1c1000080001402c100074000800307400c0c0d2610f40d26440c000040624481064011192800d118410b01c02c60791000621100340c2e401070000035083c1888601108000c160580000e003194425000020030300041c080202d0245000c0c3d0b074280070591ba40d00c002e9134030340c2003a1401d90081c030300c140311034040e24410780031800700d28804d24001c60030300726070040003200c03a0002006580440364800980c0405401440c0300c0b04002c40b50a100c6e040c5a508400100345009030170000d071062407242051801350000b0311200b00c0780e42d03004003049054 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 474736537 1250 474735287 474735329
    0x60705070b220b04120c0507050d030e031501050a0b2506180602030a050609071b0507050406030506090d03060609170c15071704030b070e030a020913060f02070305041509 75
    0xc0f0070030748055480305c4c3c0c45042490800d110300308158055800600400300c0c18940802c0c0054800424025070402c5072801c000c290650b02404400c2c416840320071600710035410078040105c0c40860f80d100d508000c0702000516400440d032a400100b0703081c40040380b0100500d60400e5005411301c2149040c0d400d540110403c20048603501450051009100412a035602c0313400384415400107a8070036021400c82c0d0503201c2482c420f40c5102e107034a4031803800d480c0b40365a14070108050740c060342c00c1114a45c01c00c0d0104000704104110088004004c0d02d0240a6603251071400350900c1c410b0b0140d0b0f0140a9501d652040203441040f00045505016103544590090840d600500e0b420591044a0300d0114548004181541d10305980960390092602040c035201c050040d143c60510480315605400349500710400f41e83c0b206505881042a0507001004070000e2810504031075003101c40c0c0c02d00501c14401640440e91003419101503070030400d40884407414a0390300341e40f090328503840300c400c14000c41058011 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 474737787 1250 474736537 474736553
    0xc03170907090b0f090c03130803040c03060c02010b211e0d120b0112050901090501050a020a0e0a0b12041416050a270f020408031b0609060705070b22 66
    0x494160500c20404100c40d24100300301d4144003107800340d11817080d4010822a9a0b82401960811080e810071509000142c0d262082504100c40540780e40d25814803c00a0100c540500c80314803105100800242b0b1040000550700c21030311211103500081c120b5442c49400e0100710050504445030068008441c11560551343d4513038011450000400c523001818070706280d0b003d08500020161074680310f8110490804c170013000c0040882c2c0c13596407120140c80c0031980a104c0c00e801079852542c09a506c0b60640c4e409007070780d011424400c0c01204100c0f0100290185c1206549070032480c2c03003804850340c9407410000200c28204803400d00c00d010b0002c3d00c401214010340940100d0300262044882165a101ba80038001100d4920328000d00d10880480c01800c06588070250b070605212006041c0740d02c650f22140742d90010000c0f001e0004001648414480c01000903d510001d00790081203940380003107000300325000341d00c0f0041000c0c216801250311100d41c0b070301012220680c41503c02140a1a0034400c0e4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 474739037 1250 474737787 474737789
    0xa03020d0c15020f120403030b0a0f08210c0d02100f020903030d110409020414030105180d0804020d020909162102150d0203010e16031406010c03170907 67
    0x240c46415110352045009403281c549081d008100030304190040e01401000e50b20080e500c8260f54810000e4807248424604c0c1c02e401640280d4002900d45a1001070101040d074603001a8000184d0203420400264002844d010a60800440300e000010810340003150b4010207030401c00a024042400b07451550000f00a144600c01c9082400394156900b0284101c4c85207007119605501b0800c0b179612440c8076600103690307841400104c0c501d0281d03103120a41c12600160800c034007030320103030052142c10304c1c0074040e1071340000103407156002c0e19100400107950b880d104200c8038180013410002505650710494040c00701500a0b1200d14285003501c0c6180d144c19208441000510070040d010030451724266040740c111649800c0d41c901d00740c40c3d4007042889403030504903a070142802c0124400e201800d0003c1c44c000c01c014800c60b40036040006842c410883ea0000440070145007002c0c0082d1413400c2607800d60000802c4c00d21240d28101c904003114140501c3d0052030030b80c20588288404110b0000d2108 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 474740287 1250 474739037 474739043
    0x908030f070807170106050c07032f030318090a06090216031805010f0c140102071241070609120f02150c030c0c0a0c0504050a0506090c0d0f0e0a 64
    0x40c841d83d100a400c0e01c00002c10000c0c0c3c00c6000c640b800601c8224081d1004080c000ba8680407510141c6d0b0300c0e56040001c1e0081740c070010100035141d003c0c0259200e02c02a4010201088000c6d50800030403403c056030a242e034503081c0c5c0c402d41c00003000c2610440a40d000c2c401403c4907060655a5081540140c0035404030300c1e01c2103002880e4100c1e0f0011265018032104107682c4140e42d16140a80e40784411900c0c40036801044d40c00d1003c40340c0e591007100713003403008040d02449040e500c19000c0c075080c03010741403200d2040d4940300a1041615813101c4001c200c1040720441141100d544d07104071800509000340191507005007403a107004041f2081c4004080341201c10419a6140b9076442440401240c581c40c0c0640700394800d4041c00c01040400da0309801640d80700c02d01809090801d140d2008462a10101c00703402c1d9911000300c0414010741c10a03001d916407041e17130f08074240030504003100452a584d500070901a00400003090000001b0300315000200308402e40c401c28410140200450360303c0b26040c2c4e10803 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 474741537 1250 474740287 474740297
    0xa05040f05040b03210c07030510052404090c030803240a0501020303130212030f041409010621022101080c010e030601030615030b0a1b02120412060908030f07 70
    0x980780c42d181c0205020340002501a01c46202121015410011783c1c0303204058421045c80001d03040101040350900440c00f500c024240c01e20014500401ca07800542122908481c3c4185880c03000c001c0300e07101884420581d0b000803107038254140490450441d80004280d07102c00824031a442403403032088071800a0a4001c50205000c0b01e003005201c61282c8a82400b60b0000c3c00016500300055100f44082c0340081c00b01080120180c00c164150f500c00012905900c50204060000d0f801085007904500c1054818140b40c0d41444009042c20700d0b203110744e510528803180c41100042d83c64042c0c4203c0d880c9541030244c2020140009090920b090188600f41d00c1180103040d4170b51710501191203600c0004e0050407542e400d6481b0310019100c081c2602c21101c050a0f40000040c0341c02c1c0045101d05010a00041c079022840c031074031800302c42c1d040d401c0210751040003032501c08070041d4200c030110f40c802021913100440900d8088007034194020054500600481008007103020103050511803540c0e0307918 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 474742787 1250 474741537 474741539
    0x1a04060c1805061e160507060e130e010608010204060e090a05010308070f060608030a030e0105132001110102040303031b030216240e1b0105030c09060703050d020a05040f 75
    0x401c5524034100d0707059140700704203090100202e08100004003030320720186400c450041300208114506070b00500b0344104500140244006114040c005000074000b1454540552150000000c115a13001c01d42d28982654030b400d524000c0c032096001d040204050b000031754859a840754040c14a08480200e14001d10800c00000e4103041a07106250503694024012414807580d51104100b4240c0c0301c204070384103551a003011a8116080015062580340b540e40840c21406480815003900c0c40036050313505150071034880b0000550301d00010003100505550040c0700504210049601d030003014074458103540b000502105143d8180c20800409580b190382d020301c0501401c0850032482503001c42001c4017100343c041400111404503019078211000c2c3d071072031212000b01052040750181e1100138015070024011044002a81c007243d110b01009090a50441c544541401458821941e156128820004603002014021400e481c40b00c0c02d50700c4111340315191810701800c40c0c0c0c058041c0b4682c071302a4080c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 474744037 1250 474742787 474742811
    0x30702090711071d01060e0303071e1a0403020a03080907180c090506030c0a0311090414060108090f2d070902030601021b06090907050904110918010e07050304030c1a0406 75
    0x14074621311143d0129180d01c0d6840c1101c1122402d2100d446642e0501080101c1008503100b8181d900450500d20040e9841c200c071413034030300000d0030981d103c1d1400c0b0071360004000109030003187c2d0900280e01070402c9145a51510140307402c00015401c00410702d1802c9401000c1c600d050340c069030b402140c130784510000c07948803000c001300ca00040380c0b222001901000b00243c141e2190308400d4059041c4c031310107814400c0c2040050181d691300c40000d81c0000004040120303540e400203d198000d03000710040e001c003414070a40140c945464500c3c260f50b01c00c0442070aa681c4105640360349911840c001a140020f8407010410065401a66091300602c5100311100c105c14152001ca03803c4040146040d1419424000707101d080c00c0000c080344107200060001f0340d100d450340d000c0c0036182c1c4155070005a42e11420401c0001c000d800014110b00d14000c14014840131085020141d007282c06814681e49070395031450102e41c1200303140802400310b001880704110340750300b100c0128042e038441c0301c040c880c00103115 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 474745287 1250 474744037 474744059
    0x80c07090b0a2d030609051002041d0c0c0a0b01090b0906060315030f10020a0912020328020414071205070e04110c122710030c0203070209071107 64
    0x3450386680405902c90800c114480d803414465801d0a00107615204800ba145030003c9020303030f074000da41c910b889076000800c02c80301340310034100f6003514001182014240640c4024505c81e40b03150003490442700010819104440b801e64030707509503403400c8a22a0103645400710901070203101d509002030614048141a00d08400506d2040802611181c156a00c988010744c449405c07504080e00340c0230300c1c90075002610701481442e200031090807015a0b5130400d11801000510a680041400c101d089044c0c80140d5001c5032082e03c120341e03811640248080711000b040903025104c4001e50042c0b90490714040180d14290142c400c081e5620b80824400744002d6440c2610001c54000d40000c7d48400c07103807820b2400d50701080c5608000a903050800384040015443c1c002a488200910070000c5500544001e0109082541c00a4060400c43d1072000b800800e400c3d20714000c6440c24191a03912806c54248200300f030390041c0b0780080443c440d500b0099000f9056182c00713010102280103218012036024280 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 474746537 1250 474745287 474745301
    0x6090b1003080a0509011b0b16110307080c070e040b01090c020c0102070618080304080c0a080d0905010302030a1e0b1009050307030b18160920030414010e01020403080c0709 76
    0x80320b11458084910412100d660041c1c0c8101d05001e8a801200e2500c034120409101c5207201e0701e4142624203004151005d0010301c803442104024200d0b80608005001005682031298003d00441d29004540300342403c240f480e801480d4015000030411051001495009040790a0610100710000c030760301040740c454142145044c0980e05c03143c010046903100d00b80c00303002c2507241f0044528068888605600350740c4140d2000f88598131680382c0c00194605506603900038280300d0000e00030710b6031511020742030604920442e414140e0200010360500341c540c0122101c3c0c00d80301e45c14002c110204140c440180301c19001c03140105c00c409800031a00d4055030003202561001001010200c0c42c668802d65404c0c4000e00d44512402002e1080c0914001004003018888060b4031685040c1d090409942c1110f04c2c1060040151440304030200068000b001204d412503007201d10bd220b850350040500c1c0c050301803426840040e42c8000f030000144056280a0314502450b901071300c1c044d5a5860700c0900307071444 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 474747787 1250 474746537 474746543
    0x90304051c0b130809060f071406090d0806030a0c0e0f0a0e071a0c03160510020301180c09170c0108092b170705030a29010e010504030203070306090b1003 68
    0x1c0b00042030381c1c1c2502004415143e44100e00182c6000720003804540d03280c000341c0f81e441810002050b110b040000c168024240b60b07202600810082c603000405549d01c180720100340f03041c411b407800030504645040c8021070090340c0040c10398010039035540440d030100303100b2240300b1090400c1d030020440f003150034001c032240300150100a203002402e201c43c00b060340a01915080c5014020000d601e5440803e2003e40121121200c05101b618401d040c41424a003103103c460704400c0c410001400f01e0880d0071b081c0403000300403541c00180c0490102c000c0c0d4600c0c41c1600412039014502416082e41d0300002246118800c0c00e9072080c8050b00d41403603c42d55081500b4900396100c110006d0082c116003042d4010001501a07e0702c01a07510b814010013100110a450300c1000500000070480384a2803070240b81541c44c0e00b524139005a503000821880d4030032120708100c0c100a4400203a80c600c0c1c0c890003e0f24061034005040d02c1810f6980d10306000100207229040f540c00e00e100d4001411603003040082d03000c60750 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 474749037 1250 474747787 474747803
    0x809010b15130509011203080109020f04090b1809010605030c0d02060a05130b0c0703021206040317130804080a0c050d080a03090204062616030c1203030e06090304051c 74
    0x100702003002109401000005901080c1c1201c00a0710740e4a94450074020104405008103400031410000d1100a050f0400c00116004000b1402e03040c0701841243c003120301c2c4000000c0e05100d5000050403281c030aa01c05000754440b0703800d002c418541035200e47c0480701c1c220112041951400c4c00c1c000251f40c07076070740a50310150074400d06141a004030000c08081a00e2284000c1035901c07103101c0c42c551340141c010a038043e13000d10f105004504081c9003039185074403000000c054034527043c0c0e0020200c0b05400d10300b0f00a01c03203550101d004480103012980178291702020164032503480c1c010f078603550b90041c1001d4a546402e00070004050801141088009404c10b03070750361514200240035000f9000300c0b0022a045961040c00003094601e010034080401500140c20842d0301e80c0d14441460044245000c641c407a88045c0300f040019a070b4046402100e01c0a60032111a061604050303005001e043d03203445090064004000e001c940c00300060003944e80480d02080135031100b102d0001a42d141c4070380107050344 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 474750287 1250 474749037 474749059
    0x5060d0206220803040f08010b0d11010f020f0d020c030d05030f0f19020f070b01090b01120b0301090f05070e0a1a1212220b030622060b1201060809010b 67
    0xe00a080c0c89400c460300b01c030340c003007009541c0e40c840c914541c0302e603101e6501101e21038424030800b0400c0c01041e41031802114204c9d5519016182d071000b00900c49001e074188428442141d14203402800003021101c4042c00392441e01190800280d160b15613004085c1c864003c40c1d000540140c000e9042d680074130b1280b00c02400580e074440421124960181070b08540c204403000c090454403076070005203101418800d50a03102e242500d07042400d03440682141d000c0d281003012086007070341d004d4045050340b4030381d03a07004c2800300000000c0b034018100d00c18040e0224107585524030600c08000f40110890300c0d5400141d182d540c031070140d80200c40c044440e0a01e8100010401001803400c081041c410704030700f00c150351044907041c3c04684250300915011601c981204c2c15408501c55400480e40140000840701d0315516040c0f001520007059400582c0302c103550200081d6444080c0d81c00309003c4c11352400c1142d601e02c025401481001802d20074840003070708a000040c101201070094108000c0c02401400c440 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 474751537 1250 474750287 474750307
    0x20f01230403020a120509040c091a070609020d0f021816050702031c08070e01021b0409080403171312121d0405040f06060501020601030c05040c050c03070b010905060d0206 76
    0x100608240d0440c40b0700105540801d000c81c01d605c004144030b86a00ea0f0707449019080c0004d592044043c90244800c94500304840c4000449403130002d940c840200740d03115410728001d4000d0000040c0030b50403101441d0400c00b00a0340080c401c4989008540010307002074180c810003441030003101c0b481005000c1e2241d43c01101e00480107050024802010f0780c030004050b06061080d4540b03100a00001074524041c8074441e07801825001051400f03102a242190165001ea8401c0700982c0c1800c0c02a40d80310b403900280a41c0f64152005140c0c801d041004000c0d051084d030b241364028100e0b410f10f1403181400021180c0248440414840d4080303d0040384881207041503a80c141c602c0e566003600b41c4107010a0940d5a21b51050602c40c40c8900003c440e41c640e10f081c00f4049580035006641954000d4005102092040800104a42c82150f01051001400c44100c841c0c1c00380c00d903480064403002c2003010030004040445030513174180c60800c02c030980c3c0e04410807020000c2c1c0712002e9040281000315a002c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 474752787 1250 474751537 474751601
    0x5030412080d02030a06050901090c0215270a0201030524040c2304030501060602010204050901120606150804060f060b0703050c07050604081c0519110a150903020f01 73
    0xd1501807400c45003400c000d60003042c00c2e64411680c2e0302031680d5502c0184078030300d0070b03606050141080c20010090038500d010040e42d07481c4401c00c001010340d0442c000508515000101a69000f0714400f4907000b2002c0303040f8190788104001080b80424102000203000c0040c564440c25101000f01040a113050071505010040000c21000f204000c11131100000b80240080c00030301075202991441c1c0c2e91441c40c10554216295600b1410031079004100800c010782e41c4051361410b55106101021100c0c880746006030060070349521072a0003040c01d4400f200d48640004000e07100314000c0b603084c0f240e080403201e40d00444019008900044806015030004248a440a4408007443c0000c0310343ca1500e40300004d2451700315500000041c3d00c01d180ca900b841201681d4204510b80d14180141010f00250301c030804601600c01400070821032a4201c100204d0030004c1d0711406800c0103141294a200d25034100141034540000c0e030261140201da5241c10805200724060000701c90030240d0300d02e0fc0ca80c14109 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 474754037 1250 474752787 474752819
    0x120c030b19020301060207061404050d141c030603110a030c060e030312010e18060108060109020304110a080d2a0809130c1e0804050a060c02030f0c010905150103050304 74
    0x1c1000141050368820703110302c01180600705603001840d081c0d240240040001e00b150301604541001813200b00701d5030300c480e01100314183e44074082c100705a00700e0003010b01c2d00fa28030305003060941051080c407601981550042c0c050703a010b1070803c0007805044d02032104c03256042c07000134000080c0050800881c3c1c8980c02100401c00020300f80c03840d05004041c8401007800a81090003001c40301d1090016945110807280320342011407015103455858840d04a484050511640c05000e0300000028104070185488042c03141004248654040e11442466a01e0405480c1c4034046201d140115090000349039650088480d60710010003c84041c1d50744030629007188208039004099a004031841d07910500070040140c1040d540c5a403c002004443e4080012a00e0548140803c440030b0002103840130480700301c620340190700030507050041101280f4622401c443c4a0710500c02080b1080780c0101900010422030050003252031104002c0d5106468080c284402004d66004100412030f0040c6250291 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 474755287 1250 474754037 474754051
    0x711030c03040b1201240c0606081507020d110606040b012109110405091b0a08030d0603051203060102030a110a06050f042127120803010807120c030b 66
    0x904001040e0102032440d0459000002d9440000c120061641c005000060040c010180c2503101d406101580c09504000758841c40108189001c485040c001d481d04450000c00105044901c0304071004034a2040920a40b00300c00140103990841c3c0c1c000e40308400099600c014900a410203449003c02c00004243d02840141480005d0000350400781d200c016042d004080000041118038144c80c2201140320001c031a61f100d0703031801d014050b41040c000b810079140303d1350002488500b00681e00040c1c6042c1d40794020700c030f5884001031560040700c480c0c102c1e00c22244505d00312149a2545c940840d030a001c1103845500691051100c44030300e5100e00d103070841003240102500e03030b10040348d162581a10401c407a5104407038501420700040064120008846842680320749903400301c03484005080d4501c03400398010102c60b010300d8420039504801d100c002030202c41201150b108017450180a260001d20070200140200c2c40c00083c072081904440e42c165920103d11030105040d42d5910004140140c020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 474756537 1250 474755287 474755293
    0xf06160e12030a020f24071b0b0108030c0601090e06160315031119141909050403031d0d020607120f0c02071406190e1528020102070302060711 63
    0x5040041c0910003007940c801142d010308081c104000b500c40c6000c10105104440c41e24095000e10b040404507180f581008903032511a00036800f2000c0010410140c00005e012045054000603501c04000300400201c1d401d41c05a0302d09a80c2c0d1020101181d03103004026a640d00320b90005000c21101800e0303815401d13400e04001401a0304a4514052030980742c1040300c20700d500c681184000c2c5000072258007000b08510840d00301c0c5060103005000c0406904400380115016007400c000210171210714400740c00240e07410005440e141c00d006014240c01b0840e00031004141c0034400c15407001207041e1118103001d40090803e41c544000484210b00300c0101146c1c21660303420604040d80c4140030b03040d00c8134200e6008060040c1801d080c50f00da80328290b526071040d401000200103d013136001c0b8466080d83c407414541401640c40e00402e81045112140c050303c80400500c0803c48900170600344c500ea40c44010310222a51814010381c200c1c844d0301c0d40680503900041c0090314040c404c4910041242114040d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 474757787 1250 474756537 474756559
    0x605041131091b1e020a060c2c0906060f0304020d02151209100915090c0f0b03070f080618060f18220201140f120103080304050f06160e 60
    0x4400101e407200c1643c02c807000c2c3c0000341003010a60142600b6450104046000c4242110000c081c0d940c1164100c0101b0850b180d0584d1012140240650b04070b94502c08020810f503001240c10840a242019105104d0140c1001281c0c80307003030400036106001c40958805180d522103400300442c2004041c03040741e001d0704602801110403440405480c040d12070303001d51041ea045c038282250400030440d0003202c0c0245440310b01e20114042076050002103980050014005480e070500341d4024016800c401e20003400c44c000020140310070401940320b040c1d10794400e00c1c031107513a442c02c0b5405001507841c142e0002c45841c1000c20160540150380c0c1201000704100b042d40c0701400802c01c00800d050301518402c4a01c800c124519140040c041030710072201544144080003980040c00240381100400e22031040424031001c544c0ca2a0b0840380c5180c4058003808903981c0d24504440990b1040750221501d0142c5032190716800d800140c003c0c0516000c51800c2c40c0e161404e45c04a54600d00340300709550042e01001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 474759037 1250 474757787 474757799
    0x180a020403061107020414061c0602092707170105120a021201020904062108030a020405040f090501200a030b15040303030e120705070909030e030607030605041131 72
    0xb244104074080700f80040e03100c42c01070042004907010856207010107014407040180e1582c0342c8065811492484035615601a031905244000340141e00b003581d000b420516142d6141c143c45100c1c1d900d901d2002d21030400d41e075503007201101c00d50b103400d40180c0c0c2070790b10f08018461840e100c1098030980420600301c1d24220301f40e400003000c8050810780c000c03143e5030008400341541010b005080140581c00d034564081c0c030b160300240e001003031004006040d50a021011900076050390b01220000c02004000b804100c0010700004010015040101d80540c40d000c50a003080003854514640c0101c7c200c0584c3c10080c039400150090000c3c452450350101c80400d0788210707030720118040e001640c082c1d41c002410010340d9a100745011541c2245c0ca007140414411040010703000541181078803841c0c0030119284499103820703160032006015039680350140c40104800940e0541c0300c181100d008540600217003003202401141441030340d0b18012a44068450444818080b015118080b845a0900c10f400c0d03544d89 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 474760287 1250 474759037 474759041
    0x705030c100c051501170a11040209030f060f0f07080601120522050309010807020a0503090d0f122102070305120408070c060807180602060708093a02010b180a02040306 74
    0x3404c031501d207600303030001400520080049100e4045150009003035010321500d405525150880c0441c3c41107800044260b900c0c0c0b018051865090480000c40d811400c002e070100003a1001120480d01421990001a0209200300c403124028481a160310380035080440f0703408054900182212801030b0144104020600000103030a001401200615120380a45000410001c006401c200465001c210400046400482240d94040c82220719505503925031421258002a503100034025034000010811019001400c5520b2107005040741e64802c0b13503903440c5404034040e41030044c001507024418040207107a45503680c0c0e0040d014a40f00c078140032095907503246200365a002200064881418804855088502d240c0e124040351001c1e14510308004000790380c0c0d03d000f0017400422540102150a902d01400107180462000039466800882400c482c0c06001080030a01c544000c0e030301c0d131601003e1041c0f1944011580040c80d80a403c14848980d0030403490180080280300d90030400040040c4042c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 474761537 1250 474760287 474760303
    0xc0b040f03050106050a0b180102070902210606160b090a02150a030f060e0403030903110d0315080a033612030e030c060a0309152a020705030c100c05 66
    0x20603500c40000741503241850950300e46520180c000c0850b00b005006036a010720a5561444200303524440b40412900100d2034400c603607001c18103440c8002501980f07450800400d4944140c0c41c0301c1d1084503266802030040c00d200e007443c0700605092030900d107000200e84403003098222000f070045600c0c0d18925000600b0f09924003103081c514000003c4c5000c3c0d650b130035000d0f9440038588004204001407070301600c041050001407005081581e40c0c040c200c201030181034030703d141c4040c0b1403c40724079036003020020303009006c911210555a1822800000c0701100010074176000750b4540c1d1a018050011080c10040c0740c0d081c00f82c0d081003800c00e01c03a032802110781c1c40002d004145500400740f60b900345060251140d0140f10065001340c01c9812800321584805007214200c408030b00d030001c2c130403080d801e000151258034481c0c0903a40b418940010400c400c0100e440480c03488121484002c0c41c3c51b88800c1c0ea40b20f03003c0c41840c0c0c160b0020b40c5003501c04e02e0001d10f031200c02d9034541014018400301c0d0ba42d150519130300d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 474762787 1250 474761537 474761549
    0x70e0601030905161215060308180102010906090c0513021303141c0305011a070f020f0105090d050304060e010801120b0712020a02011b1418180a090b1509060d0c0b04 73
    0x2002d83d172041c8850b082d413480c100b400250782000440e0840e1a01c09143c0700302140100f0111043e1042c2c40107174400d40c080004503420a034104141456441c2010042d0300a00c1418450f545075161110030032010301c21a5044d001d5900501c1100c1d2030b6503110070202e00460b20081540c01394032a698503a1341c000980321500303000ca0307400043c60b605256007941080c2d90100104429a014095007000444254410f014035404949144507900c5d088012070f800d1281041c2c25400410800c508010044000003030b10a9821070b0b101c0d034000c40810f400448002c6401d202da028008407545005000c5807038030107403030741142c02403800341203646104c01d03401e041c0e07801200104010b03951134070308581c60300406444101c4030310a441e160100c50050303031014140740121706074031002c18030314514450b040d0f48021a00c01411000500c000c114036000500d0401030400e03403402c0e1841ea08280c00500981000300402180200081c92101151541020f01c03070382240c2c1000c00c50f5010300d4080e011402e00742c00d00140000b014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 474764037 1250 474762787 474762809
    0x60216050a05060c0f0307080c041a070b0601110604080304060f02030103030216050103020f0a0e1309050706120506100f0c02120a1a0c031b19091403070e060103090516 74
    0x1492034a81c0c03405100911344150790f1014402d500e04010320f20122904030010385800e821076291200342ca0320500c11a403000868541008565642c0d030401c102502000340542c0c59652250756120064035250b00c84d544510030780e0020800140010143d2003e10381150042d20009482c0e103070591450100e0b0700a03082500540d000b00145441e0210101011000d04400c0c81d042d401c250510344a1820b0303010314001281800703449080d824482d00c40d070041c1c485586141006000403241c5e0f040260311080300c0c5c002c0b0400110088000d40a40360316000701e0740188c1c0094448580a138001c8030031100320348000496010842401806000f59442d010f07454004081240174080c503146c2c6107403860100070600000d04a189152080101190502060f00d600c105a80c802c0076141d040c20084904900c10104540c0191401640c0b400d846944058100251030a042011285c0070103807042664031a400e100d9400d0107402c12000039060b5109802140300741e4400c0e130407a107000d000d11403214002d1fa019000541006 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 474765287 1250 474764037 474764053
    0x1208030a021c0b120f062701020304080903121e030c090307170c12060c21010807030c090203040c0302190503031c050708070c0b15030a060b010807050a1b06021605 72
    0x8130340168000110040d032001010701e19100b42d012901c400c0004e20f013414800c0704107040a0b24a00e070b00184118005e42c280215984d192507c4d03d81c18a4020440c180c0c0240b085c80050034518564000b10740307200585090003201d1114045060659510040440780c0b014401d001070000c0e52000c000d0b9501a21489414001004d005c100180c0350000e00b010f5030388580d9031440040700d115008110380c0e0f080050700064030f0740c81d07400d040c0c08107034001410040c0600c02c44010002030300803c0414443d040d244290700b10425030f079440840780c0685c002074501030a00c00ca64036041005107031450070745201c44548a40f01aa01c0d40d11000070f400e54000c0341e88401181c0340c0e04d901086103119485001e40c08030903800e01629a040240c03000b415400c1043c40144040c01c41e9011403e0648080c5200d84944801030071038100408914265002c1d1088460b02e501107036100c400706048a0045003500c80b034208669a544006034200740d01407485600d00350a664040c0c0c204541c500a05000401508135405000104100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 474766537 1250 474765287 474765289
    0x6080a03031b180b0c0c0d0507150306030b0a0e010b040e010518060f010b0702031c0c03020d0806010e01120e011410060503060609010521011205010f061208030a021c0b 74
    0x90300080c40158100803100e142d060b501100d052600090301c14003245952038101394170ba010b140044148015a000303100207942c204200000400c00c3c00c1d540f10100744005030b40001004d90660ba05400028074008102000588421480e8008040786214000103e001c4107450702081c101d4040c15148241a510380c0108038101d4401e10412001c2d1454a00074107151500c181c4c0102640c4041c0904a81d88000103905819035604000001d141480094000c0c00412080c0c405400310038032100480250064030048090706001c0c2000c94404c150607103d0020342e003100303001180e20485800d1181d00c0169204900040280d0074404c40400c0001c908030030300d031810284102242a65194409000c01500700308028445e103d500686007030020a0030304a81f9031801401d030040f00c0d0007404800401d080c2c044000901a0800c2000e010f030b1600400c000c00421900e5003588042c0c90490080c1c100c00401c010403900000c0d1103d0045511801c00341005045c80e00c1a10710a00058003550150080c0d03450720301190a03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 474767787 1250 474766537 474766571
    0x20c0901170c060703020303040b0a090804060507031b0c0501230a03020304020a1208070201030203182b03060509010e1023010906030c0c110f0d05010515060307081906080a0303 78
    0x2080b0b0100e600c0390400490b980c0081d520b2200510080500038070170081009003443e9000000306507400070b2015142c60722074800400380e400132101900080c820404807c03c0e900b008100b070000c0340d044a00341b00510708020040d01e03155408503031003480005d03019803c070003528044040c0c8490f010a9a000d07940c0d00301070041241c1c104054010780c0c684420705481c000003506030700c02c4598050382802c001d620782e521040c130410300c13407500f58011a241c0103440800407034140141d07041e180401880300440c801c00b04050224121031441c02038540000410005214104600f241c0d10380c0441000d5450300b425445078101900718080a00380d155009551100804660700300022030b003d8880c1b440c0400ca00403007204028400e65500b40060145403454080040646810401c40904d00028100202c48500d41ca4514020300b0b003142c60400743c001c00a201324551501c441100e005031031650341e050319902c1c1e40c100c01e10062650450340b0005030b40d401c000503021001b0f22209a9150181e14005070300340a640c50a54 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 474769037 1250 474767787 474767803
    0x8031f0602030c06010e040f02030d020703060501080a030e0d02031c09050a0b0306011e03020c0102070308041208130b1e040812060402091c02040b0a080d020c090705040501080601020c090117 84
    0x942d0020b00070b0310030545001645a0445103862260f90310740d00c0300e04015100c1c001d1240041e405010b5005110602e41c1c00289020860b0300c03ca008000b140c3c2da81000903240c0e8082d2100800082e10312022505501c0c000d4820504503000906480200030903250f0125180a240c03500c0f000f09405407402c10961504508410042106c2c03c0d0041c514030340640028501e42009121081c18030312240c0d80032a6911942c10b940a00541d0b034002c6544215074103010f00400000c030b401729003040c0c0e6a0240380340c0501c500e40c01401940c81c640c104e5030700d200300da640c64000e01d0011b00d081e031800001e044249148030350450b81e80c02540251100c82e640c4100e41c0c0d0307420880000402c9240603074010020041071383c841301031201e0310803141e80010042c0c4030284006030182051040d2180d000920b01c1012802030000b00d4580a20b500e2a02110041c110f1542401401c640071224540460802d22040100354068803441d80d00c4001481035401890a150004024000a8005100d5803031505901182c0141c200441d031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 474770287 1250 474769037 474769049
    0x3010e0406050717040f0f12020115081605060f210601030f05060306130501060b07050313092f2101060221180105040902271c0303050603030708031f 66
    0xc4c500101410707400e908683c041d200510f904c00c054042000d01c5043d442e804110b0340e2010445444032168140240039103140043c0d031404d040031100002e080f1000155141c1080b4505810703880c11490002041050f8202c03203d0010303600302c00c01465031010308401c0346040180e0903460b43c2d00e09040c440001802c40d0b1036000f900f0791040c580300901c035045d03500144030741d8031058400d00d5000d14125031800d180036003107640c00001a01004103541040190100c00361000d000380d4000072002640c0d44a0480954110001c201c0c0e40c181802c68444142c465909101d140b642c110a40e2443c1c0001e0117100f00c000100700d20b410082c800050010311000b603040c030a60114100924800c03070f164100280084203403044016442000d003019014100f180d001c1c0040e0307001000b030031400b1900c0e50b55944002890310303030641d001f1182c01e0a441e0008100d10b00341c844010300e01e403029441502c50f41160f900350020607018114a0741441300f800344100042806009502ca4140520b260340401d609401c03d504008045c1c00070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 474771537 1250 474770287 474770297
    0x604020a020604060c0c02030a1211030f0a120204050d241109042003070c05062d06061b07030b01050909030a0c0305040b040608160302040f0b0310050603010e04060507 74
    0x103001100d80c0003801079042a009600042e0b082041e8600f5a000303410355034001d4050040e03100f140309100080b0f4800350603840588950f92403d075103100171905c902ca911035200304590207014040d007240c4a1380f0700d4114442c4a4000500d4684c9902c0018004043c81000f00c4062004c0c2920401c0702c02c5c03461166801d0002c9043c14000c2800d0b062174060345000b1600c00c3d9000310390740d110300d210f8081d45428100b0b030b250829041c3c655a0810b11401060034030030034816201880f80e1400705041e42c106021740000740e111004100205c20340c1c81c0c400c10f800100604016400f180501c1f406040d6000480000300d81c003d01d10007821428039624044d00c01602c164000c2e03210398124410000c07800b8010049803851840c528109200d44035925040c0d46501640d089000700341800b1030081011385e000b030f07100c2e4052040c818030b80c400c20300928821030a0740318034000c039002101c0c100310802881c4100c40244d50000240313070400c585192920041744c0301ea00700b40c2c820381003400c9400034441070090512401350891144e14107 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 474772787 1250 474771537 474771547
    0x1b03070f03030e040f0603050a0308072604060b060c010902120a0f0206030403020322082e0f0f0908090901060e1e04241a041a0313080a050a08060402 66
    0x540c9032450352440058140460356400d0141913440c0e61140490170410102000035035243c0c18141d54804110f50120701003011500131801d114041d501e41c040c88000c0719081c02611040090308103500343c02801c211412600c40c41584c2055981c84040c09041ca80329000054500246c010401d9224020301141d01c550028607600c004507040c8454040d0b2144c0555980c1d40d0ba40b9146801c03072440c41070f801400c46081899808801510140100c44d00f104c0310f400460314801005000c00c2d01e240100710b40c0b511503002d80125a04100c440790054800c0d140c1000700001d507503421000001c00d41e8019842151100c400041c003240b030740b51009209014008130b181c0b00c0101c1d4001c0010500460305401c0d4512050311100616540d41d4071038106460f03d070408020003419503c91152020140004e0041c14030a800c10000304801c4182d490541d012100c210340352803da000c92401c190415440503013102300b140320059000020991aa0050112071030381d07139070180e4480c03030705034003c0070944040c1c0301310300c03882c01084 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 474774037 1250 474772787 474772799
    0x408030403022101050403051803190b07090e090601080712080405130204120f03020706020c0607020f010203160b0106080114130f0e120c0d1b1b03060e1b0307 70
    0x6440c2541d6041d9100c42c41c111000c55002c14000070440241c99940c203207820001007661100140140e42c2080c60200c01004174401010744608039980190880380d5121040b40124000c4500da540001c22400d0106a007621101415000e031400c8903464400c0d84504010020700404100640042001900a100711406565007003d82d111700e22132180709442e5006c80800c00c82003541190010003000c0c0d080f1a00d4459403502c00c40300c0480c0c00c001c0d00940100f0200184c41400030502505c3c0c0c4000600c1246031150396400c110880030520079042c1144020301c0b078101c0c000c041040704c860050054866851a601d05100140304410503084100a24014000140386854105401c1002040024089485402d0203210700c02884070005240541c0720307075021038581c140d02c1801000c03008804001c1d508035880e064000d40796415021740c0d401c80b41c0c40c00b00700384000c0380c152000024030300b615030307009081140d1b40c0e104c4000360356074004048203d03045501a420301445040300d81c410640141c0c06003544514003a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 474775287 1250 474774037 474774043
    0x20423041b03150b180f06031b13090c05180102070303121e060906030303111306050a0201020f03010609140102160515041e05270703090305070f260408 67
    0x868907409150b155100803034010450080d1102034081d0020142c0c89060603c0340701042c02d4100b103c0d42c0604800c4a00c1c807064181041100c1c0319615110319034070080000a1444c040e503204142c4400c48030402440803c101071507000f5090170301d010317a03145511b9640b10813011200c141642c00081c150b52003200c042000980054001280c4d00066000084482449031141e4a810419144500c154a000c8001c59420115441704068a00a680800c0b0000f40b0f0300c0c0900d240d03c80c14000e82e24001c1014810030119103d0030041010018910000d41000b50142c00000f55400030307040f400104048050500004001018542c2c021500744005d265600030400030048540050040038014500070751003031800341946003210000c002459400780c522803440620303081c0c40000e00490344500510b030740c0d4038480280344503250380201d0040c004091a4540040540003803070589411024000140b11007000308401c1c0c00b1004109001c1c0c8124244040c006583d01091043c605052401140c02e100900603d0000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 474776537 1250 474775287 474775331
    0x60402011b020d050d050c0706020708030906070203150103201f0305090c0d2001050a050301090c17070809280b0915010602030403031b021003051902042304 69
    0x241040d04601d0096001040c203640d015900a4071501c91040c801000c103a0110041044400810540303500c10b444036012a2141c1c02c91041c0031455000b440700408500e007280080c0600c5100600f00c4540885000c00407481c0b140980c000d540050b80312510500d8281054540541050116403040c40030080c4060008214002d030f03109401c140d91140025603900b0304001c049480c2c64002c00700400040d1364581008031012004072500c1c024100c0d06907540342d502840540b1903c0c1a075444042c110ba081403c11300c0106032864004080020000c0420078009000d84103a02a10090b030745c81e4502d14200900c00e241452518008010702c0382601c1c007a0f01c0c00000500042d007a03500c1610f152640c6c840107410b034500303030380351b00b01a1819103601d000058440d00003008008480c401c0d01c4616140401e034110141110010101940000b6101c64401c1c0c0e00344030340d001e0756100320107021280d11401c0d2070130b010040f604a40c08c000702c5400d44a5201c0c005900400d00900040011141441f41d00120100d8044080c41 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 474777787 1250 474776537 474776567
    0x20312040506031302120322170312060d06061e06050c0a110d1a100e04030906080702070b1801090503070303020d0516170901030510050307060c050304050a0f030b010806040201 78
    0x2840c00500c4c1103554007a100151000303000c040340c2d16012218200c1d058000000101081d41d04c04440008010314804030000040e400d03407000e141028802203001d460950014240365000c5042c0100b60300003802841110081c015450540b00e0031828034898168000003a0011002e0120501103120003900000340840b00b039510004910342c41c131b8480003040c43c100409900070000d40400d00c41c9902c0200c0002c400b403040e0443d0154510030380d1340e4460000c0801d000d40c2c02a000507484041482198000c80c00b2a80201c000c0c0f0481d0403c0d6030381e001c261075036000301c600100c1c8100c6000030603034a50781c40100d0401420048010b880c0c25451a9400713540c1c2e4026030005010301502055480321240190300c17081d00c440d0044c1c3c40113098589140d41201035440582301c18046403806012450710a40c2c03101c0c0301c003610381c080e004114280c1010020350b8007200c0e107002202e032407004100204250300ca04c0340800040c503481e03e6607030b400c0e82546401032407079405130031502c0980c4c04242080003603030f0701c50040914051 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 474779037 1250 474777787 474777811
    0xc0a030c0b0901030908040b0a120513021c0f061a03030c030a0c030c0c0906181a060c120c01050406111207030f14072d0e060a05040e1302031204050603 67
    0x1800c00010b030082c00340c5c200c001d070600002203000600c4c002020000c01c420724040c0c2e5502020f8108040030340480300261101d001102d40d0101c201e00508000071512030181c421342c0002030940701e80c0e90b89003000051000c122542c5840d40f0174107070003110308507544100100403809035003000d00b44804103030b032030007814110010044c2c091000070906010703034110002c0c19004892440010b45a507a0358002c5c0281e4452080c0861852150000c40c6981d882440710390710240c000d102180310700300304018079500814150b000a000c1c1c4800c0076140e0b00703103200078803204800b500080b466152500306101103a03160101000c241400b000035107075150154014550140c0f250070300082841d9088481d00043c00700507039008000400601340401c03070744c0052500e9641d1600b01151b55544420000504202d407048140a000c103000075a0960303079180c2413010304860001c038540389092550b50a030a4040f0079080e40c005104520b800000001d604080c40642c0f032030100814140d29080c0b608000c1030381c502c002005200c88030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 474780287 1250 474779037 474779047
    0x3060a0f020c0708030403030f03092f1309120309080f0d021e22050627030610080d05090f0d060e160e090106080c010c031116080c0a030c0b 62
    0xc0c03003a4180d8003000400303800c485000d511118055501d038414081900840d21000c03250f0b80c3c0b0b6100e0301a0706c2600b6400303450700103198081c0b00320310b0884150210580c84101d004d04550102e0319010311070350305081094000314110150b8201f541d9002054118a0b08141c284000701c40414540e03000c0310071322540400342c5130703031403982c4107508000380035090070900380354007a1130310004040b800000b400100d000324845031342c1d916001691000e40b10f00782c8a02034220740d051010001e200100301030768048545081e01c184179401000c00080c04d2080465400458408614092010403402c000000c0d2020082c249a03151224401c0010f03a030960008207540f04004084bd00420000c59401c8041c260a42404661040b840804200042580c0340101c3d0808580b01c00090041c3c82d05000e21400c4074480f001400c2594484001101e0341032501100b541030000024007001d240408000c0700f01e00001d1990070a14040c00c0203069414805904030750340c401c10620324180040761380038860300201c3d04020011560340b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 474781537 1250 474780287 474780311
    0xf1104210203191e0b0906100303021902190305030a0f0512062110020901020d0905150f0415031e0b2101060906151103070b220516050a0f030203060a 66
    0x220041d103410b0010003899804c3c0310410070700250030340c0030b94050300a03101e40e943d030030048441791046440090010707840f050404461221600040c001280064001d290040c0201d01e1358000e11400c0d4012581ca91000440e08522944510000c94014a52520300e18094003103066084207000907102510840d0500f0a410480c4007109180350582e6004060742c00c0b89105100b031200a4004540780e60140c01500d40040ca89807044610303405603800181030b40c1c0030b050000f64107002900111007003454000300f0400442c3c0e03890b0841003042010460355000c9040c1c003070200e9842461900d040800c40c113600346220464299103021140040100790b1007400c1000c01303884007540c0588860b80c40014451310f0010045603030400480400d00c4800070f61540d03c0010382420240347d0b0b1703118080000c0c003010030081c0800c374002090540260200b658100c100b20346c402980750310b800c0c0180040d031281a4540440100401c0c103103141d0748c43c010b140b590b840c0f60105255030040b0ba201d0100401442c44180d81c0d45c140440 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 474782787 1250 474781537 474781553
    0x1030809040f180b090d05070308130311060f040c14010c0b10170c03120307020a080a0c1712062d0a0f0303120e0c0a030809040f110421020319 63
    0x42c3c0034503080c071403d45294600b00300080b20b0b8180c800462601032860750315210750103035044541607a03140d42c8500090366a103003041048241e04a04608010120088809081c41084103600440c0103a1000315a030810345022074034421264801410101540208441d42cae03084086180855007003681c1c0004c0ea07a845007450f0144469401901100c030800e0b0040c3c4c1845400512440542c205504a90b0750040411940030180000c54540005900c82c454900c00500c00402400040d151814400320f2903099681c1c4d409020450500c14025460104001402181300f2543c2a0403020594104080c1d0034021690351026020301c60364100420007181c07080c0c644d120072200e000200310818802040c1d6840e440e0050500000a001c2c45415060503c40d01014070086a0000044c500516004402d89507a40b05045a0405182207a00030b64502c1041000e11080c09500f00290035202c0341035a860a25603000e490421100042c102c403090b07004094016280010300b030b0700c0c2c031401004044101d441c030b00e40000c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 474784037 1250 474782787 474782801
    0x5150304060f06092909010b0f12010b0304030e0f03032b0f02090a0f050f0111030910050a1719020f07050f16140a031205091804120801030809040f 65
    0x5030303107028000546500b65612100400110070321816a800d110705c0040c041103069022180d1000442c40104550b91403000280313064054205000e0404400c204551080b000036406860f0070761000041104044e4407242182603070700c0c110340741d540c0c3d98480e6010a030744c2c0c000c1865041d441e2100a09601d0030885c00d00303403418055404101448060300c0c1c1040c032000394001c001000c3c042c44010710082001d0030800c841200361000a4042510101c41a00440300c4c0046018044c1250004100181141d01c0b180f0300310440e211140c40d0071b561070aa8200040c07803d00d1841001840c032110005101081d80c1424400c000740131a2280507031a80302a038204a5580f042d440014000d00c5182d004132810400800c0840040070300001d40e44044e9070765556140c18a45000c41180d00c410031510038000201da1001861203989180b504038101090800881c1c1c2d9030711148507281c0341099482c1000100224841c45164011103841e0655841d40b4513039038a01140240c8820511454560400d01c6880b116588040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 474785287 1250 474784037 474784061
    0xa2003070210020d020918010617040807021804020910050105030109020705070b0304111c03211503060509010f02211308190f02060601050a031109030105180c01090515030406 77
    0x555440510003284000d60007030100e87e0052a001e4803d003142801d01101e181251480c0e145c00700c90400c80c0c5640b030b2480100500c1110070b18014010240540c4030002030342819003500180003105c2c01d144c010011080703001415042103580b281018840b41c0d0b4458103903811941800b0b0090b8842c600c604d000c2d428040190054890900c003c0104814400f089034050007841090b50480403c1d40c40091040f615020080c018000c0740507140e0038200300c0311880a00d9007202032070000246810007035031040b50b04e0b55540c4c0b01f640d816464805001a4030002e10412101d05ca68600031407910060940c03510300c141e001241d5080e500c2c003480000304c0d0102229641c5200ca40e05c074203015510094401d149003032125032010000041c41030000640954000620980201416115a0f080c140b11700002c40c040d000c4100a014440401d00c80e08489031000d001d910300400c1d5045e219008010038403040381c902802c80103860304005000c03004100031788807090704a42001c40079031071300d0b901c0c0d45908029002e442e2031000d007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 474786537 1250 474785287 474785291
    0x2060f1302220510180216020111010e011e05150d2009040c030308100b0f1608070c06262212021b0f0f0405131a0106080a2003070210 59
    0x42607070f200414150b01502c04040c600100c1c850b001c1101c201b00d020700c03400308050b10f10740d40844000d50300520400743c08800d01000828141c203500c01c40c0b802d54501070b03542c490b1071b64071500c0800f01050b50b0040341c3c0e008103080311380740078403e0450000d0b08207440005d01510700c9801c0c0000905005403a0241c82d0203100103000181c66080074030303207140116a10703c8142d00151005c0003144c01042914200d8080b14240179040d42001014010f2030940e40c40204252141d0b181c4000b2000000c02c0840641000ca02450b01d800000d85020409015034140020038a0500400c440022040b00c601c41075913044081400d1403122900802d030f619810101e14107024002045406015581c0c80d4006112800d0b181e000345040210b03022001444032009001444907401401c20031000f0390f905148d488951b000e00c41180011520391561141c45c0c40d641d290b9507000a6103042c800501800fa00500391329000901ca007420000301480131001c1581c0744007050b9840d2780e03010010214800a2003049201c008422094007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 474787787 1250 474786537 474786541
    0x405040c0e010605030f150f060c010618060f170a0609020d020613030618030c0f05010204050913120e06090405040510060603020d050a1e0c14030103110102060f13022205 75
    0x800b50068008071818840240c00400103007c4da200b05581036201180502100d024004041c200300454000c140f0340340540d9a10a0b000503155503148907508010514000003034014141550b000d002e00c0700d900072002001e00e5400d5100c0c009400500c0480c580c0e00007500180315469440080e0a0122782403010f54000004200c1d480c0c170603500c00300c800480c0e1140c1810805040d8211a91403500000c07200039012079143c504210202d401c106204121034804c078001840d05403a0380c00128402c02c1921100d14420054103d02c007041580c1e88894814007660402c0501d1b89803c000252031485078010396401962601f02017010840c04002e5104052a5100c05001603a103a02e030040080d0006542807020504280100362912001e106103003070f401c40c0030780c021884040368010101801041c0c0c0c02004000031503400100500e0054040c42c080c5100ea509080310000801c00285021405041c0d4006090742105002906504104000081354161440d040000c1c0401e1002240c0c802c0c0060101c4603401c04003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 474789037 1250 474787787 474787799
    0x130503090d060203180f1525050406081005060306040903020c0909010212011202030d1d1f180f12021203030a140a090506010513020c07080c0103140f01050405040c0e01 74
    0x40c600c03d03000821100d088a03240318529a58008074098040316812035640e16421f001c5002c0315540c014103820468030390700c030045500782c03040d2515508030000035000305080c000b556008184175080741000c490250101d0a000000314903101c040c000a100395541c421031004c150082c02240c07566040101340142e10325080074624040c0d4094540140410b80010000c60384415402c0418805500038009041e03070321190100340c4d4100780d104008801202d40c1004240c2c40e0b515047c4d0300c003021607405c0601d14254140c00c0003174044504441035005c0416050f4007482909140c101c02000c48005814404c104200b500210b1440c5085d0301c50060140070000400c01d140e1f1103030b0004004024018920384140e500e000300501110203a450040050b00040c00400c103c0c0303000c00f0000032208944100614000700c2401c000d00c2c104065100d41e001c1c1c2c04c80030101c142c0f980c26120305141e010b13000b0005051340c5800e04555072825814001c0030310450f81c8102203030030700500c1800c5001403d0f01c0c000314103055231940 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 474790287 1250 474789037 474789041
    0xa030905030d031e02030603160902130503061603020a030b0a0e010302030c1c1118090d030f060b030a020304170c0a111008060d02031c0806030c030a0308130503090d06 74
    0x10040c01e02030b10400058041c400d100c0e00c80ca0b12201c0941d41d2081902182614180203540301410071941072149521803681042a14802401000e43d0a00107903215000c607a8841c20b28019804284250000c00c10000c94000f40503a582c030b441000d140060761440410380560041c5441030316035411035414080403c1850045a09505881c000c4044454840982c0d00300b203680000c000c0c900c070109010043d007200042140c0002c40b80c101005100040800f021502840402030031039268000e6400482d03200101601807107004041d151040c41408179a040c2002d94000d840043c06211107290300100213002d02a440c0045114505010510366840e1001e0518a507103800701c440548030917504840380f40b180e1800b124054904007840e194040742c1d0b40e6034810051100c02c21503003030380c25011724030400800e01c0710300c4440c0040400039141d600e410b0800005152410ba541005607010342e1200740c4803c04a5002070707030103074002100c0321101d08be05100d1406a0440c0161984981c010901c0011841009210b07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 474791537 1250 474790287 474790289
    0xd0906021b01150e190f1103090c10020631080c06040b0112150f09080c0a0b060a0b031b0706090303061d0f13020103021201060c0209070801050105040b0a0e030a0309 73
    0x20412280703c0e07548940001c0c00c1310f0000c0d1020348103004885100d1011025980120003800e203180c000003841d0398800240c180c1da0303100f180c28070070341e0f0081c029205070f910b00403c024034940302c1840204424580000150030881d00a0140e07140c085191804210158418212000240e0300c10000c6031a003083c0c1190702e54031041034a0864540800301c00108081034a4012a030403d90000d841d1032110345007a14010080c200940d0888030303181c407001000c4c081401840204002003204004154649050034403000d8041c001c1c1c2414032600d0f2800003040b80c2c044050076250840c0c100c0012001c44070381e9500300ca00c42d00c10902d00804d441e0038180d0350401d05401d6070240003100d203480204031428946101d4104801070031540081c4e00844071313020540f0102010240441280306050043c0b800c1e12201040c80014405da1040c0700045d00720a8200450500c4c0c0c0703556402038054200303c0402d5041030000303043d50145009070051a400481da030f0405911a10351401c036200f01074192121304803d0f05008001c1040c0f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 474792787 1250 474791537 474791561
    0x120b120d0206010810150902091804050c1003090c0e060d171306020a0302060a0c0e040504060504050d0f08060603040204091a07110c010c0212070b0a0f0e01030606050d0906021b01 79
    0x203500144e403000303501800346c0340e0380080c040a402d60b03450030030100c40002e400c28000103400090486400b81120380029103075014600980c0105280700c00d000800100002c00c0d6030300c01c1003504100540c80042c0810000d902a81c142c00c40e60f024641d40d010200c1c00400e620311025010054030064180c40100e0032000300800040b0b404110070590700c0d15001e0780d888280810041c0180d10050010b440c150b030b03d5100c402104110310340310455004102c0000c0c10b890f0240c406466040e078800921081180030012010f84018500f0304006601c0c1884002c0d04108000301082e014503800000076085580395441540502c1d0f20000c0380302824202c0101515803003044400e10003103600c0300315941c0040c80000d450002e4200c165900e011501284c0d0900180f4002c0c5c2003104554415104081280c4003180082c09a0210760303540c404c0702c0d00031074a00800207156440c0050600d89000000d000e0280d101c412100c0c0300d2103111001c00c1c1e0b02058a00b42c802403095042c0d45000c41c1d030102e0011312a01e019080b403a07803034032 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 474794037 1250 474792787 474792793
    0x30708220e07050703030c031514040b04050c0d0e12030a05101a090d0203011103010303020303040b1006090b0304150c0e0112050121030210090c051c03120b120d02060108 75
    0x140310500c440300908242d401d880868070030b1000070300003407181d000f401c006c803080c0c42c010542c0143c0b50f0740c1c4c030403500081c6c00000040c40c003103511090900b0709100324106d109044501b030295040081c068100351240d1881c003446540ca032407404019007030801802c10501c0301e201c0301554038600007034400000d001c1540d508040c002c81c158002031560066280e480781c5d800507940589096119003c20035620602003040b07802d552644c000791004d41c64100a14002c50203500559a280303000e1600d041c02400040080036001c810660a05c85242d21482c00007d0b41d0042c0e0103030b6602d8441d41000540c19100344e1090035498200900d44901e10f900039101e686172002a2980c0a028003401511402e0b0751007406280118101c05078509542400115030f1030401c2c2c06401900c125030041c612140a440c000003068461420102e4100402d0074400390f50340c01d59004200c80518001c42e0f5034006d2041ca051124000010b4581d80711340d0855176420401c4008100b07103401c80f01c6000301c4002c0030b5144c3c00c0034070a8800d80c0c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 474795287 1250 474794037 474794039
    0x81908130209011e0b040305010c020d0302070c06210501060207050f0a030f02010c0f08030a1e0c020c0f03010b1305150306090304052209030e0906010c0b04080a0203070822 76
    0x2003800344114040d95801040100d05070f00703043c000300e802001c9403140c0241c070750312520009442503070000420286018a0020841080ca414003038907020001100300d04161041103003034080340c0a4410301b0181c50040c501180c0c101c524004581e60030039143e44559200e031600d4000240c3c15000035940044030000e840f0200c00159100c1040107003540c0c1e00c4080c0ca04280300240c04010343c031906a41002034803588480a500590b5101e5003d160001c83e1100c1d08141d441856201705001d500c0c0f4142d104106403006d0044090f458802500c07001c80c441c3c00307400b5180c04424003909a40030342000c1c4045401400401030410f180310024060142503404c011814210361209103207090100724244142d8880d801545031914001c14059020440c0d04c12404e1400069070381d0165000324080c12000758040d41d15a24290300d41020007080720809011a4141304c0e200180307030300050840d440340780d0280c0c01585440d02e03118007007010707425403150f03400040603640e0000ea0764507108010481e01201148580d000c449031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 474796537 1250 474795287 474795301
    0x23100506091806040602090d0c080a0b0c0f1b0c0d05030301030213020a0815061e0a0816212c0d0e130f0e1f1b0f1b081908 54
    0x32034042c80c1e000c0064000500040c0821100e40082c1003030000603001c00c1408840b078545210b03000f0160003802c1d041e003041020b20306200c1510540b80d04001c0c811442454030303001480d0082d041c811140c03508600c02503414422060701c01403114100000004e4040964a00e06160070ba0301c0307920074002248100c9904c201d1142c02c982c50f1099881402c0251035502c09500e0310305002c000040c680c50200d0b40020200300307034100142a101c02c840a85140c000c8292039040104015003554801041c560300d5203502000350210704d0388000080d44400c451411304840d4664814024058082214031045040068608003450b080c01d0560191240d000e40c183c07028403c1007041110b240f901e040034282e0010f00d60b203200700d5a1080c0c0d1b0150b00c00e141900c400040e20200c0d58815801e083c0c010912428600e0300401e0607041f06c2c154021100582c3d80b401003120040d840c402c0103400d0301b00d9040c413001000100d81000811a0a42c2903d107542d540040c035142c3c07030788011845644090702d202e07031410004005001142003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 474797787 1250 474796537 474796561
    0x13060807140a060503040c0302030102180306071806050c03120106262406071203020a02101814070f0b04140105090a090209010e0d0503030108010b030313032310050609 74
    0xd1000c01010b4a0700d25142c40401c8406030070150082d0307104022204000b0040c0d800348014843c1c0c0c2c841d00c03100000c0c520000200b504181008209500340180c130f10b00d0780810403180e22400240d8000b4200389071907508802e41646140621148807490550074030000c5112034114503007544000c09558100f184040f070031107004000c88142d4060380f880042d1803a9401404840301e00c240799210140c500c0741868003d032180e04c0700b0800342c2c4801000c01c7c0c2c0011507206059041c41900c1101c900d481c824020004508004090300c10a4440600070610601108941410505c400c0c0002c144810a003200b10340c55145680186e0702a114030b42030225150160720080d4000c80c02d803602400d004001d501602d142480d840080d5004d10f800904201c15180f000a09590f01c1080e00e04150240c0011501e0350b0404191358210f400b10400b2034480d50051041c1d21070f002c0001e07210416070fa4410480710140d80590051180140d0410400001e4040d907091240f40d2007156103d0780c03040074125400010740d11000d00d0151 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 474799037 1250 474797787 474797819
    0x15020307081801030b03010513060506030109020d020d08040510122a11160b1c0e0a0809010c080d05160e0609010c050705091303020705010e0604090507090513060807 73
    0x1201035402d204000300304031460078604a100d0b06040210b003d45c6403d0000b170846074111408501010941e0703103403003846101d20400340c2c0080d0a500070441592640c0010fa11144403e50091044d0740c400c402104002ea07000541c0d000300300180080110307416080010f880303c031000010041003480c3c00b80c40d1030452031491000c0b10a00e843d5a1a10742c0c0c4250000031262110902c0407500c051007800c84140b011502d0382c15103401012021010303600e032030040041b6036071802c10000010110f4100030101c106d581000c22002441d507404000c0c10b40e20008840165405842010050501c2c0e0f00842c1d02d800400c081d0704110701c00d01112141c03006001010500752400700b010283d654001109000710302c3c0c603500441141030101d0095003206c82413665007000232000b42c000c81d6500c02040c03154441c4401c05404010183c05820242401034a266100c004074140e03002d60300c9003080e05901c1b000403c10030f5000c0c485c0400540005071000001640788566500504098031170b030160740c817030311a002401c0c00442e10112 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 474800287 1250 474799037 474799043
    0x9030312181121030703020f01060602030322060f05040212060c0a03021806130510032d0e0607020d170606121902070303050a06090203250201020903100615020307 72
    0x1c0303800142d441d02d48041d280d42805030782109142841c550b040c03800000201e2004048002903903141130f1882c0c020308244803115110311a038185841800900e401000f81c0ba801680303d141e0441000c0f1980001420300740c00c0e08080d0000b85080131007141c0d4903c0e500420b104900950b17000701401d9052850039511082200d50303290b50a4107000e84140740c0e22980091105103050002240b001c022403000072029032000e010700c880c845086600300042e003050115000265070310b0a0400c488992401001280c0d042c0a0340300d04c4804030b1003009106c5a03001d0348198481481c8000311109807a1400c0081d584600c1d01200d9400b20b40083c24402142c4d00541d840c40c030800016004508103204c0c41184030034580d000c0d164003006400b607040c1d1103030f1060a20282007200d0080e5800b0503941417035a00366045451a1300407181507070042040001011180100490252446510103040501c2000c00c90090156030b05840e850301860500564083c40303600308906846c0180034007441e1443e4428103070b13074a1007111001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 474801537 1250 474800287 474800321
    0xc020604170a0903020936060702070e06060f27031002210702010b10090e0606030c0703211404051b01020703120219062c100b0d0501060609030312 65
    0x10310046c20408007446d002000d8001c94900981e540303c40c20405d00d0150902010300d5520741c1683c00c000e0b81080110303081a9a4005030190030300f01030b84030b4500403008100a02580002031031160b03101c200c40840f408450918541005c0811400d400a407081002c0b00c40341c484c0c410650700259483d254422100b41040740c021120019141c070b5800086014020710300d0701955070b103200145454595440c1c0d0034034032036260307203000d0401d04003801892044006401c060041d0020300801000c20b00c554100c0e01c1c05505818452485c0c83c14841492040048500711500079091544a210302e501c1451124052072044041e909a810035020744600f0156144000d40180d01000e02040400c1080c0c0700354108140da803060320080d4002c02020492250558400c0390510b80d079007021110084645860890503541150220442c00920344095541c848400c02400c0c481d40e41204451560301c04c1413800c00349034800024800745607100300c090802c030841e100c16008990203403409012010607101360201800c1003c92 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 474802787 1250 474801537 474801539
    0x906080a030305090c040e1005010602120a0c11130b12010b01050702090a0e060f091501030201080a2f0301031703010b0f0903012a12110f07050a060c020604170a09 72
    0x200701c01400020b08100854090500c40003d0354035280248045009a00010300e0308c1010310710503000b241c405034450707130441d04003282c0200b034101540c0403150724180510741980b0190190402d940f40c0001880000d40c007080c07480c0c1188942a0540242248403000c45845200080c81404242600c5003101210300096003000004018544a55000c5d0400201a000524410f0340e001143c0390100c10b54600503040074460800403494001c003c1d90420076041940c01040394596400a0010385001d0042c0200580700c01080e02024240840e82102410030039419069194044074400903034400c1c007003070312201209006030700e1740051076003200e04039044001c01601d0034a6041005a0755040801d28036810b540b100300401945440c000102079400440c0c1e0011003030002103101904455206202c50005810850480801351030341c3d00b9921008130b00823410b42d8032822032904508084120380004e0200d440d051020f0440c503400a06a882684104940c0d0202030900d134400b801030007441002ea0000340380c110 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 474804037 1250 474802787 474802793
    0x3040e06040908120403170c1c0f0e070b130e011202060306061c0c030b010e0a050d11100503060a09060503030702040c11030705030304300509030307060519060906080a 74
    0x100c6201068043c803850384c100a556101c2112125050314241c6c0005d034650319080d040e03400110740b2600700c1c2e03540301142e290003002c11a00c131048400c05001d0040c03c1d0399940c810410740c0160060000d183e485030079541465118048502d0a80080344946001c5101c890301140040f480000d050580c2c0d84840c8100d5080c92990030044d07240d200424944d040b507404e108501c0700074442d100300040111030400105841c01c1c0c4040017000c441441007150704001d030188501c0720303585800c0d0b0307a135003a26070580d0141c81510050601c00182d01d41b0700c2c211500310040c108019060342e4088061400307008103c82d0011480c0c3d80b41d07507000590b0018020158076803c10051480145013a80c000007020801d0300344501011140c0d88031030f05580000d14251159000041040204201e14440d00030394103055094003010390345081c003410600b5644c0c01b00014003000080810b0b40e9a010000d85900541c080c40c10300107441d00075481c2c0709002d0b0140e081622282416004550020700b03000c1d200584290310000c080c0100706032 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 474805287 1250 474804037 474804041
    0x7200103050603100c12062301020c0d0213020415090303141e090d020301020f0901080109050f072303042004110901120e0307030f120c0e040b0303120103050c01090803040e0604 78
    0xc1c2141c02d000d128510700b420746c03040f8000d01c3e0061000342102600348280304184201c140141d5001411500100c03510400f0f59104604054216010703100c414096071009982c4000b48201c5d08254200d9505c0000009099444031003c400d580c4030b60741e210400803c54000001d00d01524424100a01200d02c030000c42070107140250007904070040c0880d011071070781d80109003240e008007512009105e0019200e5025604201040e0040145480c10440b9240084000c0840c190281c603050402c85812024a0301c014004038004d105201c07281c0c40e55607130a00345007600746c07985000c04c0342c5040104803c003c1c0043c0303014442d00100e803080c8082c0518100282c001101c2c45403030b15260f984920360302e21032070301c40710300400250282ca4429202c0104081365150050103850345404192109802c0c501c402c85480e5003d0b014104c4440d0540d8007040e0384000400080c150f0240141d01840d00790340b00300001c02d01030000f504038028102030f26042d0710503481c0c0030803a4491003640600019a101031010480c641065 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 474806537 1250 474805287 474805301
    0xf040201050a170708100501050414041107330b09010608090a05030f0a020f031c020d0e0d020601032a051201060312023306041e020720010305060310 66
    0x30700d009120f02c0c4400745120401041518030744001458507040201c0001d11602d508060a02400e000707040c189448100300e22103007400703030340c078082c54841d4a41e14a0041400a50f06060b9107c0112103450303100443c80001011000e041c940c0328005124503103000c1d0384610501c040514050180c042c207030f007031000c113075100d020143c4851218401c203521100411000c1c000390560b641c841d4082540c03004000d5009240080081031812a41c10802c40903540515180c0b00700c12202004502580300d2903d48000c00040c03403e1802c00b1024010400b40d000c0050707002c02d110b0b051341d2190140d00340c524500500000001c0490b80001d4484c0340c000c005002901d40006482003680d80303100045480b949958418200c0800c030412603025074815040f190408074103003d07140a0400082e10701c010003070b03450740030081060094000c6009030394a09030b001c90741c04d0205010140d5a600301d8155600d4100d845c0004000d192205500342d20800b4100000d00e541c882c1c0901030042500400500c43c2000d0900000010010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 474807787 1250 474806537 474806557
    0x606090d0221010b0a05030d080406110f04060c0339080d060f03030e090c030106180510050403060f090506010e0a0f0c050901020d020c130e1002040e040203070602060f04020105 78
    0x4009615642d00860008001c0001c02e0020401c502c07401d0600c00c3d5807401707400440c402d1300b011603060320843c0d001030350560007508850085554001070292800621807012103c43e1603000007804544150031001400440d4131039619455071a11060003040c180240c0100704900c0d16842140c021910000c98280003018040c00e0006c1c0b83c0140c0182410443d00258800307010400d12280810900d42c0110100b82c82070020765805034203180400315031001d032005005820900a41c0c04c03051040401030041d040151130050110f00c00c5e191042000b0304643c0107803004a0f0b001e8144010742d200012140100b84200703501c4002480c0a9003011001d811900000f000d41600300d1f55114004400022401a203240e6060b9440701d0390340f480080002803c00325000850819980500e550f00415140c0c0d062003404505036103000030b8400d5418035036904003c4143c00003100c8c80d001040c04544002d5149085001c0c510071800c607502103545010a98840c1c0c0111880300d01e000380c640000b000355005000900708010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 474809037 1250 474807787 474807799
    0x714130e0f01050f0607020f1c210519051309050a0612050a021014031003021003020c06190e0609031b0d020d0e040204170c09090f0601181404030f030f02030606090d02 74
    0xd41c400100360420059a10714070400c000074450001d1025650005020081c28220303035945502d4950b01620511600d80c0833800b004614042401c014030036015180150222000301c01810b5550765004040c28066843c01c01301c2e480d040d000912501281c40d0249000c0c0c3c00b00207018550266020446e0b4158805101e4050007490760002d201c2c0350104000b0341c49480145080b201c1f040c21801880341c13003002d4030140028903204210b220a803500000c0d1b2181e1010446022111078060703281c010002e8100d00b05210020f01c01e06081c0040c0503004000b9100040c0032116030181c00985041e40e079681c07404102d4503c0544c00c204a803600180c0703e815100c0d8070940c00b410151504e65114148040342046202070b10441e0000d054514441c604030701c8440e00100174000400d550040450155100c0c4810312070341e0440e4080b003e0003072100701c980d0050068491601c0e060b800610300b0f41405000350307420707004400001e481c08c1120541104c903803007568000c000c05091207042c00e1205052000602c4001d0040e40d0010b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 474810287 1250 474809037 474809059
    0x100b01021207060e060709140f0102010e010609092a090c1803061d0f070b09040b15070605100605191103270d0203150714130e0f01050f060702 63
    0x1c000d00040070101d10801c000a0565040000b0604084014081104210b804081000240e0010001b0f0303c0b014000c4402514100c81d480060b80102141180b0301d020f03500380100000c0d0420b90783c1c404132500d4010384840c82d2415030b2010703da0581046441c1c1c0104040d03038031410322420700c07240d200c1030641210703040c021089102c10519880962103a481100c90a44036114110902c5040b500320280440c400c00070040c0c0001c0d48001500d40d1306030f0180c005000d101099003002a030381c9070031441c081c00b009803001106440f0051601260b0344200810380d1184e080030702185451100c0000c1e10b00315219030745c80504115070b010707681b203d000c00c034842030003044040714082014103000d0004068140c1255900c4520103401e05d00d081c5076422070400984103e0281d0b8070840540c4010035050030500f42d58882d0304541d40e80090a0b03800032a0484003a030902e4000c502d10309200020050030f02a500d6250311200945e850006005029409008040c0c1000c40c1007036840d083c0c02e103100a80742840c80142044090 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 474811537 1250 474810287 474810313
    0x30c0c0302130e0f0109030e0f011e0e10020303090a02010f050c120301050a0803040e0f04050a1a041e123603031103070803010e0a0603060203040b01050a0609030302100b0102 77
    0x9964a81107a00300c42d60388000100d00e07600104505504050103034000d11410300d103610080d00354540d01040c60b0094611444402c010303031041c42c800201c09611040580600324401c0014a640f1000d44414000c20a090023814141c0c00081902d02c14000c610042290140d541e00440c2e400c0c000001c4c0307070107109041c844850302e82c600b4441004a034520a0703900b511b1390701d04010410039940b1580409a0784d0400c0005000b8271000d80d500f80e5115050000c40307001d41e16607181180c80c0a0301000050070812548005440540014105a029900425501034641ca4401d004900207601141c02001041000303000780c1074034020100410030303103289040c130000030030500c04404180d0382107a01c900004d2407013101402010707000050090f421100310020f506144950b6122940c42c0b106026044c20b8102d444c0004100b10440e420502c05150f00542c29522030a113171030306180c40542070240328843d04030440042411071203480d2060403030303426600810961a19000da0701c02080c00030301690460264654142071 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 474812787 1250 474811537 474811549
    0x203030309060f010f0303080a09020a0b0f03070806090705090d06230f0106080903041a0d090803090d0509181806040302030711030705010504061d0913020a0902030408030103030c0c0302 82
    0x10908160019100616109a08400e0b03e1016000450b2150b41d03c2d10900c0030079441403403990303c02141c001c001903a001600001d410095582c2c49101502400110120b01000e0301018600950243c4c272030490b161500410032005200441e001c4002880911090005240104219401900811001034800310b0280020704d11a0f0008146000d603084c2014081c1622506071614010003c5142403042428000d248640703030701c554410808540c0b5201080340001c88030380111a000d01c3e032560100074408281c9400794054104030f40b142424018500742a80d894007541c212010084000c180101c0f07460b4202840c4080c00010f80700b01000604218074103e00c0030b042044900a40c020340045858100501d0b1000c00c040b0440301c00e40c0641c004500c2003000740d800c0401daa05440075030070032200403c28181d03030070400c00111400c103500594003420300c841d640075500b4404049009680d034082c50b036180c60307140003a4803064400a0517610100010030202c4e20840c1c0d40d2100c603100d0f0010250450744c903000509 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 474814037 1250 474812787 474812791
    0x204050919060f0924030507061112030a0507171512010e0607020c0306100506040e0703150b0d0606020604020603060d03020a080a051b0a0506040615030c03060218010504030519080702030303 84
    0x11a56503084c1c42400c11170569403d41c003000da0f404420070200d0441c1d40300340c0c80d001c191050b0340c280006074003d00c61403c802d0101c04035842441802c181c60b45003180f07108024010555100c03000c1010040d40801075070768a01c000f13200f0424010b86000c0d42c0203c0091200780140f501d00d501041d540c6031030111650b4410301200c0c0c0103031410783c0144507801980f0101802d041000d00f200010ba003d50380104116241e040c242d1742180d400d05139540b0303039030364000e820303000380c0001500d10700074145014001c40c1d004000400b0b0844185030590400040780c6410307090341c0e20712094502a40c03115040c4005600d85c034082d030101c29094824416901c6007980b594409002d80c02c084415008100c01159560603240250500d109802c070660090800700c04a0710350980b03c0201403c0604a69241e1b141840c1a0388924000382c021980320070303410344e86580c90070b00d20001c0d040301b05800f4004022403080c500c90b40c82903040c1c1741a242c004000d04108031401c0032000740380b0206071003220001c005101030000750341c040c40518 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 474815287 1250 474814037 474814049
    0x203061003060e0a0f0f0f0b04030801030b0c1e130b0f031f1409090c0a08070e0f0720012910020607020c0103150510210204050919060f 60
    0x2004500790319110041d01d41c42c2d85003070b0050388010782c031a0105078684010200180c00c80103104c881d0324941807410400d24840750142c01c1c03038003401c02d2004040d40000e5080c1207134082c095004007600c503d031000741140b00d0520b1804400c49140c4179140c1890140d8024060003115000ea012282c1c1c1d01c040115440d04a1b050031445510003204200c600207400c0003441503220f07210b4400340d8103070514030b42e1009142c100c00c1c014003866040c80055506c2d80204880b08d605040182850308140c5c1c5c8402083d41c2d9859401140800761004020400a00000d404c1c1030091640391a03034100b4031940200400106800074982030300b13640307030b0315100b260102c4805150030500c00240b10a100d04015400d11804103680944e50303086500010030004d64981c081140c12103084246404160070f20f07204075080ca00146c0e40c10890740b00360940d8030300381c00c560044001e0340d0b614450800c00a411040191100c00ca001c7c52062503044039140d0b0000750129401d00c51129401402600051444e4850001c25022034244d0004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 474816537 1250 474815287 474815311
    0x807060801060905030d0f0302030414010501080a06060f060c3c1e03140a0207030501050c0310060e090114040e1b1311040902030c0706150f05011e0f020a020306 71
    0x1400382e03035404031400c806804140c004051040178804001c0142580c1d180c60000c2650102c0031078100626100d000e401805e10400034405540c440d40101d40703c0402d080b0440d0354500e03000000034485408a5420201c4441352076081441e08941c80302d6a640d400131b55040020510702c1c0701c001c1d00c1d4085020002c140004440c0c0003126440c245414419241b6205507240f040da01e19540d40d00096020043c000c9054103c901c16817038140c00d05003a0318044040d0402466542070008000e0040c108001443c440d01951401d01c00c1d2030780e130700c01c25a00142507100c40303608005041c0041c4154420070074240401030300680300154041002810600b07280441005402c0414207650340f54080c03610207102601e011034840100904100303980030364440d100354480c0583c100d40210000701d210316000c003a00c9966422400a12403500008100c4080e211a03001c1e180d865220600089010b501c42c403450003082a00c6070414192071210001540c8440b5a0402030701103210300c081d800016201401074034010a440a10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 474817787 1250 474816537 474816539
    0x504021f05091008090c01051309090605420a080d0206010303021e100903180902040807090b030c040905030408070e16050c060f04020a0302220b24130807060801 71
    0xc01110f0752a0a00d49000c11a059040c01480301703011650140490007401c20954444900b1840c042400c0650700080501d480c0c0500101444006e80200d03114903040d80f05100685403841c40340d4007a08030100d40b40c008522024801d501c1ca8410100401c44000c000d01205001da0b0319503051385000e544c20030510042c3c002d000104101030301003020481d0369100005100328940014820355641034000341180c29551030300c0d0794105240c007906030b400201a40c21281005c0a84900256000e94018031405c3c0140c0b0440d10300007018aa90320031500c00781402030260110350740140800001d041903120a0f2914003080000113285003080000034000d20441c0c11000031843c10500b90412409909002014400300300035845200e680820240c1d400314000407008643d031520b00120706a0701c190b030002500704540e518603621481000c00c0c1140080000c0d041488070050903820320444000d0781e01d500c08104079801ca40e0745107a1812000e041c5100456203583c011a43c2c0d8800306203010703019840030020a46000c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 474819037 1250 474817787 474817789
    0x219030f05150d06050a0b030d110d020d0c0b07021c030603020102010608030c030f0c0115030f060c092403090602070c1a04061403040f0f03080a0b031605040504021f0509 75
    0x40c154001003140501c07075442c0d42003010407800e0f015008002c2640d5135540004400843c140d110303210001018007118003102e0865030141464a045100c004988100242c1102c000d20004102c890310b68613540d40300840700107a4590924640280c40c4000354060a001100851720109004901070072542d070214400e840e60001a00711201c0d81c0103058960820410200c00c4200041154070201a400e44980e0b9000c50445440c0103180d001d5241d495003c0d50200002802a844e0404007a035005601c20440710440c10b10580320902c0500c5840301c546c0c110321440c40600108640d911b03038943c16040c040b07003502407580c41c42c08030390101201321804000c800b007e000f040c06241c140115010300c40302081c980b508100c0702603c1d50b16030410152041100100180c2042103188004000c00d0388060000d500070310f20320300600140300880c0c1e05815540780040d8010240b900044070000010426010741d6558142014440540f000038410303604202400a19402e08078541500126184c0c15038036070703864241da44 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 474820143 1106 474819037 474819041
    0x3061509033706020d0b0f0a0b18220b060f090d0f050f0c0910030b04022e0203041401033c02131505030405100e010219030f 55
    0x404000100f001c650080c0c000917540d0201405039200080902c8036015951449941c000408001041284480c2d170051002c160101c080c2050300240001040a60040e18101c01a120800381500000e509910800701c0500048800a01e4409420725461a44c000c80840900c152384001d04e070401c00c602601c0710100713a540310094a1402c00d90b44003007501d60f111001400d000c2c1e004c003400208140f040c56240000c5d00e502c541011a25116034084c0706220010072104a401141044c103105441200c01c01c00140c401d10b83e0045139581c0c1040c85040d0904810340c402410305061071683d00010104030214480d21164502000d00c4161000c07004281c1d459002920801903c00100c03202c00002d60300d030000030303114801c681c4044016583c6088815100441c1d018026411040c20310b04440a181c1100c18000e00090003d814010103c503500e020030845448000030950341c40d25510004068 = true := by decide +kernel

theorem cover : BRFrame.Cov 474640287 474820143 := by
  have h0 := BRFrame.cov_init 474640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 474640287 ≤ n) (h2 : n < 474820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
