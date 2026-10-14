-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0269
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:52:21.843808+00:00
-- url     : https://prove2.me/submissions/45ed3bbc-33b4-49b8-bb42-b1749eb0ce21

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 48201442 ≤ n < 48381299 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 48202692 1250 48201442 48201449
    0x20c0111240601260a180c060203030621030d1805010f050610180312020709021206040c081003060506061207120e070302030a080705070e1501020c0f01081303140706090611030105030304 82
    0x2c1c0480c6e00089408106003c0100313140c0500f14440c00240420490b80020045008207070680b10720712045001c040c050300308001c408c0d80d4480c0341c10812850310201c240f9045807010210000d9811000b84060b92018211000001c11b24040c50312001008030929018000344030724001c508003220540b0b0b071003140310486529408010000c010443c0c2803e64281f00300110006044405001c5560304083d41080c544050111800b9114071704010111302c4186c842e03803d250043c49400c0e081055107042d99544005000c3c0203100b9900101c0a0200d424113071f40d106102c0340a12815100c0c10004100e07900c024050752072224007010240c3c4150020801030701c0006804564a82040c501501d88400b4a803032420700005078880400314503c241072052100340b000b0940302401c8242c00701da00484881091244285000230014007148071440040d51103c031486114003414401c1c034009030284807840b1080385a411600701507800039079500003482044007500c9a0144a10048203080c11907140c600042d550307105600 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 48203942 1250 48202692 48202711
    0x7050418030305070201290a08010e060c0708090406030602090406050405061503090c0901080d030509071809060b06031003050714060a0c060603050a031d0907020c011124060126 78
    0x380040c04291003988400f204441404103411f030360500701ca41c00e0f91b45080354003103480746004910004d48064148100f1540091078005840380d542c4405400440d6044602c00742d424610801009000d42c1d03480c82a0000b4501ca0080142c0f201054018042114460342019000b0b07441c2c1014011659152182c40741640314054485940b55a2410300c141800045106550060303107040020402480201d0002810700c1c003541e003088655500180d89550740024130441e416070042580205c8030010580150001e64082d043c04101d074400ca101040c444e600440c0c00b1281221000d20074010000d0a1261400030803401c2d050081e02c01c4c5c0382c000164030b4462001083d081c0303c2c0f140002001c1007410b4000100942c2c019003503800003a500d08010340b001c0898030f00c0240c0a0510303440e0380b005160041d80d050040480d41d00410144084400540d10b0395107140d101811480744284503450401c405150190902116045065500304200090000040191300100041c06c4900c4031703642c1c004440f0000d60001d00701 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 48205192 1250 48203942 48203951
    0x5070504020d060f09090215040f0b0304080c0d090609050105030114010305060a0306090515071d01030e010b09091006050306150904030302070b13030809030408070b0c0c10090602070504180303 85
    0x2c2c4a0310000300740307990144d00080f03103200c0c0c000784003410f5900141c2014001d60b00342c06007202020400400348640c0c040c500d2036001c51141882480b0744a00910351080c82810310360720b8502590b2040d07280804070300d040e42c0000c234100ca0600410b680062400d00401007801c0c002d09550400361242001200c0420b10742c1055078031700011b2840d17622a81c0040041d601704034104003a8a03070742409a2164040d00980001d0804800480c50340d80c0305600c1d14070b0b15940100c20303441c02d000c0d480044000e80302c012020712446d0b413100395000f10355403040f620501a5680c940100f40c0c3c0c0f0b24101d0581d041e10280d500079032094102c0000c1003041c031114011031f43c1c802e00450b51305913259501c0c94160001d009030540030f4800c02c0ca40341007000050b80c1c550005149170081c0c645080315036400504943d28812402401d00503045040c0c108682180600a0801c00e81e42e481501c0140c041b200115620705100099000000d20180301007200c203406110300005490b09980078816006030303c0b031114684c50240401010195034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 48206442 1250 48205192 48205207
    0x2d0715091b14040b1e010804020a1a1b03040602030304060c0c0b1f05030d0509040905011b0c0b070e0a05010c060f0f0b030601140901051c020307151b0507050402 71
    0x80351203020407018003690003070815201c1e20080280c803548150340e80070398505008034440b480c00d00213460070101000660702c64000607a004442090014000301c5e0410b82040000c202c950010720010f1140340c0c4100c8a623140e0981d0360500d01910815480c401e19600200814000d0390340c08400c0320b80c0b281d081140800e00341c000340b40407a0031009000c0054005009402800b261000700d064000c1d150000c182e000c03482c55294410591602c032003076a100b0108a082104820504280c1c1000401601450002850f00d007044865808510088034480011f0243c68481c000c002c0480d1605420040c07529103220340d04003600104189003000c0c0655810b1002a03100b14041103140e40000c17010f410f05480c02e0040c1e0203042c04a1003d84220781c1e400b80311b400703601f001080007034112004405016004000001c0e9910b0a02440901440c540321754560300ca0b68100e20025850404c0080020141038000b90400401c440004000c0d90b000605615801c2541c142580401c0d40021503000740c4004450042e910f400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 48207692 1250 48206442 48206453
    0x9080f1c02130b160c180b010906050a0e03010b06030403020606011106040b0105010c1e030f0e0102061003020f030712210e030601150c0501090501020705070b03040804060507020607082d071509 85
    0x44d4035900801c44a0040c0c0c0105052145001046200c800f199051140b80c481c1001554003403028001c4a00091051142d03900c510702c50717041030800d400094000501c103030304000491529070089605a0141e806502409010359010072204007a07038030200504450308090782c8072000d910040c0304445c1007028a5010f0b2050000b45907501d00c449410000811001880f0300e4064250040070742c0c081d0103c1c00003003102c3d81b03950022075020b110744041301c511003540e801c5608004807180644100b98142c400c04101269015040d890b003295103004041e070300d03194290f80c80801c80c0e00340721040201c1089010302040d030b4691000580241503900000a101034003a81c40300c04c50b00c2802001c000f600750343c01d04884400b8000107600405406004038141e682e02038884e071920f0420321043c0d070000c1229408110030014240320700e0150040794801011985440703150303140c1e48980d40081d12048855400b90750a580070844681010812066081c01c00b424042c6986408091002ea51a962a00d580f00e091407000c028 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 48208942 1250 48207692 48207727
    0x120607140d0b041d0708071a070f1203020403050706030605011b1403040b07120c080a050304030302070b0406020307030f110a110a05060f07020c0a0506031909080f1c02130b 76
    0x400f03001004142c1001810b040d0689007500e0954843c0181200484c0002010580c1010384083c050007007000151200d41190320b034064502034800541e1400d8040002d96440b54424584660750b03030140c0c485045007485418001540d1090007070500d0843d00f00311a907000700c0c0700d050f40c0061159210b81090b0340d0078800344c3c2e00c3c48179000744081d02000030f021801205800281c911a030145244088040c0d004000740c1c0d1b0203148080240880d4000c1c400349038198820340045601500c649405400d0003501c0c0e56800080c01c040d1021600300380c0110400c050b1a6251160940718400380409101e612650100740810744074800c408020410408c0407403412800030004291019408011140350345040c14103000302040c190340060050081e160303400391500c1c200c00c059003601d80040c815481e40c6c4032413000c2a15580204100050035481d000301c940454403420244c5150030180080c9076880d00e01d0038594040708030031402031422031701c18005007450000040343c01c801c0c0c4058411490b07494201c00e0030915841c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 48210192 1250 48208942 48208961
    0x150e060d14030406050d0e161505040e04030309200a09151d07230307030c1214070f08041208060607060e0c15070b07080c1c0506120607140d 62
    0xc0c40b0001d400505558814001c0a03100c0c41c603a4200301c4258959845c903242d180d0380461104809481e00140205030301c49800300322a80d500c0c2001441c2c141e90740b928006038a000c8500742d010903035450b84642480044900300707552554051186c201110301c400003a40c03041881c05800c111598515510b82070700304062401c80a0f001c209190b2071031702844c2040c002c2548044550000042c2d600c61800c1406c0500c0700903490745004140103030309645d00c0040c1200104094015a0200303d110004c000c0518114810340c0075144c8081c40c00c000e01d03d04500c010300b0a880405945042103840c0b030400002c51403115100110508600c0c2c844072030349681000892138026a140544040e04d00907110001071000070340e03100d0850050f80d043d0700440c5003540642c641e014429010b172007820400d00088807140310308d150590003c1c84149090911708800f010325151505054280d200c0d03640e0b81d0510070140b40400b12401c5182940000b04028903050320010000c0d81d80c0c1000340600b000200e07455500d151075800800c881e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 48211442 1250 48210192 48210233
    0x10903060b0109050d060b030f06190f0b0d0311010e030f0403060207030507150c0306050105030c0d0e07120605090705060403020a0905070302120903030a0e0d090b0f070501020a12150e060d 83
    0x1c1700c080c0c10450300400ea5032201c10300c81c0c07240322003c000c02400032501500c04c401e00c0314003500b0908028500710103043c00d00780340070342d960b6510729050513a5203541c4036030031041c00f941e41c00c1c150004d411141402c54024690000d019071040c071040c4403a403008001c440c1a65404580980c03150340d140b80580740b501401c90000c01425484071203000001060740700840640090360b050020903503960040d22240b0003a01c10708001002001007200c01e40245c0c018100010303440c400c031001c0507038844c101e1011074100c00c42160b1f5180c0302c40900401500410240c405484202c0f1600c1c6414612740c00520b0903240c920402e05210788820010722264040d0b81505c1e1744180481050000385080c0b4080360300c2c2e50044440c20310311441c20401b44d9060702c00150804400816441d001012030800407803002c2c6811480802422540410401e40022801c1c005085c4050345a11102c885901d05040d81082d03400d01c004c246038405074407000300204031141180542101050b11031000e03129403401d11500402007951041d02 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 48212692 1250 48211442 48211459
    0x1111e10020406120c08010f0e040213020307020a0201200a0b0c04051003020304050d0c02030c040e0307020a1e0603050403080f0903090405090606010320031501110d170106030b010903060b010905 86
    0x18404e4021400250860713241c0000c1145800c84041600d11007028013602445010181c0103200c2e00644240c502e80140c002840d541102803400c50701c0e0f0682e8801c94205005030800b600a104558004502d1044800000070504451038100310303107981c400c01500042c00402e11340c2d0100e95850140011180500700142041c42c0740744650342c01601a61043d58211804e101e08030500f000d82d80304640e0351a615600070b0151901e10800410400a85401407081031280400c214100040c0d503403607601d1005040c480654494501d030640c0c0c1c20340f0341e01d156109200b854189030030400000d5001411942c04080000c18107100c0d101d003100e10b0310718040c505131143c201d40381105206c03942100084003841118260b9081c80324400304a01944151140503040c440020140301103000c1046441d0b25844440041c500400e01e0364100c4c84242c40c01d8840d2002d0404a218080420000c0681342d56050140c0310f03d09060050008140000f0a00f400b42d00c805401641e036110000303420b030700c1801400c0090030f0052a43c0d1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 48213942 1250 48212692 48212699
    0x15030906010608090303060a090218040603050601030b090303070905010c08070605040c091a01080103020d080906120103170405011709010f0e010209130c12090204060f120c0501111e100204 83
    0x280e89000a0003444082140350001a6a184000013101d129a0f406403512030107900d0302c2901c001075045211170050200c14a2500b2000b61207500c2604001c6000300001c4c07007203500d18103010b6030700080a001007015030170030410865011740020031481112000c0c070b40108080468140354401d03001d82c5000400b194245020701c4288100020303d4426985107903810058112000310003604940001030940c040b618207001000546031580002c08054011b06802e4030b452126000100641c1c400c1c10300c1c0001445540060007401011003041041c8010107030100d06d07107824000060400d0407034042c901104020000010004171080d00030009035406038200340501615280040d020b5044105070501403d104050490652444e002e41d0143c4034040e100c42d00e00345100d07100301000d000003c2044c0e81094885030009030f018a81c60301d41340141000001c0c40c10000481c40d1820409202d80d00003410032a46800450035004082184583c5800710000c4001e50660b19a0460400046501c6040e03854804036001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 48215192 1250 48213942 48213961
    0x4090c020f060f062805060f030103050c0108010e040b091203070309170f0a08070203040803031e060409020a0b130504060b03010611010c0e041e090c05030c090912091503 75
    0xc01d2142070903020350303002d5521032220b10100c032411501c00380e22526850440d0b454a131014000e0040c8440c001d1080043da0319a0007050b0399034040c0d000028480e078000010001d00c0b00c02e00c40840002e40c2403900c04543d51424909143e001d201400151001003403e000c01c29500c0100a00601103200c034050689a01d0041000740081248410030340e0601c60401c0000808400e0000f1140c0c50003840c48000d0400c0407040044480e010020501030130341c4000c00004c41c5c80013081010b0341c441d91400010b0f40340007040000407a041100a01350700d020b00e0a01c040c0c0001070b0380d10008241035600300c0c4005500d624000108428404290780425009864000d001c03400e51008401103060341e03216102c50b90f03115024964103080716070703100c0e0b030000040078840100c4082c600f0786c001c54403d0b00d0070140d65070018400c07950101111046042294016084007040101c2d007000d1060400b00c5a04403410b00c26458200c0069407502103000c0b51203200b4100050000465591484c0015200480712403191246400102c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 48216442 1250 48215192 48215203
    0x70b010902130b160b070c05060c040501030c0507050d050307030b150c010e0601030308040b07030603120f03060f030305030c130312020303102705090f0118060f0903050315010504090c02 82
    0x129110310201a102084241d0541c044030078030284d03081d04440410080d01d0389485400701030441c4040200c04a4034034003150b0b0030003d09000c1e40c98081c1440ea500c1c40c0c0b800160465a0900d054018840180200c80116038003082a0020842c2800d00550320f5540c08001c5004080442143e03078400c801480c0c04040a160b60054002010300b00020001c10401d88483c6d40e54a100748802000901c001001400041c2c06840264000c0603a060110b0b1080c0c5907038405503205184100f0320300081c1c14901c520045a418000d1000400c80c40b10740c1c1d1840e508544000b48644130041000f0304032000000c0b0600700c0c0100140754001035400c84060807507400c121000a40301c0d8026601d003c0070605600e0045042c6214005020180500c07110300c0e06041c0802074900c000c0e10380105041d003d8022480305030180d0b5004e0240e1000d404079410085500700366843d248040b110030002c5600d110349400d03000c0b00003d0f0450304030703900015912032000d82000c1840040741c0305d00c02c44d044260320508110300b010000760001342 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 48217692 1250 48216442 48216457
    0x2031e0c070e0912070209070302091504080c010909020a050901050315040912080603010204061205040c0807080f0f0d080105010516020409030801080c0f010e060d09050a0305070516030c170102070b010902 90
    0x15504214044c80d41400e95001e1107038003a60010401002c03c1449010354001e0a50b0a0050401c4c2032100384c00c5440e91143d0060b80c006501c50300f0210400465681c0850014086d00c1c1c0b880045040c60030780c00004049004281c02d40d414400d0000220309404025131141030158001001800701011501d001c0c100700801d244c40304081408070010a050380f506000303480c15540f1a6582c500706c00000d42881028010140058800d80401400070400c08818001c1e28043e10303015004003541048a08024500a41e00c10030620300e40158034101039550b0301c4074150303045401c00d103009900c0d00901c495000b012a584d84000b9409460280c000341092f4106107002d0494040009650b03800b108501800068060003000ba80041c1100901200614145000c0c00f041b2003240000503441e0900c2d40c50b1450955002403e90100c3c0000c140b035020071604024081c1e410301c00080c100c00880c82c0d83d44030080c104850040c540740c0d041e803405d503441200095064070196500f09401c1c03406540d40343c052000071350003050b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 48218942 1250 48217692 48217711
    0x30304080309130c2c030d032004030c0e04050f0d020703021e03070314160b0c010e070810110f0313021c0323040e160201061502031e0c070e 62
    0x43e00c8800d68030907204d145089502500c8242e06046006000d44c83c80018124507820f081c4103c84503e02c90b18100300398603203018280c400151000104511508440401c40082c5c485041004207100161030003060b40210340c06003c9500d0b0030b84880c5005824506540741c0b01e06130b44100c04040035025400100d4504030390003a01d045100e4800c6900200101901c103030020340540c441c4174100001007040400340e6610414500307840c858a4048441031a08038503074400c0100c980c0100e40b2030342090081c0314000c0342c8200880188a00783c9030040f05615004481c400540d4161746507440e2001c92030740402c40d041c500442902564915103200c03094035410349210203900035001d42680f40e501d90f450103040022150143c0b50031079444400000d1001c12500c445024540d000103000000340003090070320080c011000040682820218140001d086850300c3d44055804036aa00030210b01507008000c4a074040b00c510507500c122803d8610012140c8038490100401c0c6c0f088040025100340707003191007400385141c2c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 48220192 1250 48218942 48218959
    0xc1b0605070f031a0d050708030a03060306061401021203040c0f080303071205070e0d06090b04080706050a090327050604090606030b06070c0b071e0b01140108161b02030304080309 79
    0x80b9000c0381100c0800703003250729680701c00006001514002200c040b00902c1403080f910915190f48000e41150070900d50840402c0e1121018410400140180405050032801d54050044d170000001d41d94550f410640e4100320000001c941846100c401c1d49000d041c091010000f0156186501603407a40300316140c1c4002003106548030300d24521405003074000c81d50350b03440300c041e00c031080100003494465040484009075941002c1d40010030402549201d18015100c081c0c4544c8030341040010342d0313001000e0954080c42c18044400098019050240400075010710100e0400c1e00d9403240c80d07014058100692240001c41d00007045c40c0700307030002400d03500075a80034030003088460184121401000c82c004c0020750708803414007004100c5000f4103034560083c40caa502c5011040008114001049810744d45050094014049032980c4a240d400000d420301e007540c49031600c0c560500c00c40980d040e00c5c03810007036400c014007010030b01c21407030030100e130340040550760388a03500c0c0400c565a501c8151464000c5054 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 48221442 1250 48220192 48220217
    0x15040213051e030d0e0315180d1e0c05101a03010e0106030c030b091207060219021603060209030f0f0a02090705040605040303030f1b12180f060c1b060507 68
    0x4124280c2c05a90000e401010045030168050b40e0302860000d0054040c802e8041041344e0030045035070a8082d14108400c0081c05034101001c60a098100c40c80100b0300043c4005484203104420142120320b8240c13402600004840c5801e9003044240c2440700169400e00c060fa241e030300d2410007035030300300e0004400800c00c40700c827820618240d4030b00c0d09c40035148541c00c210170004a003000e030026911000000c1583c441c0708414890b6900c0b074000d644142c442d0380c0d002c5007500c2d004448140c152200f10780c500080c00901010f072140071140700c4901005094035000324442d810b40c0c80802004012a20705410f40d078a910a00303500c6a903591840805a02c00c0300c00e0000f203412540100c085405507030280e0342d00c1c0d00e032504545055006c2d2034840c036201190750380c0c6e40000c54030700031010b10201c0e024038942d20b684541c1e4480850400356891120115001c03001c03941c2c170340000342c004441329220541c042000305903451310900c2501c0b82d20790f00c1304042e0601206000d01c0100415a44114803c802030344071075070f0a05a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 48222692 1250 48221442 48221479
    0x81f05010f0e0f04020102030403170d050f0c0304060e1c05300718031713060201050907031b090203100e0a110a0309020a0510030b011b030206010501081504021305 72
    0x7071921030100c45880807400300e010031240045469002d4018011245003640d030750364209500c0c083e000e1554802c800810302c00310440c080d004054100e800303c2d02003c45802c1a02d1000301a1002a10040260390f03680d02a46640c00140000381c1c50f01100c1d5400110b2140b100b001038000d07440780e48195100700384a00c208180090b1043c44010261460900710700d00d6465040035108006020001242d803040c3c05d0b00040010040a00c80d060b0541e11052943c480204410a03014007905800800c1564180001c01c8403881c0009903e0081740d802070312094105180c80d41134644d11704903400409101d07000000700f0001d151104000011143e4012420700c0310b0355203040d0a42201c040c3d0410002180c1e080005141c0d9912940014982e50f00082c52080090307074400000d0800140e00b401030b408641c68029100c440d40c3c04c060383c0b1580500c05030700031a424400d0b40d0b0080d00d5280500841e4184030410740818103000d92500c0e640d80481010b0001c44d5a1115443c40c1e806400091041034496000041c51000c0c400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 48223942 1250 48222692 48222719
    0x1050402280e09030406120e06072304030809010210050c1c020c0303010305010e0d050304020109231305180a020d081308010c050d0507181511070e150901150f0306081f0501 76
    0x488c07030240c2007a03202c00070200c0d082c1c00b01364644000340b1500650480c02402c400c008100a41c03091000903519000380c00068140342030b410030602290f1a00d4104483c214081d802c0754916101c100d5019486550003408900078040c1d802a1405840301000100402005601080c040800300301116241035149108950714031045070000d00080110200f001800300340308000310007003855540c82c194190b00f0808207480303000042c0c0303003d0195211401c0c0038a143c409030408a1110080001d04041d010a4002c1482101d81200040c40400d0004513040c030726a5941440c1d02900e0410001c0c010228030303400080c015004036031904e24481c90231000c2030505004801040c1030108201c901c902d014900840e10501452200d500000c3c810031440d00003400100703100c2000035142c004940015414003804542c0c051010b00c03c528003685444006001c0b20058441c0fa1200e070440317152425101e09401002c41c0540385070341c000e4900784249600d0600b00c9924410074281c0c88060036040110b681d88140c03001a40 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 48225192 1250 48223942 48223961
    0xa0f230a060816060f030207021c02090108010908071518050109030f0c02011b060b0604031a1b03130f020604060201140703110706021315020307050d0201050402280e0903040612 78
    0x43d61151040100c3d50044160313996000242c00e00508100d920f4001c214901410f011407050035144001d60030441c81e080038003901512801008001e500500d540341c1c8410320580001500c00f42000200914601c07880c2c001441005d51401450940c1c080c9113002c50107840c6588040740450094210001042d03c91440403108a405a450300d0400d182c00020f85442c01c030252007511103c1d101c00400045c2c1c0c41c0d14000340025481003c046405c20040c12641d46c00d240c02401003402e465211442850166604c01070b40d41246061a80481e0b03440746d803420000450500c2c90082d042a00440c0000e6015010351041141c44845031043c0019a1000700031401c03500000f000354000042407001001186150307000e030030903504007040c0300a515160302c00200400c8000c0c00c90801a440000d010041250501a800c1d02e1046030009000030300781940003840d004154000326111400010040b042d44034103c1c1c2010090001c51034006203801c280003d1901ca0303200707005040120b03186010943c41610305214102c0d04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 48226442 1250 48225192 48225223
    0x705010c0305030f07090b0a050c0f03040501170a0e0111040e070f08010614040801020c0a1a0c16031205090105270c06030709080303010816080309090a0f230a0608 72
    0x6513603d03444514418580942141c0030010360700303004a41b4000c4603004102c06d551a45880342c995a007550043c2c0380924841c042512601f0501c010405030b43c0000d0748408690411040a565a440031121801003e4080f0710108642c01c0007884000d0801c0b40300100159903900340708031015501c908050380d0940c004160075001a54031300c0100702e0305114030300400c4c3c90b80c000c0707500c14075150b42c5002c10780c26038000c50514005038105480c00010020142d00f0f41b1861403602c1545541403070715250603600d07800348000c4508000700f1040d46100b0988628642d41000088000800180c103010403410b00a0004a55070900c0d03407903401c041d0824070b05041c02c444260706808000c2071070141b00000d004454001410300b1040c000840d80c082000030382480914042c00642c402045207003400318820030f1042043e031081c840740e0402c01a003861500c60f42116075209c4038101011804d00030f40000c8600034814164008101d0054601e0345a0804414406034040c07000072800b40702c040d4980461940342e48000001086 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 48227692 1250 48226442 48226447
    0x910030c0e0f0312030a050901180503090108131e11030f06010311241305010e09071809020d02041a030f01060c0312050f0a1d0a0204050604110a0f020705010c0305 72
    0x281c1d8589501803400742c0e5800307025200c42d002a00000700141c0c2041d04d05140442d100c00030004982ca00344240d519100125109903190b41d07480d2220780d00c0c2d01c41c1003503503410807001d040004c0e4000449208005105c0e8032485001c204a44840343c0001a640740c0c500321502e80c0b40c49014070451400040b812848105d100c068811f9910b1991402d42c0c80340a000c0c1650810700c4410070390358181d28a00c0142241111407045596041c001d042018404036a0700020f040c001080d802501503110000241d034888101d09006100d80c0d4080150381c0308164507840800300900000d074900303407409a900034004070740d0b0181d1001c0010007841c481134402e010885550800060311001000708610076010000d0090282c240010301000e1014a60152102100d090b9580d41c0301c002440f6040701584076500a1106007500d0071104641c1c842070a441e0002084007038421515080850b01c60b580d6540841130341e1503440005540c0d01240e620203003213180c906000c10054041d04100040300c2d4080d0007503034a26980b43e07951f5031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 48228942 1250 48227692 48227717
    0xc02010c08011805040203010605030a051e030712030e0109150204050906122e02033408010611160303020105010e090c0a030b07030213060e040e19060c020a0b0a020910030c 76
    0x44c40c00500a81c1d00d50f4031a080090161802e104081c0700300e02810180110044007010510160380c07500813128140d104012080c00704d407014022030709013009445c02199a600c0c403500b650150241d480040c0c00712600207815045503c0d00e6008200f22081030320081090340c1c5420812086c000c1001941c04d854116207070b15a0b05004019a00d030240400540441c5c4030500c0c46910022078200700c0c0c0004400300b09800080c6c441e01e0071280e000b1400b01c03210209040b01020040100401818031680c1d0901280ba440f4000008003030003100191501d1403d25078100b640c4c0c0c00d00a01a05c428491401840721680104101340004202e01c4030740407015000855403840e40d83d40140850008013600101682070101da60031000d8001540010040f5940322981110440100000c455080240510782d9000240400c072030002d4401040c0c0070741c1c11510024050b40b0000c010f0341042c1e80c00d88000c0150b09038604110032628070742c0c0580960302040c0c80700301c5803242e4403a09074211214141c00f0b0021486406201 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 48230192 1250 48228942 48228989
    0x20601050d080f0f070804050a15021c09080105041a091c051e0c010902100201020c0619150605030108010c0c0b1803040503030d2708030703020705071502010c02010c0801 75
    0x90141c3c1c0c0032240000e25200c0e405050007040d8020100440300d003803000508005515003c0302c000040c01071603128103002410450080c0d03070750b0300281c0c40c0324804205044541e5150302410001c1c1c014440c8500a0003185032624141e40d03820b05400c14034815003540000300d41d0301000090001511001100d100402203e0f0000640710794201c0c15a0903c00481200b000d240c48840102a20341d00030400000705501c0c2031441040f11044003540c40e50704582c030600050030600381c005055500b00d4401c07082900404103240c82d241c00341030108039022a01c03d50040014085510800550481304280e00800c002d00002000f1104410480000b50101d44182c010440d010701c05e44400694400301002c6900c1d213940e0783c0202c0d00b16003028208208495403101c002178462000c107125540c50394007528451641d801a13032060818080540305104041c2d011600000300f00702000070001510905200035508501002c0c000d000c1c00300713401d034603006500b000a002d0540d070050600f18107803440d01540304415401050300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 48231442 1250 48230192 48230197
    0x915020f1e0c0a150201051503070b031504050702070f0b0f0904020d0e060702011a0a060f050c0c041103010315060503060601050705070e010f0806010b070201140c01091a09010c020601050d08 84
    0xc0e100341e0140e4006014030b40e483e4111840142121542d4400003507000c0006800c449009103c07940209048542c1340380e6503404140641a42d00c0b203240e01da103980741c0d1241e0100034200f40039905d4104d490304060204552300040c4030004c8038854180101c445443d032003008081d004004c0f50781b4000200b440105403619150f0060000da8000241c00200411003881840c5010010303113072040541d540d0500a90172100c0046580144401519401e051070b15080004202480520401003000404240895000c3d802c0c4481031811f90010800d22802020030704d0586554020312040b500300d20421325401001c0124000d000464a0060190001d81d513507100566460f4804c070411540c0b800b03002c8001c208005000b003624041d10b014011100d0b0306003440001032a04c00186c0040300d02c01c005108000c0140c0e071201c04070030166100100c8940702c81c00c09802901600310380d4002402800420503004032141c0034103210f031149104200a00104030741010598440600f0f01440387c04c0003048410030b0104641400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 48232692 1250 48231442 48231493
    0xf0309120a050106180605060c0712080c0a060606080711060c0d0207050712060605010801080a03120b0306090a032c090c0f0c070503010b041116170a0915020f 70
    0x946010300300d070703507601400c4071141d030000315072480d40d400748218520312889140f005c0d081c16074460f8a4248448100342e07540c10301d481014038a408d4880c540c3c4c100044241a5001410000f00f19051640c4070325015018040394042c10001483c9000001e071141c0c4100e0740c0c81c0910303d19201411554a0758100d43c0d11f950302141c0300b96403858082011a0006104000d4000201500c02262000484134642075050f02d80c268030143c108008280103000c250707400708a050716254541452452400401440d601030f11003001d403268180100c00400c02c4e0f803900880d071005030034403941c0d0700a1100403003556038175580640079004c100e07468880480c10407814031a03030703040c2c01c020f408441a080080c400c421741000d9000481010094021702000c00440c1024003481c044854112400e1209a5075408400ca0700d0182a40025400c4074014480d010300c10446044141d07c16140c0c00c490380c070b100702480544245098402d41c1207401da0542c0c4502c1061010818900a45e02000a409000c042e41038000101045c8074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 48233942 1250 48232692 48232729
    0x606120402190815010e040c090c0306050d050a11030d02030405130212090d0206010b04061b02040b060301120c09060312050c0f1507080a05010302060a0f02010b040e0f0607020f0309 80
    0x1a40b920309580e000c0410000f000e00100074400711030f82070007040c0b00d100107911404003407921006000c0051b0388241c400050312441038000421001a0508902420040c0d02c401c1c1c001030314500d1001448000309031400c50074000c1010510100c00034050580d42c1da04d00d03a024006810600c018005c610304142d840c410302c00046005410503801440c1c400403054203a400d07400036803080303c0e4469455010f0110305e0040101c1d1072054105883c0607030240014405500d140b2405c40058659011980e4981c00410503032005008143c51350b1716407060b0b0340c0c425408001070350082244100040c070001d050080c401075940c80800041300800d01d4900b1703107a5401c04a25a611400b5510a40310841d07000c11001400c1e0400c20040002030500340c40141c000e80c0003414199000781400014000350321140200c900d0040c10349000213840982a00890042c010030480c10351090078040c80b003104d0980003446510b580803200955001c6e860f950816661814410b0301404203400c103101105003441c0c45c41c20801010030b0107 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 48235192 1250 48233942 48233959
    0xd03030902040c2610030b06060d0c050309010b031204050f0a09050928030c020105030703020c0102030405032107120213081501090b010e0d0b0606090a030303020307080f0606120402 80
    0x141d000409032810407941d100021041c0c021561100402c200b02000d043c1840100d4903982007452030340481102d13600002c0c0c070740c0f10b0000118410703864a4048416145028100700541e1904880c020f00d03c0d030095031544910340c02e040700f44146140200c1c844c00080a0504032601d0300786000140010070b00400420760340306a600800040030050750280c0b40c803410b0094041c0068002d801028003403c41e0703111410181d000c41480010000e5004a80644216024207043d03480740e80d800001c5019114080207840d01d540048203000400070000045e048000c0380058800d10081e112160000130b0354211075200c0041d241d01080c503c1102140d00a1200055040301c600045444040285c40c100c2c40703020403110782c401c1e54010400c50415110300b07803c414091a002d00c07401102030004180741c0340d112001d014403c034400425400d81e6990f0440b03840034406000280b980303903281400340003500b0403504d135000301f00000c00094005901d03a202c18032950000b407240e0704006c44042e440070b0019001703004030303040000d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 48236442 1250 48235192 48235211
    0x40e060f04110f030403030609060503060a0e010617070801060801110a030b0a0509011d0721020306030106050a031b06051e031005040f0b03070803031e150607060b0108091b0d0303 79
    0x2e10000c0c42051403500205a0f64100303403800408072400340d03008041051a000007440240d4020a0054000c0c40c14400803400c0500091140e00500301684001c03030000340c26241c2d042403d03000c0f0319081210074000080104030340d0341841c14281e903050540412410020409003409038000d03400451411006000040d6440e1100d000c1820440c080c0c0010140c004650280704042e6040e00c02c150340318013185000039040e4400c04050946020340441c001c0d58039004000149252403d40c410002090014445051955030b410890305e00c0664881d2100c450300f00110206500d07014a04035242e030f81113100c0b4141c201807131420140c5036070001342040e1039a0395060800a00c0380c0d994003580c3c41e211421040015003225500030107140007202d5010012641040c030802101e501226141f025070110464516061342d207000005450040c0c0c244030941c0880042108410320074244d012901586081c2c0b64801142c440c944660ba1328000d41a0915941ca40c40640d07040740c1c1880000d1180080c1b2909010800e9003d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 48237692 1250 48236442 48236471
    0x40219180203012306030105061e0a030b03160315050403111b040f1109060703020f060403050a080105010206060d1502040f0e0609060616080f09130905060a02040e060f04 75
    0x39020140e00c40c590044014014401444e09051080201c01e10100d100d600c3c0c0e601040c198001449813034803a64000c102d0340350750b0045800c04c10f00c400e0782d180e1f080c1c0d541c484500e028000300b00f803000c044d0091190440b031440c01d03420740b65940c090f00d401c07406828000b9001c100c440c0281c10003e10490400003c0d81450000b01c1040007400100211541c400220708012414001102c50208405494078200200240d4080c502d8044851140050b01c03001d54461590800303a1900c4003004038108140315450800c000d056101c000707801c3c40f0185640708401070b60703104012691140207a42e4035911624140c0c5401c0060503003068041140d200090140c1041da607403801315107000170303a84021540c0e85400c1c1040a10703e0085961948040211555403c216206015601c2d150011000916522002901d0403501030301805031140c040300203005601d2100754020601c0a0081d07100104c4c0d43d842140e0128270029118001c0c0d4080d41c042403c0d118080c3c1e5410100a80e80494a0060342c209640e0114018401c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 48238942 1250 48237692 48237719
    0x203040305090405040b0912090d08070f08220504020c190c08070b0d0e03070507140604090906020c070b090d0b060d050a030801060f020a02100503060f060c010915050906040219 78
    0x9006d0f03a00f54600e480c1a4400c6403c114001018822308442001001101ea5407a00c10302612500012125103803e584e1414105004581c5c20203451100e01003402030006035620004a00c414004a41300211036482040c401070703001d80764070290ba50b0400655221290112514002d56500034054000c03071700c9e900c040890811601340c11000c581d0034000345607040181e05001d40300b00ca203200c600440c07074901c40d901c40f540c4511143c02440090b0b1141080c01c1c12994482060b035001d0144803e0410901040c3d00c1d002c0e000f50f000030f81320070f850301409800090a05079031056490509000e480c1c2045419260356980403040000c02c1981e100703000c5000600450720804c29540340c18400e4690100550605001425800030010400110760000c9505401a02c83c1c240181c03040086041c01e07510394841c40001044605003a040680009010401d001d10250540250302158015200e4004181101440c14182d8108a03280c6c82035034010b2010400505000003190343c0c0007461080d0006581d2101c20004400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 48240192 1250 48238942 48238951
    0x70f080301090c02010e0f1906020d15080d090e0c071505040c030323040b090303070f050c0f09040503090f0102030f030103030f080901021801080a0b040603050114010e090601090203040305090405 86
    0x80c0d42c40303c3c207038483c2d5024071481840559000041c104402008180b655070004da2030905007500c103020100782000303080c0d0180d50b50b4010010080c0002c4c5441120028403506034420b540c040c0c407880e203040403040d0150400c1025982c4503130f2460495903a110100c0060383c0300404c12160031009084400c01010300380701c2c2500492040c0020f842c0c02c2d2075802c0003010740224034408800d114030903400300610760904044404940300f5002d640d86800b811400a8110b020300710001d03004d0a1380100c01020404003142e1041810303000c071a4042419600014413441d04400c0710000c05560080060481c145020040001c00180520499181c0882d83c0c1c85000107030400c1c0c3c02100400c030100043d008190b0003211640e0f022042100841c109801d40302046030300481d40d0a014140b11031074003c1164105280c000906440c2c0c05001885030760b07540c1c50900e000f000c02c090f910521085150000c80c00b100c81c00039172030043c03594800410380d690030016880700a5002a0044051220801c600078950f280c0c0d00406104 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 48241442 1250 48240192 48240209
    0x7080408090105040906030c3b070e060705060709140102030f090301061205010905011b17180d0e0307060504080607120209090412080f090d0c0614010b180303040f030206070f080301 80
    0x100340761010340c2c014440400040245184aa0b840131301c036848840f94402709041100c0502c200740c1340c0640546d01598201810b83d08035000181e00e0b400d2084c0018458094001562039a4405507180c04600d581071445c558580103030000c100c68034070000c400d409024484002400060141d59602e074081091841040895041e515801c00000f808802c2c495908114540702d010000c1c1020703010002d01d81d03c00301080310000c4604c1800f01d4112040c5a25402141c0035181c204c1d0b41c054601c0700080d20041c100f18055120348510140480c80a00c500166400c580d2034000800064592401c00d80d071201d4084000c0701c0e2107070700b07100c0300046e41e685690050050303010f4910700c3c02c6070300d402500904000d002494010101703688828007003104c0c0001500721500e0030314a0807c0d925201c81c60308030060a101c003140b032507010400b0000314001011500038103200c0d003a004019040d1000f10240342d201c5c0507510400000700010041000036007403030710060070b610303100384803102030319506586511040c1c0080c3c000191 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 48242692 1250 48241442 48241463
    0x904050709140105010806100c050d020a1103070e0f071107030c080606120705040e1f050601020d0201090b010b09060904061413020f04050f0a1d0712050708040809010504090603 78
    0x10580902c2090341d1242e6840049000307605000002e01720150241840d406200702c10407409844d8442c40310403500c141d00100303a83c0a80e43d8608003d41d21003e002068880c440e444100141030728000800741d04640815a100c0040d566242d0682c191440042c40b1344140041c00e462681400e07418010035000c1c503c58440c01c11440d00b80682103203003110040070030340a5200700c9103100c05914001005022101d00311004101314005043c03031402c210020008500762607896001010102da15000310780310346001c0e401c4444c0007210070310032070903111034102c0034007190201d80041c0305e801032000c01021500c80c0600141c1c03a180c2940c02203412a0402c0d4040310800c0c0d1300c120070139030314034100341c01c052903214504095003040120341c02c4110700d01c203900c9003903c244070700d0310251020744488000307000408006558200c0f44903076096080185000701da05c80d00080744c8207500c1400d40344502c0340c50301504c03840d0703520f040c2981c0c0c40d0344921180d8003903118076051000c00d000010310192180100b601852041d043d560 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 48243942 1250 48242692 48242699
    0x14040801050a0b040e100f02040b040f0303030c0c0308060d11090403020615030102180603070306080f0a05010c050a1d03010e0d0c120509090703020306040b0405010605070201180f050103050a0b09040507 89
    0x8044480900c4a80e00c242d09089511170b04a0000500c1b66980e10b41400000780000f46452010091145500158502c0e41c046030000752004030320040c20880b8042e850600c138240303942c030742182c1145100b00000c000c901c05c030700811160b040c440920a181c07841131074a024000f801100003415100e080b9011001a40443c0c10050411048225402c1c50b820903002542400c00c08003c07038001d500310055590089101000140e8001d00c6600108020f21303c00003030702c0b89035060415251b1649030104040e9003a601f4180b04000300e600c02e2080f5000c0044958418000c0360360f040c5001c130444c041c40e65160b807641d210503518000000900c044030241c00c068075416280c440901e080e01543e0204c081890034003205200e0850b4079110b80080650024403444c0069490341c684000a00420159040e80c0c0c01a14100010451580020040030158006d07260a102c03035501c40010110b480c000c0c0113000c003d41d0109030030031055020b80c11080d005280802c0c04140244140040f420b501c4080340d0a4030550303c04031040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 48245192 1250 48243942 48243961
    0x90c050d0525020c0303040b031510020f2103010603090201021002130f1203020d0c0f0b011412010902062512022a010206130f0203060c0306100e0f040506011404080105 74
    0x102800b00c40c2c0040c00350424030000207500d03406244100101050b00000064003003400458038031020a0050041c804201804402541ca540104411f0850720400400b03000301e06002c0d00c0e03101ea0300c114070610780c9560b003842400c0303001d845481000c81c194072500c281a44c205415002a240001a036220341c0d200c0c0380780024480403214585d00c4075012243c2c12682402295020030300420031005800d001c001c20080e45070903003040001007000b418040c0400c001282e03900380419004000303001241c0350580550045c00440c03c80d4400d4400940c081001c00c881d2044c0398909840c0d1903909a4040c0741041c0c158161202c1d00c1c0489581201c1005030404601c074100f240003c4810000d442745402d245c881b5040490000c1c2d40e90001910b4050443ca00c06251402c01100d89440c1401650260949405050585003031505410503515540b0030385054882e441c520388204610340d0280b07001009851030916800c01d000042001604030703810482084051a01740e0305007402000100126400040c0b24035041655 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 48246442 1250 48245192 48245251
    0x3071206141504110310050910080307030201060e01081903120e01050406050714030103031b020a170105040303060503030a0503060f031504050a06050a090f15060f0b040f080a0c090c050d05 83
    0x102140310a050013488030a64091101c0020b0707c00583d521401074440300f400307a4040d22183c0c0006040e12000400104240c0d043d0400e40440d1030481c1005c9260362120100e0b501d41040c6503203c0ea079158066403000100740325100e814200c0740200d80008041d25040200303402e41d00c04481c10380e44591140103000e980c0e175108201c0144048400a0281194103564000300007107011105440114801c0074001c0c290350342e0781c0608009105900c4e4000000848584a0307000e410121825404a8507240c40000d041c2004007c13640c503001196a25807540d51210108644140c88508070307501131284136070321072034000c140e06183e0090b8000c10081c0b5806189203014415610010b11000e12181881030040c00194255501c0341100d81c40b0200c04000381e8211106401010650b0140c101c6e20710000c000500f00d81e00c1c0005000b507a200b20b2051011640708c1d030340565180c411031070040441c2c104900c100318401d5164000384400c249460441e01d0880c42054000990b4415115031082d140d0b882c00a1083c081c2036001c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 48247692 1250 48246442 48246461
    0x803040302100c0f03050906090604260d12180602040623040506030109090203010b0405100e1b04060c05120301141905030d0507050a02060304030c030207090b03071206141504 77
    0x8100c00083c0c581d50781c0a9030501c0c1020000d0034017002007240314003551441c082e1001c0b01c6014080a84480d03a40c40c0c80d0180380d020b10085a50b8141c0028408a218008150f40003d005240c0b100c1e84801c2c49080d01c10020702481c1014050342460040b05c0c80091100e0004000411150391401400c0142e00c2d1324210400391900344100c0c01804210800c5261030341825241100e130b6080d00050080f10303a002080c09494881401c992003494034041040e450a03e01c1d40005540c0c240881030b01d90b42e40c1c1641e0b010210303041c20741040304110174003040180c2072080148500d00c620503400c2d60305403107102d80c0940c11074100f81c0060b94105603070380308580b1070308100641d458035546640c0c1207240145044040390b215000c20540804104d00010400140202000846032945e800f0b000c169692409040040558a01440c11001406059400185031269004030344064400402a2000c68908204061124407004d8115441074648852030400498100d038170340728000c242c41100020303100340d04000c211802c0c0c1e030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 48248942 1250 48247692 48247697
    0x9070609030f02010509040e0610150903020a0e060307030b07050418050f070e06070c080c010f0908151005131401060207030b0103060203060f060d0207050118080a08150604080304030210 82
    0x4001245102c0400d154803902800e045a9929440300440c0250040b401d11015620901c014031295070341e00300f1180c0c11540c11109203018143c0d050021501d0000310312010758054055403080c0702e81032502c00840d0304010010304a42c8400e94903607525130b0281d0111428804a900810200001f035098842c084076415041d10030021072601c0341411a0012010340200304110002940d02803a440d10340c21a0141d94005442c1e2000c2e40ea0380b2451903813281d40c81c4186000417241800c0c000d000d401400c01009032030b6124090403c8980817145100440002400c00042111480c000206030319140c0591061841003c0c02207920082a42580b02c17000041c5c6c0440c046520072030302000803c000107180d41c15aa030080c0c0142c0e8940700d6000148030484110840c80d8410000504060708184550003005030030305c51002800300c03c0c418103940c81e14441030030020340a9182017040e080d4807482018070940c0f201e250b00c00310108a145e00c0200d2030640082d00140c0d500d5000007424415454640301c00d031000380191 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 48250192 1250 48248942 48248957
    0x20c030703050c102109020f03010f02180405070c030305070921020910060906030b03011b080a050f15040518030d02070b090d020a0210020c18010312020a03270f0608090706 76
    0x34800203048170402d1600c0c0e4075083e5070b4807082e411565402841072a81400030001d2001103d0340041d400290300440c40050580b48042003450300b42028000c55100f56a1078035080103003545074405034007518009001da0708204040d5004184280001a043c1141030100726074800a0103034810b0040850025141402404a081c010001d080c5c1c0015a20142d6046140c0402d10700304071404203024096aa4120313001001c5507008500441c0d20407850780c4540c1c410001409252120400d00c0c80c071308403d0352040000900a1041c08850505400690b0030120300c032030124142d00281ea2407425600070429940c0b486800046070424807880e1900103030061a02d038098000d121404030065500d030402e0030002d0085100c1130503105494000e010034414048050207103841409503940395051110300740012a00d541640c00c03569071841c03001405107031080d803644807400c4040015403103030310074034880750340070107900c02064081365544141c0c9894000b06016100d08449050415806003485c201b60013000070450742 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 48251442 1250 48250192 48250217
    0x51003020f0a08071a12070f0f140a050f160b0a0b03070806041b0b0c0d03270615091404030f110a080a030207050a03090315060b040b0a020c030703050c10 68
    0x4c82d9036000c90700c0a0804014103001c40160440c240281603041c82086104e104007d0481d4100c0c54404401509a035403903600100380d44103495000703c101d003192640700c0034080c50142078003550092014a050071011424030b105811402d00e00c480a45044844801c02c2050210403c0d581c010781c50340c25800c6000c1c0101c28103000d0300320741e242c40003031001d40844840e02140014800025403035018280c1d4480d4290340f04501c0b2526a502c82d9240005400240b41c41e681000210034180040072010300c94843c04589031244d190480504921100c80340f217040500800244a09079100f908000300c030544140703003140742c2420041e00c40a850014041441142e000b844e00d18900803c00c1299103500c40035541e140c0042c1e2078110000d0058100080c594411000700d80c050541007032001e403c881c4203107054031501d0203c0703580c141a40d00034426843e07920810702c403c1c4880390101002e4002c000039441114018401440000e2500300c640c1c1c02613440e03420200e104c00007400c00700103588021525090540b01c1215 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 48252692 1250 48251442 48251459
    0x4060c0e0d0809060708070b070c02091509070e04110423040902030307030807090f09020d0b1f030504020310110d0e060601081f0905070314090111120c04030204051003020f0a 77
    0x5107120303c1d0311510001903900e0801c12034109441c00d59400180b010702914041502801024141c10709070f11801d1000000307042c1d901051406600000c016152100e035468000043c1d44580303010448652190f00c1d191489a255520f501034030081002c54031401008101e031502c4c605010007c07001d1405282031990036000758400004859071683d0520702901240d81d0220100e07003492082e00480d48800c9200000980408140c01514540e00c1c02c0c101007121820020401807000c0070a0282c50704e01a980b41d5011685001c0d07400791354070034000380507200c005299800d5401156000202c5804441c0c0100d600c03240c4484510440098180c203100400c00d40c200400007074522803004100701008001c110700303c00f101031400c85c0c0c080107081c004030074042030501c0c03200500541070510f810250f1b90041c1c000111403a805020310b8180740030b0210414506036a4149998445030001c1043c06616410440000103844070f1080d80d00c01d054482c41c2c2c202c00c900314410000c015a0a2004034802d03144c030a000e100c0a0f0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 48253942 1250 48252692 48252697
    0x60602060705031503070303030903020c1f03091103070f0609080105070905100e09180f0a230a05030409090c05041a0111010e010f050f0106020706080a05070e0904060c0e0d08 77
    0x1070750b040c000d0b125034800101074900441c071607a82c1d806000d802ca000040680640240c00401d11035004c2d900800c0030701051200354031801450044004103488803100507802a4084685140500380215401d05841c020902c0e1440d2581b04007145482c41c0c00402116500030702d10000350683d07400900c103070b003090f42c4004c24082c01400340e0303407146403086005c000b641c0c082d4107022840400a001c0c20030301c5c90101c08d018200d003180c00303850340340f401785006a44000c1d00c04640424200d5000d859143c4c680b0040700c0c0f020f406003008140005520510b428980429420800b4000600d2900c402240f107600303d02d0941803000840c2e1142e401642441b18041e000c07081030000715840002840c10007442034101007a58054807120000b02100c0d442c0510050341d120068129610410284013940d02603640c0f203404036034690452240b680016048404200804e070325800c410340190181c034003100303459422000a0213070f0300191811210342d595100c1140301d0940006010302004070860705800700d001d55864210040c07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 48255192 1250 48253942 48253951
    0x5030106020a02060901030605030a0309030c1202130c030b060304080703090501110a0308060f041103150907050d0c09030602031602070801060b0904090807140607120912080603100218040e0106060206 88
    0xd0710302040d0080360b43d209034810001030000504403403142f1304a08000d08840c0141c001075402520703802000c10b003206034090503808254050311007a41041640d48210041c204140204205901e13401d640c4241c2e03813440040e40c0220b004031a0180e9600c4946400390046401d40c3c0541d05015001c86803000d0200d010660008458041c1030000990359030f180001c000300d07444024664001e2810081d0750501c480280550b00c99607401083e600904183c3c404c2200c40b010441320800000c200b00155a11041c0030340145000380c0c018200450115240e07541c030400c1c5d8000301c4024000c0748100b01985c0004c0d604110340030043c0714070002048054244414907004c1d10484100600450f101d0b001c0d50100301340d40c41210042508800800c181c0c0311203176140b0391540710541341d800000c2e00d14695000c141009110324040c05600030b0007400c82140c06801510321940c01481154940200001d468990040c0d000400b19012800801040040e210081108440f05205101a0b982c50705400b4003c1d0f540019081d40c11 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 48256442 1250 48255192 48255199
    0x30c0c01080c09010818010501090c0314100317040302090406050f060f090109020901090b0a0203090a0f080606010309020f090103030305010f120503030106050304150c0314010b07020a0315063305030106020a02 92
    0x2540c0c1c0410b86001d2402506021b03080d0342c40e05000154580c41c50b44001031b8508155003d014105408185c9130000d401075030710811030078041004100140072a403c950f403400302c40c5c40076030034036540784c0024084080807103050f02c0440c2c681c820041540420b10400d03602c110200e600000d01c00040d000300d2203050050203184011540010b200d12541e000300c0e081030040945446c111340c4c0b010510700c000d44175004030000d10700900b03005001003080c007070300403540c8191010480100840d5035008011000780801b860142e81055003060041c165464030168580a507010340c401203072079490714039040f4030b0324070b10b034030841c04200e040801c01c0c005034010003180d044441d94602603807240c4841c10400c0101902c0f0f0004011603182211103601142c00d9040903800b00008520340c03895aa07503046074011441140802503010b42100010f000003040b85807a00030441c80c00c400000e045d03890314802184140004a400b505540c114503440300780040040400070a00d81c0d103845410340d450204e0103942c2d200d8400c0001d12 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 48257692 1250 48256442 48256457
    0xb061c050a080a0212030103050f0606030303131203020f0309010e0607050a020c090402030309031005060406050a14011d04090506060f0613030f020613060503060310050114040203040f14030c0c01080c0901 90
    0x1114402c00c0140085905d48013500c0e503d50b0340e454559690701074080c0d818010301600000510518020003600c0c42075101b1641640c402d0455510100503503140142d51081c1942400641d144180707000c05540b1600c3c5603800003c006083d08516860700d600101010100481080b10841c616400b00c8c00314006001590504425111840000c0c15400740e5204250148070b00742128011510642000340541c45c01e880401030700361141f041c405450018082c001c2140580345900c46035500c1030310011149810340380240c40358a4030340000340580e0390b41003007502c00d42e00c51014840c09242c00340301d01840000448800345000c114154a0a07103034403030310024000300900c4240700c0945d11840c0031290b400c00f503d02c0c000f905a071a16405061a00103844041c064480c2e17244001314000188600381c103958129031080b490801c01d608000103075000510886030340c6040108080014882020524103c49090185455054004143e17142145007882e10741000340b4441802044100d2000f00d8482140c00e2070300303c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 48258942 1250 48257692 48257707
    0x301060509130b090702160515030c03060a03060c0f021b0307060503041a010617060a300f08090909030a080105041a03150a060f05060a0309020d0b040b061c050a08 72
    0xe0042844484041e048070780c45040100c22640407c491480a81090044112a850703000b4000844600c1894261840b010404129090340942c040c562055000b0300c12403005403030b696280140d82a0b40390840c003042c3d802004100e00740d010b021841002e01c2030080c00c04015026400a9901c6216114200c2031000000205041c86a000413506018504030502602540d49910003445000b4806d0040e000801483c041240c0d032a01082d0b2030f00b183c40c0a03104e42c1080b560800102005000198075001c0010503032407a41c0000c1d011001c45011a00920710710340c5482c40c5806000604000519161654000b0000003082c0d6810124050540300c01b940c00040320345001550203c07540003401807541c5407144c3c4015451109a064281c1d204812000d4103001c604d583e5600c0d0407481ca19801091f900190600ca0582c00078401d50007446003900043c0405441c1d6202d44968001103401c0c1c40aa40000d007200030024103040c80c0500058142021034651a5480d031921820385901071994014121000002c0c0d42c07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 48260192 1250 48258942 48258979
    0xc11012304050a0c0803041d0f0105010f120e070806130305030a020304061e0e0c0307060c020f281e0506070b060a0801020a02150a09050d08101a0a090b0301060509 72
    0x4001c00d038013130446007543e070301c81c20955541d4200d88907414050501c44524024906506001d9000752144546d00b0800e0742044010768192140703559800c01c205c2c0901410441c0941800f4292042d014074001d0070b8620306214495080110043c0100709510798040031800090b48102181e501c40c2c0d41e001c0c0140c49458526204c0003070710b0788040c2100d102c807180254900002d400c0d03200c203103240100012244a070301551b00b4507807100e88900c20503011900300840e017405400c1454060b045208024138440c610410541e441e00342612019a054091403c2e680c1480306094040391407400c65600c05880d9542c9103820000b030060b20481e80001c003003038a42e00206820b0740f2400c3d60231018020042c000c2d07444101100c2d00a41e00c45140d18005009614032000c605215600d01c140075159170481c0c060000910600c2d0107880c2d840c1c2c042c000d203492401c13451700010441c14800b007214203559006007059562041000050100616800c4862107040400041001740d801008503070414000742c4204109200450741c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 48261442 1250 48260192 48260203
    0x803160302090607050607090e1303050d0f0e16050406150c020109030507091a060304031709100501060f020f1b040902030708120405030f0309010c0308061f030c1101230405 76
    0x2e40e0000b002081c0001040000703e5007510504203517607034410203950f580c00580c1c80721060b205002440c1e034904114000c64400c00080c0550b89040b200860442002c10110080b12004900c005250304211020001c0e02004244200205421982030101c941000c1000c20840002701e401c8092080c8480701d4021a401109140001d60b040410f480420b0380e24410017003c0d2605450400400079442c451000d42e1604a06503804ac0340c250b03903035944c00d030341c1c91300504448000a801c10302c1c203100d10280301c4450300d150b000e1140a0000c079170701c0d042510040200685880303000b500c1680700c0c0e003114410003001c1268014001d1000d00454001c10310180d81d0001c0f070b0a00c00180c2041c00c0d58091000d520034104112402042218002c2d0110346002c485155034540368010340c00b40900141349540160701091180441d0750b0040e900800d0025141034241842c00060340500518012a860701003c81e400c58002808100340740c104002403204480e03c0c1154403050310100c10400d6960302c280b02140a01000b00403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 48262692 1250 48261442 48261457
    0x40e04050a0b041b0b1312020d050105130201080703020a0212090d0512030106090f060207050405100b1c05090f060c030c040b041211060703080612032208010501120803160302 77
    0x140302c03000d4181410448070b2000302982400500350340e201d00180d0280741004841c40c0c2d90707010450f9071100b0b0402c09621002481c8003000e0703074041070028a40021510a114a900480c028542c03040d103000325200240400c00001d00396400c0c18414081c101c0050f030041020403055080901c1283d031002104001882000b6540700a04244280c10400307404460f0940114142c40361601c52035044c039542c800111000300e0b28050040140c03c8800708005904064010a0304510242100309000d500c40c02455015000748480d80d40d1095508215207240c001442460303004207a0502600b24401005a865035407003001d44081d400140c0000050000c050103c141d82c0541440600f0317541c0c4030b0b03a44c0b848651131840804d085d601280300030151407092a102d001c071608568161103044940d80c6030010001840c0c65102c1c419154002000a00c126030141d022101c60702c0d5810520545e500c2c1003551607800c64005030000d03107000c00e000a950300410054810349a001e030503c0c4604a003510028001c5020f80102407 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 48263942 1250 48262692 48262703
    0x111010608060108070f06140d02160b04060b03030c0304030b150301090b0103060507180b090a03060617062412010e0a1202060906060609010311091c120e06040e04050a 74
    0x2440440c03150000b0411078103e0701e16200b00c1c0c10242e240d001d2010410510301c01d8001041d003076000d045c00c0da07030303000090900f42c003800c1801420200760101500518200d044205c540c0f019450401c82080b41d9449560900300303084d0002c60409400c240c48950303921450102501d14808680010709000c2d00760007140084001030020310503100203140c417034580321003800100c9500707040a00161600380309803811807500512100800b440341ca89024484207500c016001a00560403410100100d0302a0041c44001d140441d0107081c03d00085452a00b08a4050301d050200000c50300b0030140e0781c80584010081c80d10464101404800400b4030500420320b0404c100000e001c3c481c2850144a00e44003224a014942e8003039402680c1d5101c0419280c3d80125031156001c034080c404482c440d4425400701600f18040c3e800f917031a0002080c0015140c4500c11401e05032070355058205010040d20314480c4505400b036081c14601c000920f4000761076030285010340080c2c11b074480009800c0c084104540004c42c1c0c0c100c2c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 48265192 1250 48263942 48263951
    0xb192d03020a090c120207050d08060d140c0301061202091816060c0209010603050601080103030302130e1503010b030a0305040306091104020706060906081204290c060618090c0f011101 81
    0x181507000c0035001d069104c4002c210110314090304e20042d8002c940003164000d0140401c00010341c3c01f640d0300e60f0054034040c1c001310208806400110030b4244d1129800c08000146031040c0c00504040c2920103d40001d240014a42d120703400503140c01d0080b5400848000300701c82144080348000340740403d541d4442e82010114032002035065003011401c08828000d6501c42c0c45070385c8844080d000e4802c151492400200d0b094010800301e440795010700b185000065464441030382e0b031001810043c0c4182d1741005100000b4604000740d1a0034840d14040500c281c002e000304a0780c070788005d000760090740700140c606612015150100031014448802d10003005004540355111030400b5002462030340030700c0c000181760100c0880c10040c00222070346800b81c0314007054135250500c181e410406118a1180000c20307120410341035155905e0300030781610801d84005180c2ca181035400c00c5000d001c0000740800d000c54040500121030000304001d5011034040d922888114200c80040314440d994a26140e91540b07803 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 48266442 1250 48265192 48265199
    0xe0d06020f04030b011802040303050313020310060f05090a050105010f0f12020307030b03010c05040b0d090c05030304060206150603071b150203100305010b0603060102031e04030203100b192d03020a 87
    0x140d141603040e9810410501b500ca070300c0310f1ba01000c03031240d404050046070042c40003030380c2d40c0c146c15a4085003503c080c00380d828660b16650f140081c1c8134550030900d01d45c03101c00401e0146003040800c8540c801e4161209008030751500c00040c1182c0b000718010010008543d004d400b44a0145000c210166500e507021541c0e032a0604000b0014031509502c1c0380b0079401c142c65031002d00d02c42e105480c1a100d019882601c2c108211030300e5001485c06200449444075003400009a1b5076090000c1d000500c01500500124981b0000007518188502044d40c81500280103004401d80e020041199906150040c454040c20301d0600141059244001e4501180000100518500070311050400c0701d05c100000d02c89400c00f81c0070880a0f01003205e240c1c4c0103074010f0000482010041d40070316405849202410300e459180e03004641481500030303000001d180c5a414086003410180040380c40c281c81216880c2001d81414089200b160780b4003402c1c1039501d03c1040f8940c080190f00c0850004650040031017590568 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 48267692 1250 48266442 48266453
    0x3120507032304061b03021b030f0312060310050709030b0c0c010e0d0f03050c03060603040c09050c030114030a030f050903160e040201261909060504050604020a0f060e0d06020f0403 80
    0x20601071300700000c14089024400744401400c9040c03031030380368010303104403030748100c21080341291418160307410f209801481c960b090701880240540100300d00c04e44194900ba0040c0b40c40e10301320b00a125402c078a0a0300300310049030f0100d0043c05582c0c1c00300201c20b42c4e440300186a0310a009040301c0188951804056410700c41c80010003481e10301c030980358000400d070101c03000c0c0c040f078004030b945080407001000002e2962401d10300030755000d1312542a0854541e140ca54400880c2d5085981600503140000144541710801d0080c0c41c6903030048004041b0000641d034018400d02944000c00c0900c000800c50344070b5a6024450350a0441c4214800701401da643c070588651660196803da02060300c4542c24200c60721543c250100b0320b036030300c02c24a01c66100d107079440e4001c1907521a82ea210594810f050800601c0601420340958020001002c55081600400859080d07540c0a83d00400b0042d108200b038039002808902520703001c0307031340108412550612001a204003170340540a2000000e01008029 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 48268942 1250 48267692 48267697
    0x311040504020f0915010f0905091503030f220902031e040c15020106030b070302030105180601020a021f0e0102060907031e02030708070f0603020f09090406090804060302070b090106031205070323 86
    0x1c009984202211f40311203000d50300800d0340c0c02a9030b002162000080c1340c09080410003020105c000d000c032850b02c02d40004104590300042026071070006d015025200c02d00e807103541a0f0103090085400c508c0c0d400d1103900c0300705810311414030061280800300018103202e4030181940c010314070100111070106420328000d009180354001105c00400250204841c20310910969040e40c01c05032141c591a400c2c2b840d04850b0510040c503003411403145600b804016140c51a500301c0300ea0780444074201d04614660090088600c0e5000a8110752100080107510240014000f0403a42c205500f01402c0c03a083d840d1344004510484080d41510400c0700000d001c00e000155141205e041c07190795514141c6070315003102648120307003000c0711031807040c0140c0d04645000e10302c1c80d0f0002e01ca41000148108556109512a0095031108001c00d50109003e010300c4035050032540c0c4844030300c0c000c00001e81141e0b6a140c480c0d02041d44103082080100360b2000305406001c20b90070004004040c0202c060a01c140300c141503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 48270192 1250 48268942 48268981
    0x170f01020d0b1903020307050111010b03010606030905010b013b040207080a17090d0f0315030b06010306051206010902030403050d020304050607090603020c0c01080c09061303030801050a0311040504020f09 90
    0x82400d03c1d850000d0a940c0d1030b400080d81d50040190138801c2c600b1004680e41c26400780b10012035561800d42d041907940034030521008080070b49011130318100d5801c1c0300382102c0c050310a00c1e0511031056003584040c2c50310b1244035510480407407018a0500a001c0e081c2d0784540d104c642503007040c400903080041c8010600600304a43c1e1300c0c0c0d42ca10415480512901200c0c40c20307074074151036501040304800b2a40c018841000103d0982c900012415540b01410b0003034201d50348183d601c101a0418000b00b540d0600443c0040e003016908101c074000f000c02107030764840051003000c400c0da601102003810144204101ca020100b020025510390426040ca151941000d45512000c40d0902100240b45070181c026a040340b5200005000c80c0c010000041d0307070a6100030042d40280400b04800f02c21545c40001600a07001c0d00100b50400f0350541c80c0203802044103070011031140020f02d0040001840b90b5550014036103090b01c000c80d20b0b44130380c804242c041381c081c04140da000d12940204110108151003402d0b48 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 48271442 1250 48270192 48270199
    0x40207060506090c070f0201030506011e0309110303071502030703020906030103140c1e0409020102030d0e07090b010504120303021602040c050a032a0e0315090303180106050a170f01020d0b 83
    0x35413101e01103480309208048004014080c1102c43c10050340c080e510082c3d00880c1814210017201420085803a94030028080b0008681d82c3c1408106100c4000d016041c10107054006502c1c14032a910b0f8040d411104a078a55105a0000b0005840c3c9202c2c1c0c0540f0856a0007810803500c9507100e2030a901407502c200c84c800541d200b40c081301585854101c1d084928440c00718000b0420310004020302000d00041841a415032100300050440700f103491003080c011080310005880d0312400d0018645c01c0d614811181410090306102c05d10005001d040f00d00c20242c0c0c5820016542d0b0a030280c00c2c0b010081d0804040e511502c1d00d4524251950000300911441d016507908012100007103030038442c0403c240e8000d1700c0c40c4800a0881d011a030081b100e00a103160300800700c40300141c90810b400302213082240c903082c850704003100380010060602105401080c403080203218450400d0042a00b0b2a040e00c20b082e036045241420b400b03501802e00104240f200000000c0d50f5885607030558102902000740700030301 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 48272692 1250 48271442 48271459
    0xc11040203010302011b020a08032a030306011e1101060e0a15261e01060e0703060e0f040807050106080304051905210712030e01080915010302150702040207060506 72
    0x1518a000d100300ca0690f9816110000041d220011a0403c03104614040744c02034280700002c507840d802000a800300001d00e40c928250b10351051400598184c0c000700360341c0300e58030920500405a800c29480542c885615800c0124280000c60071184c0001503d0903000d2540391442c081031001c91149800c1c46145080c200348012040c8082e02e01d0304c00064890b408110382e10342e082c1c0401c0e5195408000c0001e48410848e0400030b80410715003c0301d8200e90400c5540d0b03560324802c00520074144015540306501d401c00300621032070301130341001e00c1030024130090806001100043c104410b00080d1540c242d0050b0080201b5921860013039541ea1007030044503c640d45034401c4141007050f4114020682e03001500942100079540010b000c10405a10702010300e004024000c1084038000349180344080c06990b400b0100d00b4081c0024100358005000451642c001e8a0815040100d030328145044a5040d640540c94800c41c588a500714052220000e500600010310b41092141507003103075015800440340c581d0b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 48273942 1250 48272692 48272723
    0x1317030a051005030c0a0b0c030f0d0204030b0f070e150c010f05011a0a0e0405060103020c0a050606011d030a0b040201110f010f0f0b090109020d020403020a080a03300504060b0307060c 81
    0x51781d030402c003100c02c2d90110b541d0200744068042c50000d003401002c004100c3e41441140c0714022002d8100c4035120840c1680030170204240240d14440310f400140115012110f400c0c1001d00400720f08000b084076014121030034151034034107495405c40b0a0050301d1002045130740041e000c1e08010380400c1c4190f0311525000b00756409000c03440d808172045000c0a4031b80c400c88110340d000b40000b5141c01484141415030074420a903000f00140202403201e03100300003824041c940303039001506080d10200d540c0720080b101044002c260f14001a41c541d1035401500c00084c6941e01c0c801210300c01c00d01c18440206006650303401030320b800705400006140ba489182480540030580c0d11404550801c02c0d40b662120f013284c0100001c001030350041849500801001d442c15481760045005403a00303601c88092580491080c2e400d25601202d086c01142104010f036100c012000024038800d0030a0980181d07041d61040400c0c03c201c1300d81e008814401c0b0241c150351001d940d41e10043d0041c4031600b070a9405008041441 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 48275192 1250 48273942 48273949
    0xa0e0102011a060409110721020124030602091201020d090c050306310605040305040306290f010201090f03080402031e0604062f04091505091317030a051005 69
    0x1c0407000d00401d00b0540341001040141081403060200c015042141a0120303a035801281807090070b0103408c10f40c000c4002402801c42c0d142041c2d07100164541e0144066140c2d0380010581120703000ac0c400340e1134001040000b03040c1c0039004134150440d0b200107003051502403c2d80000f0840d0307014440c0300200c40d0341c032420305072111000c0f03d0500151140014a0301003140d0880074407040d6202032000c00070340d8070704d5841204880341981c05030045a4089020010006030b8080d424010303001850b4aa0310071080c0800340c20100c140d150311807040d028490484441c0e4400d600000e040c0d6082000c80e080542141005452044141c0b020382c000d00500e4003038001c007a08901c0c61200000510002c22a9944540700d000080481800c40c4404940c1e402001200300894190306034a0740300b1001c40c643d07552500c480741c4220b4100030030710911200042c0d410480c0351b4403210656800704200c403422401d140c4034904200521070311228141103800c0407040c40300342020341e40240d00c101503410078046095182c2082 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 48276442 1250 48275192 48275231
    0x5010f02010203040b0115020a0501090503040510020a320714010807020a050703030c030507060e0105150d020d0b040501060308030403020604230c0d060b040603060b090105060901050d0203060f060a0e010201 91
    0x1170041e901c50300c0101b011000c00540110340c80800d105507288030b01ca80c2e42d050b080d107800784c00541c0e003580007250500040c58140b1440d81c00f2140d600003850345003207a680b010782e5640c06031000880b000016101800d4510414090340c61013203950256083c0a84540040d07a4681011840c5800140c041d4000f5003140c0c0005908a5103942084c000c1620514565044542c0490751208404002c0188000303400260325015521010f0b03280c0d00082518585520701110325421801c46500c03603400b0703454070400341c1c84805211407034a420101c40001c60351a828290b0150240c1c2e440144580340020401040c580c1c00b250150059115480584007448a0200c0d40c42c5014005900402c0d1307080b403c071000c018a020f02020204502c26003010842480400c00901240e645034030030b0f2841a03c4051030103080c5030281c0602d016120480f2030a0a002660000a0190050807011500541c0c0013002c608240e4400d00d0b15540c61a005000316036600c889a0300502c00820000348a000d9801e1103010213620002109 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 48277692 1250 48276442 48276451
    0x1a0c04080316060213031103100c050409050604020c030408031c0b010906050d0b030105100e161e03060f031103010c020c0105250807050307031103130b0f0d06080705010f02010203 79
    0x25810b00d002c008056140200501084602039820407000d0949505400144015801420100c01e50010501403500307100401d20840081c5140008031071482d608001034409942c041c2c14002200d0b80d940c00031500a104508104c00b003488042030000380d980d00080142a5421408041001d10f40c1103602001610000e907500ca011900e00c0c40c040c001d8078801e82c00b0b072052114040c0042003200420000c6801c45400307544d003920701c1004100c248024071031207803c503400c420385815000e6104a50302d8020300c00d000c0e03145142e8a0750700490000d00c0192007504030401525007203045810750740d541e250003104c141d414a0028065402c02c40c402c0304250000c2601701300c030300b010f84485182c04866200c56194204180c00750b025481752601000110380060007034007120388150000c1d5035400c0c05040240002c80000030300c40c095030040007201900d280707681213201140c2199640e1511542070020070341c0caa01070ba4810040007480c0000c0014044400140c41040b2442a01e13400c2030f210031b002c030880c00e0b4402112f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 48278942 1250 48277692 48277709
    0xc050109080c0f03121605090a0303020f1515091e0c0304110409020a0e06041808070302150403021207061107050705120309010e13021c0b0315041a19091a0c04 70
    0x10b0800b10001c04802246c1025107801131800c000200002e2004205410590059021000e2080c80030010003507404180c0540000d0140340c900000b00f41524111006118003d10198012840301d101200c2e91881804114403000c4051400700124042070300211010b448c950720000c1500316904003849031500081c0c0140503401c400c3e082c182c483c050300b10301818094106a0743d00010407101010300280130a0742c03003894820350341c112a042c000e02d0000902c00200c4280203200c140320020790001200e008041e072840a6641700c9034541420b200400c000b846c220100100003641c40e041200104155051320b00440d59150707103401503404c0786c3d5603004400d0f0590110f405000104c2c0d9900c0c00140701150501704a03030142c90150f142c0010031036092000320490200d5141d5852701c803682b80520038190b001c9902c1140030b07040c5c81d0945406080c59850003526002100d408041000b003008803050084610380d44100b4811000186071004a0452862490710b54101250126407a488018126800c503004407 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 48280192 1250 48278942 48278977
    0x60402090112030512150a080303040606050406080d0305040302150108061006030506010c0809032104031505040b06060d1b0c0c0905010605040608072604050f1218010c050109080c0f03 81
    0x702224031700b8030302c0500241e600c00181c00c0c500c407079945c4000180000c2e0034242c1c0511f49904091030301406440c25034100314030036030070f0441c14424030100003500c8035203a0f02441c01103400e440d1410160b051241409a0b8080c0005581c000701e06400d0004420303020340544848050305980e1003d0460844409903000b50002d50100d01c0207000c1103a100190480800060940701c016801e01400500300d19030302041908210081000c1060210102e490518406040014880c926065071030f201d8074040140a10b1081c3d01c08500d08400c00c1d5294010f4401034043c400004c0380380d0081c02d020300120303240007080350503000c0b00b031020403161128041c6904030f0b42a0349596040608010f0252000200188440c0c10040a242e000c0d039031b0024014940c030071940451005000d4146401c042e420040f1201c0898101d502811801c0e1180400c4001c03228603130280341030200088004001220b00701185070300a44590b003000e010000f80101030f40240130f005100002c45032005040c0e45895240c0c081c0705104819850b44 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 48281442 1250 48280192 48280207
    0x14191101050a090e010e0601020d0509060403030503041109010b090a0f0305030909090f0703060902010e040b0112110405030609061e090d08060402040305030c070905010603062102030c0a03050604020901120305 92
    0x11400b81035078400310b0030464901e948440c041c0340201c800764041c40380c01d0400303814402e265030144113001c1d442c880c0e803814500c1c0ca010000400c00912852000030200f1200100040c10301013210b1040c40c24000c014250340080d6916031001f90503800c030b04071040c0700c0e03106440700080740c1c2440311040381101e40c043d000c1c50401c6203000800004140c02400039086019110384410804000d10071072018511035080000c985500380001040181156070113401146041540309440c1c0e00108181c0c200d004c0e0784c50100d40c171300c0340d80010000c6009070381c0240d030584280000d100600b000490480d20031f44119403404400307140c1c6094a031200e02d05486140007038122101100e00b551092024652000001e00058a00750345c07591240e1540e808141030014a400050b0280302a0f903090150302e0050a547c40c09006040c142144900c982170741d809840c02000c0140600c0085403012710503000d1013000101080345190340e90401c140c40b481c0c222401c9200b54041000801e0940c5412227806c45650103503a1207003003000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 48282692 1250 48281442 48281447
    0x180603021203160807060b03060903040905010b090d140304080a0b01090b04020f1207020c0a1806061d09100b041d0915040303050403020c040c03020405010809010c08190209060714191101 82
    0x10100041c2c9429880c2d40030f510300f41d01d0270081c2034001c03200e080045a1311850141000100e41d01130304025420700c01081480e12030366805c1d114018070391700894008920151802100d00d5481540e01020f850f000390309400082c00051b41d08541204c82c0d000c0213001d10601582080106d1045007800b5403a0201801218940700790300001a501000500403036220041140009006080c5030740310321840042c0003005c10360414540541d000918048c20714940301100c81503400700c6034a1106020b8090b0155000085e00c0061000c040001000b60440342c40d62203895051252004140c441420352500024021503070205001901e05000c80000d080c24441c2d45845d0340c11805002c0c050b00c10b50841c860103400c1a8969920f01c5101741410580c2c40040e43c9529040000d00750010041603000c0991600444946440d0450002c3d030344110002950b0303012801d083d02c580000c0c012502490f030040400300d007550400100c003c450300c810410100319455240304e550100004a80d200006001e00054081481e0390350 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 48283942 1250 48282692 48282697
    0x11090a030b1317030a0b0d050c060f2215020d0504051003090b10080f0a0f06020c0a0501020403050c010305130f020f01020102070b0901140106020609060112020402041806030212031608 81
    0xa000811007086851561241883d052001902c9041c0300000020320840381801d2007100040c0d1415103200c140e43c043c2e610380d243c0703c02d40d000317196010708400a0701c0c0030040b840108961a4036504240d200e0b80e001e4240a0169116141c083d0807082c813015200112207600014074185003240702d0350b41c98a81401d0406002030360b030040c00b1100a164480d03514100040001e0f2409205801104d85e0111981c601002280ba100142001b0b11181d085000d095010640314507a4000c40e0f40c1210001d40d80d95842d544a44c680b0204c440d01805a500c04039010007080404601082c420a0903a001e105070b4445003c910740201e41c01c130b80240380441000c1c2c85001420700300c1010440d050140001428a135a07501e032500d00c54011a0203041e5a551901c0314a071000454440a0240065100400c1240341c01490548d0b03c20042c024000f420605141c001c1c11507885804680190403114544a8481008003004c00030709040e001c205c0c458044d0300314441800e40000250f0b41020900781d0b0940b140c0b003460b140c1c810b655 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 48285192 1250 48283942 48283951
    0x4030509040b030307060e0c0109030b160216081b060301060c02010327080408061605070b100b07081306030b0d060b040f0513060b041b05130f080309030111090a030b 73
    0x7a884100040300e80d9418005440703024020355010030b0300030301070001d181044002c3d081e481c14452800e100381702207a042000d4550003501110350082400c001034083c1d140404240c10b20325009510303007000c6021500410701c80740d003240714092042407010b03900c200010750000f4004c0c1d00c001001d48140902640c881d0f0000302c3c10f800c6000e040204020410040184044204802d407400300300001d042040407010001a90300160f00061521819180c800042c0513100d140c0c005001c03070300e215020910a87e60030800328006c0c107844d0441d541d111140d02c0e0071202c5800140c6444d0850130300c3c020004600c0d0107401507174082c0c80000d010100301d00b90343e030b03481e00209100d0000c00d400917500c001e044c44d0501680b0030f1034001d001800201c10314000e145041400d41e0384444203140078501b441030014041803920910300c909422030400c076031030741c0c00c05c46540c0040c03019a12a54940d96945400240d4940100003091180c00c140c0080c0480522a035200d4040e01ca010161138000390000010000710b03240e6500e040d0017 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 48286442 1250 48285192 48285199
    0x605070311030c1309181506050d0309050909060f07050f09181009020f0301030807020f040c09050a170c0103020a05190203040f140a05060d0b0415030311030f0304030509 75
    0x7030744103103180c1c00c582c00c02ca421450103070380080d00b15294030f0700f02c4107034004040190060050f5840100411041000614000d100095034589401d0210301d5400900203000007400c801c0380c01d0158100206003080d280b080034052441c4030082a2240c00115140c1d01c40c4003014440b130602c1d202c554040710141e00521080004181c00e02c07003000c0c03a40e0344c080102540e0240d0450110581403040380c0c1c1102e5081c56021144680c8108181c4501812690076641125008200300e5111001d50000c02c0301c4407040c101440e8070504c0c00104417001e03034020a0300800c3d5141030350000c1d01325071248105072928441c42940303030056111500400c2158400c0d0010980400302c0d1030401e051500e0020401854203a1024000160f00081800c1c0209040441450700400820001d08003101b1140b0110300c5c00c1105000f110702803003001881001440490b0004969010054420450141c0d1034002e1903541100307000031000505400305621071100000203443c07441c0d08501150389941c8940d0390550307150f40700b154960b40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 48287692 1250 48286442 48286451
    0x112090b0108010509011506020a0b04020a0b070f0506060d02010e1011060a0506030c060906030a09030912050601030b09060601080c090310050114130507020a110315071101060f0e0406050703 84
    0xa910103859802805501d001203424140600c0c0d10742990008010b807400605210b604115060780003807002189600300d020482f49460711700100b003802541e904500301c03001000907a5403c11040c2407102661600480a980c1c890301e6100c100004404c0702d0001a0005014000103030a601d0b210110044503d0182410307100b494100d0030b241e040890444d24401c1c800d6964040103000c0c00c0078008140e4152007201c140e0720f8280c507140040c070b06000241001c40c10704d40c0d0741c074040201801504510041c220380000084001480d10b8075541c3c44030709000854079410b0f054040307910b44030009603080c06000140c50700399056444012a9050f900540c00c416414480e00c8110100c0c00380c54410540079010301070403440315a2400c0244150800d0980c1078084051170001000070080e404501c0524442c1d00441d043e03c06800680001d15010f42d849414540ca2101400d010040750810039201854180c01c0c02880b16941e18188180c103141144070b0480b49080340341c0050001a55030380490790000d15400e0014 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 48288942 1250 48287692 48287711
    0xe0c0c011107030905060301030807060c0306170705030c0d1a1306051003110a03150e010902040609090b010f0803030615130305060108071a19050c030a05030a1b0e0112 74
    0xc0c256111020800019080040d0080c14980e201d404040900020b450301e514651440da10161f80d0300c15034070050050b550300c0c1440d83d000351198106500030030441e41d00d5015a00d200b00190b445174880d104803446442110482c07a9503050100c40841c041d60031001440e440807181000c61035004000704121813404406001200103900e03032143c00d0290205030701d1603403118154900702401804103900c482c0314403181c480800000307503100c81185440280a10100711641d8480340c0a01404485074000c0d03009003484408161400706a100360f8201b80103012005903a642d0b9544081440d0660240c099260810030005106e4100004c0381940c10f41003d405c1490710818244a46d440728042c1c10485a61b045a00108081c1c00d00f046440068031a815186141d4604011076800340d219406041d00184610410400c0050040050f01c042d021841c080d41d036903000c4100001e005900c12500c8860062525034980d01511031101500b445400c0c603103503d00d500340d02c4001900c6480c510741407500c80b142c4600c00790 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 48290192 1250 48288942 48288967
    0x50105030309123c010b0f010e030c0301020d0b031908071e0b0403020106090f06060c1104020f0d09030906031406210118020907021204031b170c01020f07050a0e0c 72
    0x40405803100c1401340071550141459000c0c2456250710f480c100e80c102100351245a1b00c1e101c030048200c4003400d010145101000100b400c0150904ca002c0d410351010429060141c059000111100303030440a440084101e100301d65412003d25101a04550003441311000040e50400c260102c150010a2030404010541e10800a40f03802c44040700140d4440300200540c1c1c1c094062445c1c0342510050920247c0d0038604002c0c0080c1ca40030380500754048114900805481710360417034800c1802c0d40216a900c0049600c2d01d400340c014110700310700052000708d0000700d240c032a101d404040c1c0446111100c40303032100740c1000511340741048091214007500c01c80c0c1115000903c00d08000511240911013100f04c00e004004514800904000a54005c00c0506107031030007507000c94090320780c0b03c0442d0030b10554a00040380102e1880c0c0008400a4030b00300404e07501040068205080c0340c0076800c452181400d8441e1641301c035a0b9203d0b65400240c0240306000454099030300340c3e80400040035050074658440d90341d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 48291442 1250 48290192 48290233
    0x201020f042403051b16020a0f060809061e040203072c06060406080103120c0605040804030210140901030f0b0402070b0609010b0405010233040c090f05010503030912 73
    0x16002c455020000d4000d1081c41460708101c01d00a03040401071032401c6080640c07007070018100c8544220002401601e400403048070b82c520076030050510050316072180051542034005001d1400410181c1000440ea0030000642c50311403130130380107c03001310207041600902074000501300302c2e4107020341000840d004024154a00e03003056803d40d40007011001c4880603981072000b03804203001d05401c20007440300c1034001e4070881c1104d902191082c00c1001e03100044402240380040140068100420310092188240103081540c0c001c81d0000d030011180c82049e2038042e224a0701040c1140c05012490040d03000c0d03848401415482240403c420304101c002070100d9008000403540301403200184007080c14001c003024050004001c9040c6040d080c100081e648000744c90100007a00070031202c0702400c44101c100c40d00a01201420005682010314085004c00d00c9802404280c030b160244030015032100b400350030304a5002601840c6480e40c01418446030100341500c400c081c0c8284000318601450300c040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 48292692 1250 48291442 48291449
    0x3111606020406110705030a11061c0605181311042301060f020708101503050a060507020d1704060906061e0302010206060a0303120509101a0306060108011a03070201020f04 76
    0x1006039a903081060142403240130b801c0724280f5a005805c00d1150391000a0008100c6030004034210341c061880f130000d0540c1c824245500b000400745085516100c3d110f4010030247c48003210301c810300c5280c3c0d500060000c40300310b5800c40b01004802654012400e810b4403002c40c1c00004d403001c2010302e84281030031004012007141680c0401c4200040000b0381d4044105800d0380d20a2024149131868080b895a64a40410216807090340c0d0707540c520045e00442900b40b004552003000d0761111446030138803000400d0708440071000341c064810540001c074840d81c0c40c2d180302014005c65035180d840e00e0301c2d510001c001c00041140d85d13565410011441c600d54910310341c203203005a0402410141580b000a04005004c0d001d0345c0a81002401400042d03004003031078223620071110740010255101500c1601c0c04210310032402030980f40186138107291491800004040e10709034204c0b51103490703600044480c084248a02c1b407054000c17800d011012451030005541100803880050700b040000e02c401c0702164001e07030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 48293942 1250 48292692 48292703
    0xc100e06070f1a01030c091109040c0302070c0f05010f0c0501020c06190609051303050a0c020405010f03060e0c010212031f15030f0c021207050106030b0109050402010809010b0a0501031116 83
    0x80040403c41042008140c401c901c10a070122075146946403400d0003003074000c8841098441034103881c95a100f5003a1039072000028003e10101c1046c1c0c0000d00298040e180030780c3c54402605001c070b03d0850041c1b90303030110342c81079540404600c11580c086450900203402120255000c00c4241c50a940410101c0d000d1800d080b04048540206c080740c00c00c40e051035100307031001d60501040219078080840d4804125030941841ca903640d4820340c0c1100c4c11018100000e40c80b43c070707140012074404081c003007603030542e4814201003101b28107480125580b031a106211500690020100398441c828a401458002140403050f01c0940002200010402c2c80d941200240034401c1f03c811008aa25001c0c812403601c0170a000c0241000b6040c000f13449410000d05030308540300000d084020404258040c0300210b070001c940c40e28079612140d00d1009400140c1d416070010303040001241000d8010b00c01c1c048007000040003c000145408019406805002c4860b0107010040c00900500044141c0c031814551084 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 48295192 1250 48293942 48293963
    0xf03050607180f060804060207050609030c070b04050303032a0c01020a091509060503070e040f0f0c1803020d03140712030c050723010b100906020c040506030c100e0607 74
    0x1508001e0504411004401d01c64405000401c440c1920003c9481034882034504185150340328205480079104018004242d8401c04040000200010020701400038461003a0b0b0003181d6140b800700315601803070107107540c550030400200d980c4040d5148684800280400c0481c4e0049495807510616082801442866500002da10b102c8991150980c400b8100c0599024026410300800502c510b8542c0140c4050010020102d0000c0d0f0044080784044903004105000036000296240050b000c0049a500660704101c0951501400303107010b260380d003100c0034a90440c1c602c0d5800300180000c46807811b03401d01c402c82e075010211487d000010000c160080b850088612500e600090480e0000d824a0080002c04e00c006000101c81c00945c4407528100c500c00e10340c01c561000640d0040183c040900d502c03800101c0a44181c5800c074500b00c1c11144160281d8040b00c0c00c0340f00744801d941080780c0284d817580185400000e1403500c00070f4202ca003000c51403e80c070500025004100194003030041501c60740500c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 48296442 1250 48295192 48295201
    0x70303110705031204030e04110403020916020d030f0b060a0c0203060606031308031008070e0f090601030f0305070c0302040e010b03011b050301031e060501090b090603120405040c090f030506 84
    0x580200c03112990340d92045460064980c03100c81d1680280b4401c4951500b49001140905102d42d103034402c1910b004104200c140c408103c500c04030f6106120482c01406003000007440801652030909006006402410442c0c4584004030000c2c0700d241c6a003854a81e89260b80039468a80c2e0f030180000100c0d684980307180300001e0041502d408001068140305890400030441c07030f1085421100c0320994055140c41e00d030b440304601600340000300d80001c20644200e5074005000706041202e140a20ba00c94000c1d156600c40490154841c0703000d00010b081c4201110016002030b03c244d009006544c052800002400e46950004054a030351000100e8240e4440700380b054a45421300c00c13404803501d0040c80c144c00c60415480585a4041480054000341c40d0f1403e01e902c600540d500e0b5400160701120412807580c4461303150005140c1301030f10754019074403200064918100019268140034582203503c1c1080d240c103003008041c0020445d550100b2103042d1000480300c940800c034501171441440600b086140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 48297692 1250 48296442 48296447
    0x3070e010314040201050d09150905010207150e0d050a1707020f010612151503050609030a030b0102030c060a050612011b081f0b0304060b190501020d051e180a0603020703 75
    0x1140182c0303224a250a0b07091100613a0030404458401c42c0550340411022680d04001305001c00d0740499200b4036052402c81410800107500405090340b191107120104503c2e03221000864203580b0401c4010344c0f03d41c03000000103003d0380207003400c18003500d403e40c02c0c2c0500042c4051100710507a04040581c0c40b021518010b803030f0a010710f00241005958414080c0c1094885032030100c9200e8602c441241c1c0e0350300703400411034840103200181d034005007200c03045d042c50781c0250791f131744e11140f00500013a14101420041d0340c400710842c0c0c2c045450b14001c0c010364a4007401c1d800104405840d40c0d070300c00303010400c01c8000c810a019501d200c11820a0001d03021103c11400340080000421071302a21140c4100c03842120007011040c1e05a48501c20959120b565500c2d180300101104506268800c1c00e10780c254428500c0c14152000f65542030782541c03031100d00600c0981c2c8a00a00b4805900440402c1001507004816006030031205148003000500049070350110700c01580c84d0304440006900060760005068 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 48298942 1250 48297692 48297701
    0x19030302060705090a050f04111b070905060f01030f0e120403170c03070b0a150305061602030a17060f04020a0503161716030906050a020703030f060305060c0a09080303070e0103 78
    0x5003181007070313840c0140400001c1d90704116070140034801d1404070303020340054a859121100082c030045800d6501e040c2001070a002d01c40b507418491840c40f4903907010540c10b00c1801501d00406019001f500d60b074201c9070055000d400c080340341000550b518220320006107000c00000441e00d0a10001c1555035085040440104030b1800464038408001c20014440b03034000030031034000c2500840846c4040d02c485860034050f0106c54249024000b4000380402880030200d0340c18000c01800304122082c00301a00266224010141d21801164103407010040e046070f100c4036164081c00003050171444451142c0045c04a810101c603140015030040100b00f8111804a5020582100c500703068403401680d103100110050002c1071702c84941d6400881c000450301a400190700c440e8803100a12031460041501e10086d04030030401e8001a0602180340070392403941c410303401541d0700000a41110b680c1d4034481156517100f00243d1303042040160300000c503000c5c213001440c000e0a103035403504600aa9100018242c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 48300192 1250 48298942 48298951
    0x60e12010b0603010b0706140406060504051302060d0c140c0d0801060207080d111e060901060902030103080909091906140f15040e07090e01091703070804031404051903030206 77
    0x260700d41552000381d90340e0602a2411555040d651543c0d8040615000024005c02401110080200d0091000304a41e0b5004070040d20340c2550108800c2d56a0141c03802a0305100c0742c0a50000d2041208201c6407006810001c13850b01e41d4240040320101050b00e01003141d01c1340e045d032a1641c020b40d020841081e0f10900d6540140103900c014405e007414040c403161100074a001c00e800f0b21040c1040e001c0c21050502248450002e1394007506200c3d40310305240ca88440041b90240d205510b440004100484030303100752030507640c0010416007401d02d0f44042c01080100a0440c15407441111a04415140101d02d024441441500e010522080c1a100800400009098170b5003034220101000180e00f0f0a0b00b8200c0711110403540032a02d140d40b40b9210341000c0e0540c02880075107040500e004000c1c4015000b2503d003610400c40410410102040344032140015a01440090f00c5003000c1400300c2e20540f80000c0704481c1c0054240307403d9489000494060102c00785968800740a00700f00b040c103805000040c0d01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 48301442 1250 48300192 48300229
    0x70804050301181703040c050d0302060403030612030212070204150801060f090b1c020f10180b0a08010306050403090504050702011d0714060304080c030406020f010e010213170109020a060e 83
    0x104411907440f08001c03118280384e00a480000b10004090003014a903040061202074070200700c14100c0d040003034640c9000c49041d00400d0401c040010411502000d42c0300c200d42542c058401d07694102140322466005a40580c1d0068171600e20081001c06120341400030410f08000240d42d5107130510040841080da40200e410340d1400c0030740d481ca0345859030a5400140e100e546104100003e20000e80c0d00c0c0003640200d508810103004560141d0382100343d0080e05030032001580300361903132410b40118034400c5c0f4031400000348000b0010400656290805c0d40c0041c441d05020704102d0f15107002c10704841c0304441c1c2d600180e455042c010b401d4001c240c80c0186000f0110050146182005800307060358031044070075401400300000040600812100355525582030b08280d0b69582d585441c025079803146840017240c29480c08100c201c0c100c00520854002c5598000c1c3c4181302c40c900a5034081c40207a002c0b06031a255210a03040700140e5803404000d01030300c03094940d4207400116034144442c060300c1c84500f554 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 48302692 1250 48301442 48301481
    0x70515042904051201060e100509150d170403050a031d0904020603011203120903020f0d05070c090203040302030706050a150b030f04080304020d050d02030a170f0606091203070804050301 82
    0x9200c08210111403d64405a60485103d20422281c600400042d48804030039030290040c01798072080e09004408444040340c04951944800f040004040c001e260119804028000843d001440000d1031120020300a055030741081e0b41c1c0d4640a0400d8445802240042d250601c4464070311000c5003140401c4038159020005840d1681c0070650912041c0607003945050586540380805100c3c080c02c4d01a11444602441010f51900c3c02035030700c8014122001450040381c4290341c0103072055050303420150308078900b40c100711300d0255100020b51000e0015070450104018507401315085001d06030040d00401d400140c00c240320b041a02494910345c0008207040e80401c18400741c90701c442c8519130056080503020350b4030349851000030160340c0c010000034054020782080c6140c031500400600214419915401c4141044041400f012501241c00502c10302080000c2a540d05120019021008029200725035900720b000805107950081c03a070854801e01e0019040c0a00e081c20702845050303c0d4074155640 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 48303942 1250 48302692 48302759
    0x10e090a03030506062703010c0c0b070305040c09051e0a0204061707050c0708030702030c060a0c0b061216080f0105060604030312021306050a0801080d0e090907051504 74
    0x94480038a440054201600d440c00304626654607812074028044110040c142681c0c60000460807507541450107119500c0c2503e84000036000b510340c01e040307a52200941081d40e441400a4009000150044d249001d2046020a0100e40b520400b07000c5d54030101c95460540e1640815109003000400da0600b280c0180000c000c0250001e849000401d0070f00b1650b0781c5641c030b51004465a002c3d58078a42c24520441100090340c01000c00140381c464000e400f44c030580d0b85010700744487d07031140c1b00c90640069210700741d074001f2903040740525030800001000c500300ca0404c038080394689580c041000d8440d5804400070000e10004201054038400703e48001e20541c908000020100d002e68030010702442000300750020606560f0303044408003115802500545602d5560052140c1c00c030300700e03001c00320781c0070000890300c4000020404c0348103500c2d40e94155a1168141406804c500c0540405454800e011000c5030030b40c2e9002440c508808c2d00182d0907221171800384040b03565105000c00385010366000c503029 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 48305192 1250 48303942 48303961
    0x20309120f040b09120115080c040603020a050402030a0b100e030c0406030b061203070b010e06281a090a060c0308010f060203180f040507050417030c0a060903090803041d010e 77
    0x12000c444001e070f0f40035242c01002c0f0105513159058000d07034409500e414000440256004080d0088d12400811a80c0081b45001840200e500501000c1d500644034007081020b8a07250f0015580a903007a80c0c0820840e5440c0e0128000d94004550900400c4080c4004e4a0904040001480c0300d80100c40a0282503c2c41e1249aa1200083e201c84d00500c0304801c4c00550740001c00440b00c3d884e621444008285d1703981d50001ea59070b04191580303031003a00f00500040343c070b48042480c0b80754071300501c41003d012450b0441814080d5400000301d403d4650074000c210741550380030303800b5008001070380340c01e03500340c00710b180c01003541da8142c0141c80101443c903001c0c0100b5a00000b5101e507810003221044010354070000107404500103d0354140d1203401c0a003040b461a500c00080c000311100d4a54110948180941941d01d9000e0f4164400c0309078052490140450a503801c01d40800d40a4141045001d807620100c0342107a1040d0403200500100301034501e0005081100d6500401c4d4841d00001c44c0d040c011103a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 48306442 1250 48305192 48305197
    0x90408090108040302070e0103050607080601210527010506010e060c0a02060a09090507180512060c070812040b060a050f0306070f0210020a031b030504030507290406020309120f 78
    0x940c1e04000352040040c0c10507008003c43c00c0580081c0d80702101035a51f924016079120011038502e0002101c2c20041412035009084c00529481c1694035030b03c031070a40c801d50303030000e0000824040c002000003240e11240c0705500340c106440e0100100109103450a40005015241e25030700c09030003508104171000d01c81c44003250028800354111007080e911700e1184408c4405082c960402c0c600245480c003400007140d04911202010035070b040180c0e440684d19820400e20400402c030041d01038200f200042c0405195a0040007801d1050f00030070304010f015117000c941c500d41100c0840d130000404042c400c0da40f0709000301000901048508401402d81200403984801010b0800c1c0203101e80700140602040c000d02200d10102100c2404644520b07039054018040c00703a401c0c980029001e880390103c40f40344a405094030594054480030300d4446603951320b1016800c180c0c40c541000707059124400c1c2071819168001d0085010f580090b0f202d04011060303605100c0d000c0b4107a50100402c2017000e41c60700d0030105 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 48307692 1250 48306442 48306457
    0xc08091906141e060301020f16060e07030b04260702100c02031f0e06060d08070302030c03040303030e1504020102060a0b010201110d0903230f07052505010e090408 72
    0x4038012016051500704003601501c2d5071031055186240c108841c600c1800010780360014581c08100282e2501e0081c54201d1081c9852006070300801c22035030450199120003401c020f80318000020389210705a2005080404c6904122084070510041c0802e200d6000d0264544011018141c8219102d40204040300c0c8034400300280a4200c04c0e0005060314001ca40010029030003905688203100021043c1d0205c018180c0d21040b10f520b464041c0010880019034244200e0380075260240701c0c002500c641600340c000e07200450440c4030800c40a0301d040c5060018000452180d100454012404035540d814100070824000c21032403440204400740c0e03800034000c2d030011040c100c00142d402c0c51100407805498500f5410306284c0000030701c0c4840701c00503032080c42070b240a90744004258110365000024940594404030ba215010710580c0030328405200100720303451085040382c031500014080d2880000426059009412210004125550b044008000024001c89610791149061340c0d5600e8680603019 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 48308942 1250 48307692 48307723
    0x8071d0907030b0a03050102030603100204050a050d2307060f020d0e1207030c03050d17010315050717040c0905060a030b0a0c0203070b090105010906060c05101509020c0a05010c0809 80
    0x1012480e094080c2d440200c03c0c0c20050405130031140c0782d0505134040d500a41c1c03118080c5c4501c00d4074040c28000d501c00d8030242c1c0c0009012003901440c20081184005902505442d0102c0c080398504080c0b22006000350720060307240c0a054083c4c03170311501626800080b080d481c1503410091004d201c940d4010441070300203404481e0300c5041e16056982c58985100c54100074000841080048180000001c03001904c042c03d80d1080d0039620508042c4095150a200080c00703580d01c00b0401d104003100c0c0d003046030301c4080c43c5003610181c08464400c000320f00c0180d5082d02d840700055000d1200e03003903501500341d00c40d4043d00d076038046030325558840b054808000c200304680782d83d501d91031400500c00d20448484c15040700008009003842ca0b0218001c00080c421001135030f1624800041c06400303045120102074116000d024400d2040c007961b400350003106104c031071340011250301040d445032620141404441290041110401d586416400c40304140d980b44140300312881003001044001445044440c40030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 48310192 1250 48308942 48308959
    0xf060f0d150803040605030a060801020a0801060c050a0c0b070201120b06040303141905030a0e0a02010816030608030f070507080c0609060703050f071a0a0b0625060213050108071d 79
    0x701c41129807003403540c01586207400001800144154802c02460051140fa0401c011441e0303950780c560300300e100300e03140c10000c122050010800396024449403043e141c06902520b000410580c1c4020102c0501c0c0c0043c55080d2020030300400b5540c0c07011080c040c01c0720100d02000580c10541c0004c145006e144001020000c240d440c0d41c0100c1c5607101070b103459050400c6003215100d603064014203141c00071207105100c603142030425038504000060b00424590180c4a00d0b4043d03c030b40c020080305049615100c0203058540d2000140c50f4001c00043c005280003100b2107445d24282d00c2c0c0b0700d080090710742c0700c42e40c1c9a105144a00e050f50303405044500803182101c903d42d4451040c0b0b03060329240a4101c8042d400f610100d600703c00d100000b0700d0040c0703501c0c40801c0000300755a20021041102d1200c1c1ca4250400000e1040c1120128404851114010821001490558260384041c2aa40580080180b000b4104420003003560400c02d171235004041820960380c407132940182d1800118800f8400c6214070400c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 48311442 1250 48310192 48310211
    0x30608061501050c0105070504030510110a1d090106021f1b0503041403030a140601170f09030412080a090608070c0b10050d030305100b04031a0c12040507050f060f0d 73
    0x10411213040c03402140081c0154500368602a00130f41203488107541c140108206808074030258496a024003c09610840c1081c03540740084074800c0a0003d84e07428a0342d029810300c41a030700e6140003402007407540d000b052106024000290000f030603004400003181010440040000d022012105d41c45079490035944136a1542405038103e40301004031181d60000000f4800203807040e80020807035084540300141d080d1a000d0045a9107407003840881000d100c2c00d030100780003050b44240c0b950815001800c80f402c1545441c0c0c4105400121305d0100d4403080000b407001c9080d5004202c000c020003550500080314501090050b0511400c100000c2504250b40001201c071200422101e01628000d064500c02900c07921b009001004180d84510a450304684000749010445044806680c3e000b03c0c00c0444100004085c801200301a043d2840d608081c80949045504c03c000c083c071441c0600000c1880031715040500000c6c03400803001ea4086d0b041008207000c1090b402048450040300300300c002841000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 48312692 1250 48311442 48311447
    0x90f020906010207051806180603060718050604090902030c0306130b2802030a0f0203010506040501030e01021204050303040b220f020f0909010204090f0b030d0c0c181407030608061501 81
    0x111070704241d40c4500c01d841c0128846d0701010141d4800c05043da040c00204126580d101c03074421080f0b500c0b43d0702d03612030000142051301c140c0310705440c014214581c00c0d40d6511340e400a1103c0e08150003048410750340345901d405511f0308001503802450103038082c2c45e40d402c01c45040700708003210b540042c03c44458480400c0449200c0400b200360404544c1408503004240c0d140c10004e92300a44902c0180ca043c08122207200700c0a208481c12030300020012883d1501d03000054001e4400e80e8400761003550700344004000e400c900c04501d4072580c45800075690741c0c5410b2030010181080a45851082c4412101400800104090721164160055000d000241580c0300050f0104421700c2e0b0150011641c20030703c01d060805402410507100424028000164000300303801c22105040e040c6503269100c42498905980292000e0040c5801900803901a0307032580c0e40040e0319601c8014980c501fa5460341c0c800030501c0000001e6822455628084c1700d200d20345402c01e0340d920800b800c55400b4581a15000038103030f0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 48313942 1250 48312692 48312703
    0x1a0304080f03070f02010b03070e01090c0e0319020112090803010b090f030a0506061002030c0a03030203060d0606060c03031a030a080a03090f0c080d0903080a0311041205100609090f0209060102 85
    0x80c40c0c10344982d680c0c5000d50005000c10200c0d80342001541c20080c041fa810f18010401900f503900d120b2a0082e560320f400c01c6500035000303103c01d15003480700c0d4080c0d0bc159130b1000e20001c0010310055400c62400c00c0a4400100184005540c0003030b618a07000350b50001070a140708890446da2140441520344100000051401c00c0d003c040503450311070707404c400342008002f04140f44524022940003054103845842071b07803244901030000400d500701d19103074030001340a9030180da0030190180c042980b40c46d041e6100000c54419402c03600108011170a80f0b010140c0c50b006ea0004a0900e8194910030b00ca04c10109643d00c0d5240002042c004000c00c100741d015100b039003c08000c5800c841c100d00c0b030300a00d04150300003403014010340610b030060035501218a80500e00c500101c030340c010f0300740d86815607400080b4001e06039144281200d0108001c00200c3d0f0004c0c4513640d110304d018070081c0200c503140c00f10450446100d5441030411a00301004040444c0d40e4905403000a601529080788964135040104d0910 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 48315192 1250 48313942 48313957
    0x40503060a050906060d020d0b101206060e070908030a11030f04030c030c05040e07060305062106070e011e0302090a080102040e010905090601030c0b0a030e03270a1a030408 76
    0x188520400c01111104641049019083c10000c0d200a9200d00d410b000b04001c0e2100d001e50400340b00c210a00c0013907100b100c0320303921001421050071210745902594020840c1d900d020f9070401e803a1038060143d5101b40111a400c2103c0303003070480fa194508a5119103e00400c040301042c80341d2000900c5040d00c2c02e1007103441c1c2401c4841800e56603a2289030411000000340000d9415030041c450104150416100b48405c00240d0710040104610b400412006484010f01d210b400089014052169420907511195000c01d0900501840e2400020090002404240031410030071850204940d5406451090b03941010038680980e8075a604004603a8845195020490642c070000300003c10140442003241a103a0129040c005034440f01c444550303a807401e010281502d000200100950394094000301445000e0341000301d0001c2c4011310040c1180c104400e1650400c1d400c55000a40711040d04002c613075401c08803411f9035814107003a1a40010083c107a814641c803c4008003040a021b41c40c402c1c0d0700700 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 48316442 1250 48315192 48315199
    0x705040f140606030424020705010f020a030c020c01080115030605030a1103120301140904110306090105011502011a0907050706050907030201080c03040b06060a032009090702061501030f020405 85
    0x8480c2518028001099021403407401108803101156640c640041242d00841e0005400c030300804001e500205595211039011228560030801c00300051401c0c091100c843c40e5107480161078201c806000340aa9207001c992508640102031010740503a0004001c5055600e101a5504003084084d01074004182c20b400140e80b44c4170303141000c0100040e4940300307100d548040e0141d40e60350918030000b00c6140400c0c080d5000c4043c41c845402d07002c2c20a0860654840e018011000c1080c081c00003007414084107a9043c60141d4503240144500c00409520405403000740c0f00810903c0e01d503c1403048a1210441c0c00b92045480c4000704000700d1003030f015551320703d03040f10007000141050000c480d0f840c492031004074081036008000842c0c07141c41c44162441280c000008040360350701c420800c42c4903841941441d0a055543c2c1d00c41600300707009800442001d40c40e00349160764100c03c408001041000922410441d031201f8100070405906004500e0368580a00740452199140e41000d0702038003441c1c01c034641 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 48317692 1250 48316442 48316451
    0x321191b030510050a1217070507050f130905010903030b030c060405090402060408030f0a02010c0309110f0a0f0801090209060a060f05030402030307120201020315010e0a06080604020c0f06040b01121a0405070504 93
    0x400700c001a00401c0c08511412409000500c1807c2607440c9004000002d8596004140100068245841d0b68080c0302001010410110302d0301c0c280c101110310000050310345e82c3d503844c00d58003016010310032a170214100b1401000f00c1e40c0c035100003c5951040780121400b40524001183c02c40d00d40d241901c01400c151402d9a844240b00301140400307400803950500158241000f40c510f040c02445008034280e000103503610301c1d01c00801402031201104042542250701c2034400a003528042c2c4605010302044000441c4024041c01000580500505100c0c460391217494104002500310300c1010181005082054403560349000013810b5000c0c1c904040d00b40041c55078980005541940210b00c201c06d90504c80200303180c10001100c111100b0004a0b8009507454070910000380a04002640080010009450100c417030407110b04011408503801025841541823208128040030a41e000d0030716152070010050b21130700c0300b0b100c0b010060043c0310060705141c04541400010b000d041c014000241081c00b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 48318942 1250 48317692 48317699
    0x6070819090506030c07060c0905040c1809060b0301061124041208040803060d05010e01060605090915030604061107050a050d02011a03060c0c0321191b030510050a 72
    0x1550380c4004a80390018012141c04038062600b0f406aa004554984031181480301c2940d8000090a59070b0306001803082000e0300041b10f582d140240038a202d001d0b078543c0107007840d4802c506041812904403444c520700b044420b1140d040e001c0142d0341183c0c810300e02401030000d102c1c0f0043c2000180c0403801c00000909041c01408241c80340c4c902d0040b4801d507090312000072102d0381100c42c0001560001c002c5c007401c2011840c0743c40c14a2404164601a0000203010885000d81a0840e0480e5125501161020031340b02114074140103d00d501c4006035856440285081c2c0c0020740302c2c8001400106055038070544021000c1c03040381555452617100045980002150900594410781d840e0410015802d117001016a030b00031603401c034070582d8050018041503d03900f0528031541c203e0300c7e4001052000b03103c0c1c180c0340d4001c20890520f140b141300300c3d512682072400070491401c0d440440d2203401d50410500040c8080d5007401007202036901d16000503691075002c42104104020742c46075074000500382020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 48320192 1250 48318942 48318967
    0xc0609011b0c08070509010503010921020c09011e0605040b040b0f070203010e150702010c021c0315060503040204180b06091801020417010e0a030210020c030904020406110c040b0f0d02060708 84
    0x18003a154101d42d07404c40747c0e136a9010503090740d0107082c0080c0742c0302c0c2c480200c41d00c0c0302890484401c6004140184c03034010013000e01040003440240e00c80d50300b0194442225452401c410340364800307441d45140032407805040100070001440340b84160034071070788009080c4140d08844004e41d00c29550043c006d0140b507520310309043d50340900440c01c4641405445c00710341e0b135500511440c50441c00341d8015021641c1e068910758080a400700340e2109150719144641c11408241091030050602174441d907440c2d060034018031080321545d4038401040200c1c048000045141400003a500180803a01e002da035503519041540c1203d48a000d801403507002081c00300720010301c19021080c07410100f008002c40d103148440d85a4500c0121009405600300300c04032b96842c0580c0c0c0040600c035080343d04880c41e00c48924003190883c1d110784c0c010340004160031782c0e07029031240501c1001c0846808a070144000d010600c0041c244044594421303214100810015045450b9601500e14a94211a0b01c50f02e50002c0c4151 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 48321442 1250 48320192 48320203
    0x16170d060b03060414130f2108040c0e01060e12010f020c0c01030e03090f1201021608030406150b0405010507020109030609080301150201061508150d080a020f0c0609011b0c08 77
    0xd00e8801c5040021204080030400f458920400c140d000c640742c00245501d41070110009020190740c002c81e003c01b1000c03074280300004056044031559803400305240134107010be040d050301c1e0049003010707c03d0001000443d0340980500c02c6850201c503c5500d1500048403c0d004100e002402031b1034500220307980348001d0002c0b6004642d1a07080c0c80604c04070041c5072103252a4803401c0c1d045a032144010307026a045040241c10040703d40d8016000514040c0d6000c0c5815020a2180c0d007141c1307440c8008100000c020a074094400d29840034042c0000a41c00c015241c400380c00745c0d0190b241080070214180e01561720803104071340159001202000012024103214656500034050f2500501c044800c0c40202d5105202d40e4044803400c0700c50b1012000d204e10119040c000241442c001c102e0640c1002c9502d5551214481000d8403030980c986d81d402c0c02440c06420a00303001c49400c415044400e605d00341d500d82c28101e44080409280c104411480004410381001400e0f10107800d980011001040b01d00d00000c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 48322692 1250 48321442 48321451
    0xa050a080405041d0d030b1206090106061202031005132301090b060711040b06040302060a08060901050418021005190302040303230d15120606090506030316170d060b03 74
    0x3000d1007404005480c013448140b40e146444001c1d8029400385aa40b4800d6103e00b5032040300420404400c404140b44514222050383d04c82c0240c1d64031070080024030b8000110142c04112118154118502450300d010414010b1198034000d41111586086420302a4001a25000309514907030107694002d0030115210024000c0c001c0ca20b00c2e0901944281c54601d05580e074840d40301d40340300c582c5076001c0240030181c214072070706c1078000d0810700022005995901c0540b500343e903643d561000c20700d40102003048000040e0301c118025464486000b0081c06103045000b070f0b01e80c0540e4a10001500224104c940e4403d8031640c103400c0f5a1810980c2480d907242d00203100b04da01075611080748a144144a41c803040b82144103800c401002c1000700440003030b50b0081d10310141c4c4440e0021419545003003070b208044410900f115100e13607424061082032010301c200e54011205500450401a03403c0c403510840e25620005081141c1d0320084540010001080b00c841c0380c2c1905041c041c01d9640c0c406890190015038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 48323942 1250 48322692 48322699
    0x1150305060412090f090209010203040905150f10050f03060604030b0108150106050a050412030207030b15030f07121b0506160302060601020604050309100302070b01030b16050c0c120a050a080405 86
    0xf20b03007028180c420b15000c8261403c0e403c400307080a15144041c0020340c05220820b065000600000074241440c0c070665209518421002010310300d0403007004690f03000c1080c000c1c03040c000810342c07106047d03204c02a00c601000840d00ba0382e032074980b80001000f1380a5588006d059070714402c00031852030400300340404400701c4c44039a01030300e03600c42030700390303a51f0085a0107200003c81c00d1000b00324044126031032050560003401580c0da22502c079215016040c0044907004112600c0358145101070908110200d18900903c015155103800c12000c8001441040c1d0043c10481d01400420000b40d840300034100140001018280c0c1c559699240007418480781030103802500901e4005803682d4000b1070003030311559003c0c000d186009450b600b00580d00521101030300400d9800d120140c000b5449001072400307503016070001040c500c0c0558050030303c0212410394108004081c40180c402d031000003040048443e04603140c418100ca888000d40c45c00200c4640076185200d910384c000c05000c803c0c4000e105450003034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 48325192 1250 48323942 48323963
    0x30206031008100516080705071515080304050f010503100f030303050402040507080601201f09050601050604030f150b060d0c02011506051b0309030708010c0f09140909011503050604 80
    0x7411200896004546903a9020003503005c64802c240316503580ea80c40600c506040e070034161141c85002100500d4a1086241655040416a0140c10b080a0402401240b009624190030400450b950422503614a41404004004544103882601060000d844058480004e06a81b400c005002d44010b54050b4005d5180c0301c045110103105d106268801c52040c0c4500700e1306400820004a40e980340304101a03203001d50441a468a4803080300500e9010f211100840c00030b20703509001e4104101039020314440c1500300002c0000079030a42d19a00c0847d00110b10054104040c010300002d000070002095101c0c02c0062425a50102a4071402400c0f006030b008100501404810500c000030a0103000080303081844921056011081d03000c928111032001c0d2418019103d001c28500301441d00682c4869450b0382030b510840e9482a40c210b8100024500203102d60b00d0b02c469860a0b420f0a081240590044000210303100000d4000c00000c5101a03014448681c2e2400c110340c491300c0513242125501100c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 48326442 1250 48325192 48325213
    0x20a0803161b0501081801020c010624050a0c0f0c18050f06010504060c20030624030c010507120903210e04020306030d180e070306080c1f1404030206031008 69
    0x149242ca4040d01c070180c440b00c01c03a0b11003208500081c210501e10184030341d004c2140c521640c0080c06200300600f5403110b8040d003414400280c1421281ca070b0790350010000300b0f00c54040100e40c441e00398112583c2003185034805030894201a149181c458014400078501403500302c0c0d5080d125486079108000601c0d09084980f0341c0f60044030380c2c0c0724511442c00090802d21500001c82c0eaa42200c52481d101e8660b420b424529940c0440d0400c041140c502400e1844000c0c030614600c40c0c401c41d400b18180440283c2904494a40083c040303024842001e00306100c41d2003404061030041c95580065600a002d441903114a04c0c0304074948035600312800002210603841046c40c2c1418000d40380200c0c402000307041c2d05444120200c80440700c0001c0032500d1000203d0020700089044042800b079140d07130f6004522141880304452030100e035411418081c0f100c0050040304800b030102e1101c00103560340341c484001602c42c0d410821500441d00b021754032910000c00d00410085900400007240c01c550103440406a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 48327692 1250 48326442 48326483
    0x201080903071205092e1101020702120c010206090f0604140f01090503040510020109021e0307031a0406180c0303080c0c03040f09050708010b03040b060409050d020a030210150b07020a080316 84
    0x102d0008034039020700c0d01e10901e142c240c040e14400c261f002c84400014100111600090280d000c00980d4a51603041400c500303c0380e50f4140410f9920010190080401400c8141360903501e5400400150120880e00301504505505008041c82c0000000092228100d5400d00c16201c3c0d01c04d1040300c0c0b05140381581c45e0034440c018054880b1071500142600c80f19001d07000d00b608080c07a11410f03150305001e0300201100142c44241c201c0008440d00204003010324251a05a04488281005010810b10b1a110000040040681c007081da075051804071034036123032850007010318011512004901e000101d00444c0b100032110001084802c0d8000074000d0307031035288003660450020b014010310b244007000000e0108640c621055007080c0d01030300c0010300050580780d007030502c40410951001a005605900c060680c100900500012419030070040b001200300358400d4050644244007542c040802d9a40640d580c030b00c0004010211003055030703610b00500c8120390b00810480740c04c039031603000c04182e4004a031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 48328942 1250 48327692 48327739
    0x30902191502120d1104030203070311040c080f060f04180b090d05090a1406041a0a020c1903030e0d0b09030d050a0605090a02031f080d021005040b0103020108090307120509 76
    0x8680701c44207132070148100c01d00c4c40500100b85c00381070b59a10030080000140c4080000c40000c0d030040043d0f03650001c0e007404000c01e440b503010340c84040081b2902071005a808140070719401c5441180e2140b0791142d1131020074090514280c40c6a0034a15084884081c000d461218602c0b80d0030700f4080c1d5018101c00c0000395001d0165090720fa801c580d101000703010794009280da003c05200010020f43c20540d0315142d1440c4419484121a00c00c0340114660280e00d8042081c81c2d18160212107603000c8440e081140343c044001032001404128001c04100c10a03140e040c1710719100d640040d0030301d09614014050b2a5254004007251010031b103001c000543c203900c03510644044d220020082d035641c0e00d418034590b029400141c191150303181d4110210240d41c40e6140401c004144843c01742c284500f10103000780c01c00100d200224070145c03c10b4100000070f4050700496040d2542400c1c000100d85900401034510f000348000106002d0806101441d410b4100c4058400d18104a81c600e0784009080c40058050 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 48330192 1250 48328942 48328963
    0x608030a0e0d1e06060909110102010b0306011809032601030507080307020d060518011514040b030604020411130f031103010c1211070605040803040b0108060c0316030902191502 78
    0x34540c2000c41c1035510388091200801c14055032000c11165106c0441070211070402c001202d00c1d0048800c2d5003800e503028001d01d03807111400c80107446158074012000183e024a040300c14201983c0303201c402c0805010b078020300e6400e005401030b000b05c000486014a0642000e01054406100319400065040d00010031521200d80c0074212985d03d0500750f5448028100c060055200003103100362442030400c007441121007820142e02904102c82c5441800041348030045500f900850500890401a490020380140c2150b810354002132009107000f402c0b261030103004055400510325100000d40071f80c8001c092000c3e640500d0085030b0f00340d20001054200c45081e1400030104490028403100075a2691102c00c081707140900c2985015915620401100c8045400302c982e0303c80402400240300b070100b80c9601524103100204554200f07001c16102c01d002c010031800326044100c143c1d40b40343d031103a0803581426a010f003000071020100d01c85802c4038020b07070041000030030070030707103603c444030320000304800c03607 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 48331442 1250 48330192 48330203
    0x30301060c08090a1e0905070e0f1e0603040b06040c030207050607030b010908010f0e0601121a04060906060e0a11031e0405070e0702030406021504030503010620010608030a0e0d 78
    0x840103681d03103014090b046007903c0c0360301c0342c0c00003000030300f00720062040165521080d150b58050742c14940990203e07200038001104101c042c1a100e5071a48075015140c0d00540100c0b01e507010000201040b601081110301c03a08d401c407102200b40010003045079003450007904100e9050000c180b420f4030803000ca006a15020300143e20000118043c640658440a54010b061610035455a01c619586082d60f041d00003030031406075200d4041c1c5e07688401384107241c003400f40c40700c0c1486085100d0300c650003081250b00b1000f0840e0320340b03000f01c2c04004080c6c0c03104640341d070b01003014050345075504044c0c10003601c1284e5800c0040d00309414000b60810346c40860b8846d00403020400303a402c28680f42e25280d00d0005008403480c0c4a0184041140b400c0b04005520458899004550ba00e08001d0028140b020080991355180c0040090000194002040d03030b06486161905144d048488650001144103c1c03801d00980e501e4141d002c0340703031400407004048010b00c50700c46c00380412a04050001c184003110001e4034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 48332692 1250 48331442 48331457
    0x309090a0b010c060e0a0209010f0501080103080c0a0516030506060d12030b030a02060d0506011101060b0d0e150403090617130803071e020606040501090b1e060f040b0304021203030106 81
    0x51a036592128480c06810303d00038020300e14a9440f401140c040b034030740d00011b40c03086000c14218034041c84500c3c05030007442d843c036901a1828002805080c418003004110240109010f240e50000300a640c40e02500074084031840b010321280405540c0c4a400281c4c0d00340200070001790b007810510a28540150b0281b0784100440c201c51003100207086c3c1685d100c0d494024011108051f0790b0b0307140a0400b405002d500080e80d420a01c0025281b01d502e0a40f40402c4e0341800f10130040c2c00c0e680c405941c0c0e0514464000320b500c50200305034600740305003492106680d501b4001030005050740060920142d0f0320b907807a050881e0b50440c00c03900108804072340d4100510301000484000484040182d0780080c464100000030000712890040c080c400b1000e0300b00142c0c00141003003403515160181d5801031051203c20071040040780c003c1381d040000c4c40c841403988421000f4041058403900216045040344500c243e0b00c6503203c52808006a105031000c0e8410360444070a01040c52010046904030742440e2110780b03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 48333942 1250 48332692 48332701
    0xc0a02010503060301090605010902030907050907050d0b0f0904030206070323061e1f0e090601230c0f01020714030405031b03010b04050108010509060702070f06080c0d0e0a050d02030909 82
    0x1540750340001e0031150507540ba00003010003d001801250702802c0321520150712490320b09051454a4079130381c070882c851241e420038030031100d8001e0122029403c0403040071850100c5200481c02042e01c1c8005a604551840c003003000f0300d580030401a004040e182d4003400426180c2136095036281015242410100010007c02c040c0c1c541442d0340180c84c1c00d0020707074081109014000a4202d0741c2707030301c00303204480c01c081020650a500c03d0303540b0900402200c4260305400d040000918840c1ca0031100b400c425001c040d001d0034880c03034a042e40e80c2e89900d070040360a40010004068080d412101c808c54100483d900980100c00707002c025079083d644050010856241541190288401c1c40e095454040d541c030303042c0035015225401458040c2c2165030021809003040c1d03211500c0c015001b842d4408541000d107040c02031500c0300101c04c0444030245091255a103840a074802a486400e00c6804a030b85070820401e80780b0804602c0030700a500a00071341b06294075103213050b61030380714a00803254030010240024 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 48335192 1250 48333942 48333947
    0x80711100c0c080726010615120b06040b03010905091006080706020c0901030302150a06050402030403080105010e10020607050a20150709060806100513061110021204060e0f0304030303060611030c0a0201 89
    0x119100203509002240c0c0703e1380c81c081d401e10341800d4001c0c0c40016110343c100041800c654000c00032b4060086c1d900524192501805400354001806450301441e1102e0220750b10303201c100510610720003c00010000195142e92241d9550200c4c4161000f40c000c00a40c40118940501414101d94241e006400d500000c110702d810b110304002d2882c9010f85d0b0342d51000c40ca0361074610180d44546d109860307120f00303541450f0000d0203440da0000598414034900100544540c2c2c0480e4580d0000d040e030425130b071180e100360425568800e181e4242e0150000140355040a10310010340100c160036201421079142d102c00a00701c43c100b55a0040a02250100e0040750f05400c1441c1e42a400c140507140540c00c150fa040d82440c0500b6140d0f02840c0068000000e600c82d01c2c100784180c0149480d259421450b180f21280c2071300042c0401407011703007601d036a00181082e03600140084c4070022000c80c20789550f60340740d140c081c006050900400000035007110125568040010881c0d5126010b20028442410141e004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 48336442 1250 48335192 48335249
    0xe0411030f10080109080915090307030b070e03010203130303050726130506070c060b0102160509040f0c0e0a05060121050c160305090301110301060c080711100c0c0807 74
    0xe0904600002c0c0000070184028400d8a82d900d1050f6015035452030000c3c200120a00e06644516690004010442541e07400144140171a9032103480522a13580c4d007001075440c096494002038241d4000001c004400110044090185209407010011038940c0765045031499010300b604452580e04031003202c0c000d02e8407400d150b07200794403106980f5070140d182e8030302e07041c04000d503417003000301d2102c0a072102082018050a08446401c0c402484214840c8403030a40074443c034800e0a0140d03011801090903c046040204a071030b0308000c0781803400382e6403804407182207021905030200621300400b0681d50b620600240520b0412600310f901c00a500281c14402004040c144168038401044540d2032034240c0400003621a0103038940d107403140e0f04130091600395020880e602e8441102000107210b03040d04070300e894001030341002001b500c805103441c1200c504081103014070f9100b48100302016010b580080c0307078160b141c8142840c1e1007c507030320801680e5404041c010200b4494000202c44030261201b1030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 48337692 1250 48336442 48336451
    0x20603010b09060702040c180b1905130806040515010503010c0c020f12010e070602010f02030106091503060b1602041a030d110106050a260c0f010507060b041103070e0411030f 77
    0x15140740c030404d40e0003e004ca41d281d80044c004645038001d2901c0e04071603c401c400042126901031460032080e001d61005034100031100340706010001c02e0280c030701d010b1000c2c0741c8041c04160040315447e0402d0704010782d580c45510a16084214294004101c03400d060041070014100da4455520944a0741c0c00c110000f5202c0d00b9103600700703003041208848000d003400750300e6107444004050200c0c00c3c00e014000342591445600050f0040c01000104030b001d0f44440c2d0802162148070206615201004086000d06400d031b00c418201c040200701c2005030501c000f010f00303581d8421942000015900b80c1c00516802c1c1e1743c08180d6168000d9541d0380b034500d00448403141464020000099150346070310000b4010741b1150801211030b03e1205d1100c2c9088804e203450000c03020f00314020000920418000f455241d050169581004000718070340302088a075800c0716182070230082080c84080542480c4440e1600115801c40015402104441c840d080034414140700e03480c81c05100385540d0301c0082803030303d0810251 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 48338942 1250 48337692 48337699
    0x13050405040f02100818071a0a12020408011b17070305090705030f06090d11030301030602280e0102071202011d03120c0c01080708010e0a0c090513090b07030207020603010b09 77
    0x114500040c2d88060704d520f0031002c2e40c1c43d000c643d4204101ea0144190500c0c4511040c0c0d84080001e2110070400c06001d00300b91280b10700641d030ba2188071000ca4034107811800100c003050000c140840c01501c10741011104d407800d880c0800d40f94000300d80c1150202d034200d07043d6514114000c00714481e00c1c4203400c032507405040d42e02110381d41317035451003c2441c0800ca040040c509400590500c0a601c200780000d004c1000f051500548035031481c001962a440184001013000d54000f80342074002c00090145468a070301420074050342075032000060414031140250f980140035842c004605010101e0f85400d04075010b070345201d15180210007104070003030659000ca506115030100b4009032048400141900f02a110103800c1c3c0002400000d00344100c090145028800340c1c1c00144009080052907070b9019090700c1c03020a202a4014040d03804c1c0200f50040e1340c01c0084100181000d95041e00440001ca106038003800455541e42802c4080f8000c9083c020b6010004100422010030031030040e1501030b0004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 48340192 1250 48338942 48338963
    0x80910030e1002031902090a15031404082d0a05090301090b07090905010501022415090702010e0c0301020a09030b04030215190c030b030706030e0715080f0702031305040504 76
    0x502a8507040100b007129000c2c6800100300300c5810120b0383e486402852281c0207500b031040740f00001d604103501d40907000c060340320342070000b0440b407007600140b50801d0501c2c0740241d60308290420210541c8140000b806040f0444140e04517480720144480c10700f149200c145080c00c1c030300181102c076039020f90040c5d64591340f2081450080341e070700072550340100200c0d00c40285062030a0124000e0311016841a815504004540a107400303211011a02103092041b605106a5031940d00300f58241c0342100a582000c50041003002c50f5030150303c804d50541d0603108070b8103241e100400301400c0c4e114404840700021005241040000d014842d003d8000d4482c1c01a6441081100501442c2c070744102c410313100d25100300340b8442c40001140b2801e00759071843c0c034082c007003400d01d440403941d2038107503119a004044e40e68140b400e6180e0107120030310240c44521200d14070b201d0075903001844018103840944c0020310440c04204c5590001086504070000340c0b40d4801d900f4907020400008043c002d0041d213451410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 48341442 1250 48340192 48340211
    0x1207020411040e040210140715091203020901030e0a080405010c0507091b030605030c09010b0d02040806090d020106060f090603020a0909020a020706080a020702240708070c14010c08091003 83
    0x781c0140015051036076a40b4030310310340360040254a04004111005002211b00002c1e801404482141d20303aa80003150b0b042c92180561180c1c00621815101802c40c07160380707400144041d419002480c61000990301441014100014030b0b40300c94400e030009111510400c030410155020b000c01c13415150040381501c100a6403110040107841d40741100c180e581c4901a0700d80c0e60550103201c0d000107800c0580003011000844008500c058906011307101c2c121001081e10714070030980f501110040c0c4440000d68517141449520b1a66580b91605000d000d03508003c0b0120b5528454030803070301005200d07130768141c240b0b19001060340250b00032000c0200b0400b0198000c90313004040d000400046005a0080c60800c0ca01080107040780005010001254010043c40c40560f5581c0750b40340c403101c104072540c070b0340290500c1e00354114400c002004001203804240b280600005103007890890700044d40ca4600c003000721004555070040a4801040705009000e00d1009040c080981c140c1c40e1602d05000400c00d20 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 48342692 1250 48341442 48341471
    0x22050705040f0b0310060905030a030e0301110a050319090f0b041b1e0b1303020402030903040504060308030109050a020702090a0905070902040f06030f0e070e070c060c030c080609070212070204 85
    0x4035400c40300d40c010b030000c00d1101c00c50b08117010fa8014500c0d803801e58459401c060000c3d8598101e110080c080007040c10b00a182c0380e80a40c0080d55140d4420515699240d40c0d18014169410848415100c1e869451480c84800c00b2401080c0c41e0603840040c1055500c500d51340c000c4070100182040c2c030500303600804401448a084503c030301030580403521920348400c035840d0044440c031030307003058000682c2840b0008881c044000c040c816254100c0380943c5035542c58501c503203140038540c482c40e0b2003030900900100748960140214103079400504144819030303451401609070302c101030009420400301d400090b0801c00c00c1e48801400b9201b5001c0e0351201da0b40f41c034600c09981054001c0c0b07d40030350b113050800010780c15203d840b040300c1154500b40641003203283c9140d110382844c8110b5408031240000600510300c03415510a5080e400740c020000c000541c6c90040050890f5690f400100b901c200c0420700e146070408030284200c03031590050041c119502400130a60708558022604a9120b000301d8040c0c11 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 48343942 1250 48342692 48342719
    0xc01090e0403020c1e0a18051b032406030703020a1e05031303020a06050405030901020c0102120a1b05010e07090605042a0c080309011a010503040506011e030807031701052205070504 80
    0x1040d607440c400400c0d0f030b5101000823a1806018441c83c01e034280b6103c900d882071001501d601166403542c040e824035681412034a04140045030a6201d0000002c00c0380c260b8242d801790512404681c0c81003a03590115070402c0c2c50800806080c80170880030710000b804011030f250701c0d4103203d102e8810340e40202c8095840c5019180705440c103ea07603400c0460a4407941d40d04200d00b50601d00244005c240014500d59440f0b19072003124204020440b0042521400216107100b541c102680000204401e00258140b191240c1c0e140c0903146807541003640001d820f2034280100440712469120807418401c80c03030405820184014414014050071414550200e4000c0001d14410940e01c0008509413100c104100000c08465814071b06200044c03042c040460780001303150741944c1d40241031116218404010b00c0d01c83e00c480d44010000d20300024420201588032217050107030841050a42c0046c0d888070200301c0318400040249406580b561b1545250a04580003a070b0481c14905005142070f407180d60002818 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 48345192 1250 48343942 48343949
    0x513060905040308090d0c0f11010e0d06060f05060f090d0606050d080903010e06070f0e011205010305011e020a0203090405100906080d0e010206040b060d15020c0c01090e0403020c1e0a 81
    0x6060882000365501e800e000c100300e5003886e407030808000606540c0d13080003a101c0e040d016162501050f0780c0d41c5070380d0161141c101000d10040c00240c15000900c4d007000a45194080c901300302c5802c0d0000207540c10844259007004082850680c2010024814800c030114a04003d540141d1034000000b11500c5810741c0c111018001c100b450380c2c174482c10091609413003490803078010760b5228104010903e584602424800701b00b52400c0310018101400480f903d03e101403404854602c0c0c0301c0000100541580074640f00b50382d105c2d44039001144c100480d0100e00504016030050b8008000d40055071806a00856000518444401140d9110b080b154125030147d000750403180d120b9040e0010403600001490182c2800b44001d003082d140541d107110041c10b02602e40c41c02201848290ba040101c00019004c21030310380001151900c19882c0c640740e42c0c80b044400c260202c0c0c902040400c1030000c3d290204c0c41650183c00400250480c1400e01000703150805d5442a44810303034070011103d66440c0c450400a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 48346442 1250 48345192 48345197
    0x150402060a030b1c03140304020a0e0c0d0c050309010b0a050102060109020d0905030403060203060901090522080d0c08011503091a06010c140304050f0913020111030d090c0f080f060105130609050403 87
    0x40c4d0351602070702c1d403203481500d5950300c1e8040c0304000040c3c2d81c2c60b4810003070340d003001c3c1542ca940d2950b83c1c0d009030500445680a08081c14603000c0140c907640000590f21440c0c45100034040145440180007544000d8098070340103800c820018820003d590f0003c0c59200454800000c0ca8806a00d8a5045400c40d400c1210f09035000000c0c810141b030100c0e03500780900f01d02542008607040c01004080394003041d5600e00108642d290f018414007900009442411007102c000b07100f011010000200420000d020b044000c1d0302041c9802e0145100b403083c110002c3d403000400c04010301740000500f0403500189603e040080d00c203141e40008044048001100c00c509005644031400c0004111480c0141d040701d03805482110204000030080100b0000700319020300f440300034400b080d0851411b6111b104180055141004034510801c4410356001c4220703030305810741e0b64038152203a0b40d4503116001c0310300020050780402c005110520b0720b0000d000c0c5410400100103512503503817400d44217494044400340c1c003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 48347692 1250 48346442 48346489
    0x4020c0f070b0c0d020f03070204050a02160c0906120c0311030304030206040801020d1b0f03150b1b060901060305060106050c01021207020f070b0901050a030207050307020d140d02150402060a030b 86
    0x40310f102041903800c0685140040c4c000ba282c00700055641e800740f42030180c4502e858034049652800e4a80c11520221f0410440d840620a10300b007089046026115039025540782410005900d069075441a0070725500440440380c0c60b2442d00d440340e1010514407580d5050108010000c01a50750400610007414030f01c0c00541c58098240c00801180c02c5002d1070141401e2440c1d0a80d81554484031583c00d40c0b0181c103001590406442074001c4c1d20846030045d880038180028502c2000e01454040c0300c41c054a241241e0140c0d44000f2042d003a200c841c40000d080f9071080c4018041c0c3c50080d005006545003100005040c861201086501e0460603541d19016030454030131800700d070100740070560140401c006464a00600c2c503000070070303500c140c450003004c2560202e0340e142002401c0c03040740d25054004200e09010485410b200c0001e20141809105520590f041080d05c07500100d03170f1302e2904112801a908035a2247c007444030503031091013900304145d510500104103550f00c1e02d882c800b1040c4d4201485 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 48348942 1250 48347692 48347707
    0x313050601060e060a050a030e01060602010207050601090603020a03020603070c062d06060203030c0d14010305010b1f080106110f011416021204031716030c151a04020c0f070b 77
    0x40c14080d040c1c008608001408540e00c4440c0c551030104c681c00705a61138175940da1504480114010406540350300c0d41ca5007800000242c455054010306481030055003035030456640c495000302120340c0784c88025000303501c803101040075140007809540c0c040c0300c0342002445c0201c0d03a80e4280450341c1c203145021a1030040c641d14542c2c145070382c0401c00e075608070000070400c00c0d003880d40281d6680002040400804400101c00c41c4c0312030a50001105540301c3c04180e56035584a160160191400c040351601a05500c155010030030121012042c0342242c5403150b02c44e036406c14a0444854946940040c0d0a220702c60381010703040000d1140c2c112a10200f8202c81c0309040400c1c412a0b41d811100003c4115072150405210098600044404036075028654035182c148900361801240148521190602c007011809018107030450030020318203224034840418241028541e10859500717060b207030051070f042c001180141c1001e034020074807805104200c4445088000c0c010b850f1078502d801c0012500d10104405 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 48350192 1250 48348942 48348953
    0x1215090312240d02010c021912060c02010c02030403030903020405040c0803070c0e090c03070b09150d05010602010f05161101020d0903030e010f09030c12050d050403020a21090e06040609020313 85
    0x1050b440a044881403441c10705034000903ca080c2d14034010784140000c504020b014103011010784028040f10070500190391480c28541c0c001d04448610310302650803c46281c0308207101008807000d5990544403064810700319004e201c0207040080c002ca480c1c1a402c040499509000c0000e454454441c60100d0321550918918101001000d4089100c0c2e51064210031800d580104400c010340c1c0810302e07043d844090200024010500c85802d0114407a40003850707490682c00341c3c000304e040c2d800d580c009000c14286500200c00701c40c4210f41c0030001341e500c4000b000300180316140700080c45c1c028000150030800c00700341000880350049401c5001c02d9482c403a06494400c03e000e500c02c00049244204517040594034040c10944440d48000d11800308003610210840c000c00c2550b4062100010401092030103241c0a950f4400f2220240e0300424052a4406101403d145051b4521166540c40b80580e14100030203502c1c01c00a40a10383c81a00c0d80d03008101502980301440c41521075000c0407400d42c2d86810131 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 48351442 1250 48350192 48350251
    0x609020d1e1a060304080904090c082a01050307032a1b02010504050d1a0f04031107060912050304030506070e100306080a02010c0201031d03040807051215090312 71
    0x208032a07424810481d00c000b03000b4050403011541a68195525a60b03494591b401d0310542c0b00403a400f5250440030028040210000e0043e030380008210b40c1d14070740039005440440d0080f11015510012581301e40c0e0154803c03c003940d00451142030119040394030410040c041308119490b4040c155240c08416007043d0301c001e5241100c0c0d00003050910381c46854000801c18821030050a0040750032124000811040740d110951480080300940321074182169000e0b80c4400c00c0da0258002004201100041100403840f182154140d4030361910709440c00052404030450800e06940310300044c040080411010300c54113200741c50070750710f0314403070f800001c01c110918080c1010001010b260842c20f1100e041d0008a0032409502400d006e69641e81d0b6100403800b9000c07030300e840e42c222088200c0031080d42d6800000362081c0c1c0c4c81c0c0400d035036000d034407641446a00703c0320740c2445245900c001d03d008415a9491105030300821501d06a0785030881d419440b06400005482c08401e051811004074080d1590014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 48352692 1250 48351442 48351491
    0x3020f0c010e09011415030112120e01020c09060402071407031202071d180102070b06100e0105070609050c0901060513140639010515150706020d0609020d 68
    0x20030300c000324034140104107000c0050180101d0704129417075100d0241c1d075101240391b41c40340244460b9900d40e15501d402c2e006650365441100d0514414050500030390084050b02a0500180d004101d2207240804002000401600e07441e041a07080000d50040750442c040003c0d600b00f04402015801d01c2c6150100b24021940e600c601190041c2c0f40c1031080c510100310ba0304011034942855440c030f40b00e1700040320420300d514a5842c11584000b5403d02040b4080400c80c1c401c0c00c0840c0d200741d61710022082540c00407800d0034541d00007507040044d4000070350300d6400f0070112401441103443e0040d03801d011400c40c060a03003210740400c81c0070490701c80403003e814002d0050501d41021a02d2038080354049420341c0030703458a0034000d565031006280c00e28050030100d80007070100280440160f0008900d50300a00d01910142d5501c41801c01010b01c0e8101759206243c0c00600c2800f440c41e01c5801c1e00c0b010000d42000401e58400d503103038100003e05002500241c80c0350f00c0c9030000003610400d01042c80d004500c0c03c90 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 48353942 1250 48352692 48352697
    0x1b0306090708070608040c051f0e120a03051303050a03080906090106060f03020d14010605070209060306040209060105030a0b030a08030901050a051605161b0503121206010c1103060403020f0c01 85
    0x14010b212042d404070b8403408407001070402c403200340c43d20325022082c2d6070036800454004203c034268140007201c020709004207051035150050740c229800c4c14403201c084a5980501c01c0d502075040f450000b48100020201602070f02d050b504215160340e034050030400302070001d8000641880c2846403c201c140880b903044081c0701d0080000301c0c60100090400f11250894000f03044d404246005229003a401102c58080100c00ea0b01d60366031078000c06440e540040f04141c2c0101d00c030000080460070000340e001d0040b50020212402a030360341004581c90760004202c40b00340c82d11288923544544041040d15143c80c490003149849180c200c200e2821958010b05012500d030808091003611302403501880c01010a03803070b00c2030740c8030030204440c080350700905001403804003080d0360318101300c00488070001501c0044060f25000c2c107500c11885010300440f961114843c10000100e00f00350700800980b900302d882488003221611030400064102030044500703074056000310303500f122040010700416007041002d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 48355192 1250 48353942 48353953
    0x20301060903021c12110d03050103020306012903090d110a021003200705010902040e1203060f0d020301140106030b060403051b03070b190201051003020603271b030609 74
    0x4400601159061002038011152a8213003040a0320400c1142d60050304140c5a011590b807501e03000345640d6a03948007101170700034410b690060381c3c80790058038104c940040041c1034503401c00002c0000c4206103449052000c24000000300d00000c240080c4d07101e400500085d0803102c8080c240500284114000e003581030f008402c403200140d0743d9a5070161600c0380e030b10300000c1c61000d110b4102e07034191015498a5a0b01c2010036281c0400005402c40130429109070340c01d00c040c2e0700300c2e5a050f6403106c03800c0441083c6d54050000458600301400d061840d102c00414050583c00305801107421500820301001e090403850005100d0540c06004800d0300344001c0e1060b5282500d0368581540f0b41414847d6806a0426545401c5169400700003841c090f14101280a0303652060b40316048040b140ba0449c03401550803c00005e50789170300428040100c03500640945e107180e56000314a6822841102c401c030b5070304031481044804032401c005108440b100400304500070002c5800305481c0c50720003800003e265008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 48356442 1250 48355192 48355199
    0x3070f050a0e0c1206030c0d080720030a032706080a05100501020309040f06030b010b030108060609010302060f130306150e01140d0201140909070302041806140618060301030f050d03020301 83
    0x1c20890b0205a644c0c001182ea9032903010000341011080c4030f050b03601541c201d80f18014816220014440a88194503042c4403c04a0013020912140c0d0002281d05402c0b060101d80424052210050702d00b84240da00414000046000b4821544e03d400000000300035500700a01400d562244a810003002c48015100d0f82c038202c0001c0da0b07031050000300f9004a45840c3ea0801c450801e030002409540d00c501011220f45c2c4034000e810b260f8200348695004c41c4502404203546081600031030307041e40d0700540241c3c542100c04030811403a80c001d909820004921040000200328180b00b041300c000d01c00c080c1c04504500c0e01b20031500d008010313001000c3c4c01c1164140c0300c0081c0d54019904809690a003400480e004020000c1200d0340118007465401c2040700341000041d56240d80103109a4881e1043e80900440e404004012501a401419101d04000d0910046480c00602400c044a03030b40103000c03d0110340001013030064001380d10440307120154540940c1003210521960f01b0241030f502d000c605641c91f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 48357692 1250 48356442 48356461
    0x507020c0d080f0702030304090203040f0c0f0806070537020106090209060301030f082203020103050c0c120913020c0c0a0b1e0306060927010504090308060f010c0203070f050a0e 78
    0xb40e401002c00e9010001300c2d6003c64500b401034030001d100c604011500c1c1c0ca0241001d541802c8d804500315008500850301160024007800d403031058980140040c00da564500c4820f543c030740c2c0700c8003030040032081103414540251b649848001d40744a011800b50800612420080e00395042900084e01041c010303c90202c003619000f05a13811290000489009031040e410102e0a512482c00004211030b0038200c2402d00529484150048078803c0e6400c100301d6441a01d490224041d20b4059101900406410b0440f40d045602610400d8001030034031f2030340350441d2158401c0b40d103c9a40c130600e0b6080100c2040302e40ca0181c418800800202082c075103044000e04906110708205141600c0302c074400f201040f046d4a0300d00c2070300e10400c3c0203040c083e1403040e004010900300d09810840385400c40741d03800104247c101400750124040d410b440380102501d0302c404000b00c4c3c0c0800600d00341004207402320031001d0f940c100100c2e00100441c0b03407401401810181400914402c503003002200d1541c02c002d1020400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 48358942 1250 48357692 48357697
    0xd080703180807030c050d0302120114030a23070807090b01030209060d050405070b0c060a0f1109010305061201380114090f04060b04060e0405060307030b070915030507020c0d08 78
    0x20742c844122035442c0080d240980c0c0104110ba0003400f80c0c8601105078450640580c01440343d640d2102c0882556039940c0b0038040e034418013188003138041c0c1003003140c0e0b40050b6004400b200078603000181e0f07903450b90340c8501c113a14006690340302400704da11034041004006098428481064800e00e01989450115004101244110007181d0443d0350780f00300040910005101c0400a48103000c072243d507500c644080184d55070b40030798019a403079251106a4401e1807051103201c0074500d101d0081420980008010340044c4001400035401000304100201c0340c100a1003208060710100b4040c0c0701010340a000c60703d03c000b0780a161400112442c001d208240c1c1c004240c000c011400c100d51550700c13500203000c100c400007014551a001803c003400030a00c0720054028006079800c40d03039a100020700c03c2c0c0821064450548030103401d80c015907814004665000000c031341c800c000381020380080790348000c058010590300f04450002a038030320a000304154140144000e610381201d4003040e4001c039491719030389031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 48360192 1250 48358942 48358991
    0xb030c090112030519050403030e01021b120703050d0309140f07230a0602030415090518070c0804120c0509040b0c0310030b010f031a040809100e090403020d080703 72
    0x3440b02e81c110304109489007003100c1091032201d1040c0703010520804080d049410501044001c00c01803600080c1d81c1d44000b03855003000205042034000a45c0c00c0c4281f040484080c1c11402503402086000720200d5800c20803408502c0d40c039500090300072010b0410180c4450345042900d181e0b04003400c51030701940002210010b40340c1e03400c0286003002283c0e82458603040008000d54000a400000241c403a0700070010b407046a84841003a1080c11142004540f0301c1c102d070081540c0a0b03011089e090601440c1c184060f07115085045c4000e0003989030f29440700603040766002c154007100d924094810080700a1702c020061000b603664001c44d0900356902000c544008119075440280440041c10b2405083d031464000c40d0000c24020b03565031214004c01a51210340400d80340e01c41d8590000d003980c090901c8442c4503941051307003142005c080d00e0401000b40700540f0320404106012000d502e036030f42e80c08001405140329030001d00400766603140207800d00c00014803000c01e144ca0500100c1105414460301c6994 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 48361442 1250 48360192 48360209
    0x11a0301080309040f0e190b0702010e0a080f0f030a09060f0e030a0309081c050a0b030c0a060f05070c060e040c0e0a0314030f160515070e010302031e16030b030c0901 73
    0x1902403401c82100421017010b03004418030030000807240c1f030001c02c8a01008240141100c2c8595030307903214103030300342d4130301c001c030700c0c11b6948041307100d01c08a07800102802c82d580e0210440f600d8503c016031012a15001500d0400d8144d40e51a03180e000c2051500c00c080d890b88030f02805010001110225640f00d000d4100f06006060303c504140080100d414121100e142110120070304082a24034a1001000100d40c1d540e103a0b80703010612000ea1400143d50055000001c0481608a00700501103411941c41c0c040d41091050910000e000910040700c000301900c1c0300e41d112551400d084041005035002807070300d24140142681c2414880e1101b441c1c00d429260040074200c005443c03c0103884c55482007000408442d02e01090504181070a01c0f00c43c000ca44c012012a0744016640c50b03160b400780381c140d82c23000201e00e880b072401003194002d40145900000d45400d03003403010480308405000040444141c0d90b0350600c0101c3c0f0501d0b64052050310080c2d58168001d1a114080c8400300d40c00310418000e1010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 48362692 1250 48361442 48361451
    0x80f010b0304060e0105090c030f030412080c0f0a030c05061f090b0d060c0c05120a0912110a08071d0402030d030518120306010305090c0a090b0a08010212011a030108030904 76
    0x901001c1c0e0011300301400494002c000718500602e0a94a513032410318443c0c813074002d8001444440000005903015034500074228030100002da5264070301907021894503221405182c90130304504606011003280c1c0e80c041c2c2c4504250f0780062030024201b850040241c1e4590080100c00d0008451850005040d02d8415800141d01d484100006000c0390742404001c041c14145106842502e078001c0b034141200703108100715900c00700139890424281c020407a4800004104250070040d40d81d90350424005203003e14a00f0342080f40f02800701e14401e920750880e079140e600c41c01c0100301c14810281ca400494501000f40307030150a065002a464103d0407040004041d1a0000b08500c0003100300b4a04000c9681c0307040303c082194200c00541541c2049405a004c02e14140010303001790008100b6482c6480010098000e450034102e8442c010b00111189940100c0803a8000c121144248018101c05810003800a01503242000502c1011a001a12601c9507014001001600000801d41c0c041d00c03406c440224 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 48363942 1250 48362692 48362701
    0x1812070302010f140301150e0303191407050f010c02060106090305150601090510030903031103070e090c13080a061b0212030603012c060f01060c0b0a0b0301050403020709050601080f010b03 83
    0x685041c59403803104c52100700080001052050071142460a5140782c64280001889034205610380c0922412014810700c0c41020302c2060b44910b03a0480000451029241030111507180e50307107070140d03044414026030b664803040300d540c580400c902801061503240c4002c49508642d201c079103030700b49030380e202c040d640300d030303c0450f105030b00038900b11020300f0015241c1079206083c5000107000e0181145c0c00e60101c3c0c503190007605404030081c01c0300c2c8542001d03200c0c0b08410000d10180030441100800c41840c1042c04c0c460300300c03158a9541040001e02c10900105200e50040c2400412501d00d51140c01d408a00004d5141c542d40e00414458001c1d10b208010640b40e070359450210307014080350303003282c0650700c0c003c8401e5004454091024411050017003c540c1580d9464404036122002030003882c0220300701071041000203144001c5542d11020b0160701080300206000400e0940c0c0050300c1c1140541c2100c80f090100000d60320815900c0303042480e1000b001d090460b0324119008060041043e4081d0020014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 48365192 1250 48363942 48363947
    0x309060406051b01020a050706050a0203040206030114010225030302190506070c1a2e0e0c090f0d0b180c0d1e05070603150e010312030504170406051812070302010f 72
    0x2c4020b440c030b03d0000d654070921603200514641c4030744800c0342c009150102141e1114801c0c400e4070310456000e07119034a9642800042001509040b10f0b0324114410301b00c14641074032071100601c0d1101000350050149070300354070740a1300305600c0c20100380e01c82740d4122100c004a0380000b056a001601810701e101d6072230450500300700c140e10446461005404002c00d00031171850740030f140301031082884075802e0900f074040f50b1400584041d105494018203400b02240b10901580001c0280100003082c040c00303503045d9004500e8406000600f5103006500200f00070342c007020120f0b19001c00030440040c4ca0860410000502c079020001f1020382040d242d024850340e20102c442c07240400d02d07006012500c110b691901c0003009040b0038500e0140c4602004000150a04800c1040d0305880c0e02806039240d109070141d08a000b8003005006881d2801d41c402880303416180c40c0010700c0600402d42c1c03540e507203407011b030350414610804804c03090050f40c3c4803140000c914800310f003803025a80d091034492405840041d08 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 48366442 1250 48365192 48365227
    0xe0c01110708060408030f1303120b040906050405030301060809030301080703120311180f030304060c0204052a0307090510020607032004081b0406050d11060f0c010b040b03030906040605 82
    0x2410030b40c840e0b0740c1071000380000f400c0a036101c0d4011499250710b030303a12002242c034040c0c2c00c8600240801c0c021043c0c040c80c0c010395006140540d502030800501c280741341c2c03142d10680c0c00a643c10384150300000018070040341d000b10030b2075101d01c50314000c40c655450541c0142d5900100d110140c8640741c81c1e0100510780d4400e40000802424910009464071000c9140401c0c1981c0401c00740e201d035444032401e12003810040103841c1195132a417a8130000c00c1480e024400a8200144524200c01e0415928064001303503402c008025071118464075181d107000741014040c1c0409410403407098510500b40c0c0e50316580010b000750b100d811440d0204040c01c0780c85e1100a00b08200214085c100e0000c04c01242c0b0160004d00c03100600c4c480c4500c2c3c041e4000751303401e0000711109401075a0f00101911030712808104610a04a82c00c80058402c900d8443c00034940c10301038111280c2192140d4444504481510f007a010380701d144101100070710f141100c00380014015101e24800d00041c071801050032307020606071048 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 48367692 1250 48366442 48366449
    0xd0f0e09090105060307060206150d02060d020403230a080301030f060b1e0301050109061202010f0e0315010e0601020c03190c0b19180f3506060a0501030e0c011107 72
    0x8150841d007005080c15019190848440c0d01034440c0881c0010068070000d0598029000c0d0241e0b105c440358000240903d40810b0001641c012104101003481c110151009000940c06401c020382d88a001001d10300090405050038003507035006911078404103000404032811241d01159003810074100340f4000018003043d25489501034201c200b44501071425401034600c1000c100d00030062aa251070198088400501580c0068a14a0426801540207401c0310040c1c0140d82054194248440002840d01b160f4a80350f9030030f0304218004115182d00103115680088003400901600c0c904031010943d14514440304452200450100c141406003002ca00ca000c1c014581034140d40301600e403450004580781764900c80014200d98801100d0749601ca2440e015070f0005402191703034034981418007025a00440d030302c00103c0c546400301814074084e0801003891103400c401a02e424a009800c01040c406294001414942000212130151101261130b6040e60002d0910035103c48414080c05c0c64918140c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 48368942 1250 48367692 48367699
    0x1030f06090506040c02010e120f07240b030c09041e02040906091406191a030f0708120f0301030b0c09060304060906060b0702030a061a060703080f180d0f0e 69
    0x610200e008001900814403d1100f80c4082c000d40d500024101d00702d41010303665400b141c00c401100d21100e1611402421070f01d4100c1491401c00840d078842075000310400404400360280d4002610100c0c0700c6010302840c1010840140c012a0404070101e4900c0300002c0c4024480c4074901c200d1810640070031465051140c0182c010070182038280727004801802101000e5401200340b4003100e5103000001000c81c4a104031080000e04456030f2428800500b04101c00d00081d04400070a102407038604004e18041800c4c080f001b040c90074640307031615007006090280c0035501c003401c200003883c641d445800c8904403070b84844500e050b50303601307488030690340111014290b004c00000248001e00140b908050126800303103100304a12079a03004403403654802c00030001d4058018103808804104140d100d4107504030000d8150f1241c00742e400c00900d4507409290100c001c2801c0b0020f2101d91000b401400d0741c171a080300d0072180254500c801c104c0d40c0d83c50100e100c60401089420302d4824510500c0c0c44482da80019 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 48370192 1250 48368942 48368951
    0xb06040b0a020703110306040510050901021e031b03070c0f02040b0603040b010815160c0302070803030a0213080703020a3012020f0604020907030c1e050c06010b0a050d090201030f 79
    0x40402034983d8024441038540c5240546166002d2030086842e41c000c0da030050041090030106010792028000007004900ca5550138401188030b800050300701d4854030b009244541d900e28041d560003030103440905003555010f50a1080041d444e42140030b030348106401c04420001c03000107200041c0030b0090b07412000c0d00441e002c405d000401070410011416100000195907400b101d0050303004900c2c00c1140c01c90850b070440c003d0020918040c10607104054003a1040d200101d48403242580b55174000e0341d200b14074070350003e60a04440c07418040c0502a0000401800702a80b46400164514125028030010140c01101d4684418100d690101107081444a1502030103154103003086089200751903200940104840c0344504640409c02d10301c5070780e005080040c19190407800310002e081d0003507400f003440007604100e0010400c0c0d0340041d2481032989d6801e40c1e245825a00181401c0041e880440ca20805200800c1007030740000665201250541000075500c1e0603000407005030024800885115151 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 48371442 1250 48370192 48370207
    0x20030d02040609030201091217070203030c01050103150b0121021b1603030806060a080a0203060a09020c0703030201110c06010b03060a05040c080106020c01050c2a1201090b060402040b0901030b06040b 88
    0x7111000013128000d0b00e80030485035941011039005090408002c0452003494030703503100119503001402d0550b00203412a400c2c900d5001100d400c490081e002503481c0844802c100801c4102401200401d40c42031030640d00c40c1a000d094105800b44072040411a6500840c01007580c0103080184120203402104a0b5101c0342d140316001c82d060000e000540004d003400c4005074241c00e0120444440140c40e41d0f400d0711a41e1780c0c1400400035080600526441460614005800c0b0b401d40040c240756520030015000003480c40c540a801c540398049840c0410f40e090151044180300030681c181100c2071000880d640ea03991170f0000709440b2003a046240c0c012310700451640d41d25804541c1038141e50342e41c2c003102c0049841e00f0040d69540110681c0d07010b158001e640c201c503261064040045094000c40d07203541c0291141d00020148070700c00015850503995040351170280100e03c180305400c903800b03403400c503e881c0c01d1400c652030900c644c4036114145515400d0b090929191507049030010100c0b0501940c8902e070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 48372692 1250 48371442 48371447
    0x2090d0308091506060306100e0a0308180d02090c090321071203110403060e0102070b0c071221090c030c15030f0e0a150608161701090320030d020406 66
    0x402c0d035140302c162140f009404501c508082c43c090049000610a078159034a02040010402c003c01c1e8500800c010500600d219072a6030b52a000a14804c90300661a02d441084e0f401840340040d00e4030344546074030b811000250b101d2201c0160404061402035030340f03101580c04a45441c005a222607500c06104801210703000082c4054400144540d490280c4e040c9004070880c00d6840322403010f980c50b14208800c00005002da400312552180c20744c00903040410685075885c84510480d4840b102c410001079210401020020000000c03055042100c004901c01d16400034403406203142e6850f0998455070a41800600e45291f4003e56016044444441d1212025541b41c078000c0203800c00310b4140325003409916501e00684e0458200c080044c00004002d8071038020700c46102d90001209a9500408a4040e40c103001c070752644500540070401d05803400402408c085101a0b030f0000c5a450400c064001030381c002d080c3c1100e003d040d100e40454108000030141035101c0d000b039171000d061000500046068 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 48373942 1250 48372692 48372707
    0x6030c0b0a030506100801090c020f0d03020c070602010612080a020a0203010504050c030106140603042604031a0703020712120b0d0501050402120d140a05161112030a09090e0102090d03 81
    0x86060b501807110780c036004180030035900490110000f26000700010710084880e548082d02841d018070440c3e1134404007540c1c0c181450310031801100001d4000508064031001044214000d21151000700109803825985282d910201a402813081e1070000e480ca221520820900100c3c1d80c0040081145d41028a0b001d03030344240c01d4100318001d509051000071301801d410302444d102040506094a5a40c0b565038a41c40703520607103189612448010701d4913115540c190003610203144545000c1e0f91080030621030500c00c030340080c9004205801001440000703003c13541c10000b00c084906100010740030b1084e842c0017406050656503001005100785100f40f00c01500111f02442c029143c258182992801141d01d03900701e25190008120845c20f440c0200645800038829900d04c3e16286081030314010020070b070413203028001c4d2000c0c1d150180b11381c030502e401382c0c1e41c191900500001394508849440702034841130592141ca401503680c0c43d0302003d0380e0f40c20340460306004001004460b0100b182d181c040c0922 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 48375192 1250 48373942 48373957
    0x1180b03031305040e0d050d0e01060308030103030801090b040908070222020c06010306060e06010206070e031002030c09041b0e04020315040903170a0510030803073b0411040308070606030c0b 84
    0x754180317145100d08160224108130b18109650b111403801d4100a00000030b40140c804020742d41d986c9810000201389828050742c080c520984e00c40815526210703812084d1131700b5502ca9807150b0b00d00310303d00000440c1d0004682615034141d84004000440d18003030007189a000782d02107045800060703151f84400c40410054103803071040c40100105038035415481403002e000c481c46400b5a01c50030204a402d4040e80110885e19001011120b0707608207018400180d030030642e1403e19800004c02c0e802c95038545070184507030050b2036a0414201c000144001404c034120701d45c61074040c46c4e002020645111754105184041c01003c0d00c10f0020341d203180f9000708000c6000c520513034014014808641d60b1006405044d001d0540e010348240c020b8219100c40c4a682d1018240c0310601c40042c1c01e9420030051400c2c07100c9502c0d04111000c01594048000410b81c030b45503240c41d03200303500e0700700c039100c01600e00000c2c0e409590b00114415102d189a2420200a207191340000d00006c1030910f0006103060940c0050000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 48376442 1250 48375192 48375199
    0xf03030212030106050306060706091709030613050d0f020c1f2303010302100c0212010c110303091507020f0105150406080f0c010e0102010204170304050a06020d020601180b03031305 80
    0x8211101c000301414042805200b0010300d007000400c800d031400c80054a0f03454090600002e802034030780c1d15200140f01d030070100c40105070b01040c1400e15150038005603070b002c11480b02407101090340d1390b1840c0c0c403071704a40c2000051245208600348003510800060245840190071107000503110000d0009000b400c18942000664081d5104010406a41c05100d22840440c400d400e503400d640c00c00c4998000d0500301010440c00b04602405641c0359102c118400b07172940c3c0002031803000c0ea04020000103043c4c8200d4071503030042086c003002440001d460303c1541c19646184440d80c0315420b08a0901d001c8040b003c10960130f0100784030b60003120348400c0309581d0b03048504101159884908503200c441364150703a00c1c940c0040549814a5024040c00702035204148001458907441e042c0450840003a225031400359480410103204a0a050380d148000e80802d000802940424150096440405016218610295000d4503002c03000541000c4403c001c01070030349495140124191056030800d2080510 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 48377692 1250 48376442 48376453
    0x10f09050d0f1b06020a030309080904090b0103030815060910050c0d020309090a0b01020a0f020a0f0306140a090b131b08030316030c020309010e0a05120604110901050f1003060b040f030302 83
    0xf4903003040c0c0c46408955080c4c02400e04816143c0301600205400304054813040d808224100c3e003555103105040c3ca083c41a840e400055046080041c5074180013015082c01d181c00d1031890b031903580c0d000140c0f006030204542c04103618594a80490b070a004200c00c155661142c0803400ca14240c000c0090905080d080d11251803e0741c9400c014410703510301040d0b80b800342c0c00016860002c9014a400d80f1400d50014054840995550079040c80b0358100340d200390342c110b1b80c51207014015040e0301080c40e08030350304e01c0c418481c0b506151504c48091001030b0034400c0010192039100c08009104050455104d444010a80e03420303540c2a01d107032281c0c0102d8035045420900c00f203c19201d406031141c0c010300c4600780d0046042075620001943c040200620155208801400018150384c1d00283c21441144c0c801c0600150300309442c21746034029031007800310310884c5a04010320460702c80c0f030b110003840401140d18031000342440c881039000346032a411004c03000500240c00318020000138144400c0b24800e40c00c0b9103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 48378942 1250 48377692 48377723
    0xf02060606040506030f060102010902030f0a0309170705061e03040b090c091009090507150306050a0e0112060b060d0e03041802040b04140a0f060915030e0c010f09050d0f 75
    0x40e00740b10301e01400e0751041003072000c20000383c2d00b213403070561105040c00002141d40068002903c0e055805241140d96032284120000705a400b490f41e81c01040000047c801000c28500d142d600c802e86030084a004a0000c200c05665070004000311101c1d00078003084030340c0c07070070b0a042010480c42c045411000b41d1242500c2c100c100c3c102806424400c06208101d500590309112130b800143c40601c00545040c0300f00000404d0161031003421441c802800d07140041d080745083c1c01c0c4015105030364010b94901c0e6640f001000908180200050041d03171011000980c1261070300015018000c914608940380d282c440d035020001d00c008002c0050303454400300b40040300488801703a02607100300d02a405c482c041c03e0000b0088428009120303061400e000300901c0201e5125690800c0ca0105688403000080215208010b40441c1d0000303c10960082d103420b110a804c0f042665680300e5194620304c0c100714042e2064120039104020042c00303008010418212400036007411121076404003001c0c2c580913151001c5a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 48380192 1250 48378942 48378949
    0x20a0905060705101a060301140a0605070c0504050403031407020c03010b030a05120307020109051c0f0903080901111e031818071206050603040602070c0605090d1b080604030f020606 80
    0x200ea04641c41030041c2804c1d950903102d180600000c1c88904c50300400003940d103181c0d80c0c4072006140a00002412141000d04000030420004040e03404801880010461100802c10402c41c16046d40c100f0344010403507071208e20b0114024082840d080c4264200c0070f00b4040718a60102e110052514100c0c000c2c400c001c0c03142d080540310144420010460340c0000c180100c000303048800b85510001600000a01c407480303848072400d025004403100d421080c08850425420740001c00c00d41e2150f21460041265401c5580f08903482c498407260038144000c1500d10040000200f02c500200c0001d5a200884944041d501039a03079008030328542c000345004d542c818194286841c01c2c442800c0c0030f0444c15507544440f14142c0c0ca50303000b01203641d5920344070702d00070074940c442d0001903018510034400141d41e02400c0c00d01402100e01a08a1010070504000b5546030f079840041120140340c01000e10548494001d80c01d40b1400311381c1d0301c0081180a0642004181500b02120314800c5510f03400f030700d82e40d54401c0d082 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 48381299 1107 48380192 48380197
    0xe0103030f020303040b0705031324050a0c09030209070207080105010b0301230102031c0e0601060e030615060d020a1b0c081002070809060304020d0b0406020a090506 73
    0x10810540d00c81521441c90405102035411400e05550b5104941805040001002030200200e00300425030b06a02603150790001600d400c414403200012401c0f00d02c002e04150305845c0000140c43c2390900c3c081c0c105176181d2580c030f910080c3c1c00c6508000d03001070050500d2003140309115000c184038009100d41030182c16110101a2650300d4400c0002d80140c003020503c000180c1c00c00c4100645c3d030004252024130142c045640c54041c0ca44800000801881500d11024450040002059600000d009001030710580a0720965a10018501c40900c2094100b507007240e020070000301920095400703440d216030316280021010b090402c011301d22141e1101c05558800840000f00306c91f6030300b0003114070b840400080950411080f506c0303101035030007005141405207500000042c11507642c1e40c80c02c0d210035404058003000e0300741804d103600290060f894000110343c44200104592601c54207 = true := by decide +kernel

theorem cover : BRFrame.Cov 48201442 48381299 := by
  have h0 := BRFrame.cov_init 48201442
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48201442 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 48201442 ≤ n) (h2 : n < 48381299) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
