-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4400
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:29:35.028953+00:00
-- url     : https://prove2.me/submissions/b5e1f636-aaeb-42cd-bfad-1e45d8e6a4cd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 791187050 ≤ n < 791366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 791188300 1250 791187050 791187083
    0x1c030e010e07080c120d0804030c0501021803250e09120f130f0b16050709090818150711130c030c021b0123040b0c0a0c090b100c 57
    0x9450140040072030990100e0828410310105120800c64110b0440d140b10401c0800f80d24140c030b9212995840040c40304201c00074081c9070041c6920b41c43c9035030101c004c540d01d102000f43c0001c0042c420610700c0c080c0c410f0700e02c00d0303012501101d03a0100301c5482e0f1003584459841d01c100704451100c010404200342c098001c8009050314405c001d0216803074056841903c41c128804400324814059100891002c55500308202190b0f0400450f859800f042e00b029030986241e003003151901d107180e40113a18091900240038188003072540030b0a0940c510f00182100d8100c00300c20894108020941a00c501e80104a004002400543d012006050140036050010718864080c8100c1d049192480c000c603482d90060104142c2c10721181c42007403003091091100c1580c24000800c91920340018600300000040c0e81215030000c0c00a980c0101180141c0c999922040c50000c0c6e120809400c3c00c4508600c0c840010506100e203010b410b4a200c0c000e840c04d02d131042081000c40e0210043c0e00191187c850781c0e0400c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 791189550 1250 791188300 791188303
    0x30c1207020f06070c1a03070e120c19180b06030619031a0a1503111201091e03020706110a030f0c0b04050d021002090d020f03160312030f09051c030e 66
    0x100160040c040700a070a0701c0c00c2e0390b4180c07400d908940c40d25001b4040040058990300407908200c400c000341c0c2c04e207038141d0220407040c0c50990410031711a4016070151002c0c0c14203114100c604191a04222181c40c00000060041d080c2c9503030a0720541c1c824414070014070705040888550502e000001840704240b6a29160300046125060342100010305100c20448080010b000f642e000c4140e03a00d03c800381c10702d1629010652851581d0399480b40c0122000f10400c0d2000350400344042d504036940d040b00304140000ae6559500207501100540141e0310002a054011040800040c22075006413045070010355080b94904103006140c3c080c070045000300c1021980a504a41c4118460001003034800103612005c1e01d040c1d800c40350024018010084190b00d40c94440780c040a040c1e0503141509503481c0a00000d048c00c1355000014240c0b0f002340000000e0216122400a120f000c54504110000410800360151042c0b000058060350043e0304110f07814214070701400030a050f41c500000c18003880c0700c119 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 791190800 1250 791189550 791189557
    0x20111040e0708100905091c0c030c0b09070b04090e0601050d0804060c2301060519140607060b030604120305010605070f0b07111608010f051905040f060c02060f09030c1207020f06 79
    0x610a90103100c0788403041ea20600c2e4000c8008043c00c140b0206272860f03034000c04101c14940002c242815510214842c1c0c0002c00c4000003400d02111095102e0b91540403071002490100005c0f2210300c551000002c96041a00b40c0c221000c0d0404100d0f441c150030284143c41c40503982c081181c12450a0709041d402d00b8002064940b808982c00000c0703a001d15100411001c07445a24040440c0d4150b44800c220f009005a00110396a200390340b182c0d140d1f80d55050020050501c62803550305130195508000400040c801c2e4494072407501d032420000e690700c451080341c0c14003600c0c40040c021020f40100601049070200d0682d40264145000b094449907210b409040c15603030264000b40921109090140d01000e004002c4d1603e94034008200c580303401c01403c2c12001e11842854101c0da500d00c00f1900f4000605c4403504415007054080c02400203844000355206022a0020242d00f103020100f81d5080c000300440c2c00c403e803150018404d00441d442c071041c42e0780c80038800300c0c1c1c08600c0000241c0c4540303030342019 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 791192050 1250 791190800 791190811
    0x9050405040f0b010614071410320103111e030f0106030b0108010b0105070803040602040306061508160503011e080601030b0105030607030b06030c0306040f060e07020111040e0708100905 82
    0x324400b955091038030340031440068000600b4003072020000c0c1c40c0c8500c01c009543d21503412040030200b082882240c0c84c24080c035034001151150410322044050b0021061110a403221010403a10011212418919040003800020011208c0110150591420922511304001d000944401c4160341200081c64070740085d0003c0c0c490394552108209024410b10000e00400c0000002d225446c5150b00082480c85212002050040c0210200742800090b80c1660069030340858100641600ca094002001d101002c140e000500b0b90302c00500e4040811980100020441e02d6071402c40c0d08001c2c01104035041d1080304014000d8010000603036403010032119000314061940005e05504040505040610062801d81818100807107807080751503002c101d907031140c444c14205441342c90b240001400352188004401d640e50400001041c0d940d444251a401003125800070440503844000040340c3c2e005622030300302014015000118103c1c09800c3c0c26610000e03110340030703454580b01c113608400c40705d05654 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 791193300 1250 791192050 791192063
    0x714090a150806150a0b0a052a030d0605010203130b0d140c0408070b0a0503071b05010207030201050106020105060a0e0402060f1909030c06080c031b1603080a050f0906010303030c0905040504 84
    0x144026004984101d41d8034001c01e9540b085c85509226148202d48035482e204010030400207003038420021500304922480b000f252240d00c0b0075195505241d929000f442081c480030b443d001d0000303503a60000040b940064006c80312040641e242101401d200e4104c3c0c0c2a0840c0d162b260300b10044020120005c2611441400c07145030b40705c9051054084c034002683d080420f684000300003c100d125044410f51742d00c80d0b01807030841141c040340502009910381d21480144550300100d8a0010183c043d04894103070f4046600070003070b9641d030804001382c0d06a640308011415444001050160070910001c01c1504590310106151090300c013680d80010790100b55103000660506428070070801030f51445401881189402d0000e8200502800e15911001e080c0032101403014010a00d08020002905d82c03d025140300e0380c0c8000f109050107010000e0403607180c3c0c00f062030540020405500400c0050003403a2580003008c4aa0071540e09070018a0009203480502914010004180d5a5805540e1250348502c2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 791194550 1250 791193300 791193313
    0x60206040330140105120a061808070b18011e050c160f0b0c0304080d0e070f140307090c0206070c03230a02101a10140406031d0714090a1508 62
    0x3ca803192000680025106900904004107013403c0080d4500381c00360400c000180054200b4448020355019182c000d12003d00420381805014644040754402c00110104280740d154035100d04e0300f00c820341e41d0307404000c400030952080c000c1100d41c0055400035444c08810701d000d4444149054a001460048902c000b542190801b000b040398031031074000c03074035111803425802c0c19a2440741c140650041d43c60040d41c0d0308500441118108244801410103d50f010035043e00e407400c0f00c10601003c0482070092090a20000b0f552240c5c0c841c3c001c451040340d01824003030325900d904032101215a4001d5041080d44858aa030f0029680304031f460389440c2000d05030b65008500c10117414080c0c0c10460089951a15900c2c0e080511a6501004060341c2140e5448814640f054252500c42e042810040c038404040303008119150540e10000040d480140e10a84089050303881e1965252140102000c00c02000700ad6102410801c0d1003680000548902180c50051944141014205544908415440701 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 791195800 1250 791194550 791194571
    0x100f0519110a12090b0307120902060d0c03020903070e0628090f052205060f07050d06080706020c0d210e0d030804031206140603040302070806010b071209060206040330 74
    0x5410003408417482650840ca499103020700345403060b50401110f142c0b07504102046581c0c40c3d04452965442140411114141000041c020f4001c003018600901c21540c1c0400c1c40700548805a10a000080600c5004e85c829400c034403000b402c456115040d920000e0002c900840d0300e000e400c501000b951030028040c904482c980d0303696103402c2d22500012038002881c101040c0c3c082009540040702000c03078103013901d0340401202e1034495807103000b15032441c122000c903503c0d001150010071201c3c0d6901b2a50703185400307020022142c00da140001e043c1c044800703600c10310256181c4c160840c540075050841801681c07002042e64000d09000c2100050f5540341080201604018420042014058104941e5042c4070a074007201d02c81c4403032580718131400b00004040500c20020030b40030307040c0c81080e41c46a59481c0204291904201ca0407103400c0000c3c000342c41c0302403050304541c040301c51590040107203890301d450680c1c106003001854403c8801031900807503041d03c1031400071b60110b0480c3e40010b991340f19 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 791197050 1250 791195800 791195807
    0x1505131808040305062401052d0f0309010b0102150a090f02040509060609100b04030618060219020f06061c030c050d02030a0201060816030803090109061802100f0519110a12 76
    0x1c01b40c0b070680403203020f0f61001d00380d83c808180c88079130700c1f5042119071a8082034003504141c2c0d0b24a038005503045000404805007200e4a000d94010302951000b407119080d00c1005988812002e03400c01f00060134a400103c049009402002410f806031500380303400010742d000b14055a030100d6000845501c2070b02032090f070f42081036066034048071003c1c524001d141804108074642c07141d440041c08558841030484410810b203100030392320550059045503903e0200d50281c200c40456112800540580070200343c4441021440038801c003c020811103100c00070400c5210303102d800d400c042d0104140f1421000000b81e080000c210304802c682c00468444040781c400900351400c2d41c102900035044202d107001101d00403410712083c8d0b5403110209807640d0310395410b2030050501c400050500ea00305203c222a80085d100b801074124020350350200990800402610038004910191700001d10802a240c40790030441c1c005500c9140078039098000b1507640c0142132a0402026043c2d4001c0c5504503a801860342 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 791198300 1250 791197050 791197081
    0x1e030715020f070b13021f0e0118091a061306021e0c0405090321061c05030a03090503070c030b01030c090203040c030305131d06040e0609120d0b0303031504150513180804030506 78
    0x400346000004049400c1c0f40142d501c04ad07218003400d07261242ca10b201078149480c510100028003074441c540b030391400701406241454030701c100d40250044881e00840f050719a1415003e50b00f21000504441159000b1300c4002c01c401461100f80b40402d105190301508455200c89090089910f160300b1410401c0400c0f410b4410340d5980035602e1795040c3c01d000002c03004030554142d0a000d00700010508000d0901c2c03420b42c420108001c0000415140120422000c013449a05881c0a00c207806519602c40424200701d120030354002c2d00780b00c400032003000020301c108002c00701d4621a981c40e10b41e031036507a40c401140b1000c04915680c00441c8000708004d5007014800c101261390120b00801107410034104135521001c44a400c9428450f000803070440c2c07031100d6001410208000b8045907a03c0c0341c252010a11070b003400d141c8a104504264001c100055414108400c1e20401405002c3c580f40400083c00188613100341c100d20720310041c1403040410300041c041d000640c0914090301b02d614215100320304001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 791199550 1250 791198300 791198327
    0xd021305040608280f0b04060c0801060c0203030913110708070203010b010306051e0301060e27030a09060c0f0602070506101203090302010c051e030715020f070b13021f 74
    0x188444a4604070070548007450b4000f0001d100c0e00134034503480341403200b00d800705070201a0800c1101d1041c4001c019540e400070b41051015505d0340b0b12a41c80c0c0e201103440c1d402903000a540343d8001d1007090075030b283c900c0345417010344004500000c0d01c060041e00300440344c0014005441d15038000c41e8500a40c00e080c000d04441c20000d1908004a0b82003400290002c081a0107807808484411003000c2c164a00754000c2c0040c18510000c060503140460703540c852440c0d03c005c3d1806592007403e540420b40f00000070303a551043c01c0d48520b0921418a202203071604600c0310203481807003124030444042035440c4001c001150058000c0c1c030320b030320701581000f03450a00d42d80001241a600746d684000b10f40d02c428200d040d2a82468444003010482c100790707240400541440c00349218880c110b4038410400001490070380c0c428484c0604c58070b42c80c80008121300a403200c0c800d401d10100141000a2440c0c144e19900c211582c1d8918203880194000c9030404d4000411981c28040700c8201d1082e180e0000c000a2000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 791200800 1250 791199550 791199553
    0x10c09050418080a0c020607061a01030e030a03020a03150e071106010302090406020702240a0908011416110d051803061608060d02090a02250507050f01050d021305040608 75
    0x8200160340410000242c0c41d0142203103001051550b101445000c4c0c1085a503002441281c03520b15501713081c00204401c400085101032084001341c41035020340500528480c2c2d860145060110383c0707406901940c4403001050415942e06840c6611280303070b00f40310016102d00c1065036038920380141f01030306038406c460b0146910b900c0320b0300400c0103a0382c2c0820f107507101d03134400360142c0c507180244080380c044e0030b000691000102040407194480f400a401a10a0500300d0b41c0e83c00c8444d40c1c0c0c03c6500e003200c14809081e07024002c5540000e0000344079003500032042650f407070440c2d01018514407141c1496541025200000c03400241c0842003a15042030810309801100a0051800c00200050050700b140b00a102403294071000a2159030301c0a0001250720380107090036580749449840130000f5880200c4480c1c12141c0f15506080d200c42c00c070307008a00b00e41e01400515410782420f08108018142400c65810001c040024042608a5001078040003000d581088001820310040005480280d0401d1055 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 791202050 1250 791200800 791200811
    0x80c071703160512040816060c030e010b0d1a09070b030f06013b060f0a02011d0706050d050c191d060322050a08120f090c090c16020a08010c090504 65
    0x18801354400494210b80d0080c10f1641d510495100c040082c07010982c00360105207441d860310091509900500e0500c0b801200802540c08080c0c200030310b00500c1a400781219850443d802c9444140310b00c81500328001c1c00032150b540341d8070340110506a00c02c40d01d107080040c90000b80007640d600500c944401004520500c1003028501d07030381c1920101c040e2948940c201a40d02c400f81c254445000b220184501c2800c0c90350b86403401c0f9000313400381c0b000220f4658441901580003018480224206041e41c150341d407000d14104003c0e807154058800a80350640035142000b818942603409111341d07000b90000c3d1200d0b0380c40c08002007032100340395601c0241d40c01020104100240313015031211000d1800c600740d2200e2803516190031701d02d142404100e801400c5800c0041c0100b41030a1004c4030a02c00c0144c41c07140b644030741c1c0d2412216103440b401c1c19402d401000740808200b181c82030382c01824004d407481102c0d0000424a4001840c4040b00343c2c00351650b42d560340400300c44590311041110140000381c601340302 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 791203300 1250 791202050 791202067
    0xb090303011505070f0501020d022802031b010e0a0b061e010504090c02011104030c030b01091e051e0c251a0717040c05040e160303080c0717031605 65
    0x181c114109002020083e0004418040000d04920381e001142c0140085403212440b88008000394400c035042d14240522603140301610210121081501c5410340c007940c00c000442443c03221082c200c45004509540301d401c1185005010000803c41b9801103680c00c25508054003031000481719040d50403620428181c8440113660050110360884070381a000240c0c0b40b00c400800ca00502103a005142021400140002401502c081413020307030b0b0082152501c240d980742c01d45000c603141410150000e00401c03050100002c42680031950100188582d4003054844085403214200708640005000d0380115558a030740261120482c51040041d03141030f0307058025260f05441403420940d007610305510100248803d40310702c81e100b14008002c080c60020781018030b0580b0711802c00c0e004540c02249005144c00c41940300098141051101503003c034181411510100c0301c0e060000d0000c00300d02820003520001802c10000790b008044404400d0b41c603400c00003400c0c0460721420854008211091100340c1c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 791204550 1250 791203300 791203319
    0x902131503180b06030106210c060906080f0a1e0c0e010c0302060c1b120d0f060b27060c0c1e0a18060906090905061b0a08041a10030b09030301 63
    0xc1c42d45401c0300c90020746643e034100190250144c0d40000d00c0380840c00003c50102c0201c00d498603913152040e51503501c0382c0c6d1540c1040b521081e1901c80d800018000701e0208030000000d0136070540003929900045468041041d90305886618486030485041d56808061145030f88000031140d01c5100b443c1401116000da10000e41d500710250544015201c00120410320404054256911007c07000668a0b42034004280304900e400c0031503240d441d9420401040900d20082c45200183e6070303040c0d1107070704004403402801c0441751001400748081e005419080c43c030303589100184ca200c0102e9802421000d212000b4007407480c43c611072034085e2803c030602c41081981d0b0b42c880a001e0b24100440700201000480410300580712070b601554005280c00404602e400e010703003118103414001c1048501c43e8845a040b10050f010f2418200507034481800b1401050780b09500c66501709000e013200f0000b0403002c0603819001c08069400c00c0c03000d000c1103820800c200c8030310b890b030f50701280c0c0300051030840d890a094503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 791205800 1250 791204550 791204591
    0xc031b011803030209060d0c0203030a0c0215010311011701230301020c0d23120106080601020c2b1b0f1a04030609081603210612030302130902131503 66
    0x4060513008145510b41e0f84034138003614182e00c2d140c00c050088400e141c070082d40780d1f4015145000c0c51070814034a40c105500000319241c56102508490340070368030319100c0c285901e20800748681040901c2119050000644d4204d0b030217401707514017260b580c1940e142800441c00b64040900d0090b4010b0000102c00040881e0000070512a8102070b143e4010094200d174411907070742d0307121010010114519020101403000f0a0507036419480318561611004010f90341e50143d000382690100c00602d51291003080702c540e0390140403024108218103d095514041101200704106c07981540d5079804020ba044007402400c002c1822202640181e50018203044080c402c9010150009840d550350a04200480c4200c8130314404c605c090340320007141d51a000304249104405082006400e6011400104080c0301e11000ca4603500f80749002214140d03426806900010500450400c09610004050f41c0e140010619003026406107480f01d801e049034940b5100c4000d080134205403414000790301c1641c00c8000c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 791207050 1250 791205800 791205803
    0xd03060803090121090308070e0103052e1205150610081b27010e060f04030b15030d0e10050f09090c0c0d0207030c06170c0304060b04020c031b0118 65
    0x12032242500d148500308034604d4060305031a0b1a10300300361101495844403c00380600b107103644603804044104011130a894060703840001c119100e020911242203402c40310300300031500020150089039540c1d02843c400e03a80f2101a102c6d41c1001c0340c0b0169035a112507100e41e114038104c8014106150701c110052203428003d10740c070480000c44681001040341c2c14107580c0c1800713008440307841c0c0c0f1821004103d0003000b0b440d00580407400045500089140c10000e461010910300780113400c191441e2a034a00040c00600800e840342c0304c0f0300b25101c1680742400820309283c80c9440d2400ca2240341024170900005840e00841009801d004205408100c01c0072103404440856180c00661100200f0050501ca1920520b01910a0b1007004101c550040703200d000700c9004107c9940c0e10759443c0d2040e1841c203040044454500201c8000400780414500074580042c0110350001e01e0f858050085400c80c0c0c090072107003056900103d440c90744566070709284024011003070000c1c4403659140c58101c8888210000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 791208300 1250 791207050 791207057
    0x2011812050106090c0c11040615050c01060801020a14090a050d12080f06010915090e09010f0b060c030a14090618040e0c03030f091305130b09032502041410080d030608030901 77
    0xc1047c4650b100d1b08030602400e00030705220b5001c3d04400c1c001d04594810340411849509008000903064410310940c1c2281e42951255086208017003104011030b40301c0c0f039401340e126598107030100d610785441444030511481081d404140f104005406010702d14002d03e08d100f0b100c820810800140d0b4401503807021501303950524500106c401c1ca0580d0700c410300e6041020880030070350401803115015000090b40401c081401c0005405a0090082d18030502401c0031031503000f00031580d8014801c1c3d22728004080030b198180d003407a010f0000107402d46d002c41c1280603030001c807800d210250b00d01885400700c40040c500c010100c00340300350b02294980c012103c21101201c004508682651141003d00307071110a201d0082100d441c010a4010318a040e44034241c5e5501030329800144064000402c5604810400d000c4034003522a12580e00b51100c0803040898005890b0480f05540c1d221101b580d034042c2e40c40844480c0c045040c05032039490f10311107030440000c0608005007040011001300c00c45110750030a02c0d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 791209550 1250 791208300 791208323
    0xa02010c0303290a050324070903061e24060809070f0f03051203040b06040b060904090b04050c04020f0d0b01140d020304030e040504021c02011812050106090c0c 71
    0x14240d008003410f0160240918100e4644950b0200040c00b00c0000b603000c4071203080301c546072070502d59a00012980c0e403901c4280d000030f0044000c039400901c2c0d03000c2d5140c07404203c0103840369509015140e101248008400380101c800c203641c40303d802806210005035411412009041109807d540d031140708200510082d040400c8500c2014030104024020004000034090b40c0e42d0542d0ba01c4440c2c501c0280e809016108400136498110000c49000315000b0007110701941300c44003003000600040c0c0b44294001c004004410258440d802900310240c007410580c0c0c01442d09041003818002c202c5400383c8114410880b02000360340090540d4682d40351005e00051310700c50791005951070840901018004034001c501c0e54422041ca4008600c101d10964640441110b5a0140800d80d02c06413030080d4015141c1115418012910090050032401458100180030700d240860490000a030003c0449842c40076120b810300009004003070041250340c40401c040001c180004000c04040ba000408400052 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 791210800 1250 791209550 791209553
    0xf0c030e0a0e10170318030c150d27030e03160f090f0b09041203060e0a06140f09011208040308270915060d110d0c0816020a02010c 58
    0xd80081015a4000d4a09070007941c4980700040450403c6600344010340d014580810462440030000c0c203400d60041c001c609044001c5107140392048403007092034151144000d0102da0f40d407a4030b84c061000c0e10100030300307580b00b04000d1424180c402c4404064041d03000450a1100301e100301c10310300300e425010b05c3d00600661074240064100711084401d81c0910010240c0800c4480254440d5000c540d02c40c00104000c224180b15a000d0b940d5000380141c0c0000e040002501040713115009000703140e0380b45000a00940c80b0700c882411b0542c00d840c0a00100d039284024010f2051042e41e10714104000c58618454180d42000a00341e040140901e0b1700030314200702d60208000d04a07041c3d4025642c0325440c60388400100380d078000303d05003d050000040020036803100d02800c06410fa580918622005100041c024005000e001d034420001e4492081d5140107181003410300c1d2014001c1c6814128020540014001004018a0000c5c04540496032004000c04890b41c00103a60140f899080c24440b0035000316 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 791212050 1250 791210800 791210807
    0xf0a0b010201020f07320a081612020d09090908041517070305060a050904050c0618030f0a02041d0d120603140606030105011a0f0c07030c030f0210030207030f0c03 72
    0x140440885106400310b800020010070000207026a07000e41444413095245118003441c046d12107141116580001003000301085030f920090610f0009000850518031030f5036103003038800140c0d08070f2600607080000801102640510f240300148129201071140d003d66032941120b900c01c9114041d40c1c04282a003040c03040c2d011f075038481d90141c0c100c9010102303072034016406070180608450043c41034400d102c003ca118604100020301442e0088002c00d01c180158060100d40d90016241a681016152811400356010064562105036403405400c0302c400301d20500003543c042c1010342241000785a000100e032100060f6044000c12030746864158029154150030060541c1c1e0000b40001d04903c80c0341c000e2b1200003501e540190303003d400800c0903a0743d441486801e0002e0381007603400f40c030f8100540080360302044080d1403400240c50548542c907076203582e01c880da9002c541c41201c800d03103035a40a005500d461980811550503d003001d51510080b076a00602c85081c0e400c1103000c0c8004440d11000b03141c070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 791213300 1250 791212050 791212057
    0x5060a060509132a0807110d0815040905010e0c0a18020d15080109030f03020c0703030521190c0e06030f09070e011d01050f010e06030703020f04090e060702060f0a0b01020102 77
    0x916002480c4c4801004440061000d841440720041001140070410f42d0f8801c803144411083c54801034608a00d040750708a440c0c1602800c903c4041c222a5039403541c960703462080d8540d2504c0f51000285e88540f032003032581042c1200c00564419001e00104000c03580c82d4840941c84140295001603640c107546114400410010200c50b070b0405401e072012aa20038150700103810b881c00380c0c40710b174509501c40780120285e200320f2030f0200040c0c10010007040044d0184010b81204540c0b5100c01307a00300034496011034164400c4032400e01304051a0144142616a03100d01c202103000da142444019226402080302c074030000e8400c1c84c0100d0400d001030348144003888000080c0480500c2000f4950356001d605484040685840281030420320000406103414501c0f46d06009042c2c54050391480503500300300517904020805810316401300201c544911410000b0009480714010001d04c00d01415011894003100425807001d55004030140005e41c1c40e94803107a40d0007441c55201060388100900100e01a01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 791214550 1250 791213300 791213321
    0x907050c19060207200a06111c020703212a02030a0804051203090901060c0203072d3203010908070609140312070c030e03150a05060a06050913 63
    0x6001031000c0100700b0b05030018800c003409240030060840c03060b142036520b00c0d19500e0b2290f0222a00504004580c001c000c56041150004203507504056035140b40b03009100309010301c03001a08621000d0003004103640288801c40f60420000c400d002c0c805101510503605009550080c440da0107103071076100207160625130308560150959140351020315101c0c3d0701d50018003480e0b01ca001e4032072020722b80001c000255164904020a02800e903403802c482612980780460099826024524010031031016201c801201c1d050380a600700c21040c4041400e070380080c91900031107007480302800c681c0001c09009800d4590600c1c20326078554040102c000007801400e035094020038240e0081403400600010b68000c200c2c1d40c0c02415000303400707801000d445031280716016071107094001c030381c000c140914850108507050754440e0601040454000c000a403800c98018031107030b0080e2000c810400805004d024154000c034003660b0480c107083c100000a45140a80c9550310b0141c88450903000c181c0d0442d4000404c0300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 791215800 1250 791214550 791214583
    0x70906170a32010f080c060306060915070b1e040201020a0b0a1b050903010c0302071211011503060219140f1309060605180a061209170307020d02060108030403020907050c 75
    0x4001d002c40050301c04070244900d049642d00b0740c0b000103005001046026035464020003043c41c650351101003240c3c54000c0284150861850503015410500b60740c001c150650095100340c0407440c02a01e01d51562204c0710000c0c00801e01403050000603600042c100ca15654881400000c582d05e05211600610003c004078030502d00d05018150b51580041c02082d10100c1a402446074031040315042d0280e200b1240c0080c403003001c503030b20b2080141c8640440c00b00c1c20007600020410345007203844894201050340040d5600ca03400a141c607803480b590108036200742e2450404040101180400070b41500404e00300b0001a41c001134424000d0003080c003860f010f0952104200070b8503032100b100074582d40240c3c403543e00354240d40e0340780709180c50300c01c405074201c1c2d800303035503064019040c103504101034035000720115000c2500c50fa0305c015a02000f0040c40c82400164010300d544011000001c1c54881c0613484080306070420030081c405600c0743c2e001c844c1d012601e403d01d02d0341c503207402521a107040550005003065 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 791217050 1250 791215800 791215871
    0xb071809181209080c060c1f06080312151f0c050a050f03070512090a03021c0f030e0f1804060510030c03051506030d020c01030509010f02070803070906170a 69
    0x3500d40010f00d04058641c08005c840340145030b4400d00030103100b08450740180703078401c40704070344204c151086c030320042c00340d0030340c04209640d5810482d0700d15080841401c0c0769401c1a0108020841e400c03180b60b5070401c00320b401641d003400e4140c0c4e9141441200300101c003003102c0074420100380103003007101c503401c1940441111204001c10342461707140e4004001c00c58145c05443c19003030f400c4905405641440000900141081d40381d9420031820002d00c041600e06028031311642000b00340c01c507420408a81c0a0303152200c000e00c81c0402c200d01180703954071440c0301d01c001003007018060b004c503c0c1a603032140e0312000c002000d80b985055500c0b11000ba40c0000c056442c046408000c00c44086688681000881c4c1c8040146e1030780810103444801c1d500d084070040e4080c00e0b0b00e468540c0b0070f400980d040303103101c000040c01c000d1b1104042d082c4d9102e40c0003542c441c4400020f020419030b2000048004001e20324021040003502d1b0b0045514240280420031503540352100034408076845401c40e090008204203c484 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 791218300 1250 791217050 791217083
    0xb0f0714040b04030215122a0c0607032702061605061602010f062d15050403020a060201180b060f060c1506010905060409050c070c060c0b07180918 65
    0x3e03401804100d0052080042450f01017400d84240d030b070001000303141c055444e9681c00c0ca000d5a813503501140a41c003070700c0c6100300304d45800e210300501074100040050000c900c0d03d031070050103648400203003040c02c0c000b14000c00c03148014101400203159041f140c01e50f6511240c0c0090454884007000a441406294244500340b5034031040c4070111200ba800138892100040062002c44402d803051043e404e121500c41d2840e40d1203842001c40078070303042083d010300c151101d030141e11041c016070321000413600016042c0203618001c00054010a1140300a03c1800102d001d035055000e24540018444402480412800d5030380305640d100300040034013225100d282d03140d401c659400071a07440d150120011804190b007944202d411106a4001070040c9203414505068407008041c01000324080030401e01200c400102e0407a10340e40102119694100d0114071801c0c45694024013900caa020b001d4100320000c0100d1040844500319607000700300043d2104240c2070302d1006103d140b0300034010000000d0404 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 791219550 1250 791218300 791218319
    0x40e040308061804020609041b050406200304050d11130603061d0c0111070f080d0207080102130b0304063308011e09020d060207060b040e0a0b0f071404 67
    0x510940c000d40e5100440d4850038107111101c01040c03d141c020494150014025081040090025034000b4000040100d0701d211186440d258082e4080b0004600150401040b42d206140345507645007820b085142c0f2401e000c00300d03603a10580c03281c64011a4051070701c101340142c0c2000000300b12000b1305941c254481482e040c0c1c1c010302d460700040301d0311403609500c540001e50f20b4210350b0341c401e03130f0300d0007400356015090040d1141c11501084590511a820011035015500c1078118010b01003030303004105c2c601016001a080a01d03e42103a24113a2051180454101c48547c40504648110409a541e9200c030b0a1880242564004030400c42c004e4038000e01c1c60f0300007454844a00c40040c00000340c5991100001d60994484411480c017494000d1101d001c1c1007060343c03207941013a200810000c8080003a50701d0509a8008100560309035603601121509820240100b5642d0032051025040003065980d89901a12014194403c003001703941c005032909004001c0707140103513101c54401f92641d50b11307184032 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 791220800 1250 791219550 791219579
    0x708040c23010906020105070e060c0a051b010305070f21020c06090d020105060a14060a0c0212030405090606030403170601090503030d0203011805040510090f0b15030c030d0e0d06060b04 82
    0x7240041c00154000991500c184035aa0150650395242c00c1c1d090700520412001f0f802c0800ea24585001c0c903500400040d10400004400b0b038110100f20440c10700f460b0000d000c48000628000a205030782e012000750a03030242070b980c1c0350f100d40002500e030711280004020081c0a00066802940301d01c4081c0074036040006141c040401c900d60090050ba96004140644003000d44904008824001a10062480c1c070b00042d101000303051408000c0c901182c1c00140500404e5481c0c40b01e07a4200203014000d03403e0182c0d42550001080d501c0e00d10b103007841d940c0100725009d02d6480e40419881d50003c10820f80c42811801d0050030020100c80e1584202c110090081d4402e102d106140442881050085886406203910598004d03010f403803040440070360314010b4034010001321109080051a040010f90446449004182200300d140264032840107040c5814582d11103240b280d07100c0c840342c405035544140307983e0804800307507421011040149050400b0300107a81003011030420110300415840140200b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 791222050 1250 791220800 791220869
    0xe040c0e0c220b0406050706090506010f09052404020304170309010c1106090c120a08120a0b121b12010903030e06071803110105120403031b08010e0708040c 69
    0x614500d00b800100c0c220b503007190384100c01a500060008000031401030016103000e80c01482d0115282c0c6c42c56890500f0000c09821200c80d5410180b01440003541c9889260382c0f00d040105141e007406408800300010301030340d100c864030072900040060100b0542036840c1c0e9400384c92101c2661a1f0502c1c03521540a010140240400109500780c1c6a00c0d280001507545d02510180018108000031a02482a030803040d090200e081d10445541400003040310f0001c00c0b44542c160702c008202d040c03c48000d820360303a04805451040c405010600340f03080010030701d8240d404172911804584030300c40c804210850304074851850994030b0320300c0340b20030b25425810542d1150380301c2c001d603440d50761600c10030344259403c01d689080701e07840200b00b4000540c1c0300a40d11640740050600d17501307001c807400b441e540300b4800301c808400082c0c5074601074165828440c6008403614650038400d03e0fa605194081c0304514004018404000d07405000c5010703c00005040744c040d040800074200c0e0ba8076100c2440700310703620f02c659 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 791223300 1250 791222050 791222077
    0x6070c0801021902120304171e04060e04020702010e0405060d05060408071e1a1005040213031709030307020411070507060e0907090b1c0f060305060a0e070f0e040c0e0c 74
    0x800703501c03d52001c80c0d550030002a070481303541075403103d490300d8800c0f080550800c901c1580401074100034a81c84459004028186200160baa87c20814020005c40c0e0b10f0500c20b0043c2c1c018410040141e030801c42e98030a022050754002150f03620711000403400551090081c08074010300c3c007408144001b080052074000d010780b06148491b1200b0300e841030100e0ba0908087d0102c4903100c4400c020302c00d0165070a801c00c4103d0082e0010321b4580f0000b50403640200c113205001d00710144100100038401c600c6c0700032079000b641820305100c00140441d13224440d042c0c0c001e110319070340c2403001200c2c01814195482c0b103030024101c0e840c85495510242180c0440d98142d41308299500005000610960f900001da4803807503c99414000f11040c41030039920f030581c40300222500d5111204105401d88174080c01107000d40010640c0e420b0041c104c0086031006038840510350007040b0140481c040b10125682210500040e6055650317a030705260300c800c449500809140360307c078003e101500c104a0050b148100d610312 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 791224550 1250 791223300 791223337
    0x503120c101e2a110a0b060409081b150702071802071721060d0209090c370806010608070516030905090f04033e07031502030907090b06070c080102 65
    0x3c005071884203840b003500303d4a0f4000300000c800186070b4041d03c1c1e003010000d480800d442000e90358084c000d4006029803090808050b01d41e090a8804020b001701107c01c1c8035940d192424103507c000d440701818043d6628100c140098002e2500c043d0307040360000d0307421041241c94822107485543d01d607404107111409034104018240e03c500070512034140195801020307900c00762380f103600780150700c08010440c0885004e440260030581c0c03204c0000d1200524101001c400c0c20584694880d6118510000801c004001540521074807000241d524152505070504181e180d0710404120f0307982c89103082181c65012010748a000b003541000c107400903114120bc02e00142c3d84c65a04141100b0342c11900a000607032044c0027003641020040a08a0002504200d101880604240600103c8201907900e1981c0d00924080040c04407407840c0e0340a940d0303000c02c02e61460030300d106c01d00e6440340c2c10b001c0c0b04100f0383d44401c2468103650380341c12107000071780c0056451100b981da0581c6c60300075006803446400c407a0045 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 791225800 1250 791224550 791224631
    0x509010f0905060315011e0305010609060507050304061404030f030207051518040f0b0901081b06030106050a1b2915010801030609030c0506100503120c101e 69
    0x2201c4034019190080c20705410340d030f5014100031121040215a034140001c1717100d4054410368120780000394941036103011405524002008006d510242e0100040080a0210400003000801160110b03012440c0039503011054a80300307141440b5641c4020240064a042102010340214044007155001c607043d9205004c0c9141e90f50003841208044a00a0070344da00e000d0141c03400d540b00c1001030041060003d02c0c5050031000c0341242100303810000403030b030020141100e02217940c01c006600407000d0321100e0442d4544032002d040741c0140b0f0b000c13030306212910604c0d90100000c0d0b18400d1240380c00c11900501070301c409001500c1840d500c5040003003070700c00c10002441ca19030035810a10314031040c1c2d140d4529070302c0c580381c0400030484402e0032001c2000d51160340002c80d0040150038028144102c0c0b040c01030385071908252601281c0d0780d40c26420f450030b010780d11881030302141c1c01c92102c01c031000c0400c06807840928240d041102280b0400e0441c600403a01200c521064050039048030b80000e050f6182d10708 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 791227050 1250 791225800 791225807
    0x409090b070f02031b2d01050a020a0504060c1502030c090306010f051503100f06091e231318060f02030105030a14070f0902031617061e040c0509010f 66
    0x100c0700341c016030b04c00c00403408841401d0088006403100c0e00c0c16115a41c0010300c4034422130b150240b483e08400c0d1910040c051018007032203182e404c401c0e0050110324004090340e020313140740290710401e0300703100f1071100c1d030070922500405140f902c4410f50011540c81c41d00e4084840c0c290400500b040c024841c0c03030300101e103405000110038240d400091a0270042007440c250019240e0008207414403d2141a0307000440102d4018446c01a10b8640c40e124022402e010a01e2031321a18460704c4030421128000c20400120f2200d02c0080d1480204154140420300c0302c040b81e0081882071000394824501003c00c1d0091078446002e9103018400c0b1814403904002e160b0074000e0f030100780181545600507081100011700c2c07d0359122240c807004001da4810a0341c480318a00ca01255134030202906800100700701c241880c203d0b026071600d00354104070400c40d0100c52400c80100b0001e00280c02661784d5105106143c80f103031044c400b40c0f88010002d20000c40300010050040d00100c42541c007084044842c070308003902 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 791228300 1250 791227050 791227067
    0x18010225060b01020727063303022a0a0b010e2a0a0320030f040c12030c020402090102030d0e030405010305070f0804020103020a0c06090c03050f030403020913020301060503030409090b07 82
    0x9109140c1011504500c1c0021b0130141c0e540000108280e40340e10014450b080003000c0405401514408810740d420711881c0441412454825410140704104d809110080d50a42c032508245445010b00000c0300201c0d064601002e051022f040f86580d00300002d45003445041c00e510500710068801004501200c0b081b84110142000c6030100d0001d01c55030612030701c680c1c03007100303140017980048c00e0302c0000000d80c80782d0394826564603d10600e8002080180641d04203440010600940b00d840220602e450042c5910b4800d035001b07101e5900054185c0140e80301300181c030b2021910401c201b20484000c6402c03a6264000d118031404213082000052210703005503081944040103848250443c5d580e6030044000350b00c40084442401083e401403404039136035216070380d95144146000d0103000c0c11400c1803890000107421202e0954020401403005850b4440c0c01c0741c100d20f450800d400302d16107034400240541001d4101a80502c00464000380124030360b0000f58403e4011001c5691503100e0708402c888104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 791229550 1250 791228300 791228309
    0x10f0f0e0913080c030904110a020a061e0e1015030c0612060b0309030304060b1f051602030307051c08012403060e0c0d060e0f18010225060b010207 65
    0xe00202046080381812500e15078040201c0180350008003043e640d4000c0d940100d0302c0c0848941c40807424442901b80307441844010140c0584050900700c072048000e584114402c001404261140e42d40c499824405901d40b00409100206001044516036410b90740d00f141e080307550070309061003c0d1080d03100000d25160f0036660131034140d00245040ca90f00761014804280070520ba135a84000020351101a50083c5006003500c20107545e8a0a040c180b00051320f0741251014032684040f4544180c40704542c07010340406800d414116118410102c4050065020310000781d01400009485000c105010440721420005644030010b4810301c000111500d034000d0049000c11aa134007400300c6100c0d040012400020366500e0080741154403000250520307070081c1c410025400b004030b03044040e103129000d5a00544084c05840754103203000110462204805003c0c407000d00011215485172030002c0d01101c1049052064018401e142104000743e01803c1942c20f0ba2032516200320039a0640c0701003080320885 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 791230800 1250 791229550 791229557
    0xb010206151f020c030d030e0d090e060d02030a050a0f031202090303071e02120c01110c0f0103180507030f020f0d0210120b0909010f151203050310090509010605010f0f 74
    0x7030464502d000d82004007020520150b00c01e110703030103106035070401c00e10801041c2a034011480040c0303405002d15000915202c0406d2007a05d1005201d01c07450bd4404980c40310b001c072001c0100302ca990001c28185030041c1000b400a002d084000420f02203525404083c59100f5541d042c801900d4510260884c09400d46c015415001081220301103662401c401059a880c407a0300b0903060403543c00075005102c0c0c4003030709d100c0d40c0103180c0110345982c210b0b05c60800c0b505030801804425040a0014450049032803000d410303d55164480240e1340382e08105000007031340c00306c111144e040c3c032070419801030304180b4812407040c2d10018000c9291708200080540c03982c0e000c0d25160030764402c00000d0b1400d407940001380c52890b94401c0018959a90400301501410051000082c040c0b40b01c40000b0a4500c421510507004c00000810404002e0142c07040303040c1e603050300e001922511101203082170110306501032403101e0709180900203800410751051007216403d0700c9031052a15901d8003a05c0f1910180d0001012 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 791232050 1250 791230800 791230819
    0x2030a020606012a12030c0201090b01031403043606120f020418150506090c220f0b09040e0d051e0904050f1519090c021c030b01020615 60
    0xe501400001d1352000b44800398907416003007408442012000901c05680c241c0c007441c00755068941601c18800e8203680c1b48000d00100c54507854800d84883e040c440145410300801c0d15a0801c1d80a00544000e00400002e00c01010541c1919192a030a0380114254011a81204d804421510b1140100b141c100c2d21021200c81040d484042c061504407205a8000341c80d441d003000840150a00b0655403441f80d890076820101c00d0f2b8040b42154001000c1e41d00526080c428885d4005019042d181c681d5800191907000c0000c6e403110b001184800d83c01070a03c0d48002c000450041014009080440c4082d601040349024908070f0355a00d0303240b211102c011034000c0000010581403c40030407030090181c122a4a07014034000410200c0e20f08461060f61503240f0000c3c0710043c0490840101a4003045905101606011030700c40602d007658800c0c06071040c2d6498004020300e00a002503d540c004a195602c00801b001c0000713400b400c085400b00f0b005000c0c02c0d001a0982201400b1204034410150018a071b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 791233300 1250 791232050 791232061
    0x70812180906011728020a0509061b060f041208010f15030207150912030b061c1d0304080c040603050c040b0a091107030801090b011d150f0a090602030a0206 69
    0x5407010b401d65042026280510040e0412104110f004104081c00d403244100c00f12003080e21008202d503c0340c50349004104c60b0204c15800800e40e400c9400c1240d481d542c5070100d9074507ca484074500d4610500380603a908101105603a1851244034a0044101c41c0c05d60503001000c82d11078100340640724006421403014003220f903420841c0e48070302002d400d0052400c041078a80700d1020a00c1502c1c2c0c05400e0303c40207036070104402d8808a654489150a0501c12583d01500241072805001340a007103110080c880400c080c0e031590080e4148210038035110144009a604440d2694440d0241c2581413080392180035240c240742c840d5000301d0307421401800001106004020150a0700782c8420b43c01440e811000c01c990703065105008070340341901c491a650303503605c0c80c01a2000e481684541501494100e4082c0103036001464220200340c00407141c0d04420f05000011080341c00c0e017254107465400890100100701d00c0ca401400818800d4489655103a41c0d0030080b0703074a115807428400140c204402044 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 791234550 1250 791233300 791233309
    0xc08090108100f26062404020d050a060303090509010308040306050408090d0b040b060102070303051e1b0a030f030506060d05060a09143c0603011e090c06110c0f0d080c07081218 78
    0x1540080d000780054070f44907016442700700390359050b10002000f0b542e80310200101604000b02c90010075058550884642c51502c82000c10b001328170015244a0302c03400080c04100e240b200b19809080f0050641c8024003d60074000c3c01a102180c0c1281d0b100c0c00072011611640c0000b075040c04583d40f558600d4a068400b41c0303400080c1d4818100c01400c01402d01c031020745550130360800e401c003829107001043c412090782401842648091004001c1c036182800f40019921a101203440c031010519001c103180c0c40d04004030303681b03407181d6104c2540c0925010705a940c1070100500c260107821460003150041d00241d49150101c0c04c0d51604491050000c0500101c0142c0903c008d548400f0040000500c24011200c94030185c00004201d198955101c504000304141d41c2441c00282005103441c003888403000e090155038a09404d0101d02c2114035010550750380ea5043d1400341100d920481280d1241c4600c1c04580d40c0d000a8003519005005a40c81940740740d480506907009800c414a07210080103e507400c0c030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 791235800 1250 791234550 791234611
    0x706030213091b020111090906010c030e060d091a0606250206040b0703020d0e10030e010228081f06030504030e150d0b010c08090108100f2606 63
    0x14800107003208000100700386544200091110204101400070040440c02800c46100c1007559070035400030302c0f113243c0d03d445081100740d0113a8207003428840940942400d803130410820030760561219000407090b01c9008140c010828061007240e0400c4403000350f220b1001c85010880b50286c1158080c8003400060342c10b1b0a5940640c0c811144a040340300d0541c01191240c1d003d90084820038100107106420517504005008044180f85040401c080d045400a90322440b4040d0b03010800d5101c0b0006020b003042035044403e00403880003207000c03801182c0354018041141050310000710342048005010242c0803814030890800700745100c2d050a040640507801400041d1058003000903220010046031140e2200605201c45441900d07210174240e904801a0748a000d40d02d07041000b4410101c0c0050171540035582e17072010034241845280c0d00c0680c802c418101aa001060321034200d440002c8c40c0540c595007100f010401c4460300340c008807850401c4d6550000390b60b8603801616000e0a400f0800444180 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 791237050 1250 791235800 791235817
    0x2a060504150609270b0601050307050d020301031401060b03220c0803160b06010e01050d0203131208070e060c1e1e0c0901060c1e0305070f0b0a050a0204050307060302 73
    0x2040d000030100080c00320760041d0402143d050307491880c000203001402d0382203c1c2c4880000d03000c40f903032440c1c0d40d810503011020f072149041c44030110109546174001c0302503449400c4240390441d01da41c0e5038140703004480c80c001c0c0c03990003551070040c02207240c0c00d00400300c81c03140b25250f083d9000800c641446940b580003100301a902902d40c0783d07000c40c044606100420721024100c103032003a001e40c0c5041900c50003201030005814060010381c8204140d8000e016075078444940b41c00141c407599072104100c0580c2d102c1c03400134001a407a216020445070000c0a55006241d070b80d80d4420741c411881c0a01442d4440d8000f02d02013580a241c0940f41e0b02240860318550066600c03c0d60200310f0705903440046402c099145e035100d43c02c202da81da040c81c20082440342c01444d50b8a0480c95060f0207440300d403405241c3d12000000900385003003030414140500d04440f402d941c8050408810585070401c030144000139600b2220450030300000c55225030341c0c0d0080e1801d5410083c00342861500c1c2c11030a60080d441000c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 791238300 1250 791237050 791237063
    0x23030f041208090a0303031506020303271e061902070218060a09150e0609070c03080903091509010206060a080705010518130501080f031603110a060f0c2a060504 71
    0xb203e807541d1207164100c0010b602c641c60200b079914070988085400d6003150030020466000340f0802102c500ca07844e80c2000c1c10344190f5103109002640380b08070b04001c8021003022031650541c8200c214110005907007446100084541c1c051440401590420b0b4440c07400e000c0d41c00b40c0e110b05114506011045c007950041d000901d0001c8003617031051454144c1e107041181546d02c2045d0a0108003007a80d10010341c1e4000c0c421642e059240c50800c0010300a80800800541004444400901500c41c104201d030941507000300804a40c404003600311500390b014540044c0180207090120f156130410748440c40c180d41c080009400264240001181d4582040182c107541074001e0b03502c0505611082407592649000c0500800c40b5814641401d1800101e600001c90a520400581c5440f0360310440e96403d89506280c6a031441d80c034848402e240c031100d0b11300584000c0c906140350440a0b066400f1803070000b06921010014041104042c0c0d000c4010f801201e00c140f40b42005200180d21035004503442441000c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 791239550 1250 791238300 791238307
    0x504090b431205010b0405120604020a030807020a0e0901021b19032f07030204051f0605070609050d030b01022518020403050d081e070c110f0d23030f041208 69
    0x1c0704025100f00ba400280d009070001000d11050034409200030f101c0d45000c0051044c0d01b0941e0114060f840148000b07406560301080750411540c1d0055401c00514000740100b00a0910b140b0300c80c001c5d4040081ca5031040c03003002030840e20341000304484110306a6005075454a80303403074505440e02c0015001c9a0008024024920740e285240b148040d14113941400811410b801d6205120071600003920400500610011b0411a1aa040403200c151507540c5070150700c8103e035107403000103065582401412806040382801040c2d40c103501c1403940e08800d900701d44022440d2500a9140700b00c2d0078018010015070b12050044080e45d00b102c401040c0340d48001031502c0d98a444035818000c000c4204400100718109115084404804a40d00f0014050300c400c2d443c100307100050100d2070b460034014210484010290010749e100c905240c19428040e12185400c4040d00d00540c0b0701013000e00383c40320344c10201d001805c40f100c000300340d0316480c54000c01e982c0361278181414000641c0552000f11072068042 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 791240800 1250 791239550 791239577
    0x61d0d0807032a0302070f050102190f030e0d060b130b030304060e0310051f060e010c1b080f010f140708010e18030a0e01200303070311040504090b43 66
    0x20324034510314040d5010300a1b02e400c0410b40090310b900b17684450b045600c5000101c2407a115850301400190f0301c403800d9000c0c00d091b071030244d5940c03042071121035020340341034421400c1c0440d80e00580036214088940c0d1102101c0b04940f14122124100e4903501a0f10501090005501421321100c0c0030384003c080b102f520300030000c0c440665108545062000b640316403440d903441c42900d13202010384641d0400c41300a44142000a281b6588090041c1ca82c20740042050400b245141709400500b4003032055840940318040824007a00c0702030001c4c841d880c50105450031584504076450301500c401c4e5070b040315a900e0b00c0113103c001900a004c5a0080513814410b030646801000280385111140e2541c0c0b002c0a481e20001d0000c8040c10511200f42800a21014021102000303c4e6449206410300050740f0802e101c0101540c0516007000343c0040c035011962041c03007140850340b442911403a048032080c40071140030360a4500b0f04048000704400240b0030001103080c081e9501d02c00281e51401005a4415 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 791242050 1250 791240800 791240867
    0xf05073b030d0f08010602030f2a161e1404020a02160e010302180f01060f0309050a050a0605090d09300b070311090306010504090503090a061d0d080703 67
    0x682c031501d000b0880800454a071a5041000c03180140840d0014504010900c01c0400c0e0610403150201c00f0202e2140c0c3c1c0c40200070f0003010440a01d0880300441d0310100149501c180403d4442c02400c10652000300c012400c0d403424000d580903503e100240c0d00b5680c8c0c03038800780000723504084003944c250f00604041c154000e0090030240c005040b81c00e800c0b61030b545140180300c0190a021204d0186219800410200406030040541100c60a140c10564104180000c4008025011009089000340000c8030144800000c428101d540641c0003000617855000344941e440da00d14440c200450000441040141c2401103000c4c400c01c001031810b0070502803c0c480400710030390400e00b03c0c1d600f0785041c01d102c0745035403501c203404442c8800380d40390b0710385414840001d94400052144501c1a504c1d03800460030440d003402690a5408082d2103901032540341d4038058000d0040040040351001841400b03040361070480d0391030f124142c00255003854103d29882c21900d072000900408030182100c45010400c204 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 791243300 1250 791242050 791242063
    0x170d050910030243030e0d0203030d0207050303061f020d03090c0f320d0f0f170403110109140f03011b020c010806040c0f120e0703060f05073b03 64
    0x30b68a091325101c000b9081e00c07503804048803804000b4800300005100009401c040d19121000044441c6588000c031840041d141d80700740078044110302d00101d03000e070801000101550040341c080700e81000c4103404144500d001383d2803080c40001a8095000445258003960117480d01307500072001403078001d4840c80300b482c6c244c105a000c0c0e480d00e8194803030340600c800d07007072844165244101c10710310307040d00c2c0c680009881c12039504000e0060700c032100c0d80d41c1c10041c00764a11814145e0048011070041001e0b00540880d40262100b6107081000c041e41003500e6105d041444181c82038200e008000460190a100e00003904482a0381c143d036a07095401c1003c0c3c5455011110024070b0ba00411915200b42d000600c03548000c0c102900031410084501c4600350040c82900c1003030564900844514034400908000c1c00c14800b58007414000d54802006000054000c0018140311440600180c0c68084040342d1140702c1680b0021903400d550460a03000050380002d60150703412901a081400032080020700304103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 791244550 1250 791243300 791243347
    0xd12061d010302030115052b120806012601180207020d061a0604031110021501140a0b03060d141f0b0301050f01080303040204021e030a06170d0509100302 68
    0x2540d8000420440c5801d014684910000a00c00131038907203094003044401d904d201001600e03140d081d0345041403030441080d0f4049076030055550f034050320004002401c4020103a40c5203001818400c1c000328401085080031000b200c02c400c0b03525042e840d010300c05070107603505000c92420540800107040540d0700c0248840c0400d02603400040c0f41c0000301d4140100461291020b401581c041c0002c00215131341e20066000c401065400c1b04108800150880c20501d1000100d44600307003600020070900c162101035040d4540079150001607546031282c0034200c0c001124042e610109000354940041d5070141180b80114007041101c481106181d08021146c81d411448d0014590320140360090785030034024150000004600da071410b50400298940301d210081001c2e02443d00040c100100c201c40c0c1e0700e4894191504010182c40b41440d42c80354014181c01c0c4a00e841010000c45c0c91441901c004c07403100c0d2030302038030740301c00303160a54407c01c1c000c03485880c41c6070308107141d401d00c040c0c0545600c2464031041c0c0c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 791245800 1250 791244550 791244599
    0x10e031b010207120209060d06060b0406050d0c0c0f110310020406050d180c0e090a0b0f04051b0a0501080901200c06161704050f0d20030c0d1206 64
    0x1805040c002482c10040741c2c010161103078155020700151720307031605898100c1c00951b90710490711400d09180e0054840380d4403c2c10000c4001400045456001e4080c0c074110b889080d0500600c0780c0c889040360303107141166000d44082c20f4034481400042402501c0102d610b80170b0251044551440b00a1f0100d81180d44180041140000c800b19984410f200d48820f030400c02d83d040b103807039426480c3d9511071182c0e40520b100c514043c030042282e040c000c0007140140c50703105240c9000b620b49440c0035010308205603012100f07403280c0c020601590341000c2c8168080c142c040d0000210320300c1c0000450704068003405081d401c0d50307100c00302c00045102824a80945141d4014195030300320f100c004a00e042002031007122201c266000c84000941c0c8001526400b03080000d8818003030712142050360a082d9a240004254030508642c01101508412010321248850980c4021060310640950302d80c41a10307528855074100d5400501c90301c1c001c1403a50300c0311429040006045842d00260a0740085801020f0940c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 791247050 1250 791245800 791245843
    0x90b0112031809062c0f090a060513060e010605090c0d0b030a05030301030b071806030e03090901091a1e010c050a0803040501062310051e0304060c08010e0c0a0c02010e03 75
    0x69101100090894401001405420f0002c80c005c60820020241198040301001c00105000401c00c0150301c10907a00140c04001500b4002402c0300c060107001c4044400a040000c40e010202d0103201e00d900703c900180c80000f07541e6810445054980c801e1820301038550f03980a41d12101e40f0204181c0c0b4000307110320700075540c039411800c00000d036202c010701417010000b41100e40780d005842c11024008440d25403d021442d81c41881e102c3d42540034104250303400150350000003c1001894000c030440704c400880c00740001d402d403002e0002c01480012a01c1a00340340d05c4482101c2d501c0b580d40400304a010f001600d0000c4000d640b8411b85030300684007070715a40c2d1160340920007008078401e6081200d2120740244d0f81d00302c2030b030046a8039005120000052000c00300b024881000150300114203c0300780c1c030220350343e45010700c0d1060003460381c0e002e43d4001828960010815a114112190013844072940309130070003c00c850200c41c1c88156240403410803807045500d021326203042200401d0090700114a03400e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 791248300 1250 791247050 791247059
    0xc05070b030a05091612021f08071103041217040f0608090615010f0f020c0301020a020a05060109020702010507061505060a081b1908060a030804030b19090b011203180906 75
    0x942d400a0400b940c00e8010b200c0501703a01c420417150508071140c0c40e250703644203c0b950000500224a12217010004080b0402490307581c0c3e80501506d21680190301d0b15581c0a0310a15050394074001c07801200311040c5600c9002d000724100a01606000e6800034540b440c281e2640360381d044408507540305001041401040c80b160f58410300800e54400b9400100307405e00208040002c1403181042112804c1c00000444071181d42d1091090ba080584054020355656401e030000954403045000c0c180e0f0680900c0d070000c19030306014001c407003019405a544a042100f00d441d01c000403e4004803107114108010000501c9071507034406001c1c091000d45a01c0d10360311301802ea2402203881c00003012000d1200f046521844100750302005c1e0300304114604541c2c0d40d86d0700008136a801055401c05021000040303000410041d4074103056214607c5c1081c00c3d145495400070302d00036161094001040d5481c4100140320303c2180b0785041400703d01902c0c4c1181802002640310a000545820032904245c13030303510501 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 791249550 1250 791248300 791248321
    0x906090c1214030324040b091e1f0626100806090105010612020c0708120c1207020d02060a0c0f0c090b03030906070f02030a080d2c070b0a0c05070b03 66
    0x944400010b806035265142c98003d600d00c0c011101a800c58105444010010079241c952081414100103483e00400e81440d14106122080f0b000180b0644070725500000c0e0461800395841c0e80e5181e041c92403402d514107100c01910f40209840400d01c03009030f07901d00b04c3c1c0c001080110041c05221980030000050781000238070f60600d0fa000700200526810b1600400100e540301038235003030510078071100585840c0300d0780300f10b4108440b03070348504054454902d86034940c491240041030500809000c0780d0314174400c1140581c4038024a4800ba510610a4660790050b0400304000c00303107811140340c942034804059850307241420710b1000c2035800313070790101c41400640e106102d01d0003865003c60045003005a40000900c4074841e41500130854100103803088115141000200402d82d07122000c15100d000a882420003003100381113800101074400300361403403c3d51880e69810404804805003842904110b1134540300e43c0b110110f2410050540071b91000700f0350502c40700001c0c00b84181555a81e0902d0642003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 791250800 1250 791249550 791249573
    0x1e0c02010207111309022d0a030302032706210702150412050c061906151e02030c030d0614010e0607030807020114090d080a1e0906090c12 61
    0x1096a1042080c940402d900310550001c84008442e03151043d8014840e01010385142c0030b0094000382c5080a80080d00c4003c8804004e5100b4416413a66180601080201c0103c46100c05005a0000c000142910351103240071280341c032800800144400745900402e80603440207003200380c9440403480088420925020580d0880302610090651076010343c51040403101c0a40010052840144910401e078010400d4590007074050341515440d14000207413880d40300d91401881c550600d03101020500003845601104002844d55441280d40d062603080311040c20300c1c0d200070f01035102c1807100d0402680c04100600b40a00c0c00c0c40003042141c40c0000100b0130f1900b84521b01c0c1444801030740c1ca030b41c2da102c0f00c09a40007150145421003803602d482130168014143c6100ca904041d807000c04003c1c510100007605003a1040c1e503900e118407642ca0143e180b048074400004020005881c00084c0742c0d021a58002810003401030a0004030030314650307a41420030340b95a100814804181940609200c000d4002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 791252050 1250 791250800 791250821
    0x1508030d15062025080c010302030103080f07020a0b0c0a050c0d02010f0f03140420010212041e0b0a020c03072c040602070b010306021902010204051503070c061e 71
    0x200c41c8690400300d010b0481822190343c50882da061940007030b4001c0d01040f04143c034001c00a000ea981103640e01424607224203901445d8114480c000c074102440d440b910841c1e040700c2c0c00c60000d50502c400f9404040300da90194805903030203004040c0c0411180380e800e00801d40d41d92900010318000c0a07030319000b418107601340d034201d204041801c0074401603604840a1100b0071306030300c1d205c5200882810181d00425101995a051004001c100803c1244041d00c141140340492001c1e000904058012a40c41400141040040d04203100400440380c0324003180200381c1c0c00310303d06000d40b0340319a0442e01036003040341e410005034095525070075030f03040c18024180900240e0400101103994105448041e000410f82e1078042d851140c002014058a58161407900394000c441c031445503981d06044000c1c0d0090b07400540045460500391516a005100300c508030b0301c001e041e0410b0113079a21003800c0b8070b0700000c0980b03003802044900480000c0d0184905e44080b0000e0391489001c6120400c0c440c11601061807 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 791253300 1250 791252050 791252081
    0x1051f0f050d02090912070524071707030b09040b01060305090d02060408030a0204030204090f02030c0103060f030f11060d061a04061b2d0213020a09090c02011508030d 74
    0x900154540c003405201c2c403901036a0944880d00c41011035071030a100f41200010b081d80100b1102c00300400030480340300c00d4590b122410300340c18804018030305a00c025220100424111525010500d24001040394046814140007444012080100384614402c80c2c0c12a1003981800c018800c40ba0980b0503c0c1e0407008420080010181d0124065a10382010b040a0008400440000c1d680001c0303404980c051607020344203014502051402050768410360780100e200e4010390200f03900c03652180c41070008480880c0d00c20030401c0c0c65038031103100d00e0300c400c141560550310303546110209840d0302000f4911203c00060010360f00e40340044502220b03291a81c1c0c40031090040100b0011a54803110241d0364850320400459120442c0c9050101d080451300403c0700455070400300d0000d80209030500c1d550600a45441c000780c03403c4180c0b80c04920541001d10041204408244a9010181c2c40046201c1590000007254210300000d00e00702d000c503902440082c0e00004402c0c98564480c0900d002d001305150 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 791254550 1250 791253300 791253329
    0x405030613081602030a0f05030c06011401050403170906030c030a0605030105060901171501060215010503011b0c110303030a0903030b04051501050702060d0e010203161718010e01051f 81
    0xb941c0152500c141400031a1440001844500b5580c01740314041c0b00d40c1d400811110040200d00d003e83e20794104240310401c40c00b524000040d00050f0308000203042005a58540c5000d06654400b40d00d008481c00c914071404050081c40710740d880d2070b001140a45281d20710341e600c0b841d10300180720965285400485c000c1e410101070100076100e088202d81552020300f018070102c00d0b41c00c41a46804400070f01c1162881c03c2500000d081074002c00d0705400c0852000b9030b84916a200c10a041c2a100f00800e1070224902080542d208544100301007000c4030300c00c02c1700c01c00000c0610000f0b8a90782043d10b145800ca565804440c0c20190184905211008150b4040c0510b06d004807a11950020070b06d8058140140024018115952001151400100c3d200b041090180c2124144e0003500111340090a80021420080046024010a1211100440203a03409503900c25082e0789500038540070520540d01e48080d118244000c0c056681b00382d85e52041800c003c0085040301c050315444d03900c4030740312101e8007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 791255800 1250 791254550 791254553
    0xf13062a0803040f03110114090f030f07081b0a050309011b0f080d140103120206070203070c500a140402070206041703130614070f0303060801110405030613 69
    0x200241c0e540a9001001e508403202c00b400c0036542c2d03011006c90520103502e00a0360822507440c440c1c1c0c050191145004940b54810f60300a1542d99110711004510300307600c180300307040015079148000d00c1415100f5650300c0e8a03a000c1c1c490f40b4907001440340308490f16080455848103950f07100d1001040413002c0f49901041100350b45607044a5001e5010162481d1400200c0a0f034ac1451508601040360760071403420280d40e52410070134454135a4910103c01801392030049600548000250790f41d280c0c00070748210425280c0300c098003a1100440c1e074050003554402c0580030355050311409000360300c240301da011041d814076400705004c60365459a45100e03600d00380f03081c0081c82d030104036a6040003054600594500c01d170700006a9502880c2d100a01d030345841000300607644008000f825042421881c1030182c641c0f1102c00b80d40000d803000078481101d80a216000220758030341c109540c200c2c0a4140010890b40340d80c0d40303602b91580c480300e0700614000050104082d08007000842c2d800040c2d80091916030156 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 791257050 1250 791255800 791255813
    0x1050a0c050d0c0e1504031211060a0b0d08030106020d0917190c240e040207020d03080403030e06150307170c0d0c150e090601020c0907050f13062a 65
    0x100312041e50040c0ea42e03400d00000c02c1c0281d5215069280082c9407043c1030400c0c2d00f107005c86900c1400308440091800c2146885680500e01101c0e44680c500003a04036966000340c443e0013001080c1341a9408401c02e80d0503c013042120005502900141e40540060b040c10840a13042400340c2d44101c00700702d0f1110002d5880c4101050390718589502580c4a05424100e09100c5010030a03070300700800d254608094031012980c0c9841c0c0c60744036480c03030b1101004502204200401c9000c1c02e500650030007042440c400010b1f104041d1030758094401c0c01c0001d05c0c161030051552400504607040728426810021001c813515007080313080001c1c0810b0180b0440e01c00004031641e12070300542c6070280203004038524141040010003841c009401003440e121410101c2007030003008000c01c000d40c24006d426030b001145c6254070200f0085c100140180c90075a25485d026400c80701030380038a442c14102c48003448615012010840c10074024031183d540c003005005814180001c048900301c117100c42a80100f00080024407 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 791258300 1250 791257050 791257057
    0x1302072303180411042c01030b06060304211107080f100902010c1202030406031404030806090c070c0b03010e091903050f0408010212150a080a060c03140a090501050a0c05 75
    0x20480142c0384840c000c001040103003000c0c003030301c1502c4440800c01181c59444030b5181c0465a00195046501400480f843c1416400a00001e8000300e0700780d00190107070a04500031600148694800c00340741c43c0401345a415250500b03481e10015a8103400005400c0c0208500c0002d0200c0c0e0001d00b44100b10f14141d142d54044400040c004240c50f890110290380c05030444900003508035007480501c802004c4000c1d200e5000c1d00500021070300d13000b00ea40703d1140c030245c0c45101e6513241d01c8116254641c4400c11485150092141040c030784200070a40c002000303141990700422207402c00d161a541086201850003500524a410301d0303100341041b10240303203032401c0081c8071034242c1402680e480290b10075030040e1050b90007203402c030341c00015100700c000080d0200c0d9209a5183c0500700c2d51103055001c10202850b14800c00d00994802581e03003001c40c50360b0744110580d50721400e00040304da603e84d0110b140e200703048031901001030b540d43c410424840f0a00400360701c81e0600e0001c1003030b100d5607d005802c900 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 791259550 1250 791258300 791258317
    0xe06130302041a12031c0c050d0f0605040f0204260604031b0b01081b0321160f081306020705010804060f15080a03110610050616021302072303 63
    0x1502d4000c8890020341001003c1648640030349100100d803010010690b03240c0c000341d112403007207010307458035801e4a91500c130700031101e405640c4083c50b0541d514100b00182c855072181903081c0c1e586d01d03000103080c1e8451161f280c002418580140e1160315026a40000500e2210a0b8150080d030403100c4000440102e04680c1c0550700d070038521001480071481d510032034080c50005100240b00700001c6101d041c00200120b0034100e448404110325290303000c1c903480b0b039403003003c044141e185134030603407103009c121009030200805c22440c030307801c003240b40d01e44084d0340700850003d03900c2102c00220f0310b55031004108180f002d8101400203040091030200024080480140050001d541d07420b4004113000745500800250000f0710700702882161104103031038503440204411400300b048969240c000c0c0b000803a040d841065181c50341c0016a02d00001c0c48110707800719140c1d510180300701e880480140e8a008601d42c600000240042e2148007502d0041040078028a0b840582121113082c00da103640000304551340403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 791260800 1250 791259550 791259559
    0x11b091d1611101a010f09050d060b03060a060303091e03030807050c070b0405010f0305010e010b07083006012d03140c0307030606081303030b0a050405040c060e06130302 75
    0x107490346804403040c6281061281c2e503405a07501d03083c0aa00c0da600010126800b00700f82c808644c521a0040d030303480c81b240c240300001c1030304e126003008030345132150302c1454441c0a0714002c54510407800000342031001c2120001805e030b95505042c000d056002d00c1c4c10015217410081f48144032207070588860150098800101042108c40024908501c503000390780c14100c501c42281d0400740c4500030041290024060140028650324520f14024460700445040b940001c140c02100e0f403d240502945074414001500d008074100150030040a48410417400c1038408240a04940c01c088203041013140c01500c00360400c0288100c80c0c7e00c0085020340041c001c1d40c0e28982081d007100e036a100381c0c042d140d444030710003400501c1020400407440100c01184035040366035003000456119081030718101d00544414640c1301c802824800000c0c025881060b02a60082c19041700b580e5174000076040c0c0b50121411900d618490070204903d0742c100c4204c0d482003908544070790500144204541c40f012540c40041c0c801c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 791262050 1250 791260800 791260831
    0x6010b070f080a092309180a120201020c01420515121602030412171620060d021c020a0801061805060723011b091d 51
    0x10421070440c0c01c06002d07840001107440e07566551024040504e01d11405000c00741040825031454000c02e455001d0b0800206055540e4a1346191050307100010441210b0b1403164801000100710000c07118191400641c5c005a44c880d84c80c041c690959004c41c270308000c00440d44104286100c071700a40e01c50010300072400001c031018a104400c000ea08907501035500704031041080c8001807440e8006000b1510700c03170f08418075a140c0201d00200a6034201c107040040e0010321041c00702d9945102064201802032015068040034048020b8013035118441941c6c072521206c01c1d240400c48610b4005030b40071044800b0030b01600e0004040350440c817076282c02e01e41007075001034800c240018a4010300c03010620008210b4440c2d442200103800f0310300a002d00d134045072100015100303055490310005c054603005088503041000d00e80d40e1a441002d443d40103950390100010205000710240705408641d01c40407140e007000b00c10200040c20309240ea4004800107840038040c45041840442c02d544c20544440d0300300314 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 791263300 1250 791262050 791262053
    0x6190203061f09090e07030c0e0c0702180f1f050f04060f260a0f03030e0a12030c0f0503060312090303160c05040b01050c0c0111030f040801140907030506010b07 71
    0x401d04040806206140003242c242108143c0c012001c905032030a031001004821016420143c0e280075501c4010480c035142c2d0001e218a250340a02141c00440d8604201d0816a0765400141814151120260300d03440d81d1080120b0702803200d0090760414170340303601c035001d0868034440390040301030078002c5500a501e540040701c10342e00c07581e00101c0104940d0a0340381d501c5483d4a6101d5541c003116049500c10b0300c007460940c05100b800700b219105e50364440112100321400341d905501900c0f44808840c1c0c14069008100302081c88a0080c0c030a000d0260b40000d14900c1d054405402c5517a000d48a108000c01802004040e41b0000b60400800121311030381601d500c40040041c0c550310490700f0f200c003207011070f0700400c1c10041402d28070b205070380703003100c040c0304944d941c00044031107003d1032004a50036880084005095400340718820700c5d40c206101506d241c107042c0c20b140909580554040260b03a996284207180c042c1420102c3e64102c0792070409841c02a00d5500d41540d101303418051169080c1c2c0000b503050 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 791264550 1250 791263300 791263309
    0x71716050a14030a0c03290409020a240908070e040b0421050405090609041110120207030507060e0f1c0207031410242718050c030619020306 62
    0x840c02e03406904010380c0c91820800d0a8050170380307142c4010210b4180309030005103647c800003074841034a05000500031404441c0400016000c0c0800a07a0800c003070030070204561600d80a61183d500a4820080c055070f48450000d1400c00381e075200a1058114010034000d5010740800981c0060700051a1030194403181012541d0000c00d0080d00f62000041450103640e5030440042c0084541c201c881d403616a5460702404060207080358014450310205990380c0300342ca800600d0b04500c100519000200c070b140d0042c5141285d0000000350041000418900708010307c5018100d4170702080740c09130042c880e40f5040a5a1040000c05540548035140413240c1e03854800c01162000310b4004050b028031500d14000c0300e48940e41c409510402e582400c1d880580e070b0091580103211042000600d804044c038050b62248091a1000ca403403501850581150500b6100c1c0107001c0701c00e24a001120029600746003e51409115041e46400b0341c000c0c2c03040041c210705540b81042c0c4090209400b5a90369550360010717 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 791265800 1250 791264550 791264567
    0x302010e18130308010e0105100c0c0504021b010f060305030f07060b060d020301150c080a0f120f0533090414010905030409181e1506030b071716050a 66
    0xc00007400c0e40800c45281500040480b546000e52a64140d43e6260381404940300f80c01d000c1c494010700110010411148201100031004d402000501030b800d40b40c0b8002400d1364002c00e07148252800168140002210a109040c88016205004c10850b0300c0c5981d0507491b8003604c00c0084501901160030030134403c690b0845090200700600d030715900d14201405c0070094200303008504560020080780788810b4040c0c00b400031800c0d001142281040c149007011280321035007001110801041c400000d01d900024021a0310445002002150500c0c1c008146110a880c0701006100344010441e6030003a22203603080445c030b40c441500e00300f800303650f03a0602c84190761030b00392004165840c18110b007090080c040b010700151020400e040c4681c0c0c940111000c64900d02007000b500284a0507007400011009400d9440014445d91004544c8540c0104a408551a40c1e03c142c80482045d410410019030081c070701c64600000400d0f000700343c00c1c1400d038510f000d005034221100303003d4000b40345034045000b40c0c00c8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 791267050 1250 791265800 791265829
    0xb0318070b070c060e0a0e15131b02060114040207081c05010e01050f0108010e0901060506041814090a02010c081b0a1109010e0a0207061803020c0123040302010e 71
    0x11280308a90740d00c0ca03800d4640c41200d00703858601e1032900c041500b52144e411070000110003080000214181403880440c050b010b0708949102c8142200d8a81c0c50b11883c0e041e4054004603d8001120f642080c04c1011071501c583d8514119006017005001125034500d4681c2c03400e0090711700584820302813030024800e03c1184052070304946100d0b001c02041203e6044079059030f0488607a80003d90ba102c4c14441086480c1445074041403100c0014407600100162030741e17004603142c0010400c0c2d40d4800204010740d03c2a00070440a5800440e0700e858a030301c502035408400340c045010300751858441081f6442d0110b03014001c4c10405010420028400705c481550003101e80c0d00f8a000c80340300c6040e20103684119141c0201d810200c0030a0455551402c0a482d03070413158460783c0c03400280e451109260082d8401c410850f4600c0d503c503242089140c0002c0100543d501c82d40040114144400004d05154400e8200c035039503002e45100d0348400070140c001c1c0c0b8220795080c00c00d004240b1440d400501c4101a160300c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 791268300 1250 791267050 791267053
    0x60a020705070e1503011d150604060f030c0e070507020a0501050d060b030a0c02010e0313030b180a032708031c0605030d05040e160206010b0f070b011502100203040209010b0318 78
    0x180000b1100c140040310480c5421402085007c01c54003900200580281c1c21186c15009a1b0104243d1042c002c901544908028000194642c0b61a255001841150003d40b4524100b410901000b80e01e00541c83d00005c29040c0141000003560010701d40000c1401380070304000d80410080c001d52401c0d0031080c06894224001902c074540329502e400180b640281d040c00541c01c0405010344070101008643e40c825000414100703050854a138102d404c10060301600e401d455016183e41c843d0000d01c0882c4050740b09a8034901d42c0c2d1006007214400849145c600c0558079102d020800c410613000088600031346c01c2c00c4eaa20300f4142c2c010030100003001244e11440d018001c0c03007180307140c682d4080c0041041da0f0089044d2a565100c8c1d98401504c440015003590141c1e108000610003056414042c004003a20107401d14605081e950302c0030081182a400a5040d501070314640070469014000c000004042e00b10850440c50540c000501080061013894074841c000008900e2941e004142603003102c3c00703d170 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 791269550 1250 791268300 791268329
    0x503091e09150a0f030b0103020f130504031821140f011a03060f010308090607020409060c0f09120c15030605030a12180605093f011508060a02070507 66
    0xc8219202ea80d103814100d20a50040300003007462013030300c0c000b0700c190ba80250318412242c0c219800c0c0000080340001d900d80c440e03890402c074407002e502409054411886541c038810440d40c82d6407800007507181e60300040240d04120903502c10380344400004103804c0c0e8001c1a600c01c1c00c204210740c1030612083c040303092480d5081c170b0b10425041c40300b00c6042404480503012a02d15641d0000720b105866000e0000508032502049031954601c0e10001070412503000500004181d50076503603c2d0f003114400d445880106101181004103560410221001094146440704c140c98840e40e03035104a132081d000d1041425104000117084520a5104401801003d8211031840903c0d04221104d100e04685c1940003d2081110344e400d240c200d03120b48110342468480a007045d41e018100720482581c601c1003d090140c1d26884100d4285902e0000c840b03c8044140c5000b911b0107240c06800d40e0100c0d90380c9010001556000c20502000003085640200a03000050700c85210f4a051410101698000c0c1c10180d50380 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 791270800 1250 791269550 791269561
    0xb0f130905070501030b060415030f050f0f090c1c081204081806070f021c3c0c12062306040c1701090b031f0506090a05040503091e09 59
    0x40d030003900351502a0382110381540d6518011002d40301168a040d800000c02e1000300b00044a0210403041d511036400c002c18a02c5111003140c0490b641214038400385039420043c0700d0400c5003140420781003170340c601c0a00709001070900465520550a15a1301014000b8140141030089010039546107241a071103491031030525003085905a08102e01c2c61a4516262504143c00e1400004444000da440000c00480c60001c0c0c08000000102a07403252802d0103d4008100144084e50044807000c101480f0b805d00102d0550030b00c101c0096a080c4c0110104c0442044012030142400541101d8a960145040500515281015200c9044003042c04180754034030a6401d10349215503171160000391002c1115649502c0c044441d00500f50f2500440c00e40c03d0010300440d1000d40110540840c017408a45d444100035a25407080d0520020700b00702a0780d11011b10201c0d151550120390040385200d010700850801d521125102d10503c0b51040c0b280410b1680564401c514510201800707000406104061420 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 791272050 1250 791270800 791270839
    0xf060f2b050105010f082b0201020c010c110c040b0315040203100e060411040c140c030f0c01052d060f0d050d020609100608030d090c03051605090601030c080a0b0f 72
    0x28050740b04503000d00c002c0400d03c40c100255000d6042031008003540d034251f240003001c8402600ea2042c0d821950200240d910308803003402060a400000d0b07945c49105ea000c600e980c0e0900320030520305445a03090203d00e20490380c0018000040280201c00540381e5100e034030001f460005440c00b8071a0150500076455410080829003620860013800080891050307a0100f104a4200c0c040800c0491445800954520010350103841d07010804800c80346060442ca000003456004400100101da440781c04000d80740046181d40c14400e407402e80031040c00d8211806d481103185005000500540f0070031010380c2d40d0781e184145041000d03040f40984010390014000251104c004650903480340c800c1c0b07000308076150070314800d8104690344500030b5030402c00d4052440300500041081034804c080b5004021010035002e2104030203084030350b0b0103511414030340418001020380c000c01d0581818a014042c1e248690850b040c1584490704050002d000e00072400000c807030b115100d40e21070300095400c9854402c0700701d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 791273300 1250 791272050 791272061
    0x80901020a1703060f01030513060506060d020d0617011103150a0317030702161d1305030a0903060c17270d020c090a0603081b07091a090f060f2b0501 66
    0x202030381c405c61000203103c019010b41d07106860101c5d40908198104010903202e0340300c1c41d00a4001060103281c20325007009442030341c21041841a62a90382c0e0400c10160401419824030341c00c907400280440d0f01c406803405a640401171541c00301800d00000002590780f46408400030359441880400890002448540030342c00481d2000301501ca10300328060b618005030020400c0300e00315107100c2e00410300d02c5510b4140d03200290290388150109010a80051700920285c107100c074095540304c10303107465400d010017500d851100f0001409182800d6070703401c2d045000e00e0b681c008800d402c4000440c086e0014a202e50120003c040481e01500c806450b65a9010a80b07045000341140d51031410748074140140122a0648402082140104143d1f40e01078190540f10599091403001d8031811a5161881419900840c4410400c80600d000040051501e040380903084008030074400780710714054010a1070400500d41c040d101e2813000d01d6107951402205108000d9201741c48900e02d481c81c1c245040c50123460b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 791274550 1250 791273300 791273311
    0x80a0605030109031e0816030902040b030303040f050d050c060f0c0915030106170c1911120403140c090114060708040e040606320a051c03090504020406020703080901020a1703 77
    0x46072040890182c42c805d01d00540100b0b85181d51f403010080e80c4001340e0051138200d03012604075468008000346580c6c240091485140109141e02c00c44085140480c10522446012001d011003031007482c00280c0c0000e440c2c0d034040b20070131044513503440e442c2200d02035001d00050641d12008140e00d2100580b400380c05141220815201c400302c8000c6400700c114035034411110100311540074860142d1008101c003425400d6507590802181c1c189a402d05c0c40c4c2440c6a04141003801900020100204680703680004034991240c80030b06112260714002900e0b43e18103200b0005401d10058603410b06659160854060640c8410040d40e1070307660f09040801c90348226019a403462521000160440c80d50340801035610300c2c590207010210402000c085da681742c070300c00160400b440017008200d9445455070702a011034008600668400d0318035008041c54100c0d0059409640103000400015130002419803c1d254001003507a105c0140c0390040389800d441c004040c028039501c0840300614000d8500441c010b0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 791275800 1250 791274550 791274587
    0x3180e04061a100c08030709171b040207030f0c080c0717010b01030b0105030a090807150504060501140f010302070611030c070b0a020702210c120c0102070f15080a060503010903 78
    0x95004204026061094191183c0440c5081d200100000c4044001b1355100c0001d04202c1411500c40d40d48041e5102140c1d141d4a0b117a000a002074000060030203417410b1300100312825491325000d9613004000000c0b810a1009100c0c000a0220030081140c09a614440c5407004483c08030390745904c2484800400c84e81c41849510f03201600038a035120f0300a031a51100c040c0c55951560700d03002030742d8005090046003500c003408180714400000d141d4141c100341040501c00e0110701c078100381c28034100300c490680c0494039001008407800d4094841c6010606002c6003420010b07103441c0300d824810007404a080c82c00b07050740b40010070414005180e00190401c00c0c060658880c0c5503079003c2540c822441050300280d0302001c65042654028008644041101c40202c26a2003041461001c00c0c0707403d440d12415030040d040000171001303e5904000000052030f2065480b01860720f0072481c0491960720f01c3c080020003080000251121901d0b402c014003c3c00060001c007c07400045c01e00403c8070001d8460300100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 791277050 1250 791275800 791275841
    0xe07030b0a05012405160305071e0213240b1b030a0c14010e121908040b0402010302090d14070e010b0a0e0420040b030f0106020d080403180e0406 64
    0x9035a50340b04080c10781c0c0101c11440401103802c3c0311041e041842c00000c0c0708101c802c01c8100101000c000400580c10300c42d441c2c850300c401081c0380940c0f40d40310102024900445c0310b44020003698a0b02040d10080c0c0781c041000560002c0411401010b903881d642800715001910000142900d4900007000390b00302c0f548000e0fa0b040c03a080f4182c1d880e48144a40071000540581030030011a50041c010401c03c8500c2e400090341c81c801c41c01032405c04d0000840c54600d92400704450349558014813500182240038580010245416507603c011104e010308081e040680c003181700181070b128414420121a000014054881c00d903120700c0b55582d4450040032072442000c00001582c0b03403024217884508425485080e03120650805100050404c3ca010221132b120300f0200b44013040c040b000420180c9044001c0560740d107850040c001d64204181e0001d003c43d402030038000c000c95400001290050303854648004e40f078803190600444a032054000d01100718081c8144400c0080a9000460301040d12641c1d030302 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 791278300 1250 791277050 791277061
    0xf0105070804200622050a1d010b0d0204180b0a0e130b151c020a0f030305120411060d020c07061e050d0e010e160b030103080d0203190e07030b 63
    0x154584141e030020010928240c22003601c1040c03244203c0010009003c590614040101412108040491911700d01d41d44d100d007808142000201c10700549102054180380030007004024030040c0051080000401020802c84540490381d0100c5000703121102c004403000c82001c2408008000d40c20f2500c0c0709000040c0005003050400c000c0d0b522400340d85860301031441c0540c070b60301780c1c450000302110180030800304c27449642e655404190003d0400b07801c1c0c280071160581b06104604000e60400c201440e0b24100420011b43c0c090112940140210650402520385180180908002291056000e803002c51403001150b82680038250b42c003c030604840080c0d0392402c054601004500f2213100c8140419200c2e16018003450081c101c0e0450321000294481e6070401150840e03800082d00006500300055801c0c0d144100c0000d0f001400c603c201051955140d0760b036101d032900c1040a0303400c14036008000190341d4142e0401c1c03074404018030a802d010903845640810344680d260302007102c881d1484400b150 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 791279550 1250 791278300 791278307
    0x3042409020a03080c2107060f050c070f0609080a080a1a010807030c02070e090a20060a03050a02071416081203010302042c1606050a09290c0f010507 66
    0x20403054025004070744040c1542c486003a6a841070401e0703242c510550200c0d03c1c1599010341d8041520000c05c2e1590b880b10490f240140640c2c40002030f4505c51800e00003403028a860340c000301d41c02c2a900c42d03080d10b48029285051009400d800310701420b40f40307010403100e4105422180d1103102d100703034803010445c40c180b01c2e605880103600200c801d0300107481c500004020901070b43c840401408140102c6042550703c5003c1074055004441c42da00326000f0300d9200d420080d29410030340300c0d5400085500b1419071000007041490107a1100b100400d61a080820b5a0542c20360445101a8022103100c0b5110540704c2182d5881034080708034281c10050443c0080e8010000c0ba10340803102c2c0810845103140d1a640801024001b41c140d6002d03103881da1030000100d0282800c50b5050040240b000e04689030300001d0542c4c504403035500850a01008000f4124200d51100401041e01c405201d01c03014900d140710541c0140345500441c0d0b46040000828011218002400c10f40e00c4025500a00040c5c1d102c1c481103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 791280800 1250 791279550 791279561
    0xf030605031b04050a060513020901020d09140618040c11060a061d0a021603021b0a0e04060f0e070603051504060f120201021c0305040b0c0a090905061203030424 71
    0x120042c01159529003110319040c0c000c01d03004180b0312000310310151174100094901202e003c10040940d4002060b4405503018040c3c0c602400450500c501e4091810040c8036004107000d80d140e10412002a83d11102110400a00c05c400c901420802036022800805440088190104126886090000340c1c004005010302000c0e01d0000b2910007503000030109001010720083d06101c0c01a409200307615115500003e02c410282c041e41c000d100c0000000c140e00c0d80000440045401035407800c4042c06841c2d8030a1072113030420b44c00640000d00c0040100c143d0020011044500d80c10b00519000013002139140c1c0140707016491641d0b104040704401801c000031145c8074403e00d041011406070401c048420080c40501d82401030050302c60210707514202d941769615819541021075955006d1105018004030480c1d8800034130219183741c0356549001800c008070503c21204a55240c9000501c2a01c5252070301d005030802404407138580c00c5c0751030600740da429171140340e0f42450088003641010420f6400344 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 791282050 1250 791280800 791280823
    0x30f062c010f060311070f080316031a010c0501090507090207050f0c030d0507080f130612091e0804050a06080f0a060609030305030c2a010e03040f0605090d120f03060503 75
    0x9618030b183c50401c003030300513014098041d91540310501440d400715000925a0045510814401d941c0389007008041031082491545c0d001058a400800300000d5130158208940c5007090810034070344d8802c0c0c40c10601410958000812074090101c0014081e1000d80150114030311603801c0d955092044c62580c0d41d00d500d07809034554076074452640344444a0007000240080c50060380c0302490003203081d0040c506030348a0581c1421101c0954000c00c44070b0740c000810308421214810911501c0d40703030b486070601010740f94138841d078210201c100d200400c01e5540c2180c00622010303143d10300060b030700c00e00500b60010407078207802c01c1403820001071a4032046109102c207442490b120a0825030641e00c0c2240d05800040c6000b002100c200000c2d0541c032410080c500d003201c0060b0100030290b44003850740e801d40b8540314600700c0c580d20503c401e000844481803201c041d2109460b105880302c05640009100c0c11038000080c000240e0382001d10a04c5902400c1083c0300c48403030310140255076880080c181e581052861 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 791283300 1250 791282050 791282069
    0x615010804080a0c1e0c0512010504020f09060f13050603070b0f040b18040e060402130603081902031b0703030f0504140f030c12010f060b0307050a0f030f062c01 71
    0x21410b0040c0c0134100d0240c0c0c20b40600050708014000080000510b0150001910200caa8180405c140c0c07800c4442c00c180304200ca8024802414113a01041a030a40c01038020b1240c0744450000b1940e894085d0844801d0351f00521118031500000e441100038001550024024040c4100100d5018010780031984005218130804d40b910b0316110080c60759030402003404030b032141180f080f05100e0343c840c00351503205a55000944410b0520784104117110003007000c0128a941000400c001059002003518503814500001151501401004904501c41c042c40000c005000d05103c500240380014260152031191b110f0150b44100e20782d09865074025449082140d0050340d0300320150f42051001980c01c010050102c07507131902c1c03041c000f41c005d101508051005a644201e040004c102d18001c180c020b00c0e2614100d80380d0300301080000c1052042e034503603030705002d036150020b001c540c0300c1e9210340c1c44540c029404000326605c4507000800400c080025200382c10703400d42c10600603504040a18101d80302c06e00b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 791284550 1250 791283300 791283307
    0x4030218010e0f2d0702060f060a0608100308040e010e0c07110409020a03060f02120c07030e09130c150f09151803120203040816080706030209060d06030302061501080408 75
    0x348010400002008181d40c2d0302041a18801c0310b0000850130031044916010000c1031425040080c5020303c000c100b842003050440900c0360326102c49190b030059805074502881c00340d40d0b1362800d400511041e803004241601c0090000350741c10a455945040c0da441e400c2c03520490300c4100e0100c42501800707001a1450303104280700c10701450326174482a041071010340170108841e9640c5038881110302803013a2025060300040e200c9024250ad44025a000c1c480c0c0c00380324180115078800500c8014048c101ca8090312103800400c0764101e0032960310f540540c1c0650805102038603103101d1007040c0b800070b611001140644c150f1881aa015040e01d0090341c103c00c2c00f00f00782e62a5105e007207510170450401e241c81620a09408008582600a608880e54094005503070f1240741510140c43c04001400c500103003c604d00e4107000c0414040380881c03c403a011724008da1a6500c21001506c90b102d00071540741101d2030720500004058000c1040c921076115540c240c428141c7c52401035a90a1088400030318940042 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 791285800 1250 791284550 791284561
    0x3070620120c0904140f100602061905100909060b0a12050a0803060d0606031b0503030c07180b100903110301020705030409020a0905100810061b11040e03040b04030218010e 76
    0x1801800d1290001070011481d030a943d0748035402c2c2001642e030b04130088680007c1113005240e8902c414000c000c607100902a6103442d080c1103040401e40008501820349a4002c107401402d1030701c0c04000380182d244100003c640900e1318000a084961105014024030f8100043c00c0c0041d41c140e03180300d60428050440d90344180d4030b5112991006200030361000d80569070201090551040401441c41524100c0d03207250310355241000030003030b640400c1c481da20070402e4003d100b502082c0041201e00715110b004502d40801840341c0a002c04280c1540c006061107203140d07045500c0703a0325404403030040355018580100030303051609074803036910701030310681c401c0008102030307032955000b400798210b1440d010303d81a49840001d1083c002e0345050038005081e0701c0030f12105207004800c000c0102060b060903081050030481da42c82804c0c0400d4040c5c0700300c0208185621a45490b00701900f500c400e2402d4960b2151140b6800b100b035089800140e02031001c40b0b81a910f42000c00300b0450607504940e100c00100e9440 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 791287050 1250 791285800 791285821
    0xa11090d080d0e160e0117030a080903430c0603180209090c0109240503100b0c0a030e1c0f170d0903030b0621040f0203070308030f070e01050a051b0307062012 70
    0xd42a084548010054210b07001e1079444003080e0420104400c04001d41951201e03044416007284dc2080b0703002c032054440018880b88400c00c2125000d013008105200c450100042d21915600c0c080e4001d0101000c10000010105900c000e4004c00d032200a11540c5801c81e0905110000c004001c010240030344120000c1d00500155070720000c0c498490036515200c500c454101d8102000c010071980c055080c00c0100754000210041c0302d403059481c3e034614440040c0070200002c8481014200380740f00d000301014040804126030303040c104030b0001561082c000c00c814000704a0b49505800003460002c944801d0310b4a10121403800c2003440884e9034244891066180041004e003049800040080716203005840500c0701c88000c6001d415100d89902d400300300b141c0700c84002820042041300500040902d6038020003903d00ea03080d030345042c60b1100612140708010620403951038070b080c032010503e03004000c0c2c1d98000c4080c0201141d1110924904000041158011707247c4122541c00d0f01e00001c0d080101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 791288300 1250 791287050 791287067
    0x5010f08010b0f1e040e0601090e09070302120c181e160503090703051c030b180103060c180314150f0118020d0f050a11090d080d0e160e0117030a 64
    0x410200001281041d60714513120b175441170f4031141415060b8000c01240d50707044039120005142214401c4c0642c0351108903c0d8469040d408001d01c1100e9017400340680a0040260880546001d082c840d1226010f0381d210000c03c10841c0d0100102800c070b40c4070240c0c80c0803512120701440b40300100300b15800c11f2580c2942c56810041200c080d6100b815030001c082601080f006141040c101c103456418126810010260342003861100d000d4501031180c0f01082c14003020690450350410400100c06c80f00e120704659800c2400000302c01c1d01e50703c200c0401400006d013150340e920414041210680c581202c140e0201c010225000984044898010401d50b13100c24100380e04100faa44006140c400540d11850484240724001c0a2260380e401c00c001803203100d441604506885034142c03900701612100002c40704903401400038005100421080903c080640100c1c4c4505c142005403060308011859080c8000418412140544139080000800e440d44c0c0c0d801c06202d01c80030011394a0190f02e01025034030400c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 791289550 1250 791288300 791288317
    0x507020a0302034014060408251d0a05090c0d170d050a0c0e01020606150c0109020d1a10060c0b04051606120b030105070c140a05030703050405010f08010b0f 69
    0x4080300a600f1500d12a0100d0041d000c00c4031648842c060424170101c0c6000311009000740074540401c8188040d40000499001200c9940010b104002068001e02d00e01d25407a4801c0551000340d090000c406114200c0d0b46214400144e810070081c0c0e1041c803071543c0d030001100c0d52500710105201c10300111ba0341c41c85c00481401903840151900c41000140381c2141c50440325080c0050f9580a101e44665015a80e0a56601c00344001e140c2400c01c1c0002900f003489030001328058190002306c0b03003000b00082d002800c4030b68006189403501740d914102503001800525801d0088810170001812003600c401050307003540c4031030761810291489940d61540307104025000703441c81e2089883c400c2080343c1a8282c0e902401c2075a0f240b00f020a12801d8881c1942c40c6040014402d9040a08105410b60f00400400d030302138100800508840c07660328001e0070300d807444101414a001c00180d50040c0350300302c0b0040089600c02e80e5008040c03850048100c070130310300a00a40449920070800d450141050a01500002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 791290800 1250 791289550 791289607
    0x6010f020a0b0406090209060405010b03010b180a030602120f100e0c07050d0504080f0c0f0d140607180605181315230a0f0608070302091908010507020a030203 70
    0x807030711501d5034004042c084078100c0700350361146000003c40c140784030240e8010341c0a40e03040c05039505280a11980340014040c00f91880300c049040b2036003401008605604007006082c034595030303860782440400380d40125220b64001800b400032841501c581b07030800f03100b04441141c014045050031102c4003101000350a04000210601464010035014003540301c140815071070f50b598641c2340c403281d10b092040810800d003075500300a80c11541da484801d4100344070034007202c40e0f041024140c60320700d40b0300c40c0c2c80030181c40300d03c1003d0401c540c160300032808031020400b072044980ca042d60348100b102c95114803804105d9190320703020080064107003000003048008002c07401085001c42d005409401c58001ea0041305414074110104ca010708840202c80350b050b40035030301c2d2242c240c00c0c01106013801615101e4101049040400078548500c00da0544405950061080314800000708100820940d5402540903e529200108401a00014256a02c2c1b81d054001c0c504282aa400c03040360110f00103800d4034203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 791292050 1250 791290800 791290813
    0x509040f021008090c04090f0209061503010b041a0a2f0d08060a1a1c1805010207030201050703020a1205041e080d05100303050f2209020a02010b0d0b06010f02 70
    0x60b40c41a0442024201a41e00c4400900d001c50403103103840c010700c0c82c090040f40b401040c02c01003000700810038200c54050b80d0b42a041d4a0b04000314445500c040c0c09103402d0038010002180800c131a000a10440e070b680d080000b07480c9018100c80903c0c3c89a920000041104005d584105001091416100380845821180400c5140350704504003080d6401600c0002d889904015281c586007050001500309240510225030120315419080d20a0102c040d014480d540b442000100035030308240f108503c9000420505c2c1440d10301a070103900150001c07400f6500741b01c0011a018481c1c42514a04801940d604101e881d400c0c50120041c540a030040c4d40302101c10b042c081124010401d6141310350f00c00d04180b60b66540081c25a01260400703810700852440101041010076409015640c00085552a240e0303a2001002000942070040e2090703c10300d240d408000401c07645560280065540c00e40003802610700110070010b00c015520001018411450085001540300350754220327800049004a511 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 791293300 1250 791292050 791292053
    0x303060906081e0a020d080c010e2b0e060307231b0d0503011805070e030f06070e03190b1b070f120e1f18080d030606050a0203040509040f 61
    0x6561150300445034a03840740b88031400410403e541c8428448614019081c43c030004e500042602019010180882c0c0000c641d00149078002e621600055254000b2547d460030305c902030004203184401001072100c516034000340301038082c4544d136030031301d0340200b0203880c40d03444104c15908440101408841844811001009400e03602c4c014164042242400411800d05d81510342c54130240c00c1000041000900041242c11901c10000409451483c00440d942e517a03610101c030b417501d11041c007036414840c000e070409004901059031400380380c29607503005a11040b6414580d60f140d010102c00d420900c90000e00e80810b00e281d0040350894141000054081d00701d070011040c0350803a0070281d0ba5490414158020010046004c040d0644c460401c0e058071404000000c1468030f18140030107a1703180b84900c0300b8956219000d00f00c040040543c00c150301c2d60301c0f001c0d11035071042d00800d11000721b85045800b0070414003a00940382402440d074019131420b424181406010400a00b0480381d5021003a5400c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 791294550 1250 791293300 791293319
    0x2010c081f181b0504120201030203061305331c03050c0a050c0901050a060e12030c0f0f010c05070209070e0409061e0b12120708090a0f080c09010e01050904030306 72
    0x300d40b0b089440085100440000442c1107040b01e10301c001c3c103004041008012410002c103080320300b02c0d02401c0041e100e0b0b50340004601c441c00c0581c5010400740c41c100c00c005045c4100c119201030303140094860024a2a05510b8040c507480b41c1c642103a0101c2622004a18405007080d00001a4401d25007103040c03c000075407180c41c2102000c4119000c1d041700201e003042c0cac1000c1c81190300410080b9125001d951400c000a8201280c142ca414007a103055607104500c01c004000f1108414201011141000701200d0340945071048001103182c59400c00240c025000d124200344c0d03003402c1c1c000f01411040d80b14840c0545480d68204081900301c0e465400340004929540300ea0841c038190000e2010040040c082c0d000c0841700207030851840b664254061312044040080c1000b101080410f07140d590320780750304190311a0300a42541c103600414460020034612031141c18141201d404d03002f200e070405101c0080000184007405408801501d603401040f20b031403c45da240b41c01501a05002950a0301c80041c107 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 791295800 1250 791294550 791294579
    0x7020423223c031218080c0a08030705090a0b0c030901050a14030103030f0e030d1e030b130903120c120b0607060f0203160504030b0106050a3b0102010c081f 69
    0x14010601c0c410b406042d04680740101220f0010750800512910748410302103080d1a01c07010300b00d03d0002c0f0305281910000c01542d03800c0f030380126038140c8034035002c00000e285034030500b0150701400c2c0c1964005901d811030815684003200c65001b550910300301000440b1141c014038800070070400c07008922041001c41800442c00307140690384180b0844447c0c0400f406115803010401e0084e840400c04804807036001c130740512000c400400c00c800301c00708418228040c1c170301b40e081c2690050210a040340c5c0a2120303809020384d24844c2d01c510340f01d203a0f800e06203011030300d45d51040c80228401100a40c5020300b5035208152441c40104550b04019864030789008941a03024901000b41d40042845051202003140345540003041c41c0040c50310342156a585520303c03044c480da00501c480403400c0f80ca0240141440420009030801c41d07460380e030002034030510301451001d414031448005150949a0351041c0100c4c0061681510744600b151143c582c0104180e5600f0a480d401c001101008192b240078172008 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 791297050 1250 791295800 791295893
    0x1e060501060f0318051011040806100306050702060717130602071b051203180d12080403030b06090607020d050f1b1c1a07050702042322 60
    0x50140311400c2c000040c0440312205100100c4901c0c0280da01d0001d0b1001602c4848071207540e40215002c2041041c2c044a0300aa801c00038a60141004010b0301c5003101604800722801401c1c14061511850720503a210002560302034001817141c103a030070b041c5000003109504000c00f00070110010b007040d2200b02c2240c0012404450f034400c0940d0804001d0742d640c07a0040076100c00c941104000c040701621030f569210b42030b00d081300420040d12252a0350760302184180c070113070032440b914500856824000c0079108112811804649000c54244840c1440008d070360040402a0440346001c1c000c1e000c1081e8004106801c8805200b02818100501000d21410343c0c809604d00348a407691101c50b0402c01c03413440701c103d00c110b000e8140e11101e000c0303036000c06440c009610688800780e07203858404046509218899002e504542080b05e481e4640c10446009030685820072019003590b01c508540c14a260858401622440d068040c0e003000b0628100e0740c10703142c400303803001120070400303400c80d03413480c2c01c0b04403103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 791298300 1250 791297050 791297057
    0xf0320130219110d0318020904080a030c02010207020a03020111011d0312060d0c030209040302070e0c040509280b0d060c030b180f01270608210f071e06050106 70
    0x40030603100400d064028810b0390541000541040258501980c445010b82000b04040d2560f4590004051480c801d40107907801910b040310500e454104190698006150f0354006803800d405e43c4071441c4107100340e811041e0b004010000c0d452031174004440a15904041001c035540ea000094415011000191240d08810001d59180c11103c0000c00d8004070041045000b070300c08a4020340000e413804001d03c1643d50440d000510b640700c80c2402c0785051a0340c0c2040040352800818000706107822005042164001c840880c0750b540c0300c0e44204481d4010200a00062030122048640c11500b50400c507008680900141d05409040d203c65050f80c5c2d20003803500110340d0302c00200446042c1308000402208410030000b00303e0812403c50406100705215640203507850744500c4010300d40000c1d040a081d422210240141a12090301c2900d81c0514513219000300506404002c10000b4141a21f15060200900754240b8243c2d840d5030a0783c28000e469406421151103c0400144080c0300307c9010f408681d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 791299550 1250 791298300 791298307
    0x408130807090f1806111908010e06061c0b060c01020d05061914040515040203040b010618081902030114150103050a1811040b041a031005010f03201302 67
    0x144050403540c0d004003e110050500482d803424480701c0c0b003055103090780304000091240440040c41c40034000e424000e110b00744420050707103005600141090603100500c40200054456204000085c41007500640e070b42c00c44400000e80a802d6a07120b102c04150207001e6506c1c2c2803100925a089034031020030b841003e641d503424401107040c6040314044020044004100301c03400e000c01d4503139040710310701a10701c501d07140c3e40003e041400c07203000803a814102410644d12420149041a1700103001d0083c0c4002030700100d0241850358075403070080126482400603007c800c40003020841017003c9441c0c1640c0542d01c07100100400c03545030004911512088404e11200000c000004042c2e50003e8003100035181030480300ca6480c5244501151601c1c1d002401a5110b030b843c3c40403a01030002007004607440351408002c3c2864801280e8850754442003141a1068680d040303000b1022500300b80281d0483c1c11010405000090000d10b207070549185c142c480490404035140002d40304d0103c0003000c41100d4012 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 791300800 1250 791299550 791299559
    0x8030d02070b0c0a120b060f16021302090a090e0703020904080301081204051309030c0813050f191203030f062402070302032107290106030501030c0e0408130807 71
    0x6400d0a400c42407043c051480c20481200041802c004034004d90011076940c01c1c3c001c01c0b0b030346d000201d4800e1541d1102268072074140c8250000390300c01c001c00682c0101d070504180710400c11980708031208444020107625029080000810050a0202c4152071038452501b001c405a96081d0099110703034420090696030b076062000050403c045040000301c003410a1000b88883d56030110711802200d0380c144005180013007800d007114000c2d9030440203004558001074444044410b1240c07c015107100b07443ca0780340600c81102b03018401401079444061801880014402d4004841851003014000d140101c0d01182d049111810ad0302c46a00c001d44010828103100c0c010315082141e0310404089001402c0b03510b00d19000700e9224a0142c01c545081b81203008082800c1401c0c0003a42c03082504900c001024000d0b1070368210114425260540100139404000607a4500c01d01905050b642c0c043c0c41c9148582c50140030240b14031008d401124411814004004904e240c400a40c000300204c000900362103140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 791302050 1250 791300800 791300813
    0x70f0f021c0b070305071b060c02010b0d02100305060303130e01170d02060a020d0906150e01050a030309060c0804090e0a120e060403020f0301090203030d06091a010c02091008030d0207 81
    0x2030801041c40c9010031446001c90118010954090481e040104090780e6140d8101d41c4070a43c144690a5480305111607001d00c8556402400005065002046030180d10810458140084c030b0000f58884016042c600e500c512035002319400200c09403c8a0038404842e011504802e800d0700402c21b00d0325030340c004000020440700e4840c2403c5411014119480035510025110b400042c200d20f107140d0001401001a01a940400222500120200610807180414129420a40c411418a501080004181840c009920000b20380c0d00da212020942c0c5403c100f5030f80f5a060010075600e641e010710002980502e18028400c02007142e02c0039060300302d07251414040080041003080104041d0710010500380d10b403001140c09607034040303640e000400c604600080c09414803900c002e40500010400000407402e40c0c00c840e0a94a40c2035040c41009415002122500c0c0410442400502c00d410f031940035040000402da000041d8592440216490300d16451440d07011648140358540d0008900c1e052008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 791303300 1250 791302050 791302069
    0x3030414151b122502130c0905040507030c050403060b0f0616020103050a0b030c15250c0b130905090c0301020f07050c0306040b042307060903060f050402011211070f0f02 75
    0x1020300d95040142c0209010000c084d107110001c091018031007401e095548001034200244040541404804446c980003810041c05104e0b01f8061424170b0701181c011b5000e8096000c10340d0305540d900d81000d1540d1070b0039001d00090003035a50460758078040c00410b42c0b10079000300100c5444e18005d0b43d92034410302c001001c90320001c0c52510041d180c080182b02d81d41d8040340040320301a0440c0c4001c2d40151010b01c0f0201e0348105907181c00748180c601450f60710180c100a6058000340034040402c00165249919071081c46038050f000c07500b900743c51040c403900d8540d81c0002d0f0400c070030b102102c0c20340708030001007822170f846200554001840450f00104114042012200702d001c02e6026040905140e5107000343c000b80504014030616400002c104445080620000300468150484081942c1c1d8000a0100a21400195581802c108400b10814503502500b80140d9041e5100b0b104500c030031000e00c00519120210703d40c00001003041e42d000c13a0900360300a01c5a4098406410207015510400c0800344 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 791304550 1250 791303300 791303323
    0x12150e0718080606010f11010905060615040311062208060613090b0f09161517060108060f0f03070b031f0b03040f240f1a03030414151b 60
    0x194034020501590300b010441c03d8000c0000c0c00d0182014550b040140c0d01c1600e10301c09211558a4440141c0511078000f4600780660300551701c0400c420a418800b2800c2d00c00d40c00054244c03000d40035403410a0500900038005010000302494080000c02c2d10303103090800940c00f240d01c03984a402880954070307203030900040f04604d41d103041005c403827140e0f12812744110040a244428101c400003070300d40d141c140280009a07103e60148034103140c41f405030115100d03080c0c14000016840d011100a1803d1220031203003d50b030161503504065585e0700c100100440403800c40703500106c4d00c6003520101d0710300308400702c007410200d41055100d180078407549191440303903060b00854080014081000d221018101d80e00160040c84800d001c414074104011200c901201780c00c1b209007120b03101703007200c0703410b90180b102c1c4105074609100c0d1040480b062071761002c500c1405603054108101c10001242240c8050f0408040031300750b01e00340e014035003500b900794011002c0141d04110343e4a00f08429403080c0501c644a4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 791305800 1250 791304550 791304587
    0x1209050a05030a200a080d0248061c091106070b0403140702060307020c120d05040e0901060b0a020d12060605030f07021c0201062c040312150e07 64
    0xf10415110005001d00981c800d011105030b41202800644600c0c0c603810282001204031210000303491b43c002c5d42c0d4a00c11110000700548050142d80411880c161260002c00112015000d0480a801d88810300f41c140030701a40603c04012021403001682040088040194000958642c150a01680103a4400c0040b449084204807090008010711211500141c00d49010450b11b21039079250051031041c00006035000b080401086022a070000700d03044061000d4034648031194006540d0340e5100929072001300401c00034403040c85220080c14480ea80308200c50b0010580c503558200c00e480c260301075000c80c00140c02114020384bc0e0783c0c03c01f9103140505182c40c8200405407421500a1403800058141c1c90014207120210709481d10030003810780c3e040c02003001c005c0b41040c1c03035030040c3c002d203458460340c0d041e101c0c0b42080e8460202c0c8240f038202002025a060007190340e031950700b1118940c54142c0c282240d0340c0d0302d911740d00800010390081c01400703c81c60340f560b845c108148043c240382100556020074 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 791307050 1250 791305800 791305813
    0x3180203100e070e040305121902270d0215090118060c0309080706090b161b0f05010e1806030f06190f0c0c1709040e03040911070f0f08071209050a0503 67
    0x40e9200d0b00b11030700a11500248c1540c0c0c0c4a102e050b9041c08048a40244440d0020901201d040c0008540300c070305214403400090080503076000c0c1315625441f83c1c40a5400340c141c05000e42d940d850b030001003005400525280d820001c4c05404103034000e0b505e401490000359804500020960410007103009480c100c0000c0010615203030000b420600c0300d001d070580e90000400c00d84612010401c2220b40b0039401000300001c2003031140c1300400d050080c030511468070301050000685500030b0180d094801c40146c08181e10010f0742c4511141550301629041d01841503203201124040d09000c014099038551080031407103000b00e041e8906507840c0d1854401031925100745401c800d900141420b61031790b4001d00b02c6d0f464080c0e2186507030791400350803641c0c0c0d041800c1c0141c15400f0803011004000351008107104010583c15250006018022501c0c010800440c00c5200000306400b403801c640f08038890000186424a41e9451000c40f01d030031031408003c10151607040c021454070f85154005004c059009104 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 791308300 1250 791307050 791307053
    0x9150f0603090a080f0408010c021c0e031203060a1203080708010504050105180a020d0f02090a09061a0c07050607050303090705220e03040519150e0a0603180203100e070e04 76
    0x850743d100d084010310050f000150301c0d2101c90300c2d4045e500104144c2000300300350110444007a4881d00740001d032420900c450912540c029020b4121140e8200000c2d0040540341003180c0d07140300f6940041c10035940001401380006d030801c11210342e0070b11548aa560710503a8142803802a10040042e080705124501703000050000ba190841c0303440c08400070151a00c001d8a58504180003071040888907000c0e00c0c20040a400241825001060500c03010354010201c01d55401a00c030031600c06010703813141d10984d40b1008640e114802c002e4490b01e62000c0c2a0386038140d0790f100050440d48941e008941e01e410100030400031401c02d019400051006540d1114880c041101d03208445040d0600808601d581c0d050108444d2000c0094501529000e441d00e03c1200000d0500071246003948036210601c0a0010010041845141d4086050102801e10341c1035505201043d4003429014042d1a0003c044180940141e0340400c818014034441d05000140f00c151a1181401c4c0313001c1d034108840b005122002e100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 791309550 1250 791308300 791308303
    0x1c1406010c020d0f3306150c031407030c060f0c200f07091d030403150f1806050a06060e0f0f03030705010203010b0406091d04110d0209150f060309 65
    0x1070300c1c1c030b5044801105509852070318203a03011000001a04100b201c40c1140c03500b2055840382c60132080140700d070b0911a03001410311416079020303004890941325800c0540c8441c41c0901011083c103407103400c020400085110480c60607412124040d0001203a892401c07084c4940340c859044101070300c05050014404241e405440000801c0c03011030700001d41952100d56603002c1c00700c002c200031444160b440c990b40e035800c120302030668141c020410724013900c1c6244041200000b11421240d002c180c600b20744000086a90041036136911040595440d01e136401d50f03910080c4100a41da5200b40400501c2d810020000030071501c07a904184140704600355400c200e03588100c5036141c1d0410490304450341c82c01d102c01103030131400b820350000c00c598004000401c0c030003032500250054a07a6607480341c1e071480d0749122001001030344400c112a950105000704021032112044d100700f1290141c00544003050310303404a08040e40c200d881c00c03815451a601d01d07001c3d00d450011012600c1d41210745904605010781074a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 791310800 1250 791309550 791309567
    0x306091505011d041803020d08100303080a0209030a1a1e0c09040908070f0203061617150604080c100c081b1c0f080105030f07050d0c0801021c140601 66
    0x403414010720403425400b10f800a46055080c01002c0e00a000034984c09800e8110000800000c4001d402003c110218a911580c8440c0c840e80301c0395411424140b840d21305482c1654003a00300d168250302000080500c2c0c07007c01500307044a1250800b10241902c400603561600c0b40a0b09065145100d41414103c54071540107580d004803840b190786a842c020200010020217024000403c0da0b4000304849013072086100365000141d0007036081e501d0780d6903144504c541c5240c0121503100030030020070240403000c0700d013460168041c5200100000803422080055203e81187e48669080e901460707901240b07041141b81c42007100e00508140355010983d0b500e80419004054100d001100b54825661003000200300026880220000d82483c80940040061410342611141004241c440c000000d8504000401460002c0c0001c060800036081404000144010001c00e490015082c80301048003003080c4002c222070503d2054003d4903102416481082d01c6880b0f0100110072001d81c1004030b1640c022120 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 791312050 1250 791310800 791310809
    0x21002070b070816020a061e0c021809070302090c041a0301120f111503071704200a051f0207080d0f0807030e010516030f05090a03110a050f0c0103060915 68
    0x65510f6220b407510009036661000d00207940519061070001d22180c015694010100c503055030112340c07540c980c005894111074a00025044480071207402c5590400e078601541140001e025940903503034a40014402440942c0c80036800d00000408100004840c2060340c0801d1145490a08541c0f40494280080500c1c0c1d00284c011007043d0654030810035000300c1a2100e030760003045111107061807000e46150703130400c4a075180070a601300c0c6602d00341d4421092103032080368031060f0780000781712400c00342800d07500360490705410100501003c2180c1e51240b40440704411103002c1c0380303400580e01100a1a113021980b001740250040c00801c205c5507030001540074110010304201c0e0f40c0303803030302201200104407625403200340d5440c0c03c040c4140d5204050400e100c03022142e8052042da144040d8035000c603082a900050240d00640045000a0090b00b120300c2c1d4800610a5541c5450395031030303160404d0200045e003607d070307000b010402c0e0a56815201c0c0c10090b048100d07007005048a51115000000d280303025 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 791313300 1250 791312050 791312063
    0x30e10060b1b03121005120c210c04230f100311010915080a0501050a0e01050409110a0e0601021c120b0411070501150b0f120c071707021002070b07 65
    0x800344880b00d01042107030398001300410140070310315141518103685002401528440e5000d80a110030940c80065880c0b42013100070145121400c180c070403081c40e0000900714900c00d00880340d074021745a035280304070380446442c440140004944540c034030f0240702005000c0c02c0d00c40401c0050009890b1801ca070b040903030b0390121501d09940ca0322401038076070404a9003d04124000740604952095020000501654468106001c103989407820045101e10f01c0c001c0014015401004109525168000b89980c2c1d020745284003c41f0a0300d0049122403001e908403207509020801402032a503410854800705182500d0442c0035141d60140050a001104000116079911820001601c1d038456100400c2001d10344145a664411481c00a010300b140e0315601c0c41001c0000d40c00136180c407603101142c0614800441e0a0f16041242c00c030301d24145000750211060800c144403100000351103a00c00400050385a07901c5458003e14810032005100c00c0c0b550710115000f1038010000d9542c0c03d010348035295030080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 791314550 1250 791313300 791313337
    0x30f02042f21010305031201060801050d02060d060e0907060906050a05030402010c300323070f03140c0c0606040b150a17010603050117010c020c010e190303030e10060b 74
    0x141000d03080d00c03102c180400c0a001ca000004104000040100015600c45858961b2a070f6222810f41e10841c003482080e41022020031200c0c01807621500a1a41e049620400244030761103030760380c5003c41d10440705c1b0042c0354804481840002c1d0422078074401003460785411881e000ca0f90380010101d000c040c00003414044e681d0201d1040000f048641003802140700302d0541c041200d071f4040c210030010310803c1400303e843e100040c003403140c040c00c2d200d194000c0003603202080d41f01c1820807a10314803411002c0c0704142c0d0f01c00c00840320b000700a102c54046c40f2001c1232291643d1030011810f0415002626191043e860000307003865603220321560207401200c0201e500e8680210301d0041c0c0700e4440b8990303c2e9681030820000030030256055440303e4140c0309644000e80025002d2600c417070072501003036250405a03004061145079580700701c030380c905c1c80b070b40c050140c8000c000300b4074042c8440c81d4540c00c21808280c45110b8280350801c01c20203442c0100146030144890341c6040c050990a1040118002a014540 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 791315800 1250 791314550 791314567
    0x2a0f130614091f03090f11010e091b0a0c050102040902030a1a31090b1006080c090f0a0302030a1211010c050d0510080a14120c030d15050406030f02042f 67
    0xd0b8003601d0703140d4000046d90940302181c035100c022440c40c62491030100b55070405100d4a030904001c118485c00720164100b040c0b070605080007089400a012082c1000300d5400201c4c0052000e001a00017428022000358990403d8900d440c10707110f0071052111740004010042600f0765031140d01181d5001c488059094180104414400101c0000d80c5a10010b0821000c2402c2104480c8410702c1401c071440d0150650340c840800301c481d007009960701e04a50000344040c10303403031401004100401400a01006c01580e403075020a050502ca00b806136003001c00c035640345400d170303411501105140001d41c00810410b4030a0f807004e0120b0186410208465070b4903800030f80d5010000243e100034010540c1100c03002203103446c03c2c0d40b280031044203004150045040c0d007034188416800703a81941306003030301039030820306001d079000018420310b5548804290544400a4591501c0c8a054044d41c0198010110200d15006100a40d210b800844a620408098000032800121903080c8403c000041d895a140d2a1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 791317050 1250 791315800 791315807
    0x80706051804270b0108060a0b0a0317040f03050f06090c1305040f0203010216110f0a05060c07031713120507120c0f06110c092a0f130614091f 63
    0x4100f451a0104a0664044180702040401904841c1d03454100c07891039484801c50800d07030b5600c411068012102c188203100090b4900210351344a0103421085050540e50074102580e042c440e4020b4690341c112280b00c00001b5001d010507030340481c3d074400400040110340082051209210102c6035420ba461004c50108180070031a40202a0014025511918441850580081c0d460021141c10004d43c0509903d403c00c004110b8001400510001505181c1070610071a640450801040c9014804000c0001600e205134032103010003c440450b100c09141e0f0070072030138800c590800410a4640d04441d000601700040c000240c84101c40859840300452804108200c01c98100d00001420080302281c0640c0c8001324151011a2100f140ca001042d403003800329404042e58504418022003400c00d41c01c020b68480155000f002c221200c3c50130b90142e8540e5003a800c246c00c044000c24180e20100301a55001782045000710400c14200e2502c080c40c00002c8805419694400d41003a003409001e060901 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 791318300 1250 791317050 791317091
    0x120f070c06020c012d0f020f30040e06190f060206150f09070305100314030318151501050f0315040e01060b0f1308030a0306080706051804 61
    0x34040c9003920300644914000c1d44400180d9011800210525850a400c0e0700c0354421144000d43c4105032590a65002c400300c6180031810381c02e500394070406c06105005c2e1420000b07054a8080c1c12142840c5030500402480c802c001203486101005040c401804604440ea01040e0414030444500320220703a003441c9440f40d0032080c0c0c03180c80d15001a203000103400703401145c10f52143c07090105041c581c1104101f0800c50251185078560002003800028008500a5025a400c111100e5001000741c0d641d40d02c00715281c1c8035254400c541d030004002d000e100031136040741510034403003080076000c0080440e040f0444504000e22614440c083da152034800c90f4010300c111241c05441d41714003a030f030b4030f000c001e480b0030000f000703507428001da15040c00402a10720607c1100306482403803003607070328110000c07803d3b103984d0b00031040700031500e1041800003a448034100000c001e0300d1314031386010584529043d0142c1c24444a03610400a00004008410500600000d00801160200d80024203c2203c08090407080c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 791319550 1250 791318300 791318303
    0x20306220c030309050f040c0816030204090612050d030c1d060d1406030d08010b1803012a02010f150b130504050108010b040501050307051c0f021309021809120f07 72
    0x301c441e034020040c942e2005804040c0d950070707603d10a001d8902c4080c081100c038445500000218184046003070f45400c10b01214003035203145005030810303484076140c004860480c0d016030007034001034103030b46e003002401d008030040006c41e400c08014048004101a1400c0802c1099803804249800c410f0800da45400c10381d1103102404500300408010242a8400d01000340c440038442c0c440c06000110440c41030700150b0507141003078002070038100d8240381c1d1800c00d0716260344a6415502d4840ca110b101d0302c80c0300399181441c14415684920307024154041d0031600d00030b4030303280030f2810540c4c2161007841d031402d441c007140d10a1410039944e020108240c0440e0307007190062680181041d0000413250740540044203840da049808104a90781c031801c05940b650300744a191b4120f0148210501814200086001d030280101c000c2484060340b903000621090f460050140b15a5403186101e0960400d101c002c180e000134441194002d0a082801640e201d9140c4414540d0820000f441050044140e0607110002e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 791320800 1250 791319550 791319563
    0x503150a02070c090501080c0d0309060f020f0a060603170412030e0f0409140d09080a060908070803040f1a060f040b01020a050a06020301080d0219030305070507200909030702030622 80
    0x101e0301c1d044e122000d40000c0c400c000f40340c852640c0b0003260b0b01c0c0001d060211a681600d86103101c40c5043d0055910711140e1000d40290700841c140c8401d41c040c24000d0051041c800e03030000805605502d4540c0b601d2400e204401d03111942800184005004002c2e280c044d41d0305810070f0856000064001031515116000982d0814103060184c400c2000001641e13240b100719006407140544001d40071039000400e4824100294042058800481d20603400b050b1502c2c010a011813600e0525190700400340d0017a94200c0f42c8002028801081c400048103040864140020384412414203900050303030641d00d0104644680d0b615480b22003140e00811054034029441015030f0703540d14480c140400290400d10440b9064092000c610507850f10100700714049a01c0c038484040f20214a0700c0c12402081c1c010155801e0000411400000c1044a44d8040280204a4040c1070300a01c0710240a0142401380001e0b64a50081c40700320b00607980130609941c050180d545805488080c1422125448d02c401000303050b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 791322050 1250 791320800 791320823
    0x50a1715060d0b0f010c03021e070e09030a020d09080c130209032415010c080d0605060c010f1b09050d05010605061321020a090515060a02011e02040503150a0207 71
    0x400342c01101d440c0804881c02c2c20f18240d004015603410406da40000c00681003024040000700811802a01c80c0c15003104960295454801c03182d0340711000d4800c0d4945034008140e40c400c2c00e030704000100d18082c407881c2000d44540b41c140c4250351413103205c90640c403403000003000e18900e40c43c41e4180c503030403e4010102c0c2d402080f840e54507020443c4d000520074800c01d00c200010150420b42d8010240950107039105490340c15140c0344c1e900c0680010070200040c0383c8400c00000e040d92041e000d06001d010400001402c04070216503813040b10040e20341d00340c15a08041c840102a44c0107400b040c101c0300c09540f003003840d0003d483d04c00c1c0140102d401c000c0d8088404121500e4003003003240200142c4455128008131882e8400e06040c40c41c9450780025800500341000340210101a0045500300c0a40d0520b0880d20001c48001801a04940e08500c0140e56a00e0b501030502d02c181c0b0381100888424100310f00d888c0c00d010110f5140d03910a83c11810070410000400c0305204558100c070032240e085004104c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 791323300 1250 791322050 791322067
    0x606141c0c1d040b0307050616200301051609060f090b030f01080d030908030711011b120c08010f090903050f03270102090907081008010501080319050a171506 70
    0x24051081142c1c41e040011901e0812810184106100c0e594010000c0803641d11700410044980d000340700112440400d15080c01c001104865158000c15a44103007100b010480f005040c01c40e48000c00303401c03503540c0e04403402c0703440c41e00219440107540e583e00d80a07100403034818040c0d4503001a5400f4805000300082000a0302e0440d48015068900810603240c0c038618452084050b80d000d040050701e214020808900501c0c020a4414100051100007050080d103d07012110b42281c003041c0400420405411029004054403a510741000181450200c5504090207980b0183d0380c0d006601c034140d070b2061040241070080040d1443c0d200c0740ea86a070341d6464980c000000142c84200c0c0d00c2007103060b03000c0741c115500041c001c0d5211000c0c081c040d4036095403620070072a021400940b0300e00100d128000b001c078000d00c0a00601c2d029140c40401140c1d11102d0801d0441c0c0354080850100800005026103d042940074090340300c2d0126007020100d10b03413180d040150403205c001040e6540040b001881c00b6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 791324550 1250 791323300 791323307
    0xa0b0a020408010605220f0902060309060f07110604020d0303110f0705010b0d032712031805030601030c1a0f07030c0c050405270f16180606141c0c 65
    0x10550b6014402400300682c1c03036060001413114503110020320031510340002c0d51100e40d40e008001002443c0c9000c036414a240d00402c02a030f0040d0b9040c5200d0b0400420000640b003200c2c1f003613421035a2460200101c006400400c0e80b01d202c0948024418080c0e6581d1009052094008414094525002ea5540c881054070081254000304080b2403550800040810070318009680386c0186805403100090300d03155400340c525003c021140c001020407007000108100d100c10981c2601c03640f280c0c0360814134012808050a00100590000d4031903802040113100041c00b40c0d009034101d034072462035081038686138000806240178007250050307000d1011440b8401d05510498030343d1954010f0403950744136525002030205403481100c0070380031100b0714840c100182d40f400c07508000c108000d030141e07150340300c98412050518011000082020880715420300964107103d03111007807090a54410031a031494050081c2421061203042034100b04041000450014002c005521000000c8001c2118030381d2100050b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 791325800 1250 791324550 791324557
    0x1505161e1403031003110411030117191707030e09100603050702120f0703050d02041d16021c0c060e1e0307150507110d02010207030e1806060c0a0b0a02 67
    0x81c0c0d09488000040e011000010085038021508503424100716405c0da102c3c0007294551190054000799502804002c001e51680034501078150203442242035508103034043c0c40c050424114002803501e903508078000541d0502c0c0c20400143c030301c8032141c80d0001400c2c19211482c42c03440b99038200c00940304002c1501005504602520519101040a03441c0d000b412a921202d036501c0010108041051200d416142805010302c28441e242c02d6107013540030701d0100b090760003a904c0318146c000d0380d10006601d0707911070a00c41e60080c3c1d00041c610a240b11548000d59926900d440705e0800c1c0380300c03c070a03142a4461021000100c0d0080400d1040e50784030b062155903480101c0c2502c01e03460142c0c052014800c0701004503040c2c00c1d0002010100c918040d130014005280141c50071050069540419803492020f0000c0700788401680c000584a01c6c40c1d04004e055010305090b07151280030f8001d42501e100060450641c0c0061095490945400d00010b00f14982140d540c0c0280075454071804001c0c00c00820b4006 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 791327050 1250 791325800 791325803
    0x7030e090106020604050c06030c040f0902040602010c0c0803010515161208010f1a09030304030c170d2f0c060d061412031c0b09010e060a0e011505161e 67
    0x8015050380d0310b000c100d031156010b540040140d0452044c240f01c5281403406140c2065420720083c0c42d09607640d00f4003445080703d6203c44006600032400300310298081c425091040164109940a420175a40c1c1500e40d1105008452044a2040e00f2001000d0b03290306450480340c521038164102c00303850138484800000d074070712503000642800010a55002c0d40086504a0b40e01d0b41c0c400c03200c003204414550030381e0421010150588400d200000c04103819104510040003080083e0707500306203041310035051100c400c00300814000319444040300a014401c58803000c00005241c072241c0c117807100700396042045200b0b50960050303001c200c0004074905540a0011505440141c0400300242401c2c0706a141081c0310807401600b082c400e03a50b03001c2121002d540540304007500024403842c0a000100700c1039081c0c11030540642c21b04208802802c0c000840c40c0900981800040c03550714151490007032201a11070b200c104036011400300d809000b03c2c2041808250f009443e048041e90651085c0118000303000d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 791328300 1250 791327050 791327059
    0xf02070b070f06110c1009051606051c02031b0a031d07050103063c0504020a0305011503090206042c090303060108180616021623040b0f0f0a030807030e 67
    0x40604c0010248048031009540c49000d041d101d034629086400600d1200c6040d00c1c20b014400c4143d12401024480c8005000c181e111103844614040a0b024003140c040d2080c1c120a2040040c4030008456810181d0480301c0c98049681c0c90000711000c5010700141580c4013000d4040c0c20340661003001c0441c03840c0030354000780c0c0c0c02c1180d10790301d4280c03d400c0f1043c8501c0c544058581621025000cac842c000c00c140c13100140038105c2d260740e900c1c00400c049a00020805000aa86100501040203054540c1d04403101d41d1070b0501020f980d540011303030750f4030842c03007000340361900642403000a0181c0040c080041d12241600002481d1003081d01d1340f05e6008442a50006101e500041d12240360f0101c0d502600f080d9100030310082d541e42a0f50351055162034900d800350711a80180d44402403540300c3c0b0320090004091a041148682c0840b003202c00d0410080c0d600c540d04103540070510780c4504502c00d00030842100c8048030461283c0124590480b00e4002601c0710300005000742c10f05401c985a808580030035174 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 791329550 1250 791328300 791328311
    0xa02270310181e1e02010e0117010b03100803181503010b122e14010504081513020303030f071b02010203070204090602090a080f010e0304080d0f02070b070f06 70
    0xd4504a66075240042d06049400b551800403e051208100c0c403154043d62000c80708260b40c581a0010060b0410344840c840e6166410045581c800146e280d00c607000e003402401d900b60381540b00c0c0158014002c00d881100c0220014483e00d6040160078010103131a41075036520417007290410b60000c1070200c400c1c003070044c00260f0340300b140f01d51003180e0494036a601603d02b0142c04003d00d43d00d150010380712404944008000083d81040300d8200c050440e03441e490281c500303180410104a0004e841d00080c10320000340020010302c24003080040080340400081c40701d0b540e5007008000401450007000c0c0d0944808030410034003500500038580144070310380303400c56070040c40f8030b0f9141c0c002d2000310b0090040e00140078050040c03d003504092042c034412080542448004c0011a1701c0a4203a4417071800c0c0c3c7c1c09206143c603a0342d4203105403440004140c01551400703060010031a03455600a6442041100d05120390302080d1080c000d03000500913002c180c3d603586e0f0b11400c01d00c0b000d08281400356101c80c50107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 791330800 1250 791329550 791329573
    0xf0201151d060a050a06030209010c140f06161d06070524060d15090614070c0303050c210c130b190806030d2003040e220b0a02030a022703 61
    0x583d20002c9980040502d401c050814508801a40213420b581e0306000340c00780b20100064a2890040403002c00301c0040c12243c0c9007206103460400098555441e1030030089142d804142d2010040b0348c84503601418084812800d804905644180c803c05811405203408942d007000891901c8110045062044403054131108204408110483e4005160410300494801905465000800c0107401041e0000d20300315003c0fa04000d5100446080300080c803807602000415401d0f10031582c101400da01d81c20b0030098545501501c00000e0328400c403040c0315a40c0001c0c451410001260848001e102c68991240d40d6841e00b03081e00d804c8000450700035030b40210054510b6200e540d900c1d1048a0040040c0001480408213a80c1c2114095a4010038490050f02c0302c0f5128041006000501d080c00d4809183d00e443c070369001140d4100c00ca901c008014009254001c10f00604800b500000140c01c01696500c039a0080d00081c0710b00481201c1041843d040d200f0b170b0840e180078102001c00d09400340c0d803040590 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 791332050 1250 791330800 791330809
    0xa08090601080318010c06110306151908060d080409060302010f02062703070803010e01030c1703030408090103060509040c0e07210c0311040f0504110405100f0201151d06 75
    0x90061103055402480010380703000b1048401384000741e041c100784120740c0c001e4559109503840001ca901c603030300c000030a100c11030a1160054152000c000142410b0034500da00c8070a03808030303041c001c008000b80b80020a6282c1c2d2042449289103030711010b13071661030740d581c0325101c003402561100303a010a11001400038540c0c00468540d2144a40b0000c0135490300c845004242e03004108e01102030144420701c0000300198001c00114060504103c001405601d540b40c08910f107411508200380c24041d0914207407800308000300b44e82c2c11903031148401e83c943d184400100d008000c0c42e031020390311100c00c03000d2000f40b01803090f05005030343e2a184c034040295650401661b00c0019000c040304407141f41483c00c1e5034664590f1080c000280149804140003101e17800c009d600343c020340c0001e0f1105c40814420013143c9020722030031400d1103070300a00c5420709240c9030006050340540b10120b402c0c422406504003146100303603c4401c840010f042030f5500c8035280c6010302c0d034200880718027051384100c050118419191 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 791333300 1250 791332050 791332063
    0x1b0f0f061403040f050331080f15190203010e04050d0203130b070c03050d0521070e060706200715111b0106051309030f030603030e10020709020309030a0809 69
    0x108440d9185071955038072914a84c80807034041e601c90200380b080304002c004402580c010403082c0085201c2c9200740c00e01190b03107a4126400b8100f282c0c442444107a00e11408904500403540030300c051545c2c1d42c0c5d05119512030110541081061903c00800451074000c3c145805000714042c508a40c810b4007003140a0340d50340704503078102003595203289040044e019000c005041140c4125800c60f2499640c1d41c2c1d0341d29080d402e0080790301152001c1180360641c5041c02e14560307000580031000c43e40c1d090040c000340c46440c000540a00840000820f401441070300d82100b607030100c82c245264543c41d04643c2000641d004450100c460641c0710442c120648502e000d0246041d403822201c924100c600158030206500b484609120343d5282c0c0300005060f55468225248040d0b4544045401c4000d454020040031011a0001c149071526030705001282d0701c140d808610020640b000c5e015400c00000903403501d07002d54801030380036000208000c04d00300e011001c1d00c0000025120440c85881d50200d5540710755 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 791334550 1250 791333300 791333327
    0x70204051323101404032c150702100206010302280512190305040501030b030a11040c0c0f03020706030e0f0703020613030813050f011b060c090305030a08040309090e191b0f0f06 78
    0x502d580112042c7e45400511721202c10004107000786840c0003a408105858910030600c405a00701d80c0042003541084a2141e031984940080e45000b8030200d01c00369a84d1159005130b034094035810440c503400e03610810020700030348502c130f4440035080480d24008005074418003030a03000030300300840600d80c0d040000380c8415084c1d02c2589113089508044c10b00004080c449050020002020b0110010a24003a1800c244038003d13030117402d42500303111000d029268442a8603006074806c009100085401142c0b51003920743c121341d029034032403032010403807800001600050078030480041c0c0100c07400d903641e01500071036005460700c2da102c41c0e02c0001034032181c0220a0000210b101c0d0b41800380050825032000c205803609041410b890341e1a07031130309407454018084800200320140e0900c000d040d0480100b00041015410500c03242111f540b0140d218000c80c4001240003800481c080108141e204012031494403180700125110364074041c61100303c400740302d42e4460304841740010442138850001c092100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 791335800 1250 791334550 791334617
    0xc060105120c01021b1f03050f1006170c0d0c02030403060b2b02031501031a011401020d08040618120f02010504080301031e060f0207020405132310140403 68
    0x1981ca200c00c0e03600075545281254010100f5a0406508103030a43c0c5251072201d1f6a00024203250600300d605840703101510041c00d03084003040c1000620340c00030402481c6145400100219150803016401c6406210f40219041c0c0c2449511600e2650000c0500122400b81c1401d00c10390364202c6c10321030651344116013811515426101041101319040104506c80d202a0403142d0160320501c101f107840344203030401c558400b0b103c948181da4602481c00140507010140c2682075469000300041e42c2ca01c600c081d204240598a400203041c8003c96111800070240c440f01340d41e0b29116890110515000103452502080702c1002c4451802d10521a00d0b2295034001030861441e401c1d40c944400c0d400610145c4d40c6e00c020a5441900007c29a000c0c425100b40390307040260306c55050f0301c100001c1c0c620003040c503000c0924102c000e20100c6c0503500d8905851480d4111411158400c01525052040e11702050307292506110001412510108030b851289000780da50720f03420f020030f00449549241865044800 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 791337050 1250 791335800 791335813
    0x4030905010f0c0206070c0e0619120c050904030503010f08191410141504110304083126070504020a03061a0c070803030c03040f0f080c060105120c0102 67
    0x20750041078801c034484003d0030f00c010785003c240d00040340307640f00d01d0041312250354040c0100800c444111703207079400c20822036141031400000040b2142c60b4066106c0d1000c03c001c1c3c00300610a101404c641c0c800905000761110768a45000c0c10090415482840741e210101518100080c41c80c2e8040f0300030001168103480c42c0850b00d840d84030100740c41595840c0c4c3c4200c3c010882c18100401440c480d014080d2505002054a0300d02241c000da540c4404107030060242c0d0a103407007541e00700100401c0320351080e4094001e5440703508080000c40d00190a503001944890780d20102e408d4004003d40c103804892000140c44c5411204c01c04a040c0221045000b00869200c480d0610440c03820342c01a04900545190001346140d545100c00d2400040c03022000558400042810041d10140003050142030b00c0c41c021860350400008100c05844000d00180c18121580115400c004001d50175031211500110b8580d00c40c2481101540c070341c1c1c002c1c4545480794424400216607504017007620a110003050b0040e189 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 791338300 1250 791337050 791337059
    0xe09120403031706130e0d022a1e12030d060909030f0309060b0307140307082a1818160513050a0605040e0a0b22080d0905010e0c18040309 61
    0x3e0200203007546901c0b00c2a1004240c2c3c5200c4c03440340c00003440d08a4018220b0b1070700c8210107418040044e1074024062072811558a0b051030045074100c10000640d801c295040c00e204950104c0b510000c40c1660000a11090341c8000e0780000142088030300300001004441d40d07480001d0110707641044014040795140d0f900c2c84c40c0c54060703445405124000d80001c0349a20f24580000d04251260700a2a0349a1a05200c0030403400d0400081e40030708aa14020081d000c204140585150781b610102c0162440d507001c1c0009075100c0710301c00304001745804030b5101e080c05c141e2500b006c2c0c0130111104040c9403084400002a00c4580c045a10407207601070b00c00d01c0207840c1c03026841b0290034028403403070040351205000030f0181c5440c07203281ca02c20140d0000c0e04e02c2c030540c1d240c00c40c0400c2020b442c0c482a6408030728404224529038083c0014240d00c101460398400c2c042d1007104c003801640710080c000b5482c00c48000341184010900c00030b181c0040352a80240c185010b1a85150b80c01658090300246c0c8600b810712 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 791339550 1250 791338300 791338337
    0x218010f080d1b02032107200319060e010c0801140d0b1f0e0412080c03092e050a0c0e120d08090a0c14010815090a02180402040e0912040303 62
    0x2902a4000383c1514100c0b102d84103a200200103140348034940c5d20000440400703001d4a03107071040c5002023440528148003101d20000c0c0e80d48103001c4800102c01c501030040004c005260340f10042c2004402c0080c17140c07403805640600302c41070900c01c0304143d0540b00d425244030300d020542d070b0038001c0d80902c0000003500c404802d204000600d0f01000c0f6001201000481da000d990003450344194072401600e1562903083c0802405141c01600c1c01c220b16905206101c0822008502001c45520620b652588068050344184844060610103c4064504014040005101d4000c00d030b4562540e22a03001c28021041800f1218101114802c0d040e0042e000d15002c4078803031685117800003a10340845644502a40b140703090108294804452280801e880200c81e580140c45940d00500900b1071980504442c004500317160001070039020a290b0004050042218540a84883d98005001152074546503841f9400304042078a490845100390051242840e1010742201c094a5150707036441c2a541c0c001c20540e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 791340800 1250 791339550 791339597
    0xc010207090203340f14070f0602041511011a0604030204092402120c030105180601030e0f100b040b1c080f0a2304080d0c08070218010f080d 62
    0x24000440b5640c50702112601300c3c0d0300d141c2114a02c0d034081e6410560000d014040c0b40440c0420418030041203100d9800c4038100040c1c9030399030703005125503110350b01a02e0410000d109507040f025564100d4480710194591040b10301c24444132000081281407150b40c031095445010413481540000704010074001810103400c001344451052555100b021301040c02000359502e00c280300446598049170141051465001d13043d0007400b440304041c915410140410f82505a5000c01c0221b00c0b14800030819030391080e40502d4400c1109003d481200c445107050079250080a54075201140c10b011203610036240c13621070500400701c014500f4002030458032180c40030340c040000c181c0b00c2d04410700a400d200100390005180100450b074030b07609400150401c00309180000c0c42140101c40c820320041c03080b10800104480b0100f0f09003000803d2400354074100c10a403090b414000d4100801d04a500d0070200c0e038250007416039a690b5051210b1545910f1840c3d03403000343e101d0361000202204030703410600f843d81020 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 791342050 1250 791340800 791340811
    0x30c0c010e060c2a09010302010c030f020c0306180105010830071b031a072a0204142502060114062b14090703031815021c020c010207090203 62
    0x1840e00f41a030f00c00005041011900307400354004c1458001000508041d03a401c51002800c40b4014400d50450300000d2801540341c44c0101406107010920078098000c00c03220b00092401821520185044c0084030480b0072020b403020050740c284000401c4c0320300c011500c05080e0381d1080c28031400d141145a07900315002c044064440103241004002c010800304403c10f1100c851241501e194145146005c21a40f089480b482c4401e4401d0000e10862541c03100000480760000c50218640300426510090700c80c0e01e250000758041e00d807403203240341403804d0301c001c0344102046404070308150001c25041c0e8100c5010741201d40103030081ea00600600800780c083d001d2010010300780d50704102e94407254980c071070703c0480660044408006580540e65490246c0c0003205201c0411070420306144854664424860100900b4041c075080360341d6600000c03503003110080c0030302691182e44401200000c2e46074000300c0210054642c0502c40803e1543c00001d24120b2642c060340281034091a0034004030007900007421 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 791343300 1250 791342050 791342059
    0x2180901230c19120c090e0606120402220e071a03091f0207051519020c03030f07020a120c0308011a1206010203090301240e1303110102040e01031112030c0c010e 71
    0x390710703001030040c4580b0902e03c000b42c170f03404109401d0607c4034011010060059106400802c500d031456030b2030b100c8143e0800d5040d619000f04c0f5006403142102e4206917510a0210303860400300803408103000a4400072500c18550f014440120064120a1403200300d030621039560081861074802c0c00e0f00c001180c0340250a201c0103040c100c0555819007846c00d08504502d210524a081c045912618140e000038131000c070381d085103040007907603603642c607400f004046030031440a08000408550082c442403204c280d0001241c0200350101401803c1310916100c01c1d4002840c1500116160b00140d5642a601040b2072060b07080400300381148909240050003a0b0441c00180920405034400b4040c210707a2001c280300031050030312030310502011100c042c3d000102c504000014030140c4141c0d00d84152032030b500340c60601d0715118260350b07040c0a44104d44c0f10803001e04081c0b000100340424485d901029460843d58040c00c184081c0a20f07940740503008001805811001c1508015030080120a0001d4000350 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 791344550 1250 791343300 791343317
    0x80c03060a03151d070501021002090a210b0a050c03040204050910050c1c090b04021003061212020f0705011b020a030501020d05060a0e1009020702180901230c19 71
    0x3501c1403c41000030b01c00003411034480b02440c0b0410440d460155404c2c080c200209815403030303d00000d540e01d40c3e10a01c40041540094480c240b07403034040b0301d10701034207400301d1464150402214900510314001d5094402c10200d0020486821a6010f1070340a61341c401145030464541782c0070400241405090074101d07200d8551201c0b40007416019840c82160354071840c54a40c039803030b5102111003102c110392110161034200890002014500071903041501503501c4081d88503000001d0780100015001481c80c4103542034288100900000b020b07000801c86d50a0340c150404000e07049560312824040c40780070810010f085100118003e15941010b8001000c14035816501e07225142280d00111060059a0b112070400010741401481c20300140000c3c00c2d1b080203443c1c0138648466500c0180240611766400182c8541991f03600000d01680c0d4890201c1f09040d03051281d01ca40c000c040c0741d04601c242d2800031466001c4000712884040c8500c0c0750192441c07415042c0a1801685840d0700e681c0002e001c10203 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 791345800 1250 791344550 791344553
    0x1b06020a021f050709050f090c092b02040f0b150c010b0603040f02090105060304170a0e10090e0108120d110417060106031b0e120c040c050304060516080c03060a03 72
    0x2803001102002d02400005030314207061100604801c0c098102c035000d81d05030220141c65032111101d00e030780030301da0b0307240c075030700d40c121200021010987e211594013090504001954000030012924000743e208540030801110440300c8601a106000310b11580101000c4030840d554000304000d12801c8160000001d03071481d0341e0002501604191001c2c0d5441000d0a1044118100031520074054402280e540d42540341607558001f24001d0b81c209020b40c8203000c5504401d00e8000e4802d0088940c00800c110b90034040e44600409400e9284141c290f80c052850001175402d40c0401c1840000c581804640c0c50403c641c1034802c05008001c46601071040c04000c00222080c0400980015907101c00151116514086d00142601c40403000e42c0904c0e0f2108203042c1c00c40c0c0d004802d42603244001d5820f5a80c48000011881c18203031501005070300b15003880180d20035203a021008612440c4609000c00c090703142c102c0301c200c28820a14140300403c1c92200440d810002410243d0b41c04580180f1039011951207 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 791347050 1250 791345800 791345833
    0x2090a02210907060507020a12050c060c1b0f060a0804020a08072616210b070306081c0c0f051c05090102060601020c310207120f1b06020a02 62
    0x1d80071200d4010a0000d200d800503052041d0802422140f600a0601600b82c0029000d01460b2080790400107080949904220b001d100900d0b0256004050685400740c4070240d03500e07807541c12000c603600c98480e05021040e141c5540c4210324070030082c111500b0036191010690300502c2c0500140d80c015418840000d1100d41085101d000e801b00011040da200803415603220402e140320002d00050300000710303441425403810801c00440d001c01c4072480004410020003a021034141001400118580c4100843c445d055009581245c0221040343c0b40703403440006464402203954030302d4001491200c2c42c1004030f804c41d480501118001c46c152800c05501c07041d000c081345d18446801c0c000c034501082c2480326603018098698440c000380094649284020300003074a07503030413074a0a0b018411030344032188400200c8403403005201034818110340e0343c81d19040c8500d11348090445440014691268041098032648a07031144a002500e107102c07112283c0e0304d8001079003018803204110b01c81d001000345c10640 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 791348300 1250 791347050 791347087
    0x1d09070207092f07020316051e1305010807170f1b032518090b0619090504082d0a0518100810090c0c020d02040b0a03140613080702090a02 61
    0x2804290075a41d55440d1051500707115424400a081c208030a904105279200d52004248804604000320380e80b20454000501901c0d80011547d021841c01d000410042400203120058030100304081c048406004800e5680b000d00e61f82448181c0c0107014140304e1412810254404804010143d80740e010900301d004050410302400c62000c802405000c101c0e0030a903401e1014950345400003441113000a0b2541c1929000150a043c000c80000742c14106901c1e50725816009402c0340b0030300780030300d00301800c014009410801200708080301c102034022030710000b54042310f00c01c103020040a04100c0524022b8a542d04881801880846014440c00240d611583d041d500303400345450f030105600704405845141f110301d412624a0b0f0345030600454409802c1501040170035030440310f070b00130400301d480498042d0000846a540000c0c00702008400c000004960b2001c3d4001c410403644e40d690303a0310001451000000001c0d0004404100360000b505003e080281e128160304409403a15202c14901454602d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 791349550 1250 791348300 791348381
    0xb04051e030a0f030b1f1b06060e060d030c03050304060609061211030c03033001061106100e0103030309060e06180f07030201050f0d1107031d0907020709 68
    0x801c001092503409400041e0841d01444a14040011610100209849102c0640041c071180c0b1000540c03c0c2d4540b04d204201200c80300700110007150038280ca0410041d00a602030000110041c00004440b0306044210b2480950165035000c040291520144c525900240095032442d80300c044c00300c0d00000fa070061034010540411950306403861402c000384040303e8043da080c031070f42000500800d80c1d0307000000e0307404071032000084141c10000c6602400d8692440b02043c01c40d59548000000c41980107544542220a10000da0b5060341c0d84c580c0c8400b101c1018001d21103021910001400071a102c1d920070304d0342d544205c00000c2c5141c441c0701c20354581b50044070901c8904032100c00048076003000f880150803a800c40c1005001d010f045600180140c00b900000b40307000f240119550550405981200c0000c050191095a40e40e2507400c008000d820003039046c40b9032106a144403215820300c508041e01c96512a030143c0b5004c0d040c803002c1e0015046242240500c0d040040e441e0b034464281852540189 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 791350800 1250 791349550 791349553
    0x50a0602070f02100914040213150807090b0405090a1a0a0311030d090b03131505040809040506090402030a0227090a12050304110d08120a051812070b04051e 69
    0x502c41c2c81000240f10324032103a0340030441c40034010488440d203102130b00320792002203c003d0703220b040f07406d00001003000780c4d88941c102070410500501d1141c1c0002806000e10300d541d9070002d1721358880840c40068030407403280c142c00c0b0150300b0006500c41c2507039000302c801e01d182c078500344030050b21680021508415034206039505040040f0f002d0091030100000c0d0081034a0307003002c0a42c07500e0003210040324000140400035100c80382001c07100b0400100e02c07440c0703640d0251104000b02c0c01d15042c50b00464006154140c01107182c203002c01c8e02803a03c000c1c03451195500030020b1244103201d90901030707451151080c8030410381808042c0307400c07580d140448511070414440103201110240c10030340340254401071043c041c400b040040c8004100307504a00c030643c032000d840180c11030b000780c5407e203124460619401e0710b2841c020244001c0400c41e8002502920800483c140e03844100103980f5100d80031407010254500b401c012080000e2031034580558058042c01c10341c5c54002908500310286240705039184800d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 791352050 1250 791350800 791350823
    0xa0219080115090807050d05070f08010b0f090105130e07050a060c15060b030c1e0406020a0201090503010b210c060307110d0e100509040905070801020a120b0d02010c050a060207 78
    0xb8100354035103280d030320500e0b00d865110b11381307014261600e400d4042e85000b40381d480c0490040c00400c01c0102d0040c130340e40403100c844a80c1c1e0715225000708502140705100e031601c4d60349103080e464980411816031350014844d0100c3c180c0108103500500218900703201a00402400042c0c5948000880b4010702d036079100c0304440d005030300e40300c198402c5902090700c03041d14110301480190103231010389920030ba4a05403103584042c0b1880f9200c100b01c0852604100820005010030b102e94085050b030000c5100f07880340341b2120748402c00c2600761100c01c10a01c0d0003401105542003140c1c0341c0f00d2241c010b10b481c042904c80b601528008200b069004a91400110720307030202000c6424130420054481140e20720300940c0d000b08582c005101d0240c4411081c0c100301d404a190034150f03403158080310180d5488000c0f112019500d40c0001d001c0e400c032810b030402240d001c0b880c034903148896014002c42da0600401c1c1180c091140d82c010b40304159204400d03035903407084108100c0000c200b4401002c030039005d076181184 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 791353300 1250 791352050 791352059
    0x7090501031e11450c21041a15130216020616020913051207021207090f060501020f070608040314040906170c030601090518120405030705060a05030a02030a02190801 73
    0x101d9048416506083c4c20b080900ca4110060088401c0d0000c2c4500369969840e0428000b035000034030380c40007580f40400280280800c02245501ca641215258180d005141d035422150030b103022001d041154200d104c40500d181c04a00560080840207284c4010020521540e00403c3c01c070b400400150802d403600540c07a03825443c00000041e404500894000d0315510969030719912440303140070840c3e98803000f00380c1c9411580e4100300c2c0b0012210180c02c0f1200d41e40e07180e101101614000044e21302d02450980c001c90b0551012584108141c12400200340301450880c007281c203614020000d9003003040807051000303042d160030001c6c4010030200901084403824281d07504907100c1d0030301040b981c2d036000010700009038402040f1103044030540c0c0e0000030035a8400e0250681e01007029483c104074000c2c600245035440001c000340040d510140c00b2221002d07203640902c03031103100b02e00100021902c1070000501030203064004592150024402600301000c40001e2840741200c0c1100c2c0b400318420700010710 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 791354550 1250 791353300 791353369
    0x140d020106081c05090a03120f09080106030203121803061501030b0d1505070302220906050109050d1412070807021302160f0807050303010f0807090501031e11 70
    0x40103007076680d028260008000c84403c0c0d03005842c1803100284440442c4d11081a5180358115000f07503040a0510059181e42e580101403503030300450000400d1441c080822484814800c0f1002d9075409001002c40c01580b1030240b4894201d002000000e00b449096800291400d2002501982038001c00755619002000050241d50340300b40c3c003501582000700410023140e0300c0c0d130090403152021440004c6680301c0360411406845008401401e089a291100c0c1c4402c502c0080401140c1c0b00c5d1004028290710740004440f0a280c030300c5400c1d48a40700990a001103036041440c1245000e1042c211001c02448003049100c642201e28240c1e21702c02e0118440e0150b007441c5000e88500301e4401411450483c1049400c90302da43d80c400e01902107047c1034010404c010f604030440740341c5131b04036007103940725030756840030581d02c1c1d8090048821030700a00100048008082c02001c1c16a41e001040d040c1c00010460307000750813421350109079000f030598614107030140c85158103868141c81c030300da01d810008400700701d10 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 791355800 1250 791354550 791354561
    0x9240f020909040201050d0f0c2105071709070510030603140a030909020d06090603141b030705150706060b131a1602060c1002030f060607022b140d0201 67
    0x142401030040110601036603542c4406a401a42400c103140c6a00c8074002c10340007004141d40c0b10041c05c2c9406044401e05410a8242820343d0308900380d400312040f038240080036a0400c1d203201c000324000c0a011041e4410080d48075500015071811201c01550790000101d00d4001c24842c2008260f6890041c4103203d440030084002150107401402e03084c0440d03800414107801c600c12087c0c92a0b02243d08090b848054004800030251500c040c00483c0d03c90904003101000c0641c86c2c0e8a5100e0505400d01c19024000744e6001004010042c041da280360074180107007280003c610444440c0c08000c0c1200103501d9101d000050841059040d844182d04061880303102a1608150261204000c1c22002419075004958020f0080e500200401c660307840880c515020380719605203a4040c01002207041d00e403541c05107200e01880440c5900644aa00c14000588a41c600c042e4004003c90192000c03072000c600d40c04803c0300b079209083c2c1c1030765080c1c495010703c43c810f1040b0343c21500001e112500059090044 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 791357050 1250 791355800 791355821
    0x60c020d24050f09070329100501020d080c030a0b0103110309071401021204090216080705101103090604030f140714060c030702210f030726060d1103010924 69
    0xc0f2041c10110040b030343d01d103040d110082048005414100b003000e050079180c0342e101210910903025040040c140f01d0215140d0243c00e00503c58192001607042c400c1d54094054030448072200c0ca5074036002d40c2880a886007040c0070303060680b2800c0d40201c0c01c140c40000e622038400c42e006040381500740181d124502ea442c01d2604d045500c41410740d040100f844040710215010103a00503560303102c995050100c0055801e0241410034041a58420301c6000b150149002e803800e07c0c10029010f1a42c400d138420b02080c2ca0382c02d00c3d075019100150019018030745801268000b4104134541c0c460480350f00c00950b00162081382c03c031071103181c02131100100308401d941000d4807410030703425450443c01c0256202180c4000075540501220303003002002d0820110b40c0ca2211130110990341e85015a005007520803a64103680a000040071040d4824030b40d154440d00640c0010f180c6004014a509c031550321405601085616540e00c0441c01e001500422600c0c4a107103400300d00c00c0c200b81350f2400240846160142 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 791358300 1250 791357050 791357071
    0x3050306130b180612061905130305070f0302010f0f02090906092a040f0e01061b05121e0a090312170c0703120e0304090608010e07060c020d2405 64
    0x2034031090356480b40c402c10f140e080030450f00c1c0c1056485000213449002e003000040c0003405030300140034070050007500030000f00841000500140e15000040441c840e4003240c007900041081c070400d00012554400c41c10214064070010424241c6a142e6a040b9000f0601400c1c210754002810011410041c00d1154001c5045949154624128030003002c0c84140c031180c554090342020200c0c040d5081401554041c041103c1048012074544480f099402e034280100030200729a4141da100c0318600540e1b07030002540c0718025000300d401c1e0420411403a0041300c0301c2c4001c3e030640d480301002582e480d03000d004000c0e09552111007640c0355003403622031502d51000c107030101b10f240c140301003802c007041030590380295503080840c1e5100c10a090840d1034a5150010607089810300c0c81c0d0543c004c00010161042d5100f012040064030340c0d0f11103c0d4200e400300501040300d42c0103044108004c40c00b640001c1c044900260a0500180d05541c402803031180224051904d541036243d490b800584602c01cae150b00184540 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 791359550 1250 791358300 791358311
    0x2072a1d100e13060e15060f0a06030c020c03030c0304050103060b0304050c0d03110a030f0206071713022b060501050609010203030f10150e10170a0e16030305030613 73
    0x45030440c0c41e145000380c114040d1690003181021041900501d4001c1d0041c4007001100085031701c264442403444181c0f092845840c0204105140031904601d0746003000700a5010a80740c80410387c05010200c980009501a03018001180d0710148020001a12a080516611401c0c030300050300300c074100c1c0c1111035107a070305008010006400207002e50040c0030403100c2c0320f86a00c0c00c0c5011194103400d40c040702c101e402075180354003c268000d400c42100606a40079554290345500040ba05500002200311012a00d000810b030000360b01c80041083c14000b030100100400020309911001031302c4040c4402c5444075504210501c8118440c0318050700c000ca91184ca03000c14030700001d42da1b0101a040a4034442410042050150340880d401d0082031110488581c00000e140040c0003084810b00c5113019841b00c42083d030946209480100001e80c0103a2200c805485100b2140000c0520380f00360b00e100d11407900e68500c00851020310b00d0086100742d0f210342d43e07403402809010074030f02e0703e02c05400e401d400d12 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 791360800 1250 791359550 791359561
    0x5061216020115120f060f0912110709180209040506090c0402040e160c0203190201030b0a08070312090f0e06010f020a0206030c0f04030204020d1d0706021002072a1d 73
    0x40160004492010144c039805031050305001940715540304000300542d161250541c03101403150030201405000749108581c001001100391018a0314400044070b90f00648414860041c459100255880450380c8071000100b45501061000100340c800340e909611800800000380000c100f10380320058151010740c2040d1074229030140150014240310315410a2110400d24580318507203081030350f0b40041c200c0e0141036440030b850b1542c94040c03000340c0c00030f400c0c07182041c1c05003840c91940c000c03540c08000821006140d40c944841141c1010302c0c404c10000b05100000c2d900c3c4085030302d030000d002584900d00300c900b4040009464500021020320940d04030110210141c2d0b140c10a41c0d41c46860641c40740c4d40d030a000d0310360441d1480786802c0258401d201042d061080310781a4800301850010b6009100783c14100903300ea0b4881103441404010307804882103034451489030700a030a000c0c1c8100c400030203c00f6412070144020303142c210700c90401c50743c04801300b000c402c60380c503209480c0204480b80411420301 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 791362050 1250 791360800 791360831
    0x90807060c081e090a0b0301090c0e090c07140d1e1823060f0d0b0a0b092707020c011e02190302031e1317031210050612160201 56
    0x4185000c40981d214a05400583c0320400455100303403001406104096100d1500041c00d0b0020f000c0c00b06034505d0301c8180c05480740a05002014514010a41c0a8035660450714500c2940f0024003122040d1202c40400c0f00305104000e4a0010600b907151000d012412480c100086c03c3d01000074400c101c09000300d02502c2c2c52503d0901d0503038640071704c404002800750340e84640e06800440e07010781100380041c0340c000a1642c500688003200071210144801d003049030804c165074400303000389450390701e042241c1e486924203030011082d8501340d803890f030501d4a01c80d803025a24280445012001d81c002000a035650742e4040240760300038082d0340c044000340d044900029074400744c0494031410010032803405800c0c1030080081c0d402e16104007446d00700c01c040800504c020341d0401188900b90400c13440d0081254a0851940b050800c0f101d8019030031300c1d155207542e0f86055006807041b10640d2001001090035150a4014001d11003041340484d070300d080c40160b00741e0200c44008480c0840e450314607041d400c0c940 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 791363300 1250 791362050 791362057
    0x140405071b0c0f0e01090c0c1716060504120201290906060f040b0d150e0705090a092306040605011b05070e16111b04110c030a090807060c08 62
    0x404500d10780000301e01d4450840085034000b446074111201000801020303102403681602d25001c2c0900901070f48400030381c1e0759035031004c0042c500d480040720550b001c0035600107401302803000400580482031540340d03042214401e80e019540440100c81a0031503503024000e00f0f10004100216420a4948070040c0d0f121180c0d002c06644103074000700c042201c40e03441e6070030344000040b088020b6940c2d598072001080c0d42c2e880a140003c00504013020003640b4240c500b9414210349601020820340d50b40c12004640a034030442035140c1c0702c1146140400c0303170012841495007100c031002100740c04c1407a0f00f000c02c05403200105000d00c641d050040c10700060341d001082404d0542100d5048803030304942e01d007a90402005801001e4403051000411406c0c92949080462681090700c43c50814407002c0e02043d1220a4010300c10310f41541180b0080d0142490f501ca2161a10009501424a02012140c2c1d09640c03004145400140c1d601c081804504001e102003c02052035040030040155681d0340c010b0700e0701 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 791364550 1250 791363300 791363327
    0x7061811121903050d0f150b0a0e0d050a06330b040303200105070c030306080f0c060c0c0d0606050906180703180b04060501060e03012702010507020a090614040507 72
    0x2d510641c9202010b0040301540d014000742102884501a030200e1400108507000d220790102040d120300044042649084401004869840c0c10317a0484081c28040c50140300c82c411141031080000c954085002845468400301910f00d803542503100d60f003454050300002c3c15500a10000742c550400c203038411a4100e604072541070404001c03000c1c04a9001440b441d00203c0c989803035083c00100919150b01242e85128680700341c83c1004602e40702e03014290b442c0a440c0d16403a46600c51940c001c0170b8944035002c1c00a0411007011501c1e01c0e11414081103040c440000100c0700d494036000180042c1c540304012135800302c425165041b042c5100f6440312000c1c10003600e0070046c151303141804407991030301c0006440b40a07003000c00c48000341172502e4440000d11092241200040300010b6403061440c040c05044a601407038144004e020301c5070440341000c81c070754201c228140101000003900685598049000400481c400029010300e010080c41c3c00b4a45400000e10032450107081100058000c4032801020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 791365800 1250 791364550 791364583
    0x610210b0c0c15070815030d0e03100e06100e040203060f090a020a060503250e220c020f070501020102160602181c020102011b051e0706181112 63
    0x2500c0300c1c1000a040d214298009a840c000c90740f20065a010707030055980101219503c84203a56038101ea5003400308240d012081c5c1c550400380c03240d00f080348100701c03940100c06d009003079940d05100942030b0b03412500603810b204425000401005050010100c1040c010503281600d03101900e4150700180d22030500504a190082001e4007044d08424200001c09001c2ea019200d04500c54483c100509030b0b40044524070250041c400c001d042001103c9110041004181c03140c21241c1801020040784050842c1c1c48000c980412800380d0f001da110340140440030032030360054a54514020b03505400c052490300850305683c0100101071404207039018100405400000042c2c0303c0c0071001540139044998540b2540c45009040307a00103614810f0140b00303005100740c00801180d0282a85030b14a00d81d451a848041070042c0410703541040c10079a1001241c01a800d510300d4050310383d43d901c0031030310400120041000d07510415002c100b01a400030f000342d003003110652019140e060700c0366034400c0102e5207031a44 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 791366906 1106 791365800 791365823
    0x902040f060f060c050c04150302011e1d030c0307032904120f11030705031b010905100e16150e120601030f080d050405061021 56
    0x111049074400c01c1202e031800e201541e0410034844151902c3c007031074101d10100c0e034581c0300b06d0459050100581107000e0440c00014418918108405010540c103030300d03070340840c0c0c2066042c12840300c034401c0028049580381c017003804c2500d81c1143d00c1d00751003a00004801c101c02c0b00c3d0380341d040e2907581d003c1810121094511040d040425a400b40055a1103071904200901c910cc000e8034040d01400c2c0840d11168048003549141d002401c195800d400210310003415085122210007c4542c00c0c00a022204858031440d40b40c29000b0344851069656111143c400b01090184400e500b42d46002c1f50010f5654113100b418891440440c500090003120100241e80341c60108a54003c0320745000b84006d13800c0d070361041145030b28030006a030001e070305115003200090b85014143c8206c3c840c0001d081c980c1490f101005c90810f582c0c101da800c40000d41c0024071004049083d070141c071500f060030300c1c54 = true := by decide +kernel

theorem cover : BRFrame.Cov 791187050 791366906 := by
  have h0 := BRFrame.cov_init 791187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 791187050 ≤ n) (h2 : n < 791366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
