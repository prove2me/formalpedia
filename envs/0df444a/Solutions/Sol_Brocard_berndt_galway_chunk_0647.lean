-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0647
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:55:34.789389+00:00
-- url     : https://prove2.me/submissions/1a4ed15d-a02a-4a6f-8e5a-1aadf6cd39af

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 116187050 ≤ n < 116366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 116188300 1250 116187050 116187073
    0x15081303080405150f330607030507140d0f020d09030209090309040212010905062205040c031202100b0406061d15161707080306010804170a0806040e060108 69
    0x1064200500b040341c0700c0c401c42c018075080500a2407030340c0c007840301d60f81c240c0030030700309408203400b42d00040c1c2407031410180d290541c0380741d000c0c00688008030b010309541c0707181c84448174101a501c43c0a11103020301801c1c8038801071542a60082071102080c0803588919600303030b1040c50102d9803105465440c401140d4900307010f001614000414a17440b0b0303498001c6070b150025001c00300d0242d030005c04a400e2400b04030401032040d10003030b00840c0e50241c000c0d036202d410328143d0703459035081d80c4da81156845000e5403030f008501403010041c0244050354000381010501000c24030020b5581c01044030b61264030f860020302e1001c92a00d0300900c8122500c0c2d80d98101c0115002a60366080314040c2190f990102640c0215556100100c014050001d0201e840051030001030429a0f044403010b242c0e001d5410040284000043c24001038903003110083c43c00007003958492802d00032000900500760034088021480d010350301c1e4441c641038072405084e28103000940b844611669078400a0050052542000a41e81d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 116189550 1250 116188300 116188307
    0x50601120206181f0206040b06010c0b04080a03020d060b0910111002030a0905060f1605031b0c0a0b1311030d020a02060d0204030606030c15110d0309032715081303 72
    0x200e00c0401041d1400d1302c041c0c419103900300d80c41c000244015812038030802c02801406410268070020071300f008074110090342e03520040254002e00c002e0500e00f01040b008407941c030a50640d03400e40d09609082101c15111415803181d9000445400d20a10380844503800151280030700d242469924001000c42142520640000e5000106103085041d0744065542c0855000c20041780506280080980c11b81000c424504040c28500646018004104180095010040105401135006d24801a220360b401e03107500741042100000a032010300c9220500c03030f011202840d26984031b44586201240310260314203258603600b0160003640940c200c0701d00310002d400d04400034034011003000c0c0c0051606d070300e9690b40403ca91885d00300340e444400b0324005101e80c0424400c1300c1c0d603505050410341011500d44200c0c41d503840c1c0900500040585030318421040601641e0148800301d07024480c0c440740a43e10b06e04903522003240c440c0070300e640100c08422030024054041c0398011103071000398001b2a0010f48055 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 116190800 1250 116189550 116189587
    0x3060c030908090d11270109020f0403060b01020f070f05030f19060513060f0c030b0d020f0f01020123060a0e090606010c140a03120b0f0a0e1b03010b07050601120206 73
    0x199a0030003021591604c5d0703070300d13a0414401045110b406908030b8699a07121041420160400d80565204000d2496039401200551303013102e40c05000410303450390b5100100c3c00d01d4004038140c0d07a188034100c4040ba080c51070a0017041515002d900f120200340051070790b0380d5a01d1803032030320451b250404202c00000c03d07000c0c0c10581e0311002411200944e020030740d0716401220035800c1410952540c034500001015414050441a643c048480200b290000e40014080c101101c40031481845090308509499000390030050300e440070111844a0501140c0700080c1d0201d0031a1203612881101170041254003440340d1090046540f10010107056a8080c01520380c0c0d000d06e4829107244980500140811000304249405079110f07544112440f135404080364184d41a540c0154880e004079498000c3c00e45030404100b0454208120301805601e98494a0350528014907085030b403040000b0001c1880386140c0028005031b031081c01103a400c2c0c1e0b40d9140d10805500c0040c1c009500402c2040000551506c0c0140c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 116192050 1250 116190800 116190803
    0x1a090c0c030705150703181a04170409062105061609170a1406060d1506080109050304060906020102090604060e011103220902040e040320031303060c030908090d 71
    0x700d0380391900d40d4481600d4502034511000c00494090708004107154103005441041034407800080514400e692551080c82c1a621a440d40c144280002002c0c049500d13100345002100c80c500c01e03a00c546581d81540603109038050303203140c1000900c003c2551542c1c05006081c15401401038109a15002241d10500d910041124100100a480415030319620007440c0c520840200040642100c5480c098a031826000d03101c4845030488020403c20f030700da5600d0030b8403150340a110041408500a03180d40145600d800c119040c0d8684012641080800801807090320340302c1c2c90f140c015640c3c5040c124240c0c0b1500c000a90003034018801002241d01410100c04a1001410403c1c220500e0b5001e02d459074012001d408100318540b103828800700a00c10900014085a110542c502414070040c41040700010300001d0401410404404040300035203c4102c028040b4020b0f00d13591500c203d4801c1c2c501c102800b0075210a807074240c02140c013900034482c0580c80d17a4082800340c0ad100c007400070010350040c943c40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 116193300 1250 116192050 116192053
    0x3051e09040f05060906040608032a030c0a0b1012030f210225080909060d0c06030c200a0b10050310090501110403031407030306030812010501031a090c0c 68
    0x403521003036603107001d00354005540d64000030f0146080d10820001400150410b40164605001401546404011140c0c0e8030320144020080c03070030b44488580c2d1003881c0406174645020105180d05c503044c022030829a141d000f0303050503959841d0a40c004681e10841d110302e09100e001c240040f00060b01a0031800d410108a042c001d803054001c0708c1202004c000321b000055650760000c0e240d04a01c1c50300001302c00380d640b038521344c00024910355160749141c4110343c0c0c041d20490310302c80081d406a407005100201254000004003040782e41d00740190251082111031808281000c980b0a408400b000d03201c1c0304011000e0061a43c0c00302521084003101020300411004c50490034045007035101044194204416950001101075041c01c0190071950f0f149206a0040e90800040000c40c0d07104030024410345aa07011142c0d16015460160000c10803588024502e072804540100b02e90990003145040751000e80702405802d04108080c1450344444403aa40e00860030340200e1688503940005d441e595540b2070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 116194550 1250 116193300 116193307
    0x70b071704030207030c081b12010e0a030504030b010b09060706090204180503130f06020706030e0c090106080406051b0a08181518060106050a110705040f06080f030703051e 76
    0x401621080e0011503040c0c02507404a0410000c0180005181c0000c0414502031703d60200040c41082441c150711191601c52616809107040f0507000303500c0551581c00d44001c40344880d40c0d503e070180c0300b500a031106940114071072000152200c05082228080c583c001c104030b14250107036075108018192400b0983c0c2182d5120321f044da502c494103039a0b0a00034060001180c40380c060f0090440d411045410002503c40c9000003000030640000e480b105490341420f011581c080080c00381c2d85000313004480150b009400d040005001030300071640e00c0c090f074081d0b541444a5591003d02683e0082c030083c2c02d50703199008028078000280320395501c0b80c20900e441191440c00c1881c05200b49440d202c00c1c41481d00d410044180149040154192880607400c0c00280c04030b5807400c40040c1c001d02400480c0d000b0300074584030b8124401c005000c2000a046c0040c0208416091058900001e020a004007401c5214407520705408034000002d80b108198940c1e80c1034a8442409403030502e40c401c02690703180c0940c042c0f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 116195800 1250 116194550 116194577
    0xa0e130203061005031603171b0d120f09030807030b030c030601090b120d080712020c0f25030f1e06110a0e061c0507020f07030501090203120f070b07 66
    0x1489010f015041e098030860206040030201801e040301240d004412440c0b00004200007034140d02408400c440c1c100810f500d031031503001b031400c013440b0460f41d10105000301051003000c0d540001c0c0d25440344990340c4040250343d410701d500b0300c100c84003082d01901281d0f15200107804144660422580c7c0030010b8156840d211442011a00d0070758280c000701410341c1c807603c0f00002030409400d04a07510201c400144658000d20402401071080944100d007040300aa0401c180e51074650100d401031040c1a0031515150002e041407511480080380000c0001ca00002c9450301140182031041a25000811042c20684565480280071230811041c601da240b40d1701c004000c2901031081401880030401200e94030b04c00810000c02c2072183c0e0302450b202d041c0a000c51100e410100b00401d40d183c8011100160726180d44000f40d1030a40c0c0d1042842c1c0c0e5100b685000700070400b064200d03d190a100740d045800c61031809000109038020b442050342c91490034050b03400401c0540010540040075810b09042e41c0c4403c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 116197050 1250 116195800 116195803
    0x203060604030f1a130803060607020f0910031b08030301091503080301090504150c02030702010e01140a020a050c010305040210080406090c1502060106020c010203040e0402030f071d0108010603020a0e130203 91
    0x405500341c40702e121006280b01c402513a10f081c1540103040d034803620b9203440b841e40d03170343ca035408060055802000086800421900d032001601c1c20700030001e0200360145010400e4103a040300d640012501d888021000d00081c3e05da0380e080c60280c4800c1d03c00745003140e08200d41000185811580491840c03403460000010903031810041d03000e003018441c0842c691410f410903018045e840112207102d94a4544600170156010042c2d82c0030542c24a0310340041414480125425041c0030b00b10042c0c4800020102a8180c0000395501d17400e02c01c03c19500c56100c60b4005500b141c0742260040d400500d82d10110145078490103002c0d51061203807074005070000c5540c845880361203840c1c0201080c100b4010140c40c401350100400d5004001c1032008013509091000000d44900551044d4030a42e4287d0002c00e0071581c051201c480c22660071021201c0c1c441e52550301c510750701c55a9458429850310000041503540041c05180180c0b500030b8a5007240901d4040f01c4d1707061460040040c0c1545c103544420b8401a40c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 116198300 1250 116197050 116197073
    0x6060d0e07060f05030c070f020d1e0606090905060106050d02040b070309030605130c1a04090203090102030403200a031101150603020c10051303050a020a0501020a03140108031804020306060403 85
    0x40000207001e928103090014200744441000441441018801c200340040d00b602241d078416030000c110740c846c0210344007040c4800f0003944010504c01c450300b04281190402e42140707041c14007a403014041c1c5580d5450345021100d5150016005030009401030040c1c50207980104081030042d80018909996100140b640350840341045002507103445041060003600d0040355000700e401411070521105503503c085818045208016030088601001d01140b0600c5003030303800410110400f5980c034607003004024002d40c41100c044000c40c85803d08032401300c001c0310311800b26104840c0108a40c00e010b03281642c0c5404481550b4846640301c614180c61710005400d410020000e5440258540081d81e41090404005030103d00c5154038001c1000652815450b000a0603609424030039501d040c0e4007401c90502c1d02c00d6a0150446d8000280084015415032103584440c542884540099072581d01d200d85a22070781c0442402d038a0f03800c1020005181980c004c3d80c021000078031a40c0342c5170340c95560112114 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 116199550 1250 116198300 116198321
    0x50a050111090405010b0909042603100305150408090402031503030c0706080106020c0f04050705070b01032001140a11101113050307050109120c05060313030e0603090703080306060d 80
    0xa4081880c0e80b840c1454001c039809404141c1c007103410407650401188018a000344050300e08515910403030074440d0001070107280300c6c6440c03403540c0e540d06d800110501030000a1008907054480c480081d81d9a210720900b0303c0c0203503070129007146024088070030000650000341038007208001d14048070403071356001c200a003d08503284c00a0080f0034071700007014240b880140d01c0142550000c95041d600d959a01c01f40088403041280c00050704c0c0c842e44011685c500910000411004948001000340521541c0088610740300c01080400404940b00440d020383c2508502151802c007480a0380703405001c1c0304444075512a4400311210302c44e050480d403095800c04541c0c107181d140300040c0312154100c40405c1c18058202a002070032054030342800200020040d11544d60700d2640f035103408003081106000394000b07100045c001d9840782000520100e03102940302c8103d01041b4081c0c4d4144d400e0a2600980f4410954040034065032851a21003826130703480105256030094080250100034001403281400b200c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 116200800 1250 116199550 116199581
    0x4060f090222060c061506020a0206030408090d030207080c15090d020f06030a060303082208030a09060219021506030618010e01090b0f0f1b0702010509130b011803050a0807050a0501 80
    0x5404c0c50030f082c400c988031181c40c4088001b540c002070100035000620310825550591f0003554075525400d00f06168024911000c0d481081c1241082c2810390014420702a104000d00b81c03048500010100705400710310080422008109000001d00c0e0700d00300300761400c154005400c088400c1c3c5d10b40002503ca5104440341d50482c0c0d80d810041c41459449010b096000080e244405100c080b5060b16a0500030003081c02018500004000307200400c0c0c81d0080f0000d90780c041d03c00c0d511003500900e48036600280d152100018030800c881a4440351801d100e503401002c5c090b016100540355841411a000b200c888a1640307503403075112200c16480c003481004001405000c144a25003808820740d00042c80c050710000c000943d8905016400404030009d1001500da250320540e690070741e02c0140d42c50700406d120942d019000083c000c6000b0240d400c041002c81c426a6542407207070101c1400400e08026000141403607104484090005140300c0040856071b0050044034041886a9252800c0d20380f10003100110303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 116202050 1250 116200800 116200817
    0x512030c061f1e0306090f0b0a0213080309060702240301030c0e0a022b020f191704080922020a0801050f040c1707030b0d11150a020a022404081b04060f09022206 71
    0x40034bc49808002a1040d030001d0f51906010a00041a0f4080e108000c0c0c4a1a440b000701d252102d1116080900784403818107103030326584e50f8203210300e031242d043c071416030994003540c0024030510b202c1c42164807450400c004541041c000501501e100b9407605151000c00380e00f040078803085040c00c00940b2540d45264030700b101d03900015400800303040056600001c07051118040c0070000c0c042e9001c4c2c8103450001d4850426085000c3d070001c7c810001d580040c4c4d040d52000412480e61580480307000d041e03407001d841c2c3c490380c52050020f01049400d0b810320103001502c07041080074481d2441c1d02c40c6800500b10b1401249144480d000075030402c000c00c800b20340b4a8901c0518850030709128002401050b41201034a0400c001c00768042e40320f404d503140017403003143c2150f8900c4104c80c00700b40e02c0802c80c40c030f400410b40765911241c0f02e03507880114181c0e906c039041106d00390000c00d1800740190020388510810440c0410b00d0103001c0406900b110003207031800d0f80c28086811041209110303400c01402c143e03845110 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 116203300 1250 116202050 116202067
    0xf01021309090c181107030206040203060c0c10150b040e09010609060308040e0702100617060627041103010f050103030e03060606040512030c061f1e0306090f0b0a02 73
    0x500301040c0c1d110001030303801c094035107010501104020003101c80c3c149540740c040304010b00c001e005081e01e4043c4190101e010507000b05259002607038a2003a032081d41160300c01c8d201c4080c202118021600f032030019500c02944101554203d0b081942d50717910380640c80070a99101c1c442003d0b84d41113500190b040b8203205040005c2c2c07900034014680205103500c0c1c1081158210f17202c201451155000e1040c0d130a940320003040c81d20b071081065034410111103104004090b120b44084c4803080c04120058000e10585004c100725142c101e0902a6104000551064950743c0f49150140c85000a201780c600c000b450032140555103082c041c200c007000200700300084a41c1036241c00381506a00e205214004c0d4010010071449131189411601500c0342194090b008200c2004c41514508c22501174841034081c03e070a10142d0702d0341a103016078900003c480040c40c1d5407074140f551841a02c404107006039003040e0344c0c100b0200d40a80d03c100c2c07440c0d00913240002031291070307110192411015280da02e12282c5c0080d0115 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 116204550 1250 116203300 116203327
    0xd03020609070b03010f06030b0f04110301060f110d030b06041509050103110c060a05060a180c08070c050c010503070521040302070501091d15030d021f2f09030f0102 73
    0xc000d4502c01500e035046506181c841b03182400c1c180a078909040d0760f03407490259540c800c01c0f0741510381001030060011051207080c0d84d046070400e10568020410107044814000d00901c0842540c0b85a01d004106100100e4011070203401200c000c541c12110420022504052201c903a0110103544d484008400d4a040001011618051481c00d04501309000025215501081c140d40025841c0804074498840340b00082040c6002da020754000000c41049104074251a00140d00c114210385440046580f4045c2c155081030300c05100602540000d1440301056004102950300440035207461030616290400b500d502a0340c006400c00180d1040701000704069040001a001e03043c04e20b4544500c0e864010710b001390f10086043d203410441c8610000c0c1143c600180c1990b9420002030843d0002406040c01944524101010f034010407100408188105d045000780c00c03c2441102486075250420300f000101100070500406030031404215900e450b42d0704100f6185101c410100050341c805000d80c010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 116205800 1250 116204550 116204563
    0x2040b0a08040b281a0315060405010501080603060c0307031803020a021201020a02031204050a02180a061e050f0d1b05120c03120f1c020c0c01112a0d03020609 70
    0x381c0c2441c03503182030031312114981c26107201c11083d41035010505040c00a18007510200141e24139406100391030145102c100e4148000b406a8801c2e00e003000a070741c07118011100213100300c603080d4042d0701032004514002282c000460307011079076103400607031400281c0d442090074170450420b40060f40101c40103010352409035a00d903500384004000718640020104080c0d228090307420703000a204004800502440320500400c148254014000380001d500c0100701460448141d8950140b50318110011407015805402c55207a0084408041c081c3d40c500f004010526a661020a0301300e441004003c000559604024909503110452100e8286c186414813000c520b0b000c200088a074480d0904070580d4501007040c28200d0700d101002940e6450148400017a440b845005511410802500314080d800c0d950151240301b43c02c8095405464240b0011920313100000d0307200c034044d00600240848689041a03200c4c08203c0c2040c0080d82881038000101881d20080003030300580c1142041211200c81030225 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 116207050 1250 116205800 116205811
    0x3211609033c06050a1505100504080303090102220e0609061309060e0c010215060d02010c1a01030309090506280f0305100c08010305060a091401020c01060905010501090302010507060f02040b0a08040b 88
    0x10416840001b005150b40c424601c0386500031000544000d203803622600484011f0310940d02241d17501d0400d0280c0300d000350f1103c0c0001042d0f4103085581182c06001d03c0410084503940106801181c50711400c00504000140c8404d80c008043c0410002100c0c003070084800350341c010720000800100e40d000882c00c1091411900e4110740055010281111440b5142d40d0042d0741600c214850311a2071006881800c40c195015001080a007110b03160000e4044d49141601d21942c2d4402d142a5901d14045c00d548042d50a02c0e80807180c20341075a8140f10041e000044100350180f11020140c2c6d070b1440505081c52600203030b03915040003c182d011201c55004140d440400307868030743c0303e56245468040d125030002d00b42130b41d107644490000c8240001038092400d4500c00d000215550b40b600c2c20303507500a06484c42103001c52030502000060a6004040d15003c603501a16010b10b840c555070385000c000c140c80f4a061004603820b02001c00c88000100103000f0211003610345c9020380c20541000324540c5001000c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 116208300 1250 116207050 116207071
    0x14010302091305120d0e03070506010302010e09011404090611041409090601080706080712050c0a0305070e100c0f230c030c0f12070803211609033c0605 67
    0xc0802c0001c400148078000034620542003621010b420b40c4036400341c40c4409032030005110200c0c400c4180a004035081e41200d00c01d1700c07000007102e5400c044c45a6000b0034407030158116099540210790342020b40010402c18440d407000030f812110044480038035000347c0c01007081000c0c0341402810710709081000c943c00c000750300b00a2400b50325060a2030b544603c54001d41782004130040100314123601a0044803c120714099051010345858600c0014503000749810f42d000034103243c00b01cfd20301400341004004000003d05000748104600310b054803144c010030340c119082c5002928106c086140700c4120800940c4403c01b80c1c00d0f0801c0020a503103441c0e42d0308411031190304042c04040e907a5641142081c1d1064041d100c0c1d280b8042d02010541c20000527620041c59400001061300d40d1003560300c540c203c42407071200016401d4840e01d40341e060360203616401c503010441401041c40460b001080c503c8004401e0005680d9614a0048070706100982e1003029103075480c501c02200c10042c05000c3c56078804d80d60003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 116209550 1250 116208300 116208331
    0x9070504050907140607060f020f0304151505010e030a05010c0e100813030e0d3002060c03040b0c040f060f081501090504020a0c05031602010314090d0807121401030209 74
    0x20101d58804c2003c41002d01c560b0340040c4c01d00030480396400001c012101c02070110340b10130200b4005102640100c81c1140d4100018410390184201407003030111050ba103810307640d04a1b003040d005403098101020007990600c600b41d0410000340c02406038204494660b5a0700320381141301800d01074410102c001c818240400704040018402c0d0350040b100e004c94151412824004140002c10204407020b07401a003119170040a042142001c001c0240c10340e9001812840801c4650340101d07110202030760030303143c040c40400114010880054040d42c0046400642915080d80ca0380344400000c89a48110003081c080f220400506801c40843c0d0b81c801e5000049680e00500080001c0c031412060044900c84d80d40822202c554034802c0140b24842d5030b04c582280c0d0b0f520b04d8142603180c00d02e800a02240020f0074804848080280d030001140904000001040c52031400c24040e205d000c0d005005c001008060302140021210b18003131100300485145140c906541540140410000e000b08079441492480 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 116210800 1250 116209550 116209559
    0x807050a060509060f09030109240207030801030602070602090a080d080c09031e07080d03021308030f0d0506040b132c030f18091e010617040204150e09070504050907 73
    0x140c03c6503141c00c021a540c6540f0450546104014042d14400755010740c6411004008c118814001d850045000e000c0c115410b411101158180d01c81c03880d00800040f09440104005541e075009045520f00c2000c02604041320078021034580025030303101100a03032007900da003070105801c0641719030000c2c90b80d103106140030302d41c0380882c1e030b210071098441d16500340d26201a8030054041c0928805030504406488840d10000c400901070740084602019001c245d150000354004004112146600104155428451402d021100401c0000e04c880c2d0815218066280c447c0d13140032100305e8424030407500154101039400c114643c0a8201c0f07a0244011800c043e12100c80d01c00816140c3d030740070806220396100700e0304410702182080d55003035036040441e41c003d00c411900e214400040e4007500c1c0c0c0c14020703983e0740e421040b10301c4c070b8034480c0c091414012900410051700709600b0080300644001814202160f440b068403156074801c50341304a041e044a501801a844c0c07601a468201c111500180b01240c1013 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 116212050 1250 116210800 116210807
    0x20a0c11101704020111030c03090f0d0f030516050a0803040b100b031f0503011107050f0a0c12022706120c060a0e0d12020109030f0c11040c031d070807050a06 70
    0xc10010b003002c4164040001c0841e885040071003840000304058903224440446800e68a40000c0c41c0c2e5441810301040d049645e0415030b100a410b0b5400140750a104100c5890999007a40000c282c21a1141c5d0080628042042007140000c401e10a0102d140c0d24a05070034a825071000c09400c7d90402122020104042d9a4a10552781c00c00561340241c0290140c8120603c8408181d40c0025055402c00b00c5c07034100c0c60182006456500c2c040c0c0203850303880400c00c84240d110b0040d800028290202d1810900080f00c0034801e094000d0300c00b40050030f120000a07948070b441c92b03020401e06800b80180c010480207040014180010901380c40082296001000c00900c941c0100d080d500204140030384075140ba50382d4440c02c190280c0d0056165582c0c0808044024041c20444805070045969102056500d500c504c02030b900d039a0700f212880040d00400001c02c0060139900b81500100368550700d2891100c5180d41000c100080d044004021580c0f502d1025402d1610030307480340e8031400c409c1d030003041120340 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 116213300 1250 116212050 116212067
    0x402031b13050301140a110a090b0904061d090c0103020403020303090f0406030b040302030705060123010f03020d0f1e0203060108070c02010c08120601030515240d020a0c1110 77
    0x400622880c0c80301c0611000907a40821640b000d58558280600e10f260080c1c0c808810b8050302d0b41900078002c0080c000340e08a814811000140d0004a040c00204003050080c1c0142c03110100c02000812101d544081c40c41201804134241a0b6006048050000781141049004c2d603a003002c1c201542050700d0754000a4070b0f401095401400f80d100c841d103007605c03030b60380fa409000030b5940001844454241030400030340c1c94200f080c2c1155944100310002c00c2c3e8402c0c00d1f420301c003800304015407140c00711082c04c011504110328203081010315800307015511894016010740260722041400000d61164240380d440b8485001a00f1415410f00c10005d201a503644543d410b0340c0014581440350040c1c0341440120342c2e025069001515100000c241c1030150030070520740a0141c01c09a1f014003550b00c0c1c030b507030204e00365103604191540017002010001540c2640b00b0054100e83e021180a82000b0030b0070f00c400181e81c40440700400081c140c00010080100504d00c0040d110000e0303504005c0840d135031401030021348 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 116214550 1250 116213300 116213341
    0x30204020f0c060103051507080c0a0309060b03030c1b0409030c26030403030b100e01020d200a0303020703080a0b0f0d141501062607030908040b040b0a0905040203 72
    0x25000075010500d00421800c40301040310a40480304a582e507814035949031041450041140c010210210f003425101d841e250b405145070500c201e1901d002804203400034542004120341c06c946459007000d00b5a03042c03018121800440002d003e14401c01c05011030703801080b230440c070700c282d10b05a21100403983c801c44410340c03254441c200c10341c804207078145942c1c10106103400c8a1a0300300001084105581504032802081c01503540040301e0400000680302d500d0428616401644410125000140304020f116001748540042e10784104026410b10305008242c80c007030313000ca80c000a2410030145e0058055a10171107a03201000821012000203040018041d44540b090760313480308080620402c0340048008518903803c480c14074502c6001140c2c03403071091041c8000300320394003810701c03082000d00064011102d0501104080f607503007010030f4006102c20a0f050750f00180a00c001300c0c14151050040026116640b581c940f2802181d0004004c0b410940146000d10300500070b101808219040307504220 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 116215800 1250 116214550 116214559
    0x1e09060703090503040b03010609180903142104050105041707150c050d020c1e0c06030a05041106040e100f0e13021306090504231506040207060606030203070e010e0a0302 75
    0x20b150b075052552440c051a00043e1490340d0001c00026602e4205107014111f45003a808510030b40c8502010a0490310300c1c01001e40416001407510b02a1090040100144402c18601c3d490202100211030030300042102d040302e01d60741d9801400188515101c030011441d42200126203010301075070320490040040100c1d00100c070f4981181420042c082c03001d9400c0d05190000c110340750340c04103442d07a581d0700305909440103652100220000b80c0744080f8846204200180034286591100a032101c01044010002c1e62043d011680c2d59002e03595540c020701c010b100002c801803a908100b08185800e505a520820042001c0e800811013042c410000e01e82c081003140c03801c25074280a00104d00000c0d900000680320520308840032030000340e40ea00c10760050340105000e074502840b203824040119488181050350703900803542100c07410358500b81940e000c040640302505041ea10f135110000d031107c0c4d4101c007011a0b00441000481a88080091000c3e40e003403800d18000c0081e00e000c00e900f46c1b00f500010340107 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 116217050 1250 116215800 116215811
    0xc1509030d021804091101030b0f0105090f1503040f0308060901030c0b0c0106030c0603060602010f05100e0405010902040212071b0b01060c0201020f060403091d010503031204020f181e09060703 85
    0x14580111070240010f0024000340044100c5242c508010801030800c0c90100b031030318240c0341031820031750101140302e081a1245803400d14454200b1400e2460181c00c0c5901180c440c9141e0100281c6402550045229200f9901780e00305500e8040c045402c002c1450380180a8000100045002c00740c00c3c108031070441d03602d01c0e0380d88035100004c0d024003040c0d040501b94403140d100000f142a407513448035080322801e40c020405024408441c1c1300b5a44203552012490040c0d08043c0840c1c60050f4185130010700c00c1d0000502085158007240c1643c008040100c00c1900450030000300c02e801200810172007803a50961480c80001e47c0e00e800c040f01d018000e04080000c854114021640200441c442e840ca105045880d24942450010060a918012846441c0611703c09180ca225080e0300181641c00c01405141030424208401e900300e10002e0080e41e01107511210662551290200c0b44002402451003989034608042d05038480b10518000c01138550321441084001040420f0841d0421018600031a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 116218300 1250 116217050 116217067
    0x3021201020304030f0305060f0d0c0f081b090601120603060207020108061906230c160b0f0306010f0e04050f09010e0706140702040914060601020709050702191e06020c1509030d02 79
    0x149d60590401604500c10384040814020030422020840e440342e8620540e0503165204541c0b40c00c030382800075040021403083c4000d10310f01030005943c0050185080c0703039042c0c4d404045c0802e0743d200d07600666100340e001805005650f400819160710110a40f0741020b0742a00c2e0003414021381e150710079201009281c0c4904884d50803240c00082c8480590400c080d10303144080d080b2600c4090880c03072000100698070340003441c02502419100004041c0c0509815603481c4ca005450310103400e0040343c100300c8a044244010355807841590b01410304144083c0c40c3d4a00205014219106443d070000c41d603104107410451150300a4400203c0d01903888841e4683c01e0340c0c400304000d0506188000c00c0640688600241300c0c40c000b8816124400c00d83c2100c401d41d5a4101500484d00d060b82c8400060b00800d215068041d841c02e130300b00c14a845004020314580d200504a0070041c451170b0100e0305103800058101c042c04003041800d00213006100e0034a0103041c00d40700c6039a40d229600f0090a480d40118003400c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 116219550 1250 116218300 116218309
    0x80105090406091439030a06020901022404030807080c04060302091807020d020706092111130204230105091009030f08070510110904020906090307030c03021201020304030f030506 79
    0x108600c4e900302101d00390000180c1400400601d40c10175001c3c200700e030703440b4007980a031080010f08610014014085100180c0c99240103580401c91440c1988a00040b040c183e0b40c028145a8022919010390032a40c107081c500181501c0028091200300f040c060305211800c5008400c4504079605810300603a42e0314014045000c480f845036001c2c1440c1c061504000c00302c2e401141e161034103a030030303801e6074511a180c040585d0b8030356480c02018141c00384000403036501041408ca01300b03080d009091408400010000164120140d4030100328081e8010904026601c0c0d4400b030400e01c04606500c8160041c04800000c06d00e0041070025446542c508802c24201030040c9a0f100203190005540b042c00d00a0f4101480140d0000c0e1302120144143c0c940c203018030a15202d03088250380224103061501448400704000b82d0000460a5030288c1c003004022190341c0c6c104030a1000f076108054211042d03240d401001b02c6005106035411040e40100100400240d0024100d04010554240012151207280129 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 116220800 1250 116219550 116219573
    0x405060a0306180617030c0705040c1701080f010c030e0c010507141b01080610090302060c0f030309070801060501020a03050d05100504091505090c090103080d0b0604090608010c08010509040609 85
    0x10186030540c201d04803010b200ba07070481c4069546443c40d0100717081410b010583d507446070107800c8401e40c000290601151400c3d4011001141c11031500110038a40300a100d1007440c802e0f03008551039480440800c002d04402e01801c00b521199007002c200b2007070459120780e11041c81c04905410040c0002d88402040074042640c62a524030342c0440e4142060f54441d440c214070142e9285005c6440b16001a00702e1400200c070001400880d610500640c0c516824451103030001c43e01aa410b002c1e000c100030040c0800c0000d91b01c502040b0005159072444c005c0d6150840c2c01e2504440e0440d0850a03006010a810100301d078401880c1807000641030782d842d215070f8005c08443e04169402130411581205000c0321000000301030808141c100429107802e40d10a41d01d603811103005410003040c00041000c01c1d031031005004049001d100102c0d402101c480012035650040e000407001d1550b0710310034800038109124495170003069081c440d05550515000940c0820010002842c0549420000c1d04000d060040e1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 116222050 1250 116220800 116220809
    0xa0b04031202160308031909050c13020f181512010b090103090602040801021305121005040804030b100e070822050a12120e0304141c150e0c03010507050405060a0306 73
    0x343c188141d124586262a58000d940401c0502c800c5903128080e0b9525105140525500800a00e4101a901c051102407251040d2801010740d00f40038100408003d200108003a800da0801c0300c0c2c4030718075081080750740d404815081080507801d01100700104100c11016065410b1007180c15103070b104240040340604503440d801400d1a001240004090704150041c041010b0b99981d0b14040c980c4400c244010360040511141159000b400c9034101845030340e0045420a004002691605031280c880204c108016070341c403101c250104000300400400100d51581082081c41c0002980c00d101030f0302d00c0348000c1e00080c03907108010140c50381c1c01c00c00200a51205140d115818120221003035101410354403050020958990503c500e010342284080f04a0741922010b89040041041408c207008410390a000754500302700c0749103615000309014042207464081c2d0030101045d42c190001a01d81000f600704100c9009a051038240140700f0341140c183c6042e105d0513104546c41d04175820b4110040c0074583d20 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 116223300 1250 116222050 116222083
    0x412140d020a0f08060f0306131e050705010f05070209060f1305010b090a0902070507060e0a082a010804020f0103051506131a0403030507061e0c090e01050a0b04031202 74
    0x442c8500c4a4001085810084264540d8151030b590003043c0200111241e140d00c0d070542024000460602c8a400017554690040070006440f0322007900710044150b49020980700383d80f011404200c0c41da80000720203656200f610380075090181560100d001704401810b443c0c442d13907401c541c0300d6490310703525004201d030341c103640e814480c03540c0d2503440c036005504c43e805d9103006440c54030010030194024000c80307924a0303100380201241c601e000030444404456210480e44102d42d460300142c0c1d060301300a50041c8030f02c0d95014420b20070113405c0d0708603041c4809540906010014040101603502d240700c0c071030039513401e0802181c01d9440c0c40901101000b03051800d40d010b2004150041c2c1d10451200384410340702a8203480d1103203075015800b4442c0e0701440c440200000e408100034000a00c10343c00031303000d07680029646d0110300d00b42807102d0140c1c0c410890b6a030001d1200241004078090421404d80109420781e01541c03a1824401100e14074442c07070101904100a00c04000c113154803c001000d4038101c4c60030f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 116224550 1250 116223300 116223307
    0x30e0303070b040309080d0203030105060a030b060304061e05011d0a061205071706060d12090302040f0213060509030c040e0c03070f0e0115051611060d020901170412140d02 76
    0x60581945501610140c0000b60b54810120303050200251503010b03e00c092300118110707032038041044055800581c50700105a203400e07059019031218400b55002e5445642d021601010900038018070040001c4a599041c3c200001048020142560900540380c0300c289544155030317008000c0301804181e40010400c0081180203024400081510350648407a01024420b1130315000015580f41c2d0b0603141c0540c024100f00000d400900d0b5200580340111260901c00c0d0215943d400080445080c0c1c502c210340a90009001401c8000c1040000d014041500348075043c10344c1400420340e1409160306603030003690f0300d108040c8070b11001c03c10f0090501c0003c0c111684240c440c0004240b250381c0b441082d205528400020800c0520310200045400385a40c0d8141041c1210300b0302403044070a40b00a8803101c5403d00c44c402c040d22914006d003011440d0100141c1d40e000783e03000040481704148203402988030702c5002d120000e4015400a085286c2514040d2402000858101d90621a114042c81001e2000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 116225800 1250 116224550 116224553
    0x60203090102060901150b031305070e010303030b0108070f12020909040339080f1c020c070602010902061e0d09050105010306230420030709360f030e030307 69
    0x400d60a0420390a0b03880c1c0d5142c0b62445401c0e10002d5400359503162044070240701d0307074070440c015581c058002ea00d4042c2e9040765440300750400c40e01d0742003550318808000052041c075805008000d24080203181110700c2d843d081c000104107400c2c0324035410400401d00a10010071070950152032005100800c820440d00342880c003c0c01c1e00619405d2401c20258201c40d14094410400860252000d5403001100c015040d070f403071983c03c3e0f00c00c80084040300700c00d00c07407824800020340c440308025007144c2005a8401e040f01010f841c00381d40780e206104680c10f000740d07000141c40c2c000a50b0300440030040941e001044501c0307110200e004100c2c6040310f45141c50610400c0c00415003000b412607010b60800c12403aa078040c1c1c028516070b4900192043c1c2034008000c6400030f8590380503183c4503034a040030020071808100002c0d00b0b249a6510454446e83c0f22915103400b0a1b156100c1491130810b404403644102c0003a050032119001240c02a1140b0b0012403120181801551801240300e0014150303655a41103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 116227050 1250 116225800 116225803
    0x111330c03100b0408060105210109050703060516140f04080a110405010509040201080f0604231b07050d1202040506040314060c030702150c090405010b040918030801060513050a0602 80
    0x11606404030740d0710b0b40c00016034110041d00f1603040d1800200545034503030802d0103008482c04494050000c000740c041c401c0282004c01e110b8509800d20070405401c4251860074242d040c2c030406040a14203519584030714203a0754001c901c0882c500941c80c1000d8569108512084035800345a200d942c03d40180c440c020b081190070480c254010604a500b00040e903200d0060200c0844202ea00074049815003001c6040000c2025545034030250040011400811020030f0032120807511720801022001c110500200b81252075400d039030007011110041c2044d08c0d903120a65100c9802c40604140503008000702c020549940445014042c043d140d15500c603581d00e41808004c1c8000f62410903401584042908032000e0411280117100d1640203045c51400718605d0117a820020344585807001c8100a21480c60303e071401103d0007020100c0895403200e103400f001c031055030114410024500072014100c1c00080d0031034290f074151002454681d031601e01184000740c1072a03207500141e5008028643c0007495550 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 116228300 1250 116227050 116227057
    0x20906151b100501060e0f191203090e04020307030f030302090415050f010206011a0f190c0b1305030304080309031e04051c1101030c170a09030e0111330c 68
    0x2085070301e03a200d8841d10000b20f40b001e024807800543c15a038000502e180501e801a588040109051303030804601d28007081029070303540012069516500c2000078141c00a011000502d041403100480346410750021341c4a81060000420b10840d61a040c42814800e07810380b41d903d0400b80082009180c0511310f0343d20040c0c1132080a2041d00b070220000707815403003c02c0c201e040710710026802d4021604402000031070b4004108410401c8001c1c070108600c0104940c0e050140704c500d468006130810603003040410074000510000c0456501e0081c6800031301d00008a940c0690800420b81e140c1d201c2441490451040010760035900a00841040580099278000c1c800c03501c0c101c60b140150021140045480c1805600141c2038407821400c0a1030b81d40613802050101030b403441d000d0000b582106020030361400c1a201204540e80d41c01d650030400d41c0209480c07044690900b00769491010075059240d8644541644021300c0007002c5e4141840d81002c1c0340c18a0542032800d4040386458840d41d50740c0c00d0342 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 116229550 1250 116228300 116228347
    0x11070b07060629092b02040b03030a0512060a032f041a06030c040e0907051c020d0314040f030302010203150d020a1505070b04060509010b09060d02090615 68
    0x5203015070025041d001880d54082d00c2c0d072410052540900d82030b00012058204c0c2011355040224000281261101448004c045500070032600d0281c3c2005d0041c081201c2d814a40c2034000d078000c119100c003d64120007036440e0505045185042690350801140c4800f2440e84020711400094442c1c0348404541c0e0b5240c00d402c86c0c941da09201904201013008141c816000600f0500d04011a00c16041c0c10110010365215084e0300c400c5251139950140012515000c8900405c01e070403a010a01043c0b40c004d55000ca1944080c41007442d0010342d4002a01d450b1540e4001810f2280748400c6610b08c05400c0103480080104003104d11226a4070305020b8080e61040b2400810991f40e40000003031403500c0702c0c2030349030150064040a1807500b072182004044000c0c018010030f000781031044c0c100240480d220980310300d114500100300c03801c1c5142d0341d90946a0f400d14451103562a10204011912444942c1124680485645c41242c03541008280d0f0f560b2041d896420384c6000003010200b03801c80074424a01c26 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 116230800 1250 116229550 116229563
    0x30703020c0a06050d0e070e190f1a04090201120c02010b0a08150403080c04180c020613050303070c020d0503121e0103030905010f05130e0a0b0619050a11070b07 71
    0x100810741c1040324a18907406103034013041041c4148000120203074045040a100f04c1c00300c4110b2500c07504001c082d49411a600c02c0c42c660359410550f4446040d0080110303582014100744480f0b1f408059001048002e241c81501032581c520101003568400e101c0d1102035180c9500c100904544460000c1c0600b81c40903000e40240300404000584120015003202c0c1d400d050422241c00d9103e6560403540c0e02400ba010001719041804049070b4602c00d000c0d103041c4280400c9002a00001c1d1010180c00c08800400c0040028002c01e610004a00040200c1c0e9001406240c070b85500304151002612044071440d01511500c4042100008600c60340344041c0a014a0705404200712400103003440d588a0900000380017803040c1104000c01e50044414004100d02ca041081c00c19840b00c450b00c0c1c00c020303250710000400100905112002e40e02d445240e06500d0207a5030a4a40b010902c40720048410400d00c201c20000c0002d10102507a10903600c4003482d55040c42035800700c135500c400180141d0041f03081a10318 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 116232050 1250 116230800 116230813
    0x307120806030c0603130f0f05030a050409060b0313080a0207030803011206051b0d0b0607060213061202090f130e0303071106071b020f01090f1215020406120902060405040e03070302 80
    0x140351510990744114089138000d02c6e20b02c820f60302e000c1c02d00300c5003034210340c0b84210301304c03800015406202074208504a44d4809803070702e2802c1e44001c252982c40d800f10f81003074010824000d603103451244000c4165040700005680d80c0041c03804171f1501c85658005003120380c01100100c1d026075800801c5220a015020a200310388800442100d6000444694510381e90100107200410005401007445440000c060509101640e11070000343c1e0700c1101c42029240144009120b00c0c2c0c0c20104900d100e10403e9411400c0c890b240340841c0d000035180340440d11440391440708141078222a005503800030350000540e5200d05110401800e1a030307074035003021050b0141000044030148540003503105c01c11101c824040e0600701703800b40518290300d007080c20b0401581000106041d06403090701c1c0001e00c2d5058010441c1903907410f00900089024841000d903030300410080041560100c45c00b214a81002c00c0060600c109100140041c440c40d4400c03504241480f09880310b00a01001a00185000f13801341c606 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 116233300 1250 116232050 116232073
    0xf0d020915040f0e060301090f0515090c06041809020406030b0115080c160539090405070608090a0b0106030606030f0b0105031503010e0105040f1a06090105010c05030712080603 78
    0x419010b9800303044007640b5440c0c0108444400c611104c0c0e04440c001d8000201c5110a48036007500010820040d02c0d03640c010703030350b0000c503070884800103034004100000b601040c8142400a0102d209070b100701c0e4458a1031600501400035650f10100d5480c3e4024803c0101603540e251062140b80d0921405140142400f5002240781c0140d01c004d20840188014a1038480582a000c1148400040a80f040d100d034040101d041e450080c1c0342408101c100c950500c04041c405c03001201e1100041307d15004100c042c040c0000940300142c4a0709484107030806011943e6616001864034000d010050300f414100d00000540030f80550210041c1c0b540380d941402a600d043e6800410340300d1212800740095802c02c001041d4800da1000940b00030070040002ca41060903c440f1800c0d00c40c240e605441e11b131100d40501301000724051003c00300000d038200c4c110300743c501480001ca910701c0501c82c80c0d061010200f914005c2007414411560389550080e4203117803440308490007e0142c1e20840b0514000d110311082e644 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 116234550 1250 116233300 116233339
    0x915020906090607030e1315061805010806030327120a0c18020d0f020a1106010e01030b0a0e1903111902060708041805040308060108041a0405030f0d0209 68
    0x500c84403018100030b00c0c101010080c410240c0c0300e50801c1c1d00300f20030300d13107520354a1b900c20341d1a4071480701d104004030300801c0484008603070210a502040901810408121086000071000b030104d680034242589a50307282e0340860305501c0340d4407221403125009030b948035111070400b01c0001105802d0780c50003090800403c07060f41c1c070044c00790040e003600780340941045001d5409564031100110880058207125120078a042503038081180c090010740c02144005905610010004a08030791400a2040d545000f40a004101041c00040e00c4110401d0020720fa400840d0020301e5503500c0c1d40201c91448100c0101401d1401d01100200c000584a1804040e403040025072400350440007c1e40060185496003000103a9001d0b2744120707451001880b0014100340b04c2d8018120305001c04101080b1454940b40040c42c8203002031295041c060740c0400e00010900d0b011861b01c9030f071442ca0300a855500d950600520b140100c1410759000d5030f002680c40e0240460fa005414220b0302602d401e6034035100d010081 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 116235800 1250 116234550 116234557
    0x2031005090712150f090209100903021008130b070f1e021e0c03010501030f03080903251a010f0801060806011a13050301020708030108061605180103140a091502 71
    0x200003403c4200d14000b58601d5440140b48003024041d0b107112607035462040f41111001d07402411005d60106114001d401c182032449070360480c601d440f80c0020305550000761001c41d1003884104120700c000c001141c902803500041800c5800c01603050091030003000041ca140041d040d158006280d83c4801d99081d981018024546481e81d00684450045030152074005052400114540e02c070b1a01c0441c1c141c0c03401e02c2024041c600a400300d0b114543e081c140a4038602c4050b0068110340d10401c0590500030745d00011040e100d40340455420300c0202810101c01e055110000780a0651f2240c0c000240514129031705001c84003018001d21259a44030f19198a914092080105104040711840764030362a2200a11422a041c80380d081e03030b552208046801c9030072a40d01121a00d4000006004010f800c008580e444441041c0604000000d104000c1c0103014041c1002c0444007075500280961780607421880104084900c0090035103031940c0000301500b5004400e0301d11004400d9030888140950084 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 116237050 1250 116235800 116235811
    0x14030f010c1d0102250e0c0403020108010306090201110105010b031e01031703040813090b040b120c0910050315041209080d1206091b080c0a080114040e0f010203100509 74
    0x80c09040c1041002d80d149030741d8840c00e0320b811401100d000f001030040c06a5090940d00d0b080320052007407030a20070b009212243c042d0000c46817400500c42000140ea0007600d03a81540e5000c03101140401c981e20040e1201c03000244100141e50070b010000c251048154040d510a02c0108485083d101100c0e40402e95a402800042d11035000110340a0800361800021030300240700d50089890b259031001181c115501030341064407002e855140312501840c0501035010801000c45d800300c0e003515581540d581c2c4c2e0f40e0302e91160740264060000201222078031468200148000f0f0141e034000c8000011b00802154100d070116807031444126100610340c030030b400c1d00381503c5142c00181600800072030306603560405000348010554881c0070210380d8034200d00030785a03441904120854200583d05e000361138203100420b41103c030700c41400720400c0c0c03e502c000fa1604440d12034021505484c1020045005032000c6121402c4d03500c22104c103d0759588056004600c00c512a1135841102503d8108010040038290351 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 116238300 1250 116237050 116237057
    0x6030218040c060c081b0f030304050d0906031418010e0102040807090f0c12090f0f050c151804091406100e1605070b09071701060806010905091c12020414030f010c 72
    0x41451b0b03071204002c2001d03041001801c9910000700c05d90102e1460303000b2501210340b80c00142e44103400b1030300940780340054680c600301800342c81011440d1103224000145041c24031034650050032881c5000f98415900c40d0401d40c000c3d9600c82d200c0001c10b6841c00030740309944d4071600e030503055211250140300719250700703915554040c041c1e103a100f00c000140c01444000e07540e1000c042081400111403070311402070b5a110750068070003076496104004080251000740041d06c5010020000c040801c0303015929010740032500091014084e00b05500d2042c1c045402003040d12860b802c0c0880035000740f156804441000152000c5540c59001c01e00340803200641c1d80b80441c009100d60030000e0601e12407150302a007400c0441d542107940c0c090b100d01940c00c607082e001040c0d40d14181840010800d02a0318094082c0e05024025801c211440f00c1c0c0d40c589100c90b81c413124500303076600c1117118840d8101c106070040d8240306549680e200e240842e10300c2c0b24070605511038801c5040c0048403060600800344030880070f03103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 116239550 1250 116238300 116238307
    0x3070303080c03180102030412080930120a05160509030d03050a0b0409110103140103020604060c1506080312150906060d09050f030a0905030a150f06030218040c060c08 74
    0x5001d42d201e0b0005482000c4051581c512035800000034130145110324010000d5181440c01c0f400050f100007000f82c012101d641210061040d881a000080006191040bc00c9010702184a1510700b4130300503040c8080004503030906000d02c10b2441e4100f180509410601d4000307072102a00242c440c0d10445644540540040000d00c0401d40641c0c4026440504503030082007002d00c0d400090119200c0c074038112000d50210290b0030300c650345445000454600110300c1404d65040d0340004003240100d20441d810440c11010f61400c00068000d0000400c5142500744013540d19a180d00340c598016855850303100c20b842c0d0001c0d840304a00030b002c100e59040a00f400043d52602801d0081d1a0b0294003120b032101d4840454900050042010581508900b4044c6448000382c21005002240715808544a50304c4450482c3c040340c00034850758800e4288071400180d45400d07a0100d8003401c00d40c2d00195005514003041c0c0454660000014481c5115800030000380751a0704003620320340d280f108050608502407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 116240800 1250 116239550 116239561
    0xc0c2106060d0305090301090b040611070c0e04110d030806030114070c2d0602030a0b0603010510080709030f030c03020601050307120807020303070204111c0c0c060515040c031a0307030308 83
    0xa2402e0001c4500074645030b40780c14580c40c0800d00392421086c04840c81483c190801051002e1482455503c003010401c0b1031070448252140c0202c40141d0044020720300e200f00c042010003a08105011510102134034005002c002414041d03c03004e42100c00d64002c3d401d0110782c005411442c44460300c1410191188072604996840355007002120460f18608040c441c8400392010a441001f8900c881c400c400159072854a141d69109a8018540d1140070700000e20040c00303d981c8515001c02420340c0d0f4902203040340d90b410021184076050b40e1010340b40d003010346004014135074007100205036240039400b00c421503680c170070a25542c1c8016200f0070282458070a00d100c00210000e000340f02003400181264100308150f0009001c540000040c1000c05400003143c08901074121003a0a00c80704905c0e003080428100e1002803d41d20075104003c05040c0e81e100000c9a410100381a00c0d0780c004003605c10401410762803400780c010041d8580301c0b010071710703d40501c00382c0d868006100303025240e0541e501256500c07017 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 116242050 1250 116240800 116240809
    0x60301060906080406091407050f0a03051f0908030a02030f06010809120a020c0907110706030903080402041112152103040b1b0a080409060504020c07030816080c0c210606 75
    0x184c0211903568903240410040703207400024007403150800010b48251440d000421081c11403c0c01e000e170140000302404c00108002283e031207030b01302c07403c540213030f1005090645000074404104000e210800100c14841d0b0303403043d51701070352080700d032580c820000344c1b00e0302d0041d140c41408807415080380c1d005807026032111040101500e2180b6940c01182c0402801c40c00148942104469203400200340d03244c00c00f409441040b0740b400514050408026a40403900c00604440008202074003603038641a0382c42916040300d00304c0d01d2005815000ea1110709009205052403520411114403502c020401c048094940d40c0c101d0912041c200002e510789482e020010b081034101d0310b50072452405c845000015501c1c18802841010b11420205a541b13040422080848030150086030185105000d452500d40300000c0402c180c0340c01c00300d002d841e8035211520340700102640c5001044a540490030001c070710f40005401d408814112008a5401021002803244c01ca46120300c0080d54004404074400c0e080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 116243300 1250 116242050 116242067
    0x408090406091d010c110601052106040309050a230d03020c03070b07201008040615080102130803090907081003020d0308101a04051903170c0c060301060906 69
    0x6014202254295882c400b103001c0b503c5100f81c2140e021004041d1989410b400c1c42042410031030340c101041c01201042015540d54014090740c0c4c01034a40d401c2e54460000d421001100d03004a940880300d0300d18092500500403d91072240500030041002d01254039401410070410061900410715100c002810801a031055200000d0301036014103100d4800940f81403081d900500200c1504c90342c0c0f0011450440020b111070908034a038441c42c03102640030f603075400c403d14000d4216441c00d00060380310360034600010050254100c4004580103c00100f030001034001d864042c03d600050f03410b569407000080c0d00d07485401c10b02507000c0c944400207440e0900404450740c100c0422401480003035142e0380890244204402c1c243c0200d4040802c024002560b484d040b406418480e03c985400e0070101c40c400064003803406540d100f4409605030f80c040d40c0d100000d280041d5000002003158280c0f80000c10025400180f00100d0307809070090003812400c082c4200c0307048544603918034840d40d03d0032f94203d85d01003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 116244550 1250 116243300 116243317
    0x1020a03050f070f051e010c080c07151b081b09060a0207150c05010e0a151107081b06010905010302180405010902030706080114010305010806070e0105070501050406020403060b030f060408 83
    0x2d00520807240803c81c0701e00103240c001c2c8200020401c0c2e51000e0700c00c104042e44640201c81030707814091442c507801c3e030050000340c104c18450182d60b2900d890b450454141550300c9180030b042403508024003e603031107492000101990325100c0c000581c0710a00c643c0e610300050400300c1e45030303c001c00c9081142e042140091182d9102841995006900c1c0c0c0016604a5904240d105c005900210000c01380182803280c000030f84030090050000341141d0307659500d0b08560030201e040c040e65902e40c0e1510b20301d014017111f507520b1b4082c1d1210780e9002100c2e0b40d04007481860090050a02c100c0001107684009485014140e980041c045c03c00940b18644c402e0501e80c004004580c1c0b55200c180c001f0058070304020b58405072900d61603c21395036061011001c41018038a48040c100340c284401040794100216213180c026841d490007103440b00d00d00c001a42c1da4801c010000f0300c290310740010001400100c0e070141c8140c900c00c032028801d1425610030181c1d07441d803203080e4441507040900441c00103071010300181440d5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 116245800 1250 116244550 116244577
    0x90906050a1505120703020301050a0e06130c0c051f0501060c030c060203040312020c0a02040b0616020f01050909010f0e0a0204230f03010212010302091e040f0515070c060608060601020a0305 84
    0x100d51401321034030b01c103030584131040440c2d0040010301c1945484000903003d010340760f5400a4a1924074009410f10101ca400242c04030340c0c0b55920070b50f80d441500710019054020044503030b08003001a0a400d014440d10f9481040b501d40700002c10382d14440d1403408000c0360140d8a07846162107903100c100081d400034104409103c212000c0c00c0760030210b0b002903d28174042d0405040b074054140180010381e4049600d2501c41c0c0303020041e4068402400c0c00c408000c6d03030142ca418507414000300044e20a07218075505030b03901c0000b09000140c483c540840140544c0c6440503007040f0340c0c43c1d40710320078181d0046014480742c4800d40c0780340070414a01a41c0342907543c00020720124010140c4004a403c9900c0408880309441c081d500600c290304140b80708640000812003a070f00e1086090600c58601100500000c000303840c4803100e181801000c00008a98150b840e400350545d0401c010003510703010841004803405410b0400004a04e000400c1d010321505042c0c020301040300c0c0c65a0b0449180e400641c40c040701 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 116247050 1250 116245800 116245807
    0x10e1213051e040c02070f030602030c0f0705030d0b030a02130b0a170d1d100c0515010909050d03060b0904020c030705010603050106061106040507060c030e1f090906050a1505 77
    0x5980d042005408203030300d4001c0100703240915080c0300a84d2403407408442994420a020001c800c01e0400c0c04085075004540180c9a48402da040c0d16907100b06030119000380c02c0819490140000840208000d01428004011200011040c1071325501ca03048040c0d44041c1010090ba48601c0c1a0011400801e00824184500e51600401c0d0080784521107944132540c000561034850300d4000c1c00e548a20044007180c00c558808104c0083c1c00c10001c043e4000420091b0000c807000c2200c200107900020007a02c0440c07084c1d68580d41d5a100525002c281607071180300704094501c510340203202c1c0d001695008105607103001075075014400690700c1080700c4040c0d0302c4104030000c0411700038410280514031401c001302d032042c9850f50050a40d0701c54402c0c1c5034036401200520002600000e0788a040303d07607604100401c1d81850409072101341d40b05030640c4c3c0040d502e081407146a0703000c002841d4810b040e6100e9220080d00c03150404201c4800d805900c0c1c02255060341405408000c40652501c0302462415034074 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 116248300 1250 116247050 116247059
    0xf0705090402210607050a0e0105090d0305162a050904030e10022505030607050a0e041a0d030c0b0c0c060f0408190f1d130914010603080c0f010e1213 66
    0x180510031074a040001d0004198820300c41d50081e549020308c0c42c24079159003042e91035070006418140101c002070610030009a1508a04204904850416081400c0c241c03140141c0e02005440e8080740300d111412808070101280e5881c00d842118041d1b900740e5074210030309801d0014401e10100700302d025020340c40b6592003015520400b000001d0343c0e2204d504009549032615081c1864044090549030501105101c0141e249500c000d10030544d880440e00071400c0c0c0c1010510158085031142140d4120403558205424150010b400198241c450394510009603561500c0801e40e01500881d1440354110101080d501c000d0040b40c10380040c080c0c82d1203031800410240e100f801400a02e001804101b80c0710381052055044843c002403213050701c0e04c3e121013503820f00000d17003400640c0100c000081e42d5090414144000d41040c0e10381091070348001c0080782e841e41000b0f0b1440e0007a0f116816584900c419181a0007818000c2803031859045c8002c04000007581c61040c804d400c448084d4003c0c074902c000004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 116249550 1250 116248300 116248303
    0x30b0414100c0c06050708090a0809010309060c05070c091a0d050111040f0305060c070809040c020a0b19050c1201030f060e150117060907060e010c06110301080f070509040221 77
    0x801902c0b207038a44080b00d0809207001c2054940080c040e0b018442d0460030800c8120380800c43c588090707072022060340d90b51a101c006900814045101501c094a82080e00589030740120007040b02030f0284c501046001d6880110078240d401e4032502c00700c10009000f00c1503480c01c14400004034144218000315513074200316680d0146402580c1b040e0b42c0d000040b4000c205000e01442a40d8000e02160805450281207441d064201c1c03003100e40c601d0041d40e660741d400040700d10910082034220b5000e06001c0c15410040d000e07070412020050b0f40c100c0304d480c10000ca018140d800c011600300c0d40e0020580d042c280e02c0c6458004101d080024183d41d036540300c10454481d89014420000881e4081e2101d0141d9410042540c8481c8002444007005030310a41c1030026200303000560104456036481c2c0130882c84c0c0d0201c0100c2c0c0007407100700003c1903035050440e2802005001d6019506903044081250140120301e03071042d6031007180340300d065084604200883c0c09406c1001660031601d4003180081a5803004c6400603 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 116250800 1250 116249550 116249561
    0x204090807050a0c060215061e040f2012070804020d060606020d080604020c0628050901020702121504110609030a1a1008060c07050c030709061806030b041410 70
    0x102e4950b04403030244020002480150000791072144000c0c000c101650f42e070f401900302e0240c081489003a01c256a0000b560800c100070621020180c400e2240c3e5181c403041c0c2303010f0721071502c40303028003102e901d4230381413001880083d80d81050160440e0325480d2185542035904a001030803d0f80c0002000c110780c408104d0034080e010042c41c07964000c024550341740d000145030040c00b500c22441640100070241d00c90f100050342581000d240c0200580c1c4015210481d8144008a01da50070168180700810103468019409000e15600a8079100100544408071130b80f51850545411100f411003008100803420901c8a0140c000300585600e00d01b500200000e4036100118000729101d881d00318504061042c05031005c1d4100215090841915017000c04068450600134417000044c8004103010080c04010001c0b1950102d0150030f4500058840030341e40050040ca008211403100c4505007114035000b284521000c44c4d410080600c6a900e8950355407040389c070314950600c09846980c1000f400c41c82184501c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 116252050 1250 116250800 116250803
    0x30b15040e0606041a120604090b04141f0b1201020a08220c1214030306060d02030c0d090c0602010608030901120b0f0324091b0904030311130611010b060f070204090807 74
    0x111030300c500c0e0786c907010341112400400c0d04d4015400c0c14102000035680c98441508198450814083d18002c4c022947c5011004180710300d020188101d442c00c1c5c0191a03110045034541540e01c00b140142e2140710354241d02c64100c10700300080c044000681c0a8540c0c200c00c2d11201003420b00e1510040310340d00d944c3e001c0d0b4400e80050500c58000d4003400c0800040c05807902203240003001440c250300e0070100081d520301032051881d001940000000311602007260480b904010b02c20810405414030741007842c1d0502042c094403016600e030480104040c0e50004c01e4850a0b981651419010b00300405030f000505240300c0101d81290884410803400e070390038408d1004c2d00441c800140300008403003034000000c1001410b03250041c0c00c1070f02015418654039003004103e081c1555640ca2640b210310b0120010801041f030301c0c070024404181c201403a03401403010401c03201503640784110403040a03901800c03990000041c2d503100404116940521902e000900340d03c60004000207111001c03a00c650032103a010344c20 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 116253300 1250 116252050 116252099
    0x708100b030109050f1b1801140c06060306070903020d0206282106030221030d06080a060605030c030c01080c0f0c0a1b0f05041a1807030b15040e060604 67
    0x81100d0300503d0b041c0c2c03e62110800d0b081c0703480c26100c91211061880b6a044002013001c240030a0380071f50740955890b040501304916075941d55101c41d810191507100039541c140c4203000745004074958600c1414040103072a0000e2034103055030590350070410560b01020404c00303a0700f140c0c211306403680210811031900c40c8240e160003031240740244410f07107031000c41b400c4040410726102081c00507840341001d014001d0050812600001c00f00309507a451405030500e0641c036181070800101f0400c2d80810320b81025841a24248856501c9a04050729800c0210920b6056440403c0c11982076101e1444c0c0e6802500c03c0e40043c3c13a00c405255811842d80c011443c0c10401d5211409035001c210000c400c3c10300c1025140110010207081c81c80c3c229030428240f19582c03045844240902c110020f03410080400c0100405c3c0600c540c01d141503586902a00325130700f10100b454034251803c1070401c000710b00b50204841520f01d10b8075003071a06050080501074078943d0000820712001c904003010440c050800980c1c2c45 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 116254550 1250 116253300 116253311
    0xa180c0e10020f121c050601021603050c090c0301030f110f0406060c14010216140c04020409050402120c0d031b230f010b06090907030b150c060f0f0708100b030109 72
    0x510f00ca107000440440b11950050400c10600c200340c2c50465032628207084207020845840d2000101e161150024200c01c00c1450020300200f04079000844010101003a900144903546881503458140000d220103049150020b14070301c002107807a24480c40e840d00c002c065007000306848000c0343c122002d540154002ca046014800d0601910164420036441d401e80290310780300d80350b442c03240c2600b50740000401c0b0322075126101000e002e09104080303507000050300440d2515540c5031918003805054800b0703405901d01900794011140089001160210003030020707444140c141d80e085915100700818440121035610501c0c0c0041c0c0c0b4602d00720220164940004114501e40103082e050070000001075010780c0c5031110703950540d145d00044e50b108100c11161014669940e1109038050014003146c240c3c891000d040d21102403600c0c001034030741420080c0445410f60340301640d908103010140c80d48001403540ca000034002ca031181c0500d561203403d4a5088416a03603c0c96080101d400132b8000c91003807500e40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 116255800 1250 116254550 116254573
    0x20d060204081f0204030c05091306020d0914010b10050705031608090310060620030c0706200307020609150d05040c170303070c0308070311040305010e0c0a180c0e1002 74
    0x8083c51016003540207021881c062070340d503c83c08500c03054420240100e40a6000a5084102c40440d04100f0340112b0103541e00c1403c0080c0100800c0151000c0712aa5403001581c0c1c51480305201d00b40c4036030406801c19502c10705017802aa51901701220031078251000700400b02c2e070b448280200c010b070103108102454890052404140c2410041442195050310f0200d081145a5100e81c518005041c881c4095003880c0d03000c0001402c51086140e0b10347c0d21b02c0b03201d04c0003603215070100300307200150034051382c202c407110b005d00d8a29100d01c25604040e6000c803003401102194609244111403600346c562982d0324010480503a00c09a40d000c8a05441c1c09403640002c000c50807211980241c6201c80202075071451820000c060450703041e6071809002c000b002d20000f481e16009510480b4a510b4416640d62507640e83e11f0b1150290280b20540541030092200303060181c185840080103483c0620180081000703880c0141e4010b15842a1100c02c1100c00c40380702030182c4508851108544640d8040c0042614a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 116257050 1250 116255800 116255833
    0x10b0a05120d0f0302190917030a0203030114030f1f06050a030201050d09020a08031308010c1e03020c0709020c060402010305012304050405030c030c030a0f03060302060304020607020d06020408 85
    0x3a803040c0d0040192215003055000085042200111142410001e006480034101c00074000c0d0807490020500c145116403640360421049411589100e0304071502c1c0d11000c00e925228091140c081d00968018001480150190046440f080d44090111031030101c0725480d0350315001410100b072880025000c10800b8843c0039014500c06444182c0d01d00701f04500d03543c00284140305402c40b90003140c2d0f407a5182401c42d80e0320340c00c040003041d12104480d104c184507402c0c1e680142040c4130340d040743e61920382019005405054012041903594007000c0e842410120f0541c080e500c420066200c80c000c0383c0300880c94195500c042c001d5412001c0003864189410b02c0090119401038000b412100e010641d50803e5294180511002500036203000c01c003034480d07113811440d501800c15001d88900000c10743d04400403002000d000a09103d513501c0c0040d8050f02c1c0b0507021201c2030302000c1d402030020800500541442d01c024414070f880509201942c10140d1514803c81c1c000c0c0d08044d400f9001200440701c260300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 116258300 1250 116257050 116257069
    0xf0c030a051e03010302090601030203061f030c091a040e09031306050909060306011a0a020f0604080306030d080903030117100c0801091a06030f0c070602030a09022d090907080708010b 81
    0x5580b421a145504540029042d10340041c0014100340d00040011466202d60107254640440c072424961000c504a001401501d40c1c00c803a0400a00e607817400051013540103422710f500c6d607203e6141510380741c01d040040070310600042602d140d6100402c26072600969010600000b0507250381d079180c8031045801042010b2001410b0644a03611a2005001e1146080c5801c10052261507449a41d01c0800c403050f81002002c1d20101114021103040005104101004520500044040d030350400280c1d1419907042c0c00c243c50500b12940144018030120015a04140300110198101d401200c00311810324259820310248a0000b0b9654004001c1c1c20000d000e441010f00201c03000c03480220090307022407100e00008002c0450601c3c4000416040071500040f2200240c029200707541c0d85c40c0c20b8040c10302070034100030f00703e00075181c2c201c4d1a824103c104041f0301c019100710252410030b030104401c000c5d89480c0540701c044a402251800034650804015240081c2202e02c008180204010200304114a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 116259550 1250 116258300 116258347
    0xc0b031006031b0e0d0602040f0f081f0c110a0302010c0305060f0609040b010306030209040615060e0d0f1106040f080c06070c0b070602090a0605070212160b0f0c030a05 74
    0x1800d000c080f00b0b642103020b40000d0050080c0c644241689050000580ca40003036242c0500460310001d80845c0c80d0b081c00d402501624050303400103c03c40e6035004050b54a2120068106140e0204401c0c9850183e4582007003141c6c449034944510146282c2c0005428034107083e80490160f0b540715005660540c0500400354840741c100c0f03066a02c4146000403e0303661080c3c414251055948011400075603009921540103540c0190001082d4a803c1c40c1020007082001d9901c6450070041c500014110300c58070503400c09000180c42400c1d1540c007a511120b5243c03c5410885128106211300c0303d854541d1400b51006041e00c03400c5c00303da40e01d00f0480703600b000c01860286d401000c00300b25a4002c80d0103481c1c0c100440700511411503403440380e070a08800034000c0c944030550100420000161650344540a801824004ca071241e18a2181f000b03c0c50350781030040035031300000101d090308002080c4001c014200041500c49414504840380f09080d0075503000307008a40126130086816a6010b085c91100012034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 116260800 1250 116259550 116259557
    0xc0d1a030f010c020a02090406020f0c07090b0a050105040312030b03010f0c1419110a12030203091501080712020d060c0827070b0d0902030a200402180405040206070c0b031006 77
    0x55000251648010b6002a0185061f00c001c101004042d0341192000d0100ba81c80781d444a100800c0a910381c0c80700d00c07030820400d04103c0c00f180c0d42c0c83c10040700422105c0503100e080ca094910380c1daa0030303c41c50b40c103030355010306030341c0d05040300301c5c3d01c080c0035500c04000006000550b0380b480003c060851030f0341f0303030711b0a40c846018802030520459030030a40c0c2282090781800c81c003009407245400c0c40c0c06520000140f004403100041c90329140c2540207580074005185c01e84001c5010031200355040e501c24450050581d008010809c1688030f85d42c8000401c90004d0040400ca0015894110a55078240045000180c401d000c0200400211038a11326156800060b804202540320305640d84031414024004500800180100b2509050b07208501c1168050140e0744801c1d01824603000740c51582c1c0d44d00303055242c440da59040d507207050301c00c84180c0b50f140c0341078102c1c2c021b148040c00300502d0000c1c07041385c00c104c0c00c201e0480440e0300c90700000300800c50041080d6503450321000d401a0003c15031f2024092 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 116262050 1250 116260800 116260811
    0x13060305160e120703210c020102210f03010807092007060b0f101827151a0405100c111216090504120c080409050c0d1a030f01 56
    0x1c80c800140900341049241c003050307190016000404940300c0395a603100c0791043c00d00010800c4280510441e90408141d002c814140310807000b034a640404071002401600078040d98494003d4110001200d10445601e55003441ca40300202000b075402030700714101c036a01c0305008000c050001e02500703000b54030b1350402c0041082e0244555a0034028800000c11564427050900c1da0354440b00210320b0341c2c5900900f11050100326401c041c101c1d044ca44039000408400d00804649003403000060203840040e014031041c0100019a82d030002c02c0b1802c508451480e090304005031921035140b204819121103406240c0e16032070b02c010000b94001c003241500a00032880e40c0e40f00070982520500c01c01d9201030301d814a0310600091000c0c140000861030305885810b00c2c1d000302c0e9a0445a00942c4101d01c1103900c003030518603199058480c900030501c001c000c03030010401804440410340140b90407900100880f03050030034070901001075030404007001f00340341e40091a04206180801c20b41590210701c000030041d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 116263300 1250 116262050 116262061
    0x80c19020d0f0302100906050610082a09100503070305010e0c0901030f0f0216110301060305060c07150c0c150507090b090102030c0613020102060a05070e0d0602090904030513060305 80
    0x95916440018220b4901c0d4084a01418004d2156844078204000100206407952410400504080c0e982074010445e100c90180c07020b0182640501512801d2202c0b135005032030924003482c0300d0f151202605001c8041c441452551103000d00458482402d490301c076202d02d003120004084030b80c140d014484405002041c0840c0f060a90100c4248000038a80854500c007104060409800e0089510801c68400280b49070300d020100c0015041e2403203130000350702c02c00d10001010700780ea445010140980d0001c0340031a03610440603009141983c07144025010300c101c40d80540049980c2d01e0303520000704008400c900b0400c8240f2042460301c42010104010300c4c2400000284480c0c40c0b80942101c5e2400010003000c40d81c0204255150220001c0440c2d4440c9400e4007141c0c80c003907828030101d001d0b106800228604440743c0c091703203201d0a01680c498a50b52030010401c0486d4a41d448103949140d4200400140c949070050640d00c9140a51500c0f075581c00b1602d16441d110b04207500000030185000107220 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 116264550 1250 116263300 116263309
    0xf1f0302060403060e01090b0103060605180606090f180415061e03020f060c03040807060f02032104030909020d0b10030e0604020d1403070b090c040b0310050408090a03080c1902 78
    0xb4281c070707000740000034080c001400076401000b02c0039000d41044200e900000400c80340b80c001e502500c0003a101042108913036500890003e4050701c44c15072110701840701442c1c0341002c46068280000007044140039864031074031448405400c1e0340070f03281d2854008481c141c04100c1d00508005241c8242403144254a911002490500602000b41710700d003103104602140e50360600fa107541000300f8058a07985ea50340c00c0900d070744444a02c112008182c003000c402c102d060000c401d07600e031607a4110002d002c1e0054081021b10000005004500340f1200650108044810b1b20250140d030001c25000600c2e2039800c42004001084040c06c0400c145c101214031f40302440109805422513810390701e8828039042072034400b00d81290315078a4400362101042d884103110a0b00440d078003404d03181050302c0c25141ca80c801d000a8be407140314110b4041d03203c0658040c5544140c0e01169026000e40031090600219000085100050b0392003503903500d00106903505003500a000c0700d03109010100b8810f003907040c0d0340d001c80c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 116265800 1250 116264550 116264557
    0x6110d0f0201060f060309050601050108060a0e060105210718180207020319080a1806170405010603020301240803040f15050c100e0105130308061212030f1f030206 72
    0x1000c11114825001085000b50401000f905900241c0a19262107100050062903000c00556a5110303420001076154014000c8a00444000d01001400d906103c0c0140089074060303e0717181049400c008452001450b85891860b44003508600081401c0c40320004080a64004500c640c2d2103001004010892002c009100c2900380c05d100561500d0150000034289404420840d01c3d400c0144202000c0001c100020300c40716200b511540b501c54010502c8110100300c500812010a0310b9100c00d554101c0d00d0b03800ca903032080c8501d001107582512540440e0039206402110241200c070307100200d1a41180000a00207004500000c0d42040d05c0c4c048440d401e004140702c0d45a490b6202c071440440c0c01c2c8204100d60140d51001d046507036980003451100c00801150752485502d52804000c96105144640700d2138180f6090340c1c603080039031196010000040ca10380c21000071882262260401100a00003961003078420610740d18507843c01602040b62503019401c11280c2042c7d0107000c0c00165510350a8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 116267050 1250 116265800 116265823
    0x3030409090804051809070b0405010f051c06030501201e0913060b03070e0105131a04080105040501020702031e0607030f02091f0e0303130306050403020a14010b04060611 75
    0x208055015003400403043c82107030000e941051004900030142c3c080d00c5603503405015020200d820b000e40d140118699401540107941c0016001000b09054074410b102a1000d13a03001a0600900b0700460440360494100e64030032606a511041101026442c9117441005c0c0003052501741e00d0954190141c5000c0304080450700400c050224080c06a41c403a0f0040815521030078204010042d2104000e9000c0d800456845d00000c807411486d00080d4490401c0c0d40f8442d0a0385174044c50b440c1490b04d90308040752001c094044000c03080c000010303410030074011140514043d90006942e4281030042c18200344100800d0140d682c811081201700881c00a240d030340c0501d052500103100e20000f502c03a0081d01c0382840c803940c4a0740e01000fa41801c04c8002c95100600029180c541130011118203241c0c0303a0055442c2090780750a01c99003000410a00d4001702e038007520a1054600d6280146d44040c2ca210070195400c0c0d1582d514081d851160410748100c10107041c140c100100c01c540c1c161092552003000f40d42 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 116268300 1250 116267050 116267069
    0x201110408060c0313080309060108060c0a080712020d11040e060301050f150607060908090907030605010e0418080f0d140f04030f14160c0f0506040519090603080304120806030304 79
    0x81c20b00101c45c5106143c0a0344904425aa42800c072042a6210b400703005041a074050b07240030a1100308a0000c80701c0400c2c5941355419943d032914002d850344041815002100c0340c08102079820f0406601c95000203c0c44011440d403103504280884a00010040c10140030740e1414082c00801402202c0c0e0039800030b075140903a0072008850010500302d002e00580100620b0801c101d40d000c0052400180180c11001e544034411607a0b403e2088050700c90340d101b01c07401708011210101d15800c10703820105400540a00d0801c04094564900507194800c0307603104901003000c246003651118500903d00f11803546115041e10382048201c3d035003030140c042d00060600404000c40c541c0a8024020702c100d441e15010300036180d00c540c030b0100e103500b20149001c0303a200e0124040400e40108640c41c800640740040c1401c1d0074282424140010404035805c40c08011880600009111101d4051400614030400e449902c905261504241d00003000c85000c003880303110010000180c4000041e9800c0303502a22 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 116269550 1250 116268300 116268307
    0x605030c0919090b071101050a0504031409061e0403031106150108060f030a291b03220c0501030f02180f150c030c060603030307050403060b12010e06070201110408060c 74
    0x105958001c03d214000200812980810001503d402005105030b8241c00c1d0001c0c030240d5100340500046903402c84000b004030b2001031a1110300701001018000a45002d4107040c5015070210080c0032041036980304c0c2440a900190900030168082d00e90701c0c400c49100c0045c001410a1742000540c2d901000b20107042020403000a84241c1c0c400311a6000c1c00030103810755000c00007900300705500c090107140f050210340412a00300d020103506084a4803400c4001c2c4100203000141d900d000c0d241e030020300038070702881100076001000d1a49504001d0014403c4036048115864000098203030b030844603811403031364418411000f500d100e83c140c21441090071541c500703c0c0300d002d1000420300b116100b1300b0b150000020030710108070b00000000b0840c41c01d00d50704031900e5655690806607a0302c02181c1e260000388007404100700052103a000108107042c010031401e54084250300080c00c4400d80c0d044075841e03501c0720703040c01a483c2d0280300302c3d943e10324217568682c03615040c8008140d03105400b403c20001c554000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 116270800 1250 116269550 116269591
    0x10b030c0715050402011803170703030902030706080702070603050606030610050408100b09010801021903090f0b0916090507090303080c0d0213030b0708040f060509120d020c010605030c09 83
    0xc50848000650110036140d01e14031000b044001044111000ca005c030702c5982c11002050250344d042012240d1052090440b1603000881c1c003d690804c0708120140b41d00c0742111030050760705101003000b8085c02c2c0c1c0c1c1d004a41c54039100080c5031a035250f200703105151a160a101968a52004907030f0702180039165010b00148c00e040c2102c00e0f05c11035115803030305d00451612002c0c0ea03034150032400385c4003800c88000490380d0701c60031b50901b02c0c03003a4030b002c8000c0d540f1542040d008030b00980181800c1c60054035400d00010b0151550406e08100710741c1681c1036003206450402c0c0e6100518000080c0482c140100494502440c01400711038180c00082c081c05070b07100001d00e6441041089079201400c080080d5140c82d040c88400e44840320740d0004892454040000030322540c4151000c500c0303a90840080040c44032182c55060003005c000e00124458001c50351382c035148004c0300c0020491002131400042c2d48042c01c00803142114202c1e001607109811006088a199840300700b0b2581203010001030b0381d08201907 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 116272050 1250 116270800 116270821
    0x70b0703060311270c0408240612010f06030803071d09060112020d0c0924050304060506010e040c080a1503050d030c0908010e010209130e0a030e0d14010c17040b010b03 74
    0x208484000314600907017044001c01000c8060401c44101e4411140c0c0c500c0341d81e10904111240703000b00280c4000090004860740fa104054002000b2104000601b8582019209040d60001c0d0415030700c00c00000309000001d54451580000c0111282c010528503200b640041c80c00b010140c4083d0401980d003078003c02071083ca504596105e4402d41c410800080550006040248035200714807004139103540021850701c442120312480b1000e03990389481c613921603a44600408000e4010f5042000c015004851070325a84940400440c19441e80c2080345410071a0034143c0d49424401d460012441c1001c00c00510f00003100c02480b100da05002c210041440300803100340580741d124584170760801801145050701035006000b03e540c151410500241c0d581c0100b01520854940b0700e42c0348e8042400c542c0403e2045038090910400100800311b03008040e00c031594445403841c6d00e844965540d00c401d0203229005a90348050b1200c0c040030901c241380c55110f464070940c0512800222070070010009814198 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 116273300 1250 116272050 116272099
    0x2030412050c04110307021c1407060b0406050105070f060f0b131406060412020f01020c0d0501050a0b010c03020706210203010b0306030106080102040b040501051b0d0203070b0703060311 82
    0x49840224039842190a0455440c42c84101690140345031640100c4020201011240b141d0305035002400585840b1001e101c035482840c24110801800380c00312181c8602c2240182100c1d40a5070340400c110700c0c01400c00044403500d40c8880d0500070200007c0e80003680c4100d2078001c4035046040001c80c0d40e011005200a407038050407295122001003003c2d420607110358000b0055a8020390417150503075a680c00e00400f841107000e41c0c4424a5000c6011005180c811b501e51052201071050351203000c005c401060814403145001c580d5a5140d90402903441c1300d905c10b84420407002d28002a01888944010303440d0341c0d05003d10020000407110800c440340301d030002400b8400000501319517075070390303055078814681043d00c58034465402c001000540c2101402aa41661425a62030780f400e4074040064849074041c00502c18084416210740000c9101803052406824458028542c1d0302114038100041c2c00300140300006240c500641072001c01c110740e00009441ca01500c901e0886216000f00d0510500c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 116274550 1250 116273300 116273309
    0xe250b07020f151909060e09040303060503010623060703140c0102070b0c0403060b0108040203030a0e011b050d08130b1b1b07060f020f0312060a090f060e0906040209070e01020304 79
    0x2c02907064603500c50f40030b801400c110b41c1416159900d8844601c08850034503807403041100050031a00031440d2840e0140c2c6c0300381c00501c241000210555104042425100d90398844250120b180703203d02c007001c501c4d183d5030b0300389034040710b01c4c2d0310380400c0355809084415120b00d08030a41101003000d82c07154400f54115400c3c1d076045034000c3d50300d1078400014074007603019000454506007070103440b41c03440d405082080c1c0103d6005000d1030501c2c3d90550200d0742c1d0000000d00c5410401c100d100d0014803103813024682c1103980250007034259003002000c0070703201002c085c0c072603500f03c690382000c0c1020a15602003107805c03401482d0080c40301e604003003070340101d8014105c41a515a0301d41b1821205c101000488004449880d150400000e5440c001642c8078014260300310131300c3d00b0401007400d007180c060070900c0e4070181c003c059906168071410014201d42c2d82440903803040ea550319041c0041d0907036501c003c0e4803032054801800145046d9000c00c0100c00041d0000b0b0501c80c4000818015078000c0c0107031000f03070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 116275800 1250 116274550 116274559
    0x71a030a0c141206040c05030f04021e0901030f061b0c0308060604030803090a0201120c020309040b03071502031201090902100309021c06050f0f040209011502030d0f0e250b07020f 79
    0x3040849481081850207031244c920551a00080f07403907040c0141c0c1907034031400c100f280c140521754840d001d2105e000c1a1035400c0754414904034002c000341c6d84d0b2030340c13185c00303103004055020000c891445c20304102c892140e450820004080c2da80c2c4012a8807149010300c80387e0509d400d01460b211803011540c40d0013036810003000c0030004800c0143c0b1000018081004034000d80e901c1c000751003122928000c960985000b1070050b00104032141c1c0342e051070703000f408201c83e000d0100e6002c0f6039100f844410b041101c41d40c002c016000007820014052160943c1405422406002c00c101080e0f83c1c000b459100309035809205040e103484c006030030355650700c03d00c1c00940106007000301c134182030b45071210040c01c00319100300d0b440c5030035004645402000c14030a84140d5000e059100b0503400e140708120b000075010650303821403004004809640015005500c8582600b5002091040050030782c5418161040758402808032900192802d0712078041840c2c04403400600c826070340d0039540c0042140010a650201d070003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 116277050 1250 116275800 116275807
    0x40c0303110705090403120f050c0f03090a0f03020703030305070e0a0303081f06020a26090108190c0804020f010f05090d02010905030105070905010917100b03030c0a080a02071a030a0c14 82
    0xe043d081f0401c800d81c00352400782001502e075600c0d84481128015078403100021028045c0e080c521840c0002075411280040840e0100c03505a80e59100740d5098050460040c2c100001c10404c25406014036a00164281840014540b0301300205001a00511028040194800220f6200300f40410810a0700c41c1c81c00b0b00414031900c4000183d42e03907441c03800890323500c90016148996407805182640311280810802891300f04020011a0282c1d806444802801343c11010002108007a200c3c2a050801d03641b6921583e1402d801040301c000c6014003410306100580c000951400c0d0300c40100d8401c42422107a130713604481140012189036160ba040305416600e018140322600e0b0300000c2c9042100c0c0240c3c0c50203c000d86528004141e43c41442a0000d5070b031224414a00d0f14503a80c110343c21062010b0210380c2000002c005591622001104c280c2c1e00c2900054030b250543d50601c0a10050a8403030090000900303824051580b41c0310050060340b0a0b43d03504134604200c3e2150141d107202c2c983d402542502e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 116278300 1250 116277050 116277053
    0x315090204060f08061005030402130e0c090f4005210703020706030207031103030f0403080a09020306130521030106120506060904090203070b0d0905070806040c03031107050904 78
    0x1c0d4070500409000c03845030544149554810344081c4e10400380580344a05071203040310181c81580010388103c0e80f04080580b0740d41c244019101e1440b603800b060005200c000c2e011418000401303409003460080c41d034000204202d10807000c1560340021419040303002625441c1c0e40e8044000611440700142d072540810100902c000007440005540c009031405d220710480084404252050030002000340c0c220010801c0b0090003a8047e0004600078200300c1c04500485034280d086500460b2803c401c00340d45c5043c041032640c0304040c583d025032000341c100b04105c02030b0002541ca080081c4201c0380010100510707810032505105040162828001c20068402400001c02164009000e18000980b001c01e03003000c03190f44c03806064042c0d8800f0745224900385549060002070039000341c00380c0c1c00d03106074080080d40174600310003840318a440b8800094141000e02d03005013031241c9030707100c0a42da40c0f203c024031002c5444241410112503050400710300880c540e06089003040d2203503001c80ea01c00b030036108000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 116279550 1250 116278300 116278319
    0x4020f060f0d0b090c120109240905040b0f010803040338070e06070c12060908040f0303080c0c060c03100f0e07180602060105060a03060503010603080c06250309030315 74
    0x116400404c4603449500ea4034401d01c02d529000d10340c40121034004000c01004080c0855103c2c10014010000b004501600c660b00010300d080c580e400324074950754a80404c410b000480a03410f811650003036202000d540360600381d50b620300031408060302e40704d0b20601e54a8220702c0f42055903100703041d03070f00028136085200c582003100701402c271115400306201c1040e041c224170303041c0e04490055501c6245000032034140b04000304464a807410843d032007590f40c0c0e5140e0225508402030070062040c0c40402640a0545c54010f10401010b055096400e0043c401c0d00d18081022406075403100450130443e4480d5200000c1c6906038101da44103d0700e0041d50341d030110b1010814407880b0b101e43d915031915034203060780c1030410891042d544940030060300070300e005002601e400b900900303e0300b4172480c0c0810f40ca51140d00007421281182d1041780c1140c00050b01043d09003003070014079880307040401100e082c100c202238000054103c1511030010103648a080308109400b80c0c3c0f001c0e444141d50310198010030346846144 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 116280800 1250 116279550 116279561
    0x30421050d03020a091a0d0e0304060e0a0f06050307091205070302100f0c1b0e0906040606120c030b10030f0b040201091203050708070309181a010c0b04020f060f0d 72
    0xd4865004050088074010700034001c480c4180560b0ba030380801145082481d13450180070580b14403031400b0420801c9079900c440d000e454003462444018569a510f00381d03025104c4605401c0b03150164510340300070030003010103501c4523040b03600900f081070b40c1f542e0b0381600b1680d0580313030381110a549002d1f01c030000030301c200040c104007901c1c425240485c8c402c040c800f00b0f507180e000c200034007800142a040b07440001844400c504d0031880c281d950300d14015444c0c0404d00c0c04204119503029259010380c0c104400c0c01154043c03800100403a410f4414240e001d910341021b803420f0703400081c0004ca0031401040d00c446000c3e941200954000d9000c810451492400d04181003080d202079000860035200440e806400315280484140c0c1034907800d140c64140c0c5e071014901c2e0416881902806a0b00c2400180c04400b41280c041c9014422000600c041038580d441c10165000c5c00514100300c1181011000184484d110a4101e501110505104030485c000240c00f8410200d13880307100100458030070842e52103500320 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 116282050 1250 116280800 116280803
    0x150a030f020901050904051902040e030c150106170117150403050a08060603090312060a1a030106030c020d0503132604030204050f07080f150603010b040306150602030912030421 78
    0x41d10903d998400c10081195002e0b00d02034600d0b00401130120404420701e0f100302e88540301400102d9040d600c610114110342040341001c0c00d5400210078558801c0a852100b40503049a040241c2c10300b4655040121000d4140600011003443c4018400c0142c001c103c4a0103000c500c4100520b41d180901c1c0c0103200f50402100c0d0008180b81c6408540245001c400b603030b1103030b603100e00190f0030b01000c68425451020064070040d0001c071580c20220f2801c410b1140e0b0494411184140c6590f0b5250903001411030b031030b4174a01403c54109a0041e0300da240c0c408212504041c20344500c4400307500c00d040c1140106010741c2020501441b52540d00d18440c807000180007128000c803010001076480c1c9007100b606040480340c07000011070100c0083c2802d1f24000e8100d80010901c100f0613007040d4110003141256000382c0219440602c082001c008210705400350194509003480c40e100030910380800030395640241e402ca00d225078500300e2080c044403401c0065030300425500444803d810741c0d92180704080d0099920 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 116283300 1250 116282050 116282059
    0x1101090305091e0906040f111207020f010507081b19110d02030c03040504180506091c030b0307090e010b22050709030b0415020c0109061505010908070e150a030f02 72
    0x88500140802e0340f410103c0503000d0450102c6aa41d001048001c1c80604071a4446a0351146202c42e04103c0c1d00140002300501c0349040350900301048041e11f02141d4512007140d41c2c2c180302c2000314555000d40884d0700700d003411000c5500f502c24068421128041c3d050207543c0c02003203000801e41e0130f031b018464a11020300c05054450007042e04030104e0312885070b08149510f40e4020002003001e81802d81c000d01511520000c2818181c0480c0c1e2031605140052b9000c00403a408007074035020040150f60901e40c0789081d4101013100303040b08030101740c03604800d06c600c022055641412001e00c28080d006450b10101c002c00094480b04410b80c41a441c441e0f80342d4500c0424501000950000d0141c3c400b08240ca40002d225040c5607202e550310a002d03049400c0d40f8924540902c4203c10b051000d004440308107120781d20100b205d042c1c2104d030b492011000d034012070401c000050b0030012101c0210387c0b5001e80b03403880e00d005126540c0c444007201d4a1920100c00b0b40011441c40004280b06243d0001403049100b1507 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 116284550 1250 116283300 116283319
    0x1615091103070308030105060c03071202010203041a01051c0201111e060f060d080d1418060c0301050607081303080a021005092a0103060e1005040e01020f07030c03110109030509 78
    0x506640c1d14643c000203221040410061103e8078121010b8820300808408403450300c007160303a41200c0240303007042d4800583c0d00481030200f04044001000079800744801c1c0802c0e55032521000580c20480c1005010340c6940602d110000d6902c521030030030404080c00100c0340003811041e02407c24040402c44e04200b4000c99010035058200c600c50540111001410020345c6c860b592226411680001c4420001d665644101c0d100061613101d10b92043e40d0320000035042424078070320035003006402080d00c0051101040103000c540c1e200c800740c0720601d401522883e20b030b1580b520302007048003103500040e001d520041592180154001401c0582040180f070034040c0742c44403848076a40f031214502c0e004100300401d25840e11440b10304446807112405160101e42d040d521a4046d40b8402c05482d000700c00c60040364103200d1405d1074090b10765501d00d0200210700d400c1c890794000c0502c1c05a030100400708000601c0c07040038075218020004400e20424001c104290440c980980164007580c5586d00030700a44 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 116285800 1250 116284550 116284583
    0x61508060a06020601061202070b0f060316150e060702060316090f050d0201050c0c0d060209010f02061509072616111f060306060e06030114150105161509 68
    0xc200c207004a03050358008103003903400c060068a00551200005007919400e000074008901e04101482c022004400482d8203070034560285414034814690b078140c05580c2c84810480c0e881c03086100840d2108500e44526440c001d44001629407081d800040c0d407010010050081c5c1c02030b0340a0701040b601450301d80c0c804459840c1401d1205500d80c0c4030f06a0b1004030b0011203405540104001c01b80c0c1c08011003030b40c0c2c0003c4864002031074076010640580707031140d020070b084442d946c101c0414024840703107000500d1113103000302e660380701040ea804500f8003a0700311a000c9005140a039601d01d000d0100804002d8450500c02240c80c40e03c1000c40341419001da000003080d031218060403950040420483c0035080071032448041c58414805646c0d040103241c1d5500000012074064032a440141c45c181d00704009504001d01054256400c00c0d01d000c555018003c18011042d03240000000407803400e0070910745910801090300d0340170507240000f80c207080c134100d42d44c14002d5041d803185129500c100800760307486240703 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 116287050 1250 116285800 116285809
    0x120609070504230423011d040f0201020a1722031e1e031d01090b040303080405100e01020a02100209030c19031704080705010f2a050106150806 63
    0x140c6809011031010402800200c0d2008560311032014a400c010b0110407181d000b00c1c0442d0400a000c006210112011000380e00e45003c0b00c90041101d01e071480c4e400c00d1401441c0c00180000780000b0010300c01400d084c0308590080c02403100c05500140e0045460400d9502402a9448000b401c0341d040b460340b03034030f84815215202c2d0300d041c0c80d00b00d4192010120107242240c01250040015150f0030028902e5507640385480a510030494826507540407610390141400070100755020016052050380902030203220443c1d025101143d40601d090300039520340381000b508001d40d403203001071414140ba001048062054004048004c1140d08480b4000d1001d04440124003131144620f51503000300203031018510b0294850240c0040d02d9401c2041d540d541c0e0355032800144010074a01502001250030025038409100b254003e280c00c1c240700461207038600008100310022801d01c0e500c0c00d005042c1014482c028581c030b01d2880d0b4018020080c1035290300d2001c4104441c0c62485000030010310000365681403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 116288300 1250 116287050 116287069
    0x305010b030c072f0f040b030c061308010606050c0f0d1d04021b0601150203091f0507050109080d0606090819030507050a061d031801030e01020903010609021206 71
    0x300e500c080e0781991203800e03946402c1c2e444140d09907030300044480c0d61007000c01d40c808080d40c1c810000c040c860b842e04d812002d0040d0b20840303541d144d1103185040d44400c240e071070115118101000441d0290f90320704442d032551145a0701e907000201950302e0128081102c0d600103009084441c540030446142c1692103800554601c28010102c0004252850800c020040310005040421000304050700b000300c0f5060a034900c0034103030742c8104240e014800400124500700100c40c0185c00d03620140d843e00c00d0b1100428500d100c5005200341401041d034802030f420740305805641070380d50f00c80e000748218501400e00e00003540140c0041d10301c041c0380c11300c006040d41c015284582207034450760207030103070b40103160745914046190842174003802000c02458000410600c00080050701c14040011110807904481501640c03c211501540c0d2082046900c5040c240042e54000078003461702080307079035004601c1400780c042c6101154041d0308084000c41c5001d082e0b000381c00c4000316010849529a185010440400d5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 116289550 1250 116288300 116288309
    0x12090c040f0209030c12010f111b070b030c2a010e0601060f0e15160c0e1305031207021606020f010c0507080d09020f0901080105070f0f140c0106090203010b041401030501 75
    0x90006154051601308446000c2040050000006007241c41d20720f14810759039009580720441c3c100003102c407401034400701d8291008101d0001481c2460610381081e1037480080c010400c1980e001c01c540b00742010301940301e003031000d0031421000007030380d200301d8940038100850046025004000011070328a00c1200804040b920715901c003d20601044188040107080c81c10508980c4010018a03104002400004400b230307100d00d80c500e0384986040d107020074101000d40315410074540d03004500f01062001090301c00700c101590002e48603440e55141a4030b08581240e160b22a030321040c10003c0c0750354010650202d40c0d52100028003610304138820403180b03440780c0c0724001c03c8044c05000c1078801c042154001084c891000e840c1c08170708980c0074001041004264051702c0b1580d103900410020540c00f200e100c011a80324103100302080142d241c0075100ca0041c2d500e5454144011800600b102c109411010003400901d41c115600c3d61650006011644280550384d42c141c24212034003402e500c280f207503a0494 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 116290800 1250 116289550 116289553
    0x14030a020105030405030405061b07081609020c070e09011406030601060801030b09030705010f09021305010b0301090b030322030203211602190e0703110f030106031112090c040f020903 81
    0x4181603801900d46400c090320990b0316200910012903d6110400240280c11481d01028102c02041146514140d4190040c20305500300311444a00340300300c1c402074030581d22100310140e141d07840d004140d031420200b0781c00040c0a454441c107100c0c20324019485420710000007074244040741c1d58401810340d02c10003071007080c0000700400010800300300c00a09151300511700764256440c00c034058a0b04c60a48680a00d10000385550307130110f44c11460302c4044070b070002c11115024070440d031400f0951021400144904600300b41c4801115002d036034144119426142001c0f9403140100e0503201d01d4012084ca40422400383c070940c68403608401448400ca41074201c0c1000c1c1c00c0c0f40035503690319950042600748040f41c02c100c05680d452564915600144007401d4044c1154219241650703004041e1403c0d0000c036460301c4010000e0031035800c0a101100d040d19014107002c55448080000c8041500c124030101182d000414180300400d000403030a03003440d96013140c0074008507000d00d10103000c80c40340c4060715070315 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 116292050 1250 116290800 116290813
    0xa0c02091812040e0c0c150124020c030a0b060a030c080c010e03060f01150909050a0c0f0908100b0604051008010311092503061a0405030f0d080a0203060415060206101403 75
    0x2041d005c04014540c584402d825101d451487c183c282c4280c62080c0c000740c04071901c0249600304416280010700c1e4070086480103200f83c0708d802c40482c0c0c03a52002d900213408a00510000756440d264001c42000a540c81881c4a000e10395400c911030302c07050b6202000d40041d908400710b03c02860001415409a030126880744040d034a840020008003d2081102092164400c400036842c10b60b44580c41c4120385a01d00880c0000c0905c030000c2c10384101c020f0311000c0c4a100c54081c8000c10300015120f2400d10002d900041340903a180c001043c2b402203501c000d03440070541a46107102c0d603010840e5812a44500c403010501c880348003c101e10038074221190b007011000b240214603107020040d001051240c0c98100001c02a880d00896400c900d1004404600d00600040801075401c2c01c0111010400021000e80102d01c040900140f0f91030b80503090360030842c0c011000c9480755846901c4a0016044208031042840d51050040e4580748104d030100300c40401d040000800c540c03039420b8408210780041c00b8005 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 116293300 1250 116292050 116292061
    0xf05010506030a0b0d02040f0203040b0106020706021e16080a050d0e0f101107090905060a05010806010501050c0f030304121e0e01050c07211203060e010306020a0c02091812040e 78
    0x42c02029072666001030320b1740c150700250304c2e00c1c40f8032035403942e00480160b40c0380b805060603800700300b041e4052011035205907000c21486601140000d002100049110f0181f0040700c0e0350f601e40303a166000b0303c5e000c85410300c0008840b98002150b1100910946c00e03500c1e100400c1009481001c4c0348401186c116001c00c8203100145403029259820a40c1410b000c840c0050201c2d00c02c1c40e05260750460b1842c0d69440b0004030910404010455016600c2d02c0c040c4020360600003825100c1d00180f00d1541407080c04520801c40e01400c2c840e1041c400da642040b07984910b4035007484c1c01d04c0701c42c004114010a406100d031300c500b06032038401010700700300d1525410143c07410079004484607404265860040e01440802062807a6030100c01030004815003120301c145032141c00e10f54005900800302c070041c50b1600398100840a40c15103030038110ba400c400016203840d04090180e0f21111f014034025030100600080000c81d851405a90429241e46012150f4071016017040200310305c624040c80e4000e007808000201c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 116294550 1250 116293300 116293321
    0x509060a080c160b0601020f0a081b120a0e0f0613031b2102030f030307020d08060d08270303070206040302060304060207050304030f060b0a0b030417040f06030f0f0501050603 77
    0x42d00b110920286a242a015030301c20011036051180440d024002c08080c40071350340c1d041081900141149005d8420001c05a071104200c3c400c00868600d80341484121090050301400b0908404549080456541c000560010700400c00885514851402c00c078610740d10307090810548030100c010181070795005040d500c442e8190300042840c50070170215980041103071280741000d10f1002020360f82040c4182082d00c10503050032101901021035034810300070400440d071300182c4407a0312041410020060344814010844030344140002909003035001907000182516522062001000407100043c84420002016241d205000c2e000c0e5200d942030200b4009882d140008603007043c45990010728003806580c1e400d0464215038410f8071660f06101d02e90081c030006018150b028081101d150501e030303051000001880c00050300141000c06140c1c440305400304110100c6020344886420040703440e64450000303018295140050850318201620b810b40d4003114061641a100300800c0c890840d0394210f03649 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 116295800 1250 116294550 116294567
    0x3070506102715090f06090902090112050a020612090d090812090a0e0f0109110403030813050c1c17090906010f0c1211011406060a0c02120609010c0206070509060a 72
    0x1070b025540c0d540010407007601001d01e010007400318043c0440ca017421882590111407880d88180d8146092225240050b41c882d02414151049180d1100c00c0c41b50f541841d515003144880001e40000000440401c172200100c000c61040d10074000f150039509a00d4000c0740c20003594850a05258080d40c00b003c0140d003a00003601400f0006019440201e5980310a5040705000341c90b84518050f101c07006202c001f80c1401501a55100340c429185400d1a40e90000c02c0180018803490785c00185030000000c0013401d0006a0008a0013020448007045a411001e540d1052090803518001c110b41c0c1e6042009060081d102c444800411144e42581c03540c006588250858004400300241c116402002a10041c1f001d41c52094503a101c1d04e0120a59940500b155030203111280c2143c803140820500740c3d20030007151541700241c500300c1d0b0f20401d24404141603420104400e801c1d80246420024000015071108428820036402c58085846400090300c0ea441944105900302404101c00889640503400c41c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 116297050 1250 116295800 116295869
    0x180411030d0f200a030806120d0e04240e19060f0312020f030a0306060f0e030d0318020a0b070c1509050103051905041a011d060d030c0f03020307050610 67
    0x55000e010319900105090203510013040b80410103d5091155030f041213404282d04400f40b4000702040021010050440304030780c0020b40c8070719120031082c0c1d19812128080201c0301c82c8800b080e980f0540f91102c080e406001116180d01c0301c2034070400020740c1d011074001c06084482080300391001504540b264a0b0070742d52102803070150702c281824000a0f42c010001003070f4003c400d0340c00103440d0b0309048000b4018903900c5d40080400c5041100c1403101e51f000300d4807002c04591410000307840444107600c00f0341e4001c503c0020303520160800e400514140c2d510001d00c500d502c5004d1100d4650384400103862b5000728490605e001401d465010f00040d4000c4d032080fa003114841c0c0c1949990742e17601d00c90a040e02c4044500f10340611600d49004004945a2000c40c054200d410001032507600403a12007080c2c40d4024883c44c4554503940c025800e01d4098450300e01074a42240003120002e0582c24043c0d41c80d48125022074091280d0b00004500314500c1c9888000c4e20210200e00901c4111007040c44c00310a100c405 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 116298300 1250 116297050 116297087
    0x30411060c030c011b14030f04110310061a0304080403060e03090a14010f021902040f060812030f130f02010305061801121407030f0f05010209180411030d0f 69
    0x1d9060084100003030a0901000c3d80041800380070035075080e800303071004030781300060200b020721102e2540407074410303a980400c0082024002d5aa0b50034000ca81c044559180f5405000e03003600c104003a0711940180050381c0702202e508070b003090020070200040c4811503001e4a148014030041c800501130f03820110445000a007100e080a05040001e584d81000e0b40c09484c0c0b81080f030040004950b0000c8000b500c4030344a00281141c0100c2c0c0c001203c40c2140740100a101c1c0340d481c04503a8190207254440d0014000f0362042f1448070f003042000c061268070945002840a210500290340380242c07000c0980c003117a100a9070400082c0d55030043d00a08005440c035503210341d100000903803480242002500070301c02503040c10481e010030b0410852901d01c040060140d03070080c28081c03002c1049004145c1010303034032101104900303525042143c0240658581c2560040603413008000300070036150742c240254000e100d014000070400d0101560790341d0301c0b41c0e4880810300c10b40307980d400d05004040004041c01c8464 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 116299550 1250 116298300 116298307
    0x2010905060d0b0a0e0a0b0301090c14120d021e010501080d030e100c050307030f050f07180e01080304090c0509012a08031905010b0a120c0507050f01050a1107020603041106 76
    0x600143c064006504a600c0e85c01c8050b01b001200780c2d860140c00c80e2102d054000700101d0b8020744814800b4083e600070721510b822a800c3c0d031000e0381c96a20070b5030280300010058600e0340280c000000e40390f48100010081040840107082890803041c0700b054100c1e9000c100030030401041d0034080d0040c140201d80e462080c09440004560004180201500010b440e5200c69907441d04000107801c4501400150242c5450401040003044603012081d810800c90b04140500d0f400600c07445c4401a62a005050001a403000025240e1000405041518103284c0c0510052811080481e85401030b61b1b042c900040034069080003c1030000c41c071030548092030341c16280c040000c0d01d4120b03041e80140c4120942204071220134140d00031320312845000d4000d00d00d07600d28010181c100100340c104100c607544280d580e90316000481a0203001154406940b02c000c0d10400e40b80c0c001c16900038441240c40e64000c1341007049800d03603e1500001c80b141d481c0e0060a441c20354580361207048001c08030042c065044003080 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 116300800 1250 116299550 116299571
    0x908010e01200a080105040b1f0807031a0d0311190308010807090e03071103150403020d020c09010f061b060203090304090f020f0904050423151302010905060d 70
    0x80c02040104000080041403540c2c0803054018500c040001202c1d03140010710181090651080407141101e03402c850200b0004203000000c0c032001103400e03c1d80000010a0003002c1e03443e800c4206984200441d03201000441d01e00c882c003001c0c0740300c2403240d0b95014010040f10f4001030b000e1140807181d24009011180b404c0011203440e52507a00012081d40440c80170401001440020002e000140207105001d112680804056035038901900800500711440701c02d4890b181d840c104607040c000040c548516803a42841e080194540c80c0034a01940180a1340da150040c0781814001e8904807134a420f00751101c0c5142210480d007a0542d600411490b920010840c0045a041c2c005503000300801805156221300d4460302d4000c44100d0740c0c0205680d07005003c0d580310300440ea03007620941b48051ba80490203a96600d0505801c402078150079800c0c06440a00d07000c0100001f03007a4001c0308802d00d42110340d4461548420210030700300d800900042c1c9122042c003140c00d041c405030140c0b1180c5c40300480d170315280 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 116302050 1250 116300800 116300803
    0xf0d0606090c020102180a0b0a140c030403060c03140705030109091703040501060f141509010522140a0b0a140f040311010801060c0f080f09090114090c280908 70
    0xc0a4059005070f402240c41c4103a51b0b0030000c1c80310759050031a845c00c0c900386070500b44412405240300060a01101d8100c44c50074500d94400c4a0b60003603100140c95685840c1e2900b803004109c0600f20400191500c9044151032001c42049401440315840e15411603103441340c03110140042040448207100541000000b001c0602c000d0741c06036104070000720340242025880c0d5003800d1941e21020003031090800110881d15514070250300b40066002c0c5540d50303010a401a100307481807501700340000400c40400e000c1446040081405c1ea584c11442d403040da500c5404000c0040e0840c0581540050208201d164075401844844a00a030f03070070341103084c01c80d425000c1c4c215402581c070685001c2a072080200c2c4035179002c5445805010309050040c4080c1494991040005503000014440d40b40010340c00c5641d551307003050300c814000c010b1500340c26684440b142202130f40c0310100c09010340702c601c010640c0b1b0541034082d941e0312103101c00d4002c60103207150420000d00210300010f00900c40340b80c60200b642d040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 116303300 1250 116302050 116302061
    0x507091e12050c0127180b0d0f02030c03030a08060f0a05181b0301060519030b150903060a140708070e04050c0a1d0105070305071514040b070801050f0d060609 70
    0x30304007810f082c4500c0c3c40050451070201c980c2d14105c606940e184000c490201d2600000e6400044c1031070894801c240c8190f00510f0800c0425500035250051941000760903003941e80168400d9058030031440039082032580c0c84c000c040c0d0030400f04842a000820078140000d055151000003082030074490380c0c1c0c501080101700000c5045500c080490100450494100001c1c4441c000c142801450341d0b15280b00106540500010410035480101410061a1180d0000325241500424401d0342e05c1c0e604294948650004c00a00e00a002c0c46000400c1c401d164803600400b900d4201030004155102c0808951505004202c201400902c0b10b4650060b221751040303a03c6071742c540400c1a5103e550103405000029a441c0142c003034048900700c0c0002c1d903480800c2e1400c03a54503091142d1601d21070f18001c2d08107401100c80d80e5039185802400c104511844202c6800755000c0c1d40e904466484a41c0700f01c8000000b406016046011864503c0c0c042c20415400a81c090080c41c3c000307034513612070050074103550 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 116304550 1250 116303300 116303303
    0x90a060507060b09010b03010302060d06080d0309031722050a0f0305040608060a03020a140310020f2203080f03060301020d0f0b0307060804150b0604080a03050d0506040507091e12 79
    0x500c0411104100038079031081074002041240c20110640c548107600120b4401404028000d0402081c0d0341649500303500104003418402050303410001e2110380080040c8180c4005500003029460040d0080703642004003400b42185440180b08031480410301c0305e00c441480002c031180d106109644022a041a0302008002c0c8280c1d2100d5075245003513002452840098980f91146080c2c440420041ea21141c0140c00c6400c07201c4903600f0003017540d000900b030880c0d0041c1c1d94a000d00010303c030070582031100c0040951418885000449668203c00340c11807518030302009200b04010040710f0500da1195000d1a440b01e03004001500d803071100c0c400002610464044d2031140e0362202c078000e115282c14410300024069610704041e0340c1c50251142d10352302c0152051141444d55035007068010742c40300c40403200609070402c11110f9404441ca40288580e021071000100540b5201c0800d2080c44c1c02c0c01400d0003448640d95007a42241001d04600211000070141c10080d00f00034000200208603e803501e0301079 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 116305800 1250 116304550 116304557
    0x1324090501030b090c0d02090703060803030f1006080103110103110d15050f030f060a050601021603030f090632040801090602030901110702030a080f0f0414041401080d03090206090a06 81
    0x10752551900c640c0001e4042c1210009402c103041010854952012000d00e041d01111582c541b41c0b41d660040e4001c0545030030441d4280400402c04c030071144041c150b54010080082e5079050196562421a0b5600081c0001403416001c001c0000856200740c001c4804100c3d01c02007546072010f10b540c2c013400c6803400c10000c2181c080c142c030300300301d02d2034124003074504a9016000381c640e01600c4c4010070388030100180300402251f030ba0804921283d100308030040c80726109200004105481c5d040141100011105140000d02c5020000c140b2512400081c4221015a082188a00704070950b1140444031070040d00b001c13103020300000807511424043d00c0140c0d40103c40050381c80c01d14043e060b0a44208114420f40b6501c208281c0340180c900103442ca500d6500102c0c01915407160703500110051040901c461180d980104010406e103d02e660201d00810040b101005007401c00945211150400d205101d100e030408448100070034000d0b00000d525038401000ca42c40e04040c0b00001e058290541c00c802d000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 116307050 1250 116305800 116305811
    0x703030507080f0a262214031216020706050a051b011a0a0b0c1203070e0405040b090d08010308040b07050a050f0c0901080309060901050706151410030209132409 71
    0x48400b542081c2c5807950040c14901846c202c2003c40c0e60140c04010075503d00d980a032104244510140314441042d490001d4a950700360800344000e10300740560f001d1800031020030292401c68000246801268030302c0d124a810481001000c0c0d03030580000b501c40078881c11112215452140030b128007003222140c42c2e1b900341040000c02c28000c0810484c0c105403901d8100f08031500902500059440007074420040150781c81e0780c0d9900803520621014500e540080c100014807040048030202280b00e14151001c035080740c85040c10841315420288800b0700050010007050090010700c5009046041c050001c54a00301d1003590344034507005900210300385a80103001c0d088120320b03010181c6801414010011406d2661880004840d403003240e1016062160004a130b0040004a4001410444054920006440ea03404c1c040d00c98180b80c50102d885201101b00d0190481c0c0240300380c840c0088050500c1c4030024004e00407c0c0180240c0b01d140c00700801504046440c2d885609501c000360144100202c0c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 116308300 1250 116307050 116307077
    0x20114040503130f0f03080717070c0608060409021e030a080414011e12020a0915030e0c061218010207080d06090b040902180c0409020a080402030712050703030507080f0a 75
    0x122072016402001c40443c01001c10041031760000065400c1e25000382486659045138504030f112080c03403082000c1c1c0e10384081001004d1040b552100380440d51a0740b00d800e035551751034081200b01c0eaa1358000941c82111101c40c0e108614141c00620000000901140c001c0300d030071b0301d0b804511b0304070707038840004042101c3d11418a035900c071503540c59000407110700721a8112441c0c0e002c0c001e4405840c0c10307504140d010403a08043c0344203424000c02012001c1e2806500d1400d00030040103402d050340081050312030003401e0422030900c802101c1c078070000000a81584e4644601040c032051101c0c0b141c45007507400b401210086458400242496145a800000c90601e4004440143e44101291901c15454031901c1030158545502d0745000d8640311840b010f503039446140102c140d0107640c10010095102040d000c44158010490602490003281110241c03507885459010072540044001d01d6074000c101c042000038090000f400d540d600c00d1010a00b400c082c0c29001d455a00318020f124005010714a80b04c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 116309550 1250 116308300 116308327
    0x60b1503061203090310020f07080d09030206010f0506090409021f09030c08060f0105060304020414070201060e090105010b0f030a0b090f0609151507170a2a020d1101020114040503 79
    0x100d600440405141050744d6840000d4070398401091408100b6000a0a110617044600450f425a0303400280152542c2003104510010600008210050300c5000300101d0890b403285040f0003260f40c0140202c0c41c0c00101400c0c800903080707282007203811069420150400e1000402030412442143d980c41e20707044e245040040d0b0701c551503801100545c0141050000105501c58060305403001900c1080c0d070780c1c13039a10209004280340c0c003460002180100600545641c103400134001ca9014002403540c503140c45210900b00c5d0003e200c0c0c80d190840030004941c0c1060b51801071035001c9109a03001404c0702d0900003180040004441d85180c0121441c1000344610745404180c0c0c210203440c01654061056101041c2c01040340b00c00c5010141011855038100300c660050820220401034045841700715041c0060104901c01d2002601d07118500e85404182004503510182650020b10728040030a0300e1300c0f00464402c4940c0030354115522134080003501b102c0c5080d00742c000c07440391005680d103041030760600 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 116310800 1250 116309550 116309569
    0xb0f07051903020607031a090108010213091a01200f010b100203070b1f0305070e150105030f04110a05030607020f0f07030308060909191208070f051204060b150306 72
    0x141819501d810000010075800039481341c2c84002d40c24009111001e103810050b0130240c2c0b00b456540421010004282404190064003201c2c000341880c03040c42e80c4410307180c030640d003104645c0c0d1200380c92410000200e601c62594604862a564085610002c40280c2142083c0c004007901440d6034507014146d04508140f405a43d001038544065404c0c440e042d40c0e074000501d030140050f41c0c80d01d0300002c8441307940303030820202c8000d41d4040200c414480d551810210003010880701d070035550320100000340300780d40602c0c00c885c400d01c4450108525079542d40e0f6440048555049070503000449a440412603442c204041c0740200d00980082400c0e5010030742c1d0b585002044003181110740c02c14001000060f401060542c2c2041080300d146c5016510180201d00d00b100445841c54070781a00030055050100b9041e170800541e01caa55a440c0c3d5599041043e190310000d2451440040c40801c58000c410410700885504a40b04100115041d00442c00003410440c401c24200030b040d40000610016203002000c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 116312050 1250 116310800 116310823
    0x80a020d1409040f11073212072315061009030303110c120a03051e01060507020a0e010b09090a1413050106050d0602070605090a17090103060b0f0705 66
    0x8071034100400c20150107a4041c403200d450180340c40f01c00010300d00c201500300740300d03000c03540c1c942a49803c09420041c0460450342c0811200415506200421400c0f21000100405803200103000c603103408420760145074007011080d14204800325401107492000400888000c84120040500544901c2c3c030781c0348128050311862003910b1000c81c500150b904940d410040366003600b40002d1344810614180c0301c9120320f4414072120300038042d11140e585c10020280c1030b189130340d03030382004180c1d540003e403030310010b004441d24030740c04185c1c004001ca036110f40000d15117548040c143e004110340d601a2020001c00c20380008500b01c601180c0c007221400c00d1600e660340528004400c3c8a0244500e010b2184280c0c00b900703218240f640c60003054113108007500700c00020040030784940c010819501b00580290032189007201c0090421021030326541000480141c1c4907000020b44072440c0080d030342c85a09a0103000854107042e20b4110000d110040b1001500d035085072510304a6030340e522860598103011904c0078 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 116313300 1250 116312050 116312057
    0x312060e15031b010c03170a021e07050606060f0c0d030e160f1e0e09010504140105090c1002100213030605070203030c0412021203070606060e0114030408030604090807080a020d 78
    0x82e0352100c45140c0b040a503c0310013030802d905980c0c3d0509040b1201e0f042104c68035007468140c0180008803040e0ba000713212001d0802146990a00030000240162158507409849580181e004c1400e03881c1501c01030038500a03103103000e441d00783d450405034200303590350f900d14011907514441c0c12030ba0501032059005a42141001030006400c20300d00005140560003215807a12104a5100d0121140d1a6107005041d4515000760b17240b03040461580a400202d170120f0341240792400f4101c9030081401100d01820a1138081e21403404614240409104001c07011421403284040c000c0403800541b00400c10740e502c074070012040030705606094055400140005045500400030010520582420b4800361303940345d05160318400c45800011126060051948074074003000500e0f1007000011303809101112403540b40c0c1c8d150144e005005450707081e46a000120307000000c000203000200c40b50700942e80010014400180040380c0e84414580b0b401804081b200300400141c0260303542d804004d000c00000d02840d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 116314550 1250 116313300 116313313
    0x106140103020f19110f240f0402130209040e032122060f020d0b03011406030309010806120a030513050604032a170703060b0904050d0c0312060e1503 66
    0x240e02ca18074803540424444c18030b400c51014018a1081900ba40c8038050136046909001a1802d81a22400f141c14001e02100c4111094501520381e2240c071071084c1d200f4144031046a036140c0074800301c10500300500d580140e00b0041c0000720b03580c500c00c881d001c0400d007008503210100d015030910040040b030240182c1e00044000c0029000003140d18891003031803513540380d1081800b0b181040c080c041818200c600c8900202d0340d80c090480c1540b0800312003400301c000b404040c045414481d0408410365000b905904104540450340d4010080990000d002501180c8420388000c003203400c05504c180c0c110300007000014859001c20180003000c3c0a0300084900e545850300d10f07914404400039490701c044800c192100c00c0401031108074640d00041ca081000d004c20204601d80641e1a400c481c00115103488c54403801050074180010464419540080100010400540c1c255800d004860048082140d1590485400c5007103025600003072074004440070b00c60034891100088803000c00da40c1400ba91150303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 116315800 1250 116314550 116314567
    0x20a14030112050f1605120f01110d0f0b01090902070c091407090f050a06030c0e090403091a0f04120503160302010204050a06050a020601030305131a030103030311120402010813020909010614010302 87
    0x28450400720b8100b120587c0400040507403190810103441550851940790000d90070400030f48100a02111141400401903c80003c0c404c2e401c4a0641c820340e0300051290b030f002d11090203141d0040c00700d140a010b044400d540d85a445a082c2c031102c000d01640075800340240510b0b5034005001c0c1d4003170300c00600003091160038000401c80c0e489051085c2001c1589444a220a1501581c0001e0305500082c1546c5014601410094100c0b44140f080b144460500340c1c801d280550303020180c0e075039800a807081c585000e140042a04800d1452001650103000800c14004034116807001c42c1d031003a100342c0000da1507030700c1c000801c940c1030910340c4450103008007007261500036a03020601c0340c1982d07407600b08581c607011500c0f510f00c02c400d250b80140d020403c5480c0411020ba04000145040341d110340c0e0140400c260b1300e0241c10036030103800c06440d44241e0f64004a8010342c0251041640800b080e150801800f46a800054925400b5180c06603603035503601c020702c032004010071882c11041d804c4c24250310f03020a0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 116317050 1250 116315800 116315833
    0x403030e060f070212150a0c051c02040f092712030f0b12100605030309180c0702060712090801050c0d1805030a0f0207090c0c06020a14030112050f 65
    0x440c030115214080001c0d542c1031140007481903516550700a0000c6038070103089030303c1c195180048003c2501a881d40c100142e8412070500981584c040e02c4c0c2c0e40c543c00e085c003a08990a1101c940c0c0c04084405400f448042010701c40c07924030b074004124505010400c100d146144400c0000d0840c000100780030000040700c003040c1503611507203510042e80780002e0590100808540100921204c0c980d0000c58607201108040f000034051106680100b01044925030b43c4007095500d2085c05000ca400811512002942c000807108180d4041484060645015221390018120381d0200d1011929048103d82d4425030341e52000c1c0702d06c05008018002c004a0a00c40040c0005010360901a034025840b04019030b860504092035840950b444001c49488a90481028204103403125031500180308045c0c001601845a01502c56000d4413503c5d84108070802d9143d20000e544a81e410000b0302a0350341503012803440402c002c50080c01400d02084024001c4c1ca01182040314090329200c042c0d100300c2c40c020180b201e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 116318300 1250 116317050 116317067
    0x40b0d02060309010b060408030901020606030a320303010f1e0b16030203070b07030501150e06030a020c0316030f0314010b12131203090b01150e0f061b03090a0803040303 75
    0x301140c486841e9691000618007420407100202c0d000a00403c00240e80e60002019100054098080e52541d56940051503682d80b005c501c081c0001511041641008000000c40281c4200320308521030082200100d0503e50380c000c0e4056000300440080400c5034242040d655907001005604440e03a6924080c50002980100d440c112103110340c041142d410135000704112210140c0c800e582502c0d074608400d01074001e002c24420344d0310b0301c8040d04517540e1552282c200e80c01e481c54009c01542c02d5854800c2444025086802454110700c0304000c000020682516000c0c4518403da40304100c0c420340d10001001d840528000c01e2002e00d900005001401a150641c0c1701020034904116203a5102001d041511104842c007800b2040030003480d01342d8076410f8000e01c09007801818015006c2c2d83e11041440f018441d54011000200f00c5411800b00c0d1a140c0c100030807040b8020f244505050900002100c0503801ca071010089900000d0b556296081c00105100200000800385003003502d182c80c090a40d00707 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 116319550 1250 116318300 116318303
    0x203090a06050c0c0d060501030b1b030f070c02030a0f03090807120206091503090c03010506011b060903110706030609051003030f08130602120711030c0c061b06090307060b040b0d 79
    0x200811141c40e41c1d0f500b081480c2c8816001800d21304a2055401c20704000e110a01094a089034034400285020101034208010288280c01041c40c5584e5860400030801e0302a14980070002405000c0025039010803840742d0701ca000d4000301d00140040c3c6405400c1202c5940b00d50216084020100a0210b944400c44c042940581c0c400340d54a41020025085a250441110b2500404418011b00f0000014280d00c2d107241500204210f0700c844005582e03c001c1c0031481e030042401e0351015000a02560000d01c1c54522900b001244e400e0800d801c28180407880d008400020b07940c0104000c00c6001d802490341101000010100c0b8034115113004240c044104142418449a080810076400d10421010b045c01d030480c1c42191101041c1d09200c01c1c100d0255004400580560301902d900071011048660f0f58030342100420345585988140000da8119800300c61540601c0d1800c0d0548100510400744140c0c60304010b141d58044516144c4112255180d041c0c4c0124607020844240c2d4907510501100a0b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 116320800 1250 116319550 116319557
    0x810090c051c0b060301030c03150506130c09032306060a0b030f070954091109100609060903030203030f0901020c0f062710020f1b0c010801060203090a06 68
    0x58490b00ea406015000820b100b64102c00d00200000511400900e04420380b80f040440daa08580b40c01a200203036101078502c0d60780030440034031184bc000d40d143e10211a091403030a02c0c0e50030036503c1e1120000303a150030b040908200315400010000d00018020154004411aa0046898203048007901540030040c02c1000890f8501c000c94032031805802c4e108004d082114820043c50071110381208050075910000411805d407030500081b02a00581405074001c0e0740b400b8124485411240308064150400107927031031010f6913003a500c251550000144900310029506100601c0c241008041c2c0b034bc2640017808026010034103100195000c400c49070401b244881202060b21480c1c1c0107030080c402c000000c4e009104169025501311400304e10a446031480c8070b04034408041c28000ca8555407080c4100b240e2941114105401c4440c0b50340c090b203109203440a00c142004800340404003421050321040800341e101943c0c0081c03d6a21920441c00f40040313101842c24444035102145c144445806803c051 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 116322050 1250 116320800 116320837
    0xc070b070b040b040f0b13031b020d0201120b09010f03020a0501170604151205070602061515180a0b03090616080417190e0301140108190204060f060810090c05 70
    0x920079540c4c0c05e003070256000420b203505800e02004c940b110a140c1781c002c802241c082406000b0107044403840b18100c9030068400c0c807000786a0b5004640c0682040e0302d2240b425511450640207480301880c1502034200079040d011400e04600412051040e113a001604210027030520004080e0155142600403c041c0c5000c0f0700d07000300310080300c1200600e07040168400c41065002040c0100090507404450407030702641c007a0b480c0d000300390385051032803813242d82c120252404400b003c41c1854014440c034011b10400c0c038245501e140008a03400b031075610240382c0a030003009202900320148241c41e0401c07004440049034051000c8054074520006202805011188020480103150b440c00c40d05e0f052440403c110b440d4440072405040d0352424041180250720b4102d03443d5011764031194883c10b860000000b0070078a1002588209002d00301c1c0c8003281c10540700c1500140542d0300151071409042140c0343c40e802031505600c18002c04080d81c0c401d404050801085802c450f40080848818401448101b42d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 116323300 1250 116322050 116322053
    0x6090408070813090c120e0601050d140319180b070c050904020f030303070906170106200f01051003030e0f0f040b0120060402030708060c041203020a0f03050c070b070b040b04 77
    0x41d00b4165a0000344600d061170501c80c8095404508110b92058002e8100120350807004010790b01c240901415800c0f005440a48000c00d060701c41e42c09080081e88101c03454220322403000a02c075044170541d40c02240000e64141c3d48046e007440004094080002d84c0ea0802c0c1840d101d903001480d0510602d03000c0d000c48004181176442354a00d0035500c045c0a0126580d03418181001000d9813164458000003a01100f004e43c0c110a02e089001c0c12100c0c7d5070383e5401072040b41038030301918a00400031044144108110010b000d10f0038042d880c40f460080041801003443c6060160100c9108840d8511440503103840741c1d07090703440c000520b001c8a019200000c4690410005a45400c1c3c4244600e00e06201e1714515901e0000006451384a14070070343c01e68169554400140d90f9451041d05d403881c03140428042445000000c2c02a10403150007403045803d00389003500c852010f8400c0300c2c4180d002441c000385404441e0010403080d001000c000e60300a280c04c0464a8003000d50307174058002028280e24501240 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 116324550 1250 116323300 116323327
    0x7140d0605010e0a0c11070324060603020301060e03030a02120307030603140303010305160e040b0703020708030f101202030a02060705030702030f2b020607031e020f070506060904080708 82
    0x10106a400282000196155080600040c3d4119510b122050500345114130352031007040d008064001c2d1034020020903041da44c40c450400e4075182e075054107107841c070400d1440360310034003810009007041c0d1001070382ca50405600809604035200660700a620811020a440307600003400e00d4030960280702c15880303499100e012400350103554000b85c43c2d0703e8900071403c4081d202100860489119a0840d01039000741e040c40f1100c2c415900c10281646102c80010703010400e00c0c801185c0c4580f66240040c0f40c0b04055451301d0340ea400558202407940c1010b002c00080124906552005d0804019150301c0022150300190f0b40704060000207020309000303c0d82004101040040c5c80035140c4c0181507500c41c403038500741213555101504021301819100d0100040c506003000700a03105140c1a4040e2109549901058010b07102c500007417003101d4180e02450390b0700740d074078800342030742400c8400704a03652026030030403629108025099921401200e401d01c4006200c481c00c81e184594010f02460b26200c0c2c0d175232140c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 116325800 1250 116324550 116324569
    0x2011104060206010e060405090303010b0a020c09070804141227150d1802131503060e0d02060a060806010315020403020402041d0708010501050a0e1507030801080d050a020714 77
    0x824022808100852001e8000c41d03001e040c0c4d07500c1c450400f082d81e40c0c0c404200030340740d0035541d1201c107810400050141440100040000001074012660402e2020010408901085608074006a442010300041011091060b0300c0e8020b0240204031003100e0031081c1000b48108046440c1904a0041c00300e0308050300c0278a5048039000404402c5846160610804541e000e900c00ca66100e2134034030041396400c030085c410502c07141c01030480c2c55400301000c80c44000705074051040d420a0400840000000d8407030058508504400c0d014003401d500c40a006454000e0182c4502c454a080c64420301241c50300040340342c1101d801060f0001d640810304041c0c4003e00c29608041d4100d400014049a00c41c4080b0031040c0c101d0503010440c89a0b42d4685003265040e00c01e00a060010b0000c00078600b007903101c0e805000d034614005280360142e65000b0100c410552103076100701c020079649001001f82010a118034281c1c4003c6042c010310300b030007205009455031070a0085500340c000303000d18410152a0030011 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 116327050 1250 116325800 116325821
    0x90204091407020c010c03120507050405030d030905100903120603060e010e030c120a050720010e0103020a020706180504090f0c0e160507060b031b0306070c02010e120309090c04030303150509160201 87
    0xc1018ac00c0c08a0010850360050051500a100305144051014031900c22140c0340d035040300103007944203020072404010384030050701a410001202d9245100f50001d104030801144100ea00092403030162802501b540c180b120440d001350400e00003500c05c40c80125031800424610a841359440e920700d802034855008220020301a0b211038190034489010b4a81142d84c4d03402d09803900d4042240c81d0740114280e200e03021003000141c001503401c000f91409001d080741110703850350980407025215808201161107020081e41c00103e804c511078248502203400e40090b008441031544140381c01c150401004414440807020807600049481c240500c50f2300424440b44024141c2d403098582d802c170b4038600445009402e109000300404103d00b40c0c0520204040954180c4450542d10070b0481001a4807005041c090f040d40002c1120401ea030b59010082489403049561558845096050003411215945012405a0303508030052215503603030f0f0301d03d40d446041060107040c6d20300348c00c1c070490150054420 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 116328300 1250 116327050 116327087
    0x3051207020f040b03190506070207090c0e010e0f030a06050a050a0207020108010e070318050606040608010203010f17010902030106030b0a06090203061e01030e0303010b12090a0f17090901090204091407020c010c03 94
    0x15806c00304000461154060581c55086480907615283c2c040c0c200c40e0080c1c60030300819890000c4040da5401010745c80c41402d4020310011101500c900424245045040100da0031a5500c041050400d084d1103580c1d00040d41080443c2045082d03030001c1c10004040c080d9205440c211800140c183e4802c4e0070404680a241c0c0c8860b101c0d10103807416036a00c1d00c1c02d03280700f4461401d01030081549041407080d84d0407604100c6805554a14044091021041000100c5440d549844400300503840034001c103030045100d00d200503d00d00c0c0c4090300c1812140c15800a1101a00400c140801c031f507213442103400c000c11581c070301c240d100c03d00c0c00c01030f0014294000f09500c2c60101100018541485c4006049140c5400c9501b0070f2039680c20241d21380351049210001c2000868504850208103070f80e0344c5202c007019240c2124075006036000040c01c1440264014950141c0025060045171424081c54034913070020240b2950038144014080e4440500002c11410000d8243c012402e0520490300c18034058006003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 116329550 1250 116328300 116328343
    0x90303070803010302030c09040c061103070c0b09120109470718030b0c0304150608160501180b0f120a0507020c0d050a080a030209130603051207020f040b03 69
    0x141c2032003990000d1209034131074041c0d1000c40301b030f5003025400144030790b034845025443c0314148101075418400748030071011a480180004800220450b1031440503050701800070b41ca4691301c004000707400040c5000d07c440ea0341044103110019072021101c1030a094046840c0ac0e030480b000c1100c2c100240c0624465030b003808408150901a4042200b8034003440099940512410b6000c030030085101d01480000c020300b03851400a07001d00400000f858000d0300c510210000b0360910510300c2c040d01d00e141c101d42115000a01c0c1ea0384050303003111000008007402e00b0f21190072504002030480e004154456042d000000103084414110440c080700c1070301e00044213001060515408603002498111010001f610480052507080e01c2c0407808410030035403041c014803c4c1901548c4854003604442c400c031051540900203100c541d0341c6d0038004101c1c0072690304005139041c614100140ba1070200f90100703000020400102d00981c403000d1b041034043d1000e0301e01064514000001c41d1404004c1d1405440300320111 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 116330800 1250 116329550 116329553
    0x16142803060f0f030309090506010507210914030303130c091119021c0e0103060e01080a0309060e01050f07080906041e06030c0e010e0f041e05010b1905070809030307 73
    0x5512071801e440300300e00001061510b0b4940e4040c2c0080c1404064041092882c04108451180d00195448417044c509039040c0f00b1980d4840c045201801d80050f000395862014035661a48500007d004000380e0825020384200d8501003916444090500005030440c10008401d00001c04100001814060010040315800703549490054000c040910f03031a079491280f03105400e03c000f0f01e505507108403c100d81c6000d42120310940710074103001c2c0c20a06042d180c400005062030301c4081030f4001c004031005441a030300320b0b1900502a46a5030400d0040c071203603104100680e40c1c001d0a1b1050150303540341e000c0d80c44c8070382d04001125014600c1c0140d4024000180801c80f04100c0c9801c0d4405175041590a02140d1a140242e003079a4403100400e00180c54000c1e603c140e90310038080c0120000300a0032803000c030340040c800300c2d0545141c285c0c0310700c50302a4140c0c1403445440310b1260074010650071040c9424040802500c0004004103541c0e001080000b0034010203108045c811034004800040840b542c1d003516 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 116332050 1250 116330800 116330807
    0xe0303070905210c220207030e0316080c0d030201060f0303021c03050118050c120c09010e1f0305091603120801090b030a03050a11070906030209161428 67
    0x2140980e5020b21070b0342d0070036400c039441c061001c4a5207480c1d0300540f81c0130403c20140b10403c1c0104070b080000440090042410400c54070003480b10341d0080d42c2d0103000201c01000c1c14540040800010304038000a4410004444081046c54200310300301c428040011150400304d02501c01500200615150307040c0c000704264000820002c102c0040c46d50383d20001c40d90200398103e5509200c0da6141c1c0444112008a9030180c2e400294000c401142240c00c1c00c4a08002c603150300c004075075000000100196440417503030414005240c00504960b910100c0040c20600c8031290b14117a40c02051689420218114050030b201e0b48c0d040894035100b80e10411380e01d05043d14000911030010010408080022900452074018100c03011009030042c90728503402e5a044070950710884c0b05d0401c00200c68107120744283c0038040c007801010101004100f550642c010400040800380218414404d16440da00305690048210710302065002c41041d2103075488402c180c0118804041c5070542c070912202101e14680 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 116333300 1250 116332050 116332067
    0x30c030c12031e091908060406020702040906020a080603010506060a20120c030d0f09030509010809030913060503060a090c03061116060e070f051302090607050a0b01230a0302060309010e030307 85
    0xc1150701001007052542100b030722880034010500e06807c80400100421000d40040640c6440a4000904498982c40312001c03a0040309804001804002c20b200c90317403400b40110b41d0011710840e0414604504048060207075254000d40254094800c06012007040c3c1c14006402903d501c0c0101c141d840c83d2245140e03440790f012800c80402d840c030b0310b02610040c012600c1540304699142c1c540b50b1a0441c00401941c151070010160111480308002019464a6480c103081e205d9580f00d0700030500a0a0004060038400002e05a01803e840c201c3c60701d0118800c01c403040704682e0464800507032180082442c040ea1f06c07520343c12101c42004c003140c0304200070066000c5100b00f101d1409581070b0b80e840e00c0101130f115501e403255581c4990440b02400588046500502100c0d100414003417402d41c291f510541481e021038800c1d42e051a0300801000f14040c61184a0210301c040ba030345644074a00c0c00002a06807000d804042e008130700c003100141041100350311002c1d05861f030f007041300d40300e01c1c104000030718000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 116334550 1250 116333300 116333317
    0x2040b15030420010509010309060b2808060f0420030a0b0108150402100e03010b03010e070608070305060a06030c02010209030a050714040e070b0a0c080703030b0906030c030c12031e 80
    0x80340341d150802d20a220040745140c3c984140c0d036031490140d00350300440192001c0007003075481c25581c0860302c00c17a6503859031002e003880c4000681000e24455030a040702c2480c00350b000070102d8001a0070051841d0100c0d001c69407155105601088400c25000000d40154403081b40d41d0b0035115044805c8244610300000604941810702100c9010070040c1060709210300a46000750030100c0108031403c0103000d000c0c010300840f00503000203001800000020b0035600b000901508da600a404103200041d0300404140e84504a420144994141003000c21081202403090f80105a610401285928401e40490f514400010216600000d150a201e51140c015201c0e000b0011605850005c0c2c50605014000e042d809001c080d110300e030b00d40f02134183c1c81c2e44050040c10402034520700460018240750b01511605003c6d030340004144280005210075500041c00c3c03a8407941c0300d2102040c0702d03500090034403002102950403031400c11030802020310718062180010b010040000d503201494040f0b002811545 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 116335800 1250 116334550 116334563
    0x12030503190c080a0203130804090e07050d050a020d0c1d0a061e120309080a03020f01050c040b030a090c0906031410150b0a0903060501080604030306090203090a030c02040b150304 79
    0x9041c0c5a595400c03200551019808034000e2000566500ca09901035030f4800c1c3e128050100f01e840c99604e907001a8450340018400c1a80c0d032880c804442d001700818006040c0c10360f08403000e00f0741e41c0c4074544d603084100d0000b0310030440d10115200f0404000301d2030008003000e203000c140107031441120100066085030400711951401c5000074001c907000b08000310a060014a120080782000d01c070020780d104010303065040c4400c240e400600a8001c11400c980305000703074060411058401007990945102400508003d80103010610040f2020412682c00260f2a140090884800d190440c0081c4055100001543c6014000014801c1c08119030944840d80029141d1202001508404403600e003410b880701c4030701c043c2043c0300b04601000281050205030038100000e9942e603844c003041d107809811032012a0400c0061104054160142c036000d800644410350441c42d0200c0c08541e2204941c001804102030500c48209548890348003000c0c50001a21855207200a428110400d500903030301107520 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 116337050 1250 116335800 116335831
    0x1206020c01050c040b04140f0306070903140d090e07031b110105220201110a0204020a0c050c030d020c19030203010c0906260c09282d09020c030412030503 68
    0x180f00200003181c0551300b91a1501e030600d400c10b0000000003559406140c2c1000781001500e40f00c0c1d4042003100e10804040e510b2850150461519400c000c855035040c1c0142e621142515082c01e811800d4441503482a5a0f80c01c1203644012045016044010740195429105241c400315141c0c0000b0046110090b04001d00590312011005126004500c0307007590451075030303d044d000543c45a140350048200034011500a6a10303600028100e0340801c0340724020840c0c0d42200c1c03040040038010504060700440140150200300380c00a07441d041d007842501e105000310009220807902441c40e0101440d0094000c000c807109100014200c60f00a004003004680060a16007000c030440c480501100c040c06a0500c294481c08085517640d00003030312596025120b03100140d41048088504155580e02804c0e0307240e0145010520342d0b5109800717800040e004500c10050010004e5844001308684000f8801642ea0b40c03000c079200d0460080760058080d00d07100d9030f480e009166124015601070700209800410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 116338300 1250 116337050 116337061
    0xa200616090b07030503070224010f0e070c02012708010c0e15040e130b04050c010f020102040e06060a051c02070c0605040e04030c02040b061b010501120302061602071206020c0105 79
    0x70448110310079801c01c800208102000684a00c000e0b50f0030102600481340c540c0e074481038a50003062403061600701d04119100412060b48040721000003000014040c200600b0040401000642d40e840042e0502003941055109040640800100440e40302c1d504811f941d16041240d02030030b41100c2d009d0005410a5800e00340b4038041801c0320b0700c47c3c50903d216140c5881e01004a500c038600402400140d100d4804c620081000403504e284202c0c4282e001d0f2802405140000d0300c1c110511103050110782c0305000a01800c40c0002d00300f90000012112030b525000042402c496610803100c041130040300d40c201110603e1680c3e005010024071920507155025100c210881d500c1c060f030312030601404150320206001c6405103120034001030004d4000708100c5000d0011031444c2e4050941c100401d42c00b9482c050000340284100e1f805040009034010b848103061302d00030340da40e030060900141c0341440c50003086c84034002c210505c010104040c1c503000c0d0100e541002c100a40100d40d22982c1542400300040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 116339550 1250 116338300 116338307
    0x909043f0e03100f090f0602030f0a180f0807060606020a0b16050a05091207080709060b0705030910110d0f081501050301150302090402040e01170109030210020a200616 74
    0x4041c04806401050000301d402101e0024060341008a0116503641003000040b910403103540c101c2034000e1102607030f642411800c01008803c0140b041c02054500740d0040c019100c1ca8142481e0281c1101151103400d85504102019100300e500040c10f03170b0300d407010010f40070740c01040300d201c41801940080d98658814120919054110400d0340000c0d000b001801d14860181e006494240b001610404013031f1b0103005001e1804100d42c000c65019444698100002c0d48640a02c1015008601c610f0781070a150f0ba070b516a6901500350214440c041960403215000d114540503007600c01054115000350701d80d81d43c094412809820104001455040003a1165050004601001e441039403054a140c1c82c0c51655818000d0702045441055000c2141d800b15503107900180010381080100c10409514140b0702c000804080c1c40c410360580d050481803030200c0d4002c02c001c4000c42c5003000160b070ba121151000c843c4103420302c00110600c00009602507041400068151141c10402490250540307401c0d01903 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 116340800 1250 116339550 116339567
    0x60c0705030a081302030106170111040506071212020406090608060105030f0705030702010f060f0501030e120403020603040c09020a030902010f2f19050309090a05010b0909043f 78
    0x14000c0d500401c1480402d51107508040d5011403040410101001107900003420350350990710100d4000e100c071a552004107802e10940341c0c0c50046944240c501440c0c2800304e2014000d155003d0518401085804002030040100c3c565808649204640e9240c0b40c84000d481e4800341e006002c0054a03140000310154050300459001d1000352940440a80d01ca42c0c1c112420b620003007000d01107549806803280800f401b801000007500c0c421141c43d00040c14080010121401441122074581c01428656001002c0008a800f5250144c032400d0b80c1c0d6985003072041403400c0b294840c84482d8400140c4154007a8180d001c981d0300d0303200b40e880e095000610381046980c0403401d091547e00300300c2c2d6247c1c9000004c0340440942c1e4622101d06645d00c00c80003141240246540f4070003a0f07003d40000400d0b4070f0601c2e080711465806952407000b00b10b50350420306520028011791403c9401031008001140c01e20000492400c94850303040b444c40c001005040032030800700295144c05189903858219218668080c0c1d141 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 116342050 1250 116340800 116340803
    0xa030e040204180905010227030c010305010e0a0e010b06030a1d0607051b011508031b06010e06010c020102010b04290d170d06050603101401020708031801031401090e060c07 76
    0x2040001e007409400d80002d00086130115407642d820010290040c0c1c0161328004072410f540c084003890303d85241810b04254000b03d00e14105031030140144a098114400b00d40c0214104e00000b0b000440e4026090041c10085501540f1617804000c215402a19410140480b100b11424030b4003502607503401e90350307030b082a104000407500c140120421821058000050844580004214070303a5202e012800d02200360040945078100141004140d82804484c461404401c0001c11096140044801d04108083c01a40c1005002d00c1d02c0d6003560f10075000781100510080082084c01c500000740c0e2500b205902d01e5070015030303114111080520703016000315900b41c1c01200b19902c0c12a4800700c054642e004440100e0107542c0c80d80c001c103458072840060361143c11001403515146061441c2c01d2340c04c4502014250456001000500000c0808420348003c81a0703008041000b0896400580280c0529140e6910b0b51082800005c0d203440c0c19046400c1d10186202a1030030754132a200c4040507886007810 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 116343300 1250 116342050 116342069
    0xe0f070807120206070b010e010302011b030807051b100203070906260c040b0a02010f050f07021002030903040803030c04170a2a090507020604050f0c0904111c03020a030e040204 78
    0x30802c07405040030341c2d086000744014201c3d4900070321075843c101d82030002e80080380380d0041e6034014001c650300300842940300c446580201c8000c038050365005101c040010621400c0050205040c0024240850600c4008040d182904c0e4030314070001080c8000d4008984903c0041d00103400019414014880c01042e000031400f1748405202642c100c00031558041d0805450000c2000000f0781c00182c1c0d4040d10403210360b6800402c503000c84070005426110050440110b8012070030074420200d070002001a0050001140503031282d40b5448030f01c0c194051a0301c012002d0000000300b00001140c0b900800070b071001003100c2c1e9482941e400555644030300310000140088020002c114201031024000201880c0d45c00e916424280c40303038484400d49205035546400b590114003440700b001010f00c495480c04900900600340b04940c01c00103040e0000151010300b8000e00c01014800603240e1401920034a24680b452a0000d030380d070300e8000d41d00c1411034416400101241c61169480c07800b8000c03038080302e00508 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 116344550 1250 116343300 116343313
    0x1202010b0306061503010e040309030803010e0106030605061204020409030306050d03050c100b0a062118060c050c0c011b0f030504030302010501050609060d0f0b12030406030e0f15070c050604060e0f0708 89
    0x203c4c11f000c000a8003c0c2d051041c1018000300050072840114003902600c0480c941783c0d4035049014080d9000764000d544945800c0c070100880700d001c0701c0081e51050701140c2c0421103071828142034000b48100d800694000000c807001c142456040002407101e000704400301c0302084028403141007140c0c50100c0d190340c400d0110342c00f004078901c038050f8030503a45542001c403001e842900c40c0360070881c0d14a44500c80d2070305a44500500707218075480382200504603801c0c55490700c50800000390b100c0c2c0c20726181d24140149440a8840c801d802c04100b6620303076010a500c1d1603c0802c0c103000d8403c2d00070b0310045005608000000c103082c18500181c40d00d080003c0c244506020807101c007a40504400301200045a588926946151381c442d480984c042910402541d503032400c0030401230503202d001200c50403990180b2003040b0f01c1400000c01c1521001e101c1100c0207240c40e8a01c0840300d50180b000060850b01c110803d0009012903644074000201442c0200c2d0f400c0300404058507240d0b91140700c0c1926941118 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 116345800 1250 116344550 116344559
    0xc04020310052403070f03200406050f0f040308090907140d02210a0b1003271a07120605010f020607080c0d090803010302090619050f010c1202010b030606150301 71
    0x180340101d80c80100300d460140e24204100003e000e400c12204840015401900120195054451201c030014040100d84180820840503040f41c8a140314500402c180021107183c000007a90a60310003000036012a80d8440c1d41c0d0a04400741d8004804451180c0780d42d5001c100414020085651180003d001d01c90034080720b41004402500a200e030324001c0c800706c13020a506164507001c4248245074814001440b0b60004050041008bd403440b14001e0500d4042c00110300481c0c031000540c00c04207c4c514019002c007611b000c0074002207460000700320309480300610103030b20740200054004440d000010815243d0b01d00045607000300514011b80560090004116894802c00205601140c03a514482c0382420075200d80c42101c0d10410181e440e003101000510851500100d00b0743c014404503800d1902c909121071248510050b481000c0c4901c00c2000c0c0f0150036405140030080940e080044200d400b4412040070303020300328460b64544240290380c0010300d1403900d81c11801c4140e8030383c4034480c09c40e82003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 116347050 1250 116345800 116345809
    0x9060106050a05090907020604050607020d021011070c06050405040f09021807020f0703080c060105010c02010504060809150f040b07050f04270903050406080a0b0105070b060d02040e010c020c0402031005 89
    0x4880c490100f02c4100720303c2d02e090716400301c898040c082c0c0b03900501d001c0c900f50900e10b003440c1000e0301c544d0840d000b60b81d011150360342c001404003485400c0b62000034003100b800b4103c0621f1240500041881540400001c1c4140e00180500100c0d24255070501c0940c002c031400340b080705d807a00e10080d1f000180c4c0c10981d0440007201c2602e640201640120346842d03a50020207403510300d00d070b070003280c11303190020300d441d0008070900c8114010042030802c401c06600d0740d80041c11a001d04c0c09444c080003250000240424410040c00007441040a08409681041900003007842c200711010307100c1d41200804103800604c65011180d8590141c01e4250134103040803460489007040000312443e41003020035500c4041001e11039000c40c6032082d103c0701d54841c50118060302182005000201051030095248241e9811400711114030b64000d600c02d50541d20a40014400c61901101a41061615145115400055100b0f010070500c0d40c00300c4100d07044107010002a40b200712050703044280307441420031507400d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 116348300 1250 116347050 116347057
    0xe06041a0f0f0a060308030901090c0503060c0307080406140a0e24010504020a0309050d0e120d121d0a080405040b060414040203091203041127010b090a03021909140906010605 77
    0x269003d0115815980351100440c0360800e0700d0030840c50355140031040800c04200260001001c0a41c082c1180d40745c2004081000d000c010080b200340801280003501300603055000c0710b490192110b1502e400d0611540303000c01401343c01001019031140c8402c00d003102007511303041c40d6209000204403005170b01300828407001c2e4004000d0b0405060300c0f0481d400010f0402e020045440c8507550701c800c0000914000c00061842100c3e100b00941c10220804c003070268070914036030b04207416500c0410255614120003000b0104540c1d5000640151b008820411608100400031074000f110300344141500c2d0401c0001c284554410b01f1050030494005030700508094019543c81008002610601140d00d042d01c04558401c0360110350b40492040d21851500d4800308110103108085400e004001446402c603501203018042d20030042404629101c1c10741e6560101c0020756409405042c2000d602030052411502c82c0c040d920880b410441c84480444201401e035200d45103400061074075074680841624280e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 116349550 1250 116348300 116348311
    0x110616030612061401060504030803061c0503030702010e0c0102010c1e091d01060909090f2a0306060509060102011e020904020d0c0f0f08010510110106090e06041a0f0f 74
    0x60311110001160244100080c2e0001c0c010b00d40401c1c0308030700038030081000b02c058100c2000e100c0248024004507000c542529131180c42920b26400600c0f981014030701c1c6c0122820020304601c0004108032202e80d041d0000080f48903903100311015182010016420303141149070b0700b0001011801d806200d014204c00501d80a1154286001c0c503c1d1954280d410204104c81954110300c4480c0c010031002d0342c0000c1040081402e800104500ba041d60f848841c07030f0344c0a61003e000700709a0358182a4210b14580102d040f00e006078040c446a40d13607450250050701c02807013003502c2403a0360400554a540107000303442c04003100328004440d21350504803c0f002504408140e82d0450781c2802514403d8100e0301c102104005151550381074080050002055410020b0001003007209030001040b840e10740041d801e4104400e070030249070400d5004082e41c0103100b0b560002d50032a0410a84501080010907454041d03400361009080e48199403071009501d000660b00400401615000034487c9040c0c031900030f4018 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 116350800 1250 116349550 116349557
    0x10506040b0112110f040312081e040b0405100e0c0312070302060c1602042a170114130f0603050d02150f04060b090703240b0a031119020c0907110616 66
    0x842202c0c2c000c2170030307006500308940b50104030b00c82c00c0c45540c00840302a840300d541c00307200c2000400303140048214080900024141803202c00420104030b400d103c4134a0300d07450011f0420007103000c03184132540d41e00d903c54007a0081c0a0b14090341c0c84400c070803045800080c0c05400800244c1c4540d4000c100c150700c0005440d0b440c0b282e4900030801a035841c092040c044802c98203030141c626800c001c4020905550782500c041c0602d0725a40000c402c600800c660468040b54101903402400d1408149503202d0300e96a0f19507207141c00d60b12689000d0b1648210701740c1e130080e01100c0d192415200141c0c1c0d03031454180301c1c00302d184d600c030700281c500c1100c5400760b0b620038420180400c03c4001d4401141040e24180e032140b01094540c00b242c020b07000400401400155811980a0703801c0c80c008483e551441646202020152980610f00c0714400741c00071600640070b0b4000d0107410440052000b51149869103d5912600c0c50001141805120303603c050000307031600340540640d450361344400606280b812500c1052 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 116352050 1250 116350800 116350807
    0x308070903080d050a0c0e0d1b030605010f03030e191211030a06140703090c1203030902030d030501050405070f1d011413050a05060c0d050c0102120a0e010506040b011211 75
    0xa107125001d083c641a41000c0030a40741003540d000000d540c0e443c54240100101c42c81041e00b941d40d0005a184284d4100c909521880b072203072620620301c1e00c1900060801800c1400004a0038103c805140443e4029a107050045111008100703032140e50484d40d08d0301450900c000c1c040d02e00c030a0008030710b45209a42c0a441c0010301c10100341825071040c802d0707031030550f101480c010143c5075035511684414540b070100079a210940d80c1d45160780007802241103015a4900d04010907009602001407190001d0444078505c1d00c0303070002409040c0900409001301c0c00d1601140e0480d0107070075601c980310304580300c11322218800c64154401c0b0a81402c07a50401246001040018180074000d04064003014a103da83c54202014803800c004240c0c449030044034204480000e00c500410b03103146e00001440c0140e41c0e1160040c91501900400014510342c0ba035060621803038070300580c0304444a0081c00000d100301d40c1c400c0304000440b0341407030416020648914088480d00303420f911107642101c10041040c203 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 116353300 1250 116352050 116352053
    0x3020f030406151a19142209060806150105041409060d06020c0a020a0b0a050405091b0427050103030f030b0301020403050f0303010e01150c030c081c0204140603130308070903 77
    0x213500c860319010420704000034104d00403041c0403c000415880c0e43c00c18040005103503101c180c2520503030540780c14030b000d80c1041201c002d42c065140c1000b0044d00d201484100d03120310341a615550b0a41e900030021f50942c8011501d940503209031821251000002c3c03c082c29510305011901000401c41c5134000c5451005000290342c51028100c0102d03c58020419220244140030180f404d5400c5448a0f6000380807007000c0c194490304a605858040e585a9041d4030740f05541d900d000d441100c0c0d0514200c020901003850070ba840300410300c00104d56401104d4518140e141350464000307000207000100040e0458030300e0343c02a00500185d5002400043c030746603030794484078141074400f0020f00c0d00c1e03003001004020341c106103540a0301501c0f01141030414180019806001d0142942009052000b04464041408042025540e00340a00c084000e501403a019070302000354018021002c1d9140400310740c00e02c5003040800c1d80e22071003482101110039405d85c4c5055414141c0185007508105c8920008030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 116354550 1250 116353300 116353319
    0x1e0709050a0902130b031015210f0303050615130506160213061e150c060609021b010e0a03230712020102070308060108060d0b09010e0f030c06060103020f03040615 72
    0x43c80c4503030280001412045d40c4082500301454114008402c9007400d5450070f100402202010403201d020b0002e0340c40c2021000403020030114490098400c41c04164041c3c241501600301c43c2c8940411201d29202c220f1841d001e40c018062082034110700c407900f03038080c030840c1807520040c00c0b2504840c029850303560156000a103000c00743c00c4e9462169480781002c0154480c4070162001405400e40144a898240030307110304403c209003a80010040c8030070340300080c00115841030002d840d03840340c01e6545180c034030300941402d000c91010303038455842d0022100706400e000c14107426680c0d165130341003078110006a48010360f080c00c141d04400319800700400c40c0020004900c00e1291942d80e000548c0b60798560030054901c1c10014003007414002080100302d00303a030b2001c0010820a9001c20454a241c4400d0182c0c1d00400240b0030003e0580325404a1580d1304078000090880d0140d11822a00310b50307510070044043e4082e01103400c0c0145010b0010400282c0305070010340c0c10900e005180c080c05c0740d41d4590312 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 116355800 1250 116354550 116354569
    0x3211404060929340506070806010513121703011509050411030a090c0302210f0d02060423030403140105070305060102100b01090b0406050c1e0709050a0902 69
    0x308401507001c0103001c200140460243c0b039812081c11641c0d2004814403440d1094001034492602211042812103000c0c00e01806400440040741d00d96604601e46580c0d04e1034141c441c140411a0300c00087c169610640c21034510141c221001c9010364a04030070080c8441c1c0c6a081103806125401c0b2417040c050313009000e54001d2000250200f80b452403148007a10044c02500802d020700e08240000e840410400701712604410800000180c20700356040a04641c075964000175400303402001e1704401030382e20290380c00e80300001c541507940002402c840d05a5031001d0000d4000943c200500180c0030030040c040c080723010b4102005040381c21100b41d0302c80342550710682046400c0b02290901d540c03500c90910641d50300c9070250404201d00d09018001030340c1d80311587d4001c1020364441035035900316442826180700502c4800005c5031503030b441b840040e1a41c0c01010180038984602d03200c52140b08807040e400c0a0700c46034100600241d505040400c405414002c007038159450711103039500016206c90003a03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 116357050 1250 116355800 116355809
    0x1107030b09031909031a130f0501020c10020301030218060a0801062301080906010b030a020405150703030b010206070f0513150e040605101d030106050603040f030305010501050403211404 82
    0x40e5541d12090140040d5811000c609041045a81305043c00003e040308840e100e1903100d900e15083c26a50000703040c1c0540140f000040810303018015840c100003054000c0c107009040340f01038503484e0003000c00c10401c0340003d21000c0c0d800307840341620701028011503c295401880180940d51000d03190b900f0a829110303140d02c001c10f10030200300c54901c4140c0c50700c0801d24480f02441c0c8180603040c2846d00e6a590803041c090303a81d00d150700102258204115504913001054043e011502c07a0041e80601e104d5608119401d501003801c3c00b02d00c150661010590324400c01081d211340700c0c078a8113005c003101c0c641c1242001ca19070740580c003008107c12402d100c896840d21300303d80d10f040d840c00681d4140800e548481e80260700034040804000480c9801520301002d00d04041c80209510b40f15030002800340045601c1203800c000300105000034041d1031a41000c030a4000d46041c40281da07144011981881184006000d0301c11542052650210240703198103030100a18080c4144000c00c46039000310780c841c1e4132 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 116358300 1250 116357050 116357053
    0xf040504080c2a010923120d08040b010e070c03030e07170c100908070501030902030c090c040e090a0803040f050705061603110102070c031515170c03010b010e011107030b09 76
    0x640c101da05541c10410410202c20310380841521b1401032100c1300d034070450024000321030031400004d8187c0c5514a0400950303005400300c8013492034410303016100703c0d410fa4043d522112540004a03140c50801c104034018200c40c0c5d10200c00d020030b62030841c000d00b803c542c005914010110001aa00002180800000303090005003828040d86400c00841c03860a100a5007440b4a50301c0030400400c0204400d0104c0c0c3c800c7c00d0100d4811003074130010b800c3c401062080c5c2d0f0320400800038004100308040240c0159040000351080700d450b00490780d6941e8a4400c0010558081040094000741c0c452010b5841c1d248114100c0364059200d900092954001c894043d9a64a5100c0d59000303050f4012010040080e008e4021440c01510341c442003c2c0000500000c0d00c0088410100c0c000c06540c3d80c44810311220b002a05c0e1355050301c2e8102d5022001e00125005032510946800c3c814916040c41040350102058555200b00c42282005450520041d120704446005140000003c1014500c015214145a90 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 116359550 1250 116358300 116358343
    0xa0f060f0614010810050f010f0203070b07081812030103170d14070207050f06090409050f06010b040e09030901090e0c070209090c030d0f080103030503180118020102100b0f040504080c 81
    0xd00040c00c10000405d66941d00078054030400c680d4540b070580c40e800036805e20b480c0f26000c1d43d400060b899441100c00c000c203103000038410400403a6100707400d14080c04072101110741c4410280300a0750303100c032084140001400100010000030b08810032a000304948020340509124110303012108a50a03000081407200b4420100980f81d94140450f40c090501203c1c840c66104200001c01d1841c01020b42e018041c80e69812407900b0f01104004a002c1d030140c100480c1d440e076865091445442d0070a218070b4140740040c03404105480008015942011810781d100d42e60702e440e00c1100c0c104594042e1054900030410002130000d0384503403034054800c0040000402100035000d0600d07240100c0b0408000400070743c24505048558480700090443c0d81515199880380c8420301d20080403140540031105940c0781659100c9440140300440c04250300076001c0d116481c025184e000141c400240283c3c0d80200d0b103104000d900c0c80d1550086070043d008000890808181d01c0d940c61500b14400d0185903441210b2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 116360800 1250 116359550 116359589
    0x50306130e1014090a05100c0504030b0403090306051b090d020103060b040f0f080604051209270403030b0603060a120f08030405031314011b05120a0e03070909050a0f060f06 76
    0x4002c100d411403107140050003040041c1e151640c4901034101c011340d45a48234010082d500340f0035000d0b03401964014074200c1c0f0fa420180780251500d10b15202c1115440e08000c00212442d0b80b412400401e121204002440d00e4454400c00a01d01650034049040c035564060104813088100c003d0300c09010390201000f5540d003001c0c40a0a0500c40e94004201c0c0e070b210b0010400000d8020a03000c048080603540962030300d44820019018040c1500d442d042c0e0b600c4441c0444400075040142401a8001d0310200840c54001051044034441260720940240313050701b003001100100d41c1d044080a0042e140001c3c51140342e078419400b58001c0d20280c5056101203183c0350603c4240c8449001050700610342004104043c00180954440c3c40740e92845034408101c0000f800f40038060100e405103110b03211544c4000001c0c003d8501304043c40200e02030311900c00082280c000e2407040803109d542100c010b000c0064581d0f501e244110710310340c04458142d1607a80d0605500c88501484019090711421030840d040754 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 116362050 1250 116360800 116360831
    0x80406030e0c0405010311090c09060a1713021c051009050a150b0904080c01090f03020601090c110318030f100b011b02130f11040e0106020607020706050306130e10 72
    0x2c0d42c02c0c2c0e8802c80c580300c01040002d0002c14052090041502c00b0400750780c41c1d032104d203800c3c0206294035070052400102400d41603800350000c0003025140300d0700e24490b11245510740e05030b540000020b40004071103204074007030b0943c240c6c1410102c0c1f061048440b110b003148030200940344000d00c100c41903401307803009400300320070b0401503038841401c9802082502481d07800140c03c40e0f4041c03c00f0300044400952441040b10a401503620783e45c02c01c800300d85440f0940790003907031450244502c0320208c0c68000c0d03100c507840c07280481d8041f2403002c1c0003d40c2061000c05020320a11100e444141c1d25200e84160468091414400031506140300c4600049403051031001403c500080d844a0f190005c02c00e48070001603a4211740b40c0340154900b330700068409070785e2461000500300f0989035104c045000c140010040d541b002d610341070f0b40300341d406c0e115580c13107000043c0d0b6952540c3c0542e501281081c800140c00342440c8138140100702e01c01c0d10115060300400519424a8601840d00c01e07402e803142c82d030300e208005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 116363300 1250 116362050 116362063
    0xa0f1220040302040501060f020303150607020405041b08010216060c0e030607090801060b0f1206040209040e010e150606030112020a0b0304050c010201200414040e0d0804050d0503071b0201020703080406030e 91
    0x41c7e424030002035544100700940700e01c030060000d000c0c0c800c483c6c01c1801580b918819034845680c05882009a400c05092008801c0040252010644508034001c9201c1c071042c001d03140d40c52100c00110414a86d01e541d02c0703003c2d22040c1074180c2006164078140c40c080c4e5041003024090f054a403255102d00382002c0d0034500b0744400b50813456684104001c41d40c2c01113100320448292030f481108072402c94581c10000742c0684070340c1038542d500500b4030681614825040d8800030b040c078619011110800101c02c0050a1418100d90b070f40e40c17007003050004014894200003021100c03031004056006480c2c540c091041c5070b07002910140c40d140e1109191504a580921400c1311424003010b0b5407a180b80c100304031180038480c50190036042d07e1040c80074480740c2c81d21f4200c0701244880ca410b982d4058400040202203041c1101c0c20358a62042c550000041170141003180d024046c4c2d0340d03504800300768090300c05d180c2520001d01241184118171000011651840251000d80915a8046141c07149450003925194 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 116364550 1250 116363300 116363309
    0x10f1d0105090c060304030302030702070b0c0d081b030c0f0906180315010807181107060c090b03010305030712020a050d02210c0c0906011818110a0f1220040302040501 74
    0x6002400f40001981c40030107070703640182d2500d40541d0301c0d55050720807404d06100358040740c0311078008a450102e004021951041d041d442d5944e542ca00c1e9100c00f0021951440380321203c20b001810004070b54800c02c0d180c000e20102400340600c0d4905503064000c200380c1d900c5101c612402c01485503069103140f030b051050840382042a2120103055043c0903502d03844000f40e10810118408500038500654499042070741000c85811885480b0026030a00f030015203048400000040d440d20f8010031107844000a03641603c0d041070045051002e075a654105200c5881000c3d810341c85001c20758800035130704103c07260039001c840d0701900d00041104418101e021528101a0a80e0410301c00100c5482002507041c0868200315407a28aa071500c200586031b42c084c142c043c0b4000000540089900000c00100600302495850108044008200d80300e9680c051105040b000442a003c0c0f503030301d40e20800780d80400c92001e9a000440c06000c9216000214448206802000002c1410001e51070580b01d05030040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 116365800 1250 116364550 116364553
    0x412150b03030a08070f030b030601030b010f0509130210030b060d0e0f030c100b0111061509061c021e04180b1006081b040905150f0609061b010f1d010509 68
    0x10f030101c2e401030080030000703000404001010350040172161203034100c0c5850315005804c0c1c82c07480d40c4074140701200002c240280790040a03010340000e15820403c032810f101c0c0d8200302401890b109142c1c20401c41c1d0b103c1000341420151515540c8013640c1e949401012200c00401d000107104280126260401c041900704242c2c41c1c1061004c91440740340400d48503096510590001400c1c2200d4006032100d0b5004401c0c50041e00c150010414020101090810340020480c1c040d103096a901c0200b00e10041c0220140400f908104070080050030b101480120100c50514180120341c03c1c0808107044032482512401c8130f01840000c40c091000c0402c840740c200020502c03c42c005810444090306c40c08001d03124004058040c00c0081d5150320001c2680c0107007a0840050103541400350581205a0701036113800d20511891000200e6071400c2c07003c0361441c04001d40710b1400c0081101d04070100a03041403e059085d5200e01c50050b940585215604000592140742c90601d03030061040c80c00c650300103081508a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 116366906 1106 116365800 116365807
    0x6060b07030503011d070f030b0d0212030703031503050307030c050a0203030412030e0d0b0105010309060204090c050703141c0e0109020a1413140a0902060412150b0303 74
    0x1241c02c507100040070b517420380b43c030042c15020a46072440480d007100c051407c41800b9401540104c20700400b0035101c10300e16008181e18500840034407806820000f001d00815805200c1d07202c641d100c1c240040074060071aa01c0079038a00c1141c1000d8203020000c0305050402208204540c82d15a02500743c948a542d50081120000da65800440100d044d4460300744a509004500c0312200d508100e02d8081c1d40d21b84001500200604081520419002c010210709440c0c503000354a074445c801e54842e5550f030454100108005a14090712855900422200f49644985443c8441e00c8204e0700e0000341e81c01900494078014855244001d4011940c6500011803503448455071404d80420b540b085502c001c0031140f2412580c581c1d00a24001480d03c02250b092030b030b56071140e96406e2003e002c56140ca0f4480e07015500394001c500d81110310700b141c1414441120540d028000c02104150001c508 = true := by decide +kernel

theorem cover : BRFrame.Cov 116187050 116366906 := by
  have h0 := BRFrame.cov_init 116187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 116187050 ≤ n) (h2 : n < 116366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
