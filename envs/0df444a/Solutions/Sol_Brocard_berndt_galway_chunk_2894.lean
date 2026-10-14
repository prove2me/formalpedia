-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2894
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:03:22.73871+00:00
-- url     : https://prove2.me/submissions/2c2ee418-2901-4547-a4fc-453fb56dcbf0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 520323741 ≤ n < 520503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 520324991 1250 520323741 520323781
    0xb041e05122101050d060b060403140304030201081e1513060f060f0504140114040909030e041a010c1719270602030a0c060612032609030d0c1403 64
    0x5440b031051000240c80401c10b0341210000380406030010180c0c1c0c0e501024182c0c0b00c40c10f41d000390050000002280010540c22401c250400107155900e086000050010b10300411405202d05405600c001c0c0c80d00e04410745902c0140d208142407071410080024524406864a404649080000c0402e81c17558400f161002c5903015107402c4814a00701c0f00c155902e01540c0308010400218400017246035018601c5c552441c0284604030345003035103c411440031111140001e074001800c0403140b15460400340f040b1105954283c40102c00d014050b0002065a20202401403600700030b100700c00340c03101078001650014030a03e1840355041040c0780c4002c000030f21800007003802c03a9001c15a403200c0d20180850005031403243d4050b5103400c850550948416800c40c00440c1da00303903a0b08000601d4409600301421807032090751038080412a4031210021102248005840450f0303100174041c1c0d01800104642d81e0568030440031920700310003c01692000100c940c09207049900100b0030092040080e05007000c2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 520326241 1250 520324991 520325017
    0x30309020f122a0306072f1c0203040803090607110405071d01050a0f0507021f0309050705040c0906120e03030a140a060620010209030109030e15070b041e0512 70
    0x80c3c003208520f10f510034410701c8495016001480480c0340c0903c1000f6121800101000001112078030b8490488280f8000e017480f103a0b9080200c21401c1900c0b071401e031301c0f0b044a040c8021801c3c542403104054503445a420030f42d10030080058820b08000d80340c4008150000700900400c480e00d04940058958500c0308409a00000300d840d40302d03086c1d030041c4141c80031801e5954820201c940c6007001503441d580700840680e400305480e01c40310b000c44803900070201549170329076005c01c0c019041d2410701e2a003a06500103030712590800038840040d5034410441d5040707030070f903103000070610100700240d078018010450b014500380400000c104e45402103800c0111a42d0b005c190302d0082c1c4d0307034100e04141280c00c280907810005604900d840038600139421010a4a40140c000518200c1c40c040001d08564040f28110f020030700080964020746031031421144e058410111007481c0c001c95a541c0d13408040000c1c07004043c44d000c4600601482c105180400350f25503c0f6003255503890401d8052000b58001c00d019900c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 520327491 1250 520326241 520326283
    0x10e030309060708040507140303070606080d2003121b0c03030709050f0d120e0901150201200d15051e0a08120d020915040306140c16030309020f12 65
    0x4600e2007070191078421760304100503209007803c04074001c40b22a1640c107615071500c0203224041c0818210f03c640402000c07400014001981d40050160210000c9002c0800301001d5107400041311202100b140c0000281503003a1003241d0754070b2600c1c03008015051012440d40da0108004030a148000300a41c000e540986505084a41c0d0310200901280c200d2000c6030014a40402c40c0001620b06d9918403d5449034100700303280318810404a40d21101c26880300790783c1c3c0c80e15400740c0343c500d40a2140313080011340c2e01d001e0000d100d00c4a0341c2d5001445a040300c507a45555910b80140300c640c030448004041c05c0d00400d146201e0b0160740309a550b5090b14203c3c6803007968080300004124000140321560301e10b403408642c5c20003c80004800003500324501d071981003115160200407900151006101841c850840007401011405e040c808003030004107c600d0743d910800c4641c00e00d640c4a0f8144c0500c07907041ca00400c0962191020946208110014a4100410580c0510808070114030110f08400f840d0203005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 520328741 1250 520327491 520327501
    0x100504080d09060e0d050a12051c0f05060a0e0f1015120606020303071d030c18040303150e010e100f09020406140a20070e0a3c020a0908010e03030906 66
    0xb5101313450b84801841640320001d80c00010740703000c1c14841401c08c1400c0040c2000e00b03400042141070b00c0005200b011a544200b54601400240300d41c5811072000c0e907510b20800e091800300510311502511882400017004000f03400d189040c1c0300303100a040b4424600306070702840c04019000445420070f254045040142c0403503524400002d49104101c00c5d03503030158014050101007034060340f40401d03030340500038440d81c040c480e100c02080300001d04500343c07403464919103424000d080790b001c11800c100310401681d042164a8081d520340c2d040d10004000d100d81521402e6040b040240e0320341c4a403000600b40100080d40381e10990244c4200c0b051602d40310042d005048881171203200d81c00400011440c0b903403c4c240c4401024810341005000842200c030b03080d4841c0c6801040b07440c01c0310001202c0d0b8070786d01803400005411b401c01c0d0280c2a05040e070b6140c414801480c04000811481d4080b2550340820f140342c005214008420003002d02000811200403144882a1640d200300e920328014410790340425 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 520329991 1250 520328741 520328749
    0x140906040311012c060a090503070b2d030f0601030f05090f0f01020f0708250602041a030717060f06070b1b0c0709020d0204031a01030204050105010518100504080d09060e 75
    0x3085144c000004082d020300c00000300b14036600040e16281c1040920f1901041070f4034100101c0020744202e0900640342e87c1e016559a5000908440da07400c4070401d0203c000030018000b064079000181000d440c1410399036080103d00615540400b845042d0405041c000b4004006c903911184c40541c400b61500700c41d03c00c2e2050300740d2080b5060091061000c2143c800800d58600103001105903030485c104d1015910030b1030390355404280c00c06880d2564000b508100310708000d100c680c021443c603d0038608503e030200303000d00300c1415107035030048000180d00000c0329680c0b07002304000c0c1504020f2400e52500f84900b081c6509a00848506d01601c03001340c00b500f52264600207032074283d50a28001c0c099141088a07807030280d04003150340a0220307024080400014810013204c541c104101c0c050910700e61450040009580c0103901041c1444001c1041c030040000410f40025a0001034940d4000c00c4040c070300c01c40b024801d0754003c0e4014010304400b607000c6640054401d044440c41e6450041d624110320802c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 520331241 1250 520329991 520330037
    0x8072f1c080f0a090507061e09080c010c0602040f060e030105152d040606020309031605060d1e020309030403050705030c0a0603050a091202150a1103040314090604031101 75
    0x101000c61105000244491000c50b10240e1040c0301c18400301d000306290303071158a007420700c3d00031002145250038480a8032070501031242e943c107168500b1030011071519000e940c40c5c1d85101410303410131003c0002c540a0048075011103008050f844001842c00d6074a170740017440281c0c4042e000384a9420480496880500ca40c003040110200408450480309c00749080120061030f8002c600300c00d01500c0d544000e81d901c030b1040400401c0c1c6d5030007941d5a16000710416041002440100c0352981c0d2180040c80103869003400d4641d8800d01e07050002d4110842000503800300d028100442e03c80d4000404c0114810000c40500105c0344240110307540b85498a08254540458031401030b08131401110800032a4803c0c0c00060f00403501c6030f8000f6900e45240c40d007000c110748028401e0090382c080310000c0901f0802030315169224034a034804000b50026405460080d100161015080140c4904109071100303010040350100302c0014003032591603503a4a007110300265004402408103021801d141c040c500c1800329 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 520332491 1250 520331241 520331293
    0xa1101090c0501110708150a1d2a0301020a030603170405060a0302030721021b0303040807030c0c0905010810110a08040b09070e180601050a0308070308072f 69
    0x8103007922400d0070011260701d254000ca40450703104040d00020498424402c021506d42c00b003401070380382d1410112a4080d01e001009524008001300300050890401040e4010b20649410703004d0841c00c80c0401004020140318540c1d903140d440083c03000f078842e4059100b10b08482c411940c907001c1181002d1610305501030f40c0f00303035604620100400041544070307500551744650303281403035684c07000808440340c594606002c116001c02c1d400100801411030300310109040d92a4800150301d10b03d40340e030360241e0038024480d008062146052106041101d544502c9000e0f00001404101569461a95903521030640c80302c10742c0e0b54074201e900c0040c8030314501118001501902c3e599003540311070350380000040000f4070b01c01290052210101ea000844110240500c481030a040c0a500c0040c040d00d04000060780881d106040010040000807494410345102c55010304101d0015a50a4407d0303449079201145031100169039074409441960001c002000c442c00c140031558905d1010300b82c10860002528 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 520333741 1250 520332491 520332503
    0x150a0e040b07051c09050a021f0e061b030f0a1b020d021201020c010c05040f0608060d0b0c04030804080307110609030304090f0209030609070611061605030702150a020a110109 77
    0xb45181d030189000340084140c103001c8a8200e4036556110741210b0070440d00300c42d19040440d0080c150700c1e2000c07070215000a00040b10703028800c06c540c05841c0040c60444603024030004601091481e1500d8404448140150700343c80d61580300c00c40201d41303907104201c0000440d110098078480701c01000d240c080801c1c0c4c054a00b051046203602000120700c1030031f01e4040c456400700945005544e0a00546d0b88801c1c9a4031256111400d00c04c104041c0240ca410442c2048490000c20000c1e90b00c0ca4099030407150090850300081d01c6040e200c0030303c3e10580d000545610340c0000e0000c0e44080000003400158042e0b0034000c0c6480390001084003901c2640180313603143e4028002884940351607481040d80d5500004018078000300480030074140f820844020800382c2100f0000c2050319005036603038010391420000b60407103240002100c15045404400300042110100019031010300070030013201c0c58090300c00e0b609820301c1e12800140117580110000310000300024044a40c48105001c0c1c00c0e80190300c40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 520334991 1250 520333741 520333763
    0x10617102a031508030406210e0d110a050321100803040b09010201060e04080301060801061106130f0f21050903060a020306011202040b0d180c1503020c06150a0e04 72
    0x300d021000b50114862004141403c1000015a66010130044c8000c1c003075504c0d00ea0305044503100c03880710410400c01d04100345041002500700380d034010401d0444a03009003403001191b05560ba1551601c8a8901c00600d940320004846091158040ea400ba50b0015503007840030590f0782040c442d895141911480400c1c1d40244000d016100c070f01c0003d000320900620000401c2ca940d508044018034007500d0a031010381340000140a00b0364481162400f40c40c0c0c43c10240b50325000101480d5036408014111030f081500c2c0c4804900700001307006004142a001000050781461904044d42129501c808002941e0006440c440c400341c062401d50306151030040103030ac4240d41c1d0b81d685a01a501c0201503030f0400180b03146070324600c1014070181015000b0210304540b2000342e1547e0b00d04641c01d1406a074061190b00c0c0313130030000448404420069602c000c0004091840150003039010f0301400c103401c28180520380402c44400300c0c0041201c0c04400031500b80c00181d0784d41c030402905140c1964040d102609070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 520336241 1250 520334991 520335071
    0xa0b180a0b0a0f0612050c0904260903160e1503060c031f06080709091a040c1103220b190f0c2009060406050d060e01061710 55
    0x4406541d0051021001040442c541d0f08048100d444d9a003000802c0121a241075050180030031140c9199041610140300f582090b803201c28540d00c2c0302c102160f0041c2240c03030f00d10b0940c10300001e558484601038115425282c024100c04030483c80b1340940d01003009214000740d850490801c0103a458903014008c3c106584403101c40d20065440103150fa002d9030b1001c2c025052400415804030001e107041d0b42e58080d181440079000b0103400c0164032400703116007800032245550484000224030761400302c0c1e0001d49125595820b44d100840d110508100340408070300c3d0804114000c00d0400140c0100c604502d0a54544200083c140070345030040405070b41030510090514055121804054843d09044403100e80b560ba0b01407503602c04030720303080710103201e500d50060070f0400b07900e6960040e41c115802e10501d4180350114221100b9550090411038032100e94180ca448203500c1440600030490303900c00791007903c1e00f61a5035204140709000c8010300e4000381740120135420321000d10148038100400c44400785 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 520337491 1250 520336241 520336253
    0x10909120f050a030518071e050901150f03091b0f050306160f0c02090709080c03012d0e06070207150903170921010608070e010f030b04080403050a050a0b180a 70
    0x140707600d400c0c06c91041030382c3c1c07a00c9040002200900e21004040000a81c540703800f03505c0d868a91040d0b014141d2603005004103084031a00354001501450070740302d009003111003140a00440040500030181000812050440c1c00d001003080d80d529000768a582507072081490360310002159031100c040c00040b44040d080307110750903500304140d05241c020707008401900003a4400350107586c0c000200d07900c0b04080120710700174040ca000e204821002005500111000740c0a2160040e02c8948000b184514040e0300b102c40d640664080d442c0d107000c4440b00d29003482c2c003943c0d601090140c00c0000c1c81e10701645030000d104241403015031b0742c00080c07d21584108030400090760455096250701200c1800c400280c5905503110034801401d13900041041842c00d440303c0d007014180d410106201d2965001848080c80042140c400c0300e0f4002204a00e61b41c1c3d90418400c98080c07500000c15502561000c0001d1210025181040b180103007005102c80d214008140c6815a03580d04c003000b03a81200c01401c0200d14 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 520338741 1250 520337491 520337501
    0x6060f170c030109180602370207060509060c01020d050402210307061808070605191a060901020705030609010203101202010f0804021912050105013f020603010909120f050a03 77
    0x150442004807110a81c0d5a06d405a0f0064000e86099816158148160a0070808182e9501c1d44007100d28401140c6100029214072641c0101e10034031030002525101c0c0c1d200d1900701c03030542103000021504c4007652a1008003802096506a10524100c030062038200d43d000480f84214241c200290310f480e1070383e610b04010b0007503042da0001c2800d1071182c440105200c0c84c0146880c074490900012180f40c400f0140780e02d03110403101088110f240104240941c02d00188002c406002240d103e0348500102d40102d10302400d03500010f415014040031302c528850150042c5010f805100e6440751540d850707455524615403507180c044d0000d242d540c0d01c05c080f680206030246c1c100e800941500422211180c15000c0100c0c41d80c000d110382c050b03c440b000103014080c880c00c2c1c050038a2004900064140e07403813411403003c1c001101c1000c26a1186552441a003030425607400e00e60142c80c45803250ba40d26a008003c2502c014252664510f0541008034984180ea0b1801064401d8071118203094601c1c2040340100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 520339991 1250 520338741 520338761
    0x100c0b070e0a090e03070b160807021f18080a050301060f0e060a050d060801021606050f07170a1415010e030a1e11120105090d0207060801052206060f170c030109 71
    0x800104140c00200f441c1c02d010360303c101c0344485110404080c00400909c0400300400d0303034045400c05003103510340e8218091b0350403081e080d00c0400f1603849a060b004c0001003041d02d00050860400182504403144c020004d58100e65a540314180e044000b15002c9d1802c00006000382d038003134010051480c4080c0500d002d040d10485a01d40007400e03584800b44942242e000344400e1455601c861450400c001483c0155a4001c0901a640c1e405003011200903003004d805c40045003131071002c4000109600d031158803400c102301d1411091011420014417010f140106d00301040d0004650340c0403041c55017000102446010341c0f000c1401600603584010265140020004841304203490f50026165038030407250000c0291014000a0341e81081201680b8058142180b20306541151008202d1141c200e400141120400d403038a59224040030304e0602c55603101150342002500d000c401043c010752001c000c181e840002c0d155001c41c003600d0140784804210807115400c54201c10001403110b02c0f41904941d00d00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 520341241 1250 520339991 520339993
    0x108100f090501090308100504110d02160c06093209060a031403030a0b0a0806040609020406170a0c09060e041e0b0a020d050609010b1207020705100c0b070e0a090e 72
    0x407425603911142521051241070f0009016001448800e5000280d103074000d08044600f0080ca0a042c0720b042041d00440613040080356001c9424a161405090ba884485510801940c6003645a81c0040c00d405200d0044202030700c0000110599002c03080ca07118906d0b404408100c00521110040040b1844002c0c09a60403d0302c4000001c0041d041141948003081c010700515200d207440010141180c2815a400303103d1a40c5036020400540041195a0850742004020805003254008280541210391013200000101070300704c0e04190000c0f42c441007051241440e9640940e079403002005271802030160551010700d28001c100041c1c40300c2d0700c0210100300000340812040442c3c85400d04000f045404100c525000241c420050080340701d07060340b242c001c03550b481082d410700500d8503071801492140083c02d12207030045042d05008100f9a80100340043c107442c00720300c0d20080140245400a800c4440c1c0f01a8000300d51340a0194540500d114005401a0101840d0081907009085215120300903 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 520342491 1250 520341241 520341251
    0x51e040902210f0c0d03080417040308180910080d1101060b0f04031b0f05010c061e14062e030b03010c030b01020f0106060806061e0d0c170108100f 65
    0xb16101c1101002000d20320840940140e004169106052043c40d10707010703200c0d16407034940c40006900039801940080e08400c02098104600c00313800e0b52072140360000317041075801280e0201c00b884074126007503240b28152000451611403048000b81c03140703d801150314a400058000043c1440f50b0b1008090a08001c00071070080c0c6d43d0514412a0b0703100c0d03120960207480c005401e006104101007440b1405c1d021a0401407090302d40000206944198094581003110400788a400d010b41a00084100c40d12142080c00c02d441b4241040000d0190700f03c039403090001d41c000105c140c5440d03d00205040c508007240001c040010003000604d03000724105c0418543e0319000c80c1c2003a18240b2031410a01140d03240021542c014000192400c8006030694480c0da041c00000c0c0400c95000c0740c400d42026060b140c19864100000b007010440d0302018030701442c02c202042c200d24440d0a6080516034400d01d4a6080320444051115804c6002c24003400c1942d6000340c009440645059014149455040e01c00040d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 520343741 1250 520342491 520342519
    0x30080d0c0c110f06130807030210020f07090b01022b09050906030a06020307020a05060c03010612020a0c060b04200417190f02151c050a06050112091e0f0c051e040902 73
    0x81171518640001c80c0c191f21000c0d091045080007688100c1c580c2c51400242071441080d03000d1a40e80b008d5024283e8010340721014100164000c0024600010040345445040741c1c03d0300c861401c203c01301c1c0b11407001904100000410f03081c8400050f0180c28080c020380080d04458271038101075440030f0100c4d400c520620882c03001151061080600031340012824590303035490150010710740c2c50803443d0081c0d130074410003091005d0341d0072a60b00510958070800100e2200000400100100340d500c00070000c040d40c0025220b003c01c002001041030702e18101c07900f030741c40e081d12651580c1d48180459001560411007440b9011401c41140c1c849210310040285038821800300502a1541041141c3d01e40300a40000500c859903403405540c5c4c6c054003c00e07040124615090008010300c0981700d400c080a5500d650610921010000e4428141080c440c101586d03180e40c900780d042031100e0101940c01c660720f0207003c00c080ca0601c05201442e00403039423080c03c5510070704c10040107250552049074015240b00b0144 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 520344991 1250 520343741 520343767
    0x30405191d041208130f060e100203010503070f1a030a110a020a02040b01020d0c0f141213050103090201140c07030b090109171330080d0c0c110f06 65
    0x8290701e1403401000480341040c0c500f1100c80002d0341d50240500c80c600c420020900e070407041241aa64205141c585009124146400108002d2484402a018a0043e0740498180ea0019412030b88190101e58140e0b42d1540b04800c200598003a140002540c481807040f6000031303101554112140100001c1c0755140000c001180358402d04c001005604242410307820b40c0760034410300c01c010741c00707001904c800c8030000001005001602c10061880840360309003c00e0001e00217051032a84258002c0350105114058401d005820602e403165404014a1003c5003551180c000c00014580c10384a2000201c540c4606040b0794108a400310f5191050540c0040880c0c60030150702d00800c008000000c07035083d00d060201443c00e0340d203201a10900100144101c01058800e0074040301c42142201d04003080746c00302072295155204e4941403044c100c0c0710210603c0000401888040d602c91000c110034a51040c05458080040c180070b0103681e10000c003600e40d41460038502c2c8100303130000d200038138200c4280580c0f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 520346241 1250 520344991 520345019
    0x70c1b060309061808030a090804170606030f1c030b030a0b043507020402130308070c060e0f100302031b030112020306070c0b130f082107050c03040519 67
    0x500002c1c0c9604001c41031040798072403480042da090541c1d0500c2c2889132500c0105110150945900039515030f402c4061140b441c00740c4014000541c000142085032030a6076a441c001911498828042c00c060780c0015100080c03211000884100041100d00001600340c004008464004c0c0c0c050007003800440005461000c02842248500c15000d810b03041902c02c000000070a08a0841c11008545620036040d500c0081d03c0d42903904490240c4d50b03084d400c510210748546540002d2041d00040b515108000c1030310007400030f03501281d8900205054110800c517840f001c5601254000c048940e0400e00d00c0c1c4241c008503803200b04d8585d004075044402d40c840c451039000340d005001c1d400340c0601d40021454203102c2d05800107250f00d00300c26101041e4a0300000000c0241c407031a030320404000441d041103e02ca40020540f6003018660b600c501500c2884504a07803003045071000f01c0d00403000101014000c0703003654117000805006500345800c0000348030340145003503207000c2e2091519100041c40001c00c070312 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 520347491 1250 520346241 520346249
    0x60322022e030605120a08090d121e08131b05030a03020f0f03090a120203070306290a0b04060e0a050604031b2120030f0a02010905030a0b070c1b 64
    0x4110800c1c68111006040300c1071500b06070b10912101007020b40f50742c000280d4014131b540001c21a5a50005080040c10444031060010426050342c1d01d0340401940104580881030182e80f1100d2250140c44021254400110b544211890310801d40d003000c84d034a03090181051124aa012031410b844200181c80e10074005811401039000386c581c6501290240141c25000407004001c40c146042040000c408140070b0040b102207600c03114413441955010040e4000854008004001d0ac01c00c07030074442c514010442050018080810300510f0750304002c14000e00702c0d054942c2d45030800d4142071040310703000c00d20f451407548042010004500c90b641e200080005510401040003110301060b0204840c440b59402580d4050191500b003521000488140b201c46510941281c0a0011502e11100c0d5084d4481201c0d01480717103640580000c1c3d000554103040d03034003d072502c0d4000c0da0345e00c040681c0d42c0100f16006048004210115032400e004561050f107817441030186481140c2810440300312a401940 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 520348741 1250 520347491 520347559
    0x403090905100906092703020c0913050d090608150d08040806010312031b030c020312100503190503090118030501050408030a050c0a020616090e0c031506032202 71
    0x20b000c20220a05110740030042c0400f0005010740c40380389070032402c112040c6074000c0300041d0386d030006001c01d482030011150300350004100c10b241d81002403005040500c040c10403115440381c4503541e0f44c914000d44001c000c580b00ca0381c0380b49859030340c503501c200c0b4101c204007400d41080c14110648009040c80010b000645071510040003590700d5420102c0c14031a400d00404207152400050f514140030b00000c000660409007004103a000380000200c1c074611602c00703103041c825403402c00c0c400c451441f60307203a8044035411021555842c0c00d445900700c0c00600040010450b40c02004000d01035406207100110400c900003501c0a40c6503651506820759601702c508582c1c8840000801c601c415452190a4110a1a0003424100b40b10404003950360400a041552809140c5915004891284011401034040d44c00b000b086030400c200119010b810990758a803040910f200081086c1c10a402628482c070901081c41212610343e149070190802d070040242d070400c005802c3c41c03280c03a031900481c07400300c2d119074 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 520349991 1250 520348741 520348771
    0xe010603052b120911130902120714042a0e01080f070c0b0901020d060602010207021c08030121210e030d0210020d0603050f0303010e060402210403090905 68
    0x24440c82d8041d003000c0000c40c203200360a00c100c0200da9200441680c440390740100014084005e04121040000c1802110f600140b240b0051ba914266500908419842039610a220700f480060960302d0380c1e0f45000350074419400034040070342840e20f500018020404442807040c4400303040071022020f031407011740d0303030120754214002310407541d02842e6a80c1c4560040d5621840d41040c00e00102502c1d100c0c0b6001c0d06064902d404250080c901790304a80110012040420440707580e080d019000c0e42159070280e200c2c0134036011007104409000300f2465509d03840b1040d0761840c1e007008040b54143d6241030125030350f0398003469207900180390040342401101d90302d412040300321542d130002000d20140c240980d009070040c48a0011082c2c001440c0701400c0d400d24405038440611640f01401812107910180c134a10401d003038000100c03000320045060364030500c05821265100f0041c40300742d03c035000c00c0d1510044a4214607100001032640c05070080d20900d44501c529503140f507000242c550030748084040c81162 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 520351241 1250 520349991 520350013
    0x31e050709080601050105030105010c11030f2a030601240903150b030f12030a2013060206010b13050409061e06081b0f06090a0f06020606180603100b040e01060305 72
    0x1002104d005100929040707156605000008285d40c10f82d28000307010814481c1000e180e640c00b4001c0050030b004482c1110322034011000304404407450681c9400141c0340c1c1d11001c0619090103c2c4003416141c080c6450a4001d00c21031076020403802c070710324400400c80c24010204c006843c00704045083c030000c1c1000301c0c8002c0607404040c01e2080d100360600440d4001050f1200181a03082600e502c04401c04001441d60310761005041e480702800d00c400f05091000680503140c40032a00300790250380065086600076038a13200c69051610070407440710481c1800f14410455464507400c0109814440c04010408800807840d1003003030107800300c204610540b1800244404c050230410851201c0c01440202e841d81d0400000c5210311f82c500b010039000384000100f58200d500e070382e0070500c018030b0008500c0001e142d032084001c1d252001661028803940d5400c81c000c3c1100e0000702024015a0f0040c00f41040d40d0048030590000d01030b00c1d11058000d910354140115840b03080c4103940040d4003d41c050103040d044 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 520352491 1250 520351241 520351243
    0x2010804081923180f061c050a1803021b011223060f0a05090a090f0f0c0501110c12190c03060e01020a050a050309190f0b010b0a0f031e05070908 64
    0xb21001d103c01c2c1d8080c010812107a01011001c1000c4034140e800c148040110b00c0440d100d80304945000421030a50843c07140e9030041c941c811071041e125a00104003519160b22a6403030036012070382c05001648004e0f4800c1c00405e17500115103100b40141000c145500d4802c2d40c01d0161213040991006810496411800c0c1d0600c1011090b407014040340d41e21420903052002070181e4545004032402402100c0010b80380b5040c071350140c0500c50b00405105140615880d0010008262070001c84000c80c0001002955500510781c140c01c02d0584005000c0155440050092500c03451541084d5842070441d203d00e02a10104e0712041c20b80035040001d2003c1c150708050302135440c00421480e191b031040006007603c5502c6002e4800d191001c0c90300682e0707500c41c06242c62403c403d203141241490f0b26417490000b00300c45940c4455019119441c2c140f010b03030744c0302c41c81ca6107030040407078010104003115102d000e4070341300354020760522103407a0207892980d590307040072011501c04454100100f03c00c28802e000c6204 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 520353741 1250 520352491 520352537
    0x180905010b06190813020405040803090c090f130510020406020d02120a09060c030c1703061e0f0d0c1a0405030f07030807080c1c0305100e090604020108040819 70
    0x1041c0da82c0351400d0100e101e8100040041c007884802c00480704d01041e4055500000e580103c1c1e0003c10034030550805041802c0710380d00c00d41d54568144100503c0c12400d040041100c1e11882280c40103161a40c0c40d020111040200034500f2102802042c5e8800c0012056201402c040d01055005028442541d00040e180081040301515047d01c24070140301d4070b81d03100d0034507019504e4a10300106000710070300d815100041d02a0004003032291400000b5400c00b029405180300c6e03003040741d900c6002180c040c0980c610b44d4a5410180c2c100c0542c41c002c800505141d04120320300c0303110740f032003d0485654040c071203086002c6100c40c0520b0000000c1c100150f01d400c02c207500700104190084c204041c03542ea1100000c0c401d0010043c50514082840782c85440107200103418100c2094040411589100c0c0040c010203084612851582d510840032800c0040001e1a510911411004003040d03144c0b40c00559480b0801402182c40110402c80202005000302551801800c0382e02c4440441c0c06082462050320 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 520354991 1250 520353741 520353761
    0x1120f020d0e03040531021303050d03020307261501020a0b0f0f090f03190e0402130501080c0f0d05270d020d0e0913080c12030402040e0304060f08060a18090501 71
    0x1d02c6d2040400c0365a0b40213a460b0011040310840181c1e190500181c102030b0518651000d032050141c3e03a0041c108681580096204208540d1034500001e004001f494600f0003603d020388181203c000052040003c040c105192250140102c40202c110780e5504000c62008640392106a8004400c1c0444411211046500009408081d00d0075485100340c4039504d00a0119610310360a1070341001e10500e001d0315001f002d5541c050825596400020354a44188400b880707164009030a080019a1820750641950000703000c12012034603181086032880060040a8611460201a41085654840214568904480804060503a041d0014000303801d06166440c04418018100040c00c207680e510105254002c002d0402c01c5204a011708028205008007203045119104654609080f200510042c41c4100d01c01c0b20140202070501038070035124081c0d80300765404150050559001e0500a08805912500140801c161580c0c2d07105c030300cac6506981508440300d50340c0cac03011450140042801018030b00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 520356241 1250 520354991 520355029
    0x12a06022502010c1205070c090b13021303020d060b0301050124020d090303230a020f01060510051611031903030f09030806060f0f070302070e090c01120f020d0e030405 74
    0xc03014070b80000e0103a44c18104010194014015041e800c54080e10544040d0390304800000131507074455441c03100500b80d14480e41c0c1301c1e1104000d184d04007021030007154200c6a4080c0a40d009514560034420000d0850a00301c64403a140c406d00c1036651000d1291600030081038000e600c0700021152070745042c0c910910072038210340028006500540d00600740300d04603940f500d011805040141d440041c180750307420920381c400100046406020740d0005407590850f841c2802004482e03500c5040000740014007041d0741c040b40c01400000c5001c1d2903180341c062031502440d02c01d40480e8400700000c1c14058135148000350340700300d6052035050640c907116417a011241851708010149142e03d02130422440188141d102c0c0900041840004901001340c49126050703076151500c444451602a403680e126000345180e130503440d0005820120f000550074041c2030103840d060802e800b0a40c1c0140642204000301006c2a001c01c0322061500851140c100380c0105036010b11340395814101008141c00d0034110031125 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 520357491 1250 520356241 520356307
    0x5040210050304050a02060c010b0301060906081212220501060e0f0a090b1909230f03040b0304061a100c021201060b090405040219090501030b01060906020c012a0602 73
    0x611300140c0c411041e40c04440c0300f03484d1003001a01c0d9000d0005c4c2d007a42078055080400c0007038800e5590b0041016608581c013502c0c0c40c903500c50b442c55628080c1d000c42109440011010410600b03088802e0400c82c1e0449901d08208a0036480da40e09451155120207404c88044040000b2019505525030700605100c20504c81c000460311040c84c2c02d00050107076400140b94148440c1e000c0c09980c0040101c1ea07020300420307040030700003201250101010031041c0d80ba001d1860000c41c0e400e404000c0710140e51400b20803e0941e03d0300d403078410080100c1c01c00e1080b0448007042c481e8495603211080e5014604940c6c1c0c544074828140b040c00f10f40e001c070b8610400268107001d0240a00111901590001d00040d100050980e442c0e0000400780354030450200d1020301003900100c0d21810701e400c082e041c1d80c000d150610756a40e03210002c8543c0c1c08688919001078000b450035035002c0d8403070300500a25000009a0120701c500c4c00000c0050801c14010880b032903640080c440a022030392140180c0118000102c400c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 520358741 1250 520357491 520357493
    0xc030b0717060f010c111c0f0213050f0112240207050d081012080405090702100c0c0c0608092d01060b0406080c0c010929060d0c150306031505040210050304 69
    0x1c401c0c001c0e640d0040c9600c08001c0071b04e14a07101c1c060348895074005945c00810420103070629400000f07428400342d000f2480ba0351203c0c100703a001e000307040c041e561842c40c44c8002da103061400080010750040498551107261f41e4a00c030082d05541e41540c0081c180d800603916603851402c1481e2107011192003041c03000750b00402081862003004502212104402070b500e039209480d054034144a160000e50344070713002206000300107500043d5140c03204083e4604121403e956442600d14a05c04c010041c40010803e83c1800b80c01c2c03240b601d00f07800044207400c60380740a00d60031036400c07107500e500d05010b140d07000c08404c058071140c00d000c3c0d24001c00c04800340c1c1c2c5c40c103800c01c42e0062240034024020710707030310300009503100c1103d6003540070080f00c580014041154040460440f200c104228200d0f9603011010740116000b480c0042003125400c3d440386108200515003048a414600f14900c20000e040d510394000000c034030700c0c4001e95140e034100c503400203e1389032506c10001c100e03001c144403004200007402044 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 520359991 1250 520358741 520358747
    0x70f0201111902010f1107031b0f110f2e0e0d06091406070302030f25120e07030b0405010c05040810090204060506180a05030d08010e040c030b0717060f01 68
    0x15070102c000340b101c6800c0492080007a805041c10811080d045482d2600c1900c20058803009820b00911a946505003d600610a0040c4240000029014001c000102b0000070b50600050000c00e00c080c00c1c407540740070884001402280e0b251940954060441000003515100d5001e58550384640e00f40081500f049002007520b40043c04401095290b69842a0061011001e00380d40d2996048044030202d182104009000c0d401c06c3e12211640600d24011038000f0000d5908501d50555140d964005980c449504843c459605981940720719524401904011403c3c4100c50285009006d0001c0604040c41e0141c02c40d0118034450b020000c0501090050341303004074108d00e0700c01d46c09034081980303602c034000100248450380c0919031059000030740e40c101c2c0c41988a02c42040ca0222041d011480e03442c001c0c10b0304d41c130f20211440000b030060300060140c0110442c1c07040d0428011450303c21119100e55850b8072400303080d2132080204141d071000e1000c081006010750b522910540310f0420a0450030700103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 520361241 1250 520359991 520359997
    0x1903090314030c0607051324080c0405031b031506090f0c0d02040603091103060c0702150405060a120b15040e090a05070b0d0f1a060f1201060305070f020111 69
    0x3000d00e0075030082440640720410a0350202c02c162003d95840b42400d081c003801541c4101860540b00400c95400901d000d01e00301031a040c4804403006a03025100c030721048440140003405c00500074003d00c0f000c00d80c2d4030108143e0030008010206184581044020149001207c1500c0405500a0020000d051b1280001e487c1c12a0180800004a40304c2c40d9100119001c0c0142d21a0b2561001c5400174000c2d900d034200e40d0903d07004089000303941c0041020f05032200412038a900162004100010050070701842d20828030201140040c01e00341c96a002410b41c0e4008610040056080010147e248007280301e172040c0144100c41c00810342d01003840205090145101d0702c06540300c8480080d0000500348162140c2c240d200c000e8036407041d20350181d2280c175041040941001407806102107040c42ca01d10540080350040582e0545800d0300354100001035002c4030070200c844000b4031091610201440995000e0945c1d501c0104061404480090244000c0301d83d0302d045a05006080c0c0c1410b04103011 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 520362491 1250 520361241 520361243
    0x8040f090f050c09100210050c04030201030c020f280c0f150c05060406020a030914010203090f030c0c090c1b0318030a0b1b1b160f06050d0510080f07060219030903 72
    0x441741d00c2201140d000e9041500c500107400002c2c0c10001000881200c80c0700900949100740c8040242400d58501240e54461079503050a5a44c0801400390002d100d006440e010104041d1030401483c8895440c0702d0580c1c02944402d0700c40c40b0b10001800a00503090100034410b20b0791a21941c0c1c00c803252215a40c9101c054806051701741e00051010307061340303c0d40009601765002113504c0010710b230106926000f07500894000100c0d0091149114128501008036a10024540c00506223056a40200490170902070a4901d01010411040030186221240d85220ba426180510344440540d50120000b440100383da42c0b1035004401140c0000e0040c1a50710b400840741110108101001e002c8185548a42c42e00105120082409403001480001d20300f07002d41d03d2048034040540d56000768203903d003034902603803020031014060265040001d40c0b06983c0041c20800304a80c155480f24443e040c10004174071003049821001e814804240c04000680c030007c1840e9440c01809855100148000080e000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 520363741 1250 520362491 520362499
    0x2120a0503150604230a090b03030d0c1704030c0519020d1209170303061503040c1401020a0c08010e0d0912020d020f061209060106090321090308040f090f050c09 71
    0x9040b80361600c4050907503001e44281240070801100350048409915503441c1001d00c140c29404d000b0070514628096a89800c5000e40194280074004c080038001d081104029010041c807001c0323002d0300080451000e0b00a40c0a52100309514001c2e081050801c081102e075051030b48240000e010050b1901c0d03014111081e00f051010b4101e9100c05001c031107202e400ea00c10950305900f0b0740322081141c0040021402050304440203050074030b942c4503084d560b000468002c0c0444100c0241080030707050301411a00d2580c814070644505080304d640b00d0102040540101f60035a56031224007400e8002004041e001e0407181c1800c01e005882c10710200592a40c65a00038090301c10389190000310346a00d03031103144c9140020400c40c1c4803065405024160841110001803502c50301c000058450b00a40701740d000d60703400030300c03a24629100d0b100d15904c0d1650481d8413020400e03a01c0b03000020034001e80c0900040c1c0420b07070400c0141c6181518070000d403841c400724100d10300d01d084280900f180f640c0f0102e440e0480c06503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 520364991 1250 520363741 520363771
    0xe060112020c0c10031a090f06010c050c100f03050a110a0e01020c0604170706050a020a031d0a0f0f0506271c050706201209061e070302120a0503 64
    0x20b012820010481207803908405484081c41e600c07074140e00b200350441c0324980508001003c101c10000541401d807102d04c01c41d04200d0201d10f165200c0c0c0f400e2044103014000312001e40c001600444c804100040315480090a100b100c90105507050003030a030400200d00c0c040c0202510f05003194440c1c81154002e200748126042c400d038030b690007400340c00242d01c401000f66464070350b40e5000c030900b03413010854413045000d0803c0c0030401d1806803069541c6000310b5401420000c4085c2e80580d40101d03900448080c4075150381400d003950350391140e220082c00075611040b0000e4078181070111400055044903101c0c40062002240002c0100440310040000c504806c0c05052034401250b4010380860782c211010180004250910900281c0f800840e0015074078101507219000c28020b11012003126040c498020901801c0b48000f24005407510500003004035241190404000041d165001c5440c13002000c0820014203141d0103210001840081480d103615102d6542c100420354840144034145c40e58500c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 520366241 1250 520364991 520365007
    0x2010b0102060c0a110307050c011e0504050402070807020d0f060e0a0203060a18050a0819032c010f060905090c1801060c0812190509010b0307030303050402031c05130e06011202 78
    0x600e41143c4001542ca01b0380b0340e2007219013080f039111315010b0000b50216030380300714224442117140d400020350740190703a40b14140f509110410010398003101d410380c0e09400030701c15000075039107003c1c0030141c0621039152540d8040e5185084819100724484075107144d00000b12171710150b100454580d500004182c800074040c80c0e0b01c14281205210000d0203401480b400501d0410814a480244010038170840c821511141c1c0300760480c2030341d01c40010b06482004280364400c0c1d03405480740c0c1e4500da0300c04c00300100d00012040c9524086a14507449811683d03251005e0240c0d070641489405d000a4084e524040c0380c030348041c3e0400201006209081c02c06c0aa02180000d100c01c50003518085081000c5540c03083c100711055402c6482703080440c0524a04d08008a80e448d41c05114600c856480179024100052960314158020400100184e8043c01606145203481002200c00701040540c0c0c2c8540c1c0d11104454440020007040703400c000d102d0080e00040c401aa03070042820030041d9500c0c10090703039440e98 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 520367491 1250 520366241 520366247
    0x90f0b0a170c0607020d120203030a0b0d0c060e0307091b080109020c03030f0702030d1103090c010903150c1e1713031d030a0c15030e0601030b070c24020304020103050702010b0102060c0a 82
    0x10050150042481f030590510700fa9002c401035015000d20b100900c001d02240d010400b032402c001000400d41c2c0e841080c108425401808006880e07400281034079580c40c0d5417210002a180740c02e0f000609800400400039186800a01c07039405015880c50442c20a181c80c04410343d6840081c0c4448400c000000000706407174800c104441d50010719400c01e00030040000c00c40f040d150425160a40d550080042003d0154480d581c03010032280c100200300401c052450224008001d03a00d0404104018020488400c003230442c81c02d000f02038181e440105041c40c45001d0983c0800240914081028031200d450200740d00c59580300c81001d003c81e180030107001c4440000d1400000d02e1008111303040d103280008500c3c224482c1804003e1903134a052000008000c280382c0c841c103003400002d0030340000d000840c1d08148119a0403080ea03210361a02440360562004007030250746080d1008101c10340002c1004215680350140b242c0102a500090103040300410000c1d44030040101a40c842035404502054050300c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 520368741 1250 520367491 520367509
    0x4050d02091312031406010e0d080306030106051f030b01080c0304120e18190e1213050603010e04020f060304120c08090d260316050c07090f0b0a170c060702 69
    0x41d02181200c40140089030103801385c40c45585c40c2e03002802000c0082e84039401020003150080b0003d00c0011081181d9488900c2c03500007074010344d0035640e00c02d404603041d118500c0c83d001600444004032001d001c000e100505644035100020f04004100007441141440c01c01626001944101000c01309550f1050481c0c9800480307110542c00b410b121443c00e6050f40c503058407406451903460f01402c810a1008a5060701d40c0308101f210710394400803005207180004000b1700654001d00409c101440d50341c1c000204030790800c0e0000c00c085800380007800118a401c40b100c8c10b400000340c03102411454151642c800c4040300f05204402d111506074100f04004904088850480c00106403414076071241c00e200c003020700d00003500322028444050a05403d9030010a4904c06c4420f548030b018850f45100b030440e02d5410488103420a442000004500401d150181c0b1011603102c00c00001d040040d40c00b003015990b100d50014035500008250f4268581c0c010900c184091002d07a4001c6d9907101d14400b00710642 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 520369991 1250 520368741 520368743
    0x30d12090c030f05101a2e1e0207050906040c030e071202120f0d1209060501120218010506090114070c080618010606020606121903091a04050d020913 66
    0x4829034202000b00721030b501d010420380e1300900454080c0e102008a860443e040091303482c207060205181c14056150003c1100340481c0250803000000480702030b5a1412038850480402051625800683e40b021520400c4400c000c54401050f2041c40d1202154807090003a1405024070f480e00c01c40910705010750891043c0e06040411500b080d0784e1850010700b02108100200d21500c2c0c6180008143e0000050303900030f040d0380c40c2c0640740c03a92840809070f80d240130114500304801d4880107010301245840c0308240c001d0094001004070052244100304d0a0b0b1060340c01d65145185d601e005100c0c40c1c68071401d45007415030a00b4001c0c0212140c01d007141090082900c010b2580106030000b292808012803000c0c06521007881a81c44035225005280c02e965880c091036005921070720004030740b40f511035152b2014a81031001c1d5100b000d040d20151b1601d000065094010a031310a0080101980170b284100401045503400350500b03080070005201116031204c0a4032440800000c1060902144c0c2d1243c821703 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 520371241 1250 520369991 520370003
    0x15011a250b09070603061a1b07060f0807051201050405060f060f04053606011205090d09090c091401050405060d0609050105010c02031f11041e0b0702030d1209 70
    0x540c500e00c1c01c4101c2a1040703a415080f4050500700041150080c001e0a05503030220b160350020321900000e201c49030b0030400340d0902074201e10b082101c45800a001480140ca52070359880964040c28074064009c00300500981e041003020001d0400a1402d26000e50541d50704071000300e0345845210008013181c840d00c101c16407250b400243c15028101d80300050003219401e8403040d242d040c0b44021043d4030703e000c0007440380030301d00c84038081c1d143c2022807021035200701c05040c44440c0c0000c01d80154211081102c0010150340300000c800c2c103458005408000402c01640180f0090004c1c07100241808a244110300b50b860001203450341580c05a000e59025000c0600410313224884809180c014240511030f6500c400c2c40d280020819512403c912440e0a40140040030200003d07180e00140520b0220f0100c401680c41490011740b00564000300b00401c0c241c0000d14900c1048000d800307101c00380350711001055504005983c01a1400b0550400c034071042d003420040402030b0701ea01d1000e800703d100002e00c2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 520372491 1250 520371241 520371307
    0x80c1905091207050a050102011b050702010504030b0c09031605010c030813080324010302030601080402190503121b0c030703080a1b080a11160510030e030c03030915011a 75
    0x30207580007843d201124001c95041141780e56504c0160f003215198060480c1000303000e07011620441c020401448054030614046152542d41d40315400c42c094250b0f44500d05040004c1c0080c803d140400500c107601d103801507041304003071400c0000f0300380e0008480018244400c00780000e4086030040000300105800c00601d50ba40d25148490140e41d16403801c0d00051245400c2210070103510a1007524461101a142c20189031599002c100b5400322841d44011031040c810310102c1c00b61820b01c00d17580c400780b01498a5458230b0714144a00001185242100565800a00007004a5800243c01c800b100d0304211a55900d0f041c03c0c00403559403014540c0203030194054107a55003084034000041209003203070380e11500484883c3c2046516000803070180702da40300d014441848145402068006c2445207803c000508094284505045400640309580d95400110400441100610074100d8980c1203407003100709581484810b0800307102114409006000c0480d070b807203600e41000000c41524032130080f8588 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 520373741 1250 520372491 520372519
    0xa020307060221030c0406050304061503110111060c04030f0c0e01081c02060907170a020924090c03070c06110c060a06080a050307080f040509090f0d080c190509 71
    0xb503140603000d541c40c8461072003d1056002000b08050303a0217114444105803610740350450454540d0000350054420035070710f880c2c1ca41c03040c02001c11140190300c94905442c0600a00c0d002400000340a00c00c0a03481d04003904210705025484111019260b1150114101d10541c2c2401015a001138000380944450300c80003190180b800601c02e100e8240100704a440240300c1c0204903101c94054031080302a5028020034401d1040826880507200e44250844008004036000212032187c243d520807510703012090311800500c9400c899a21405c130507076042c09241024030104449200007403847c800c00c0090301c442410401c1c00e0b00607a803240d94200010b41c89032144180107481d0101900c00c1d000051400e5070000d0081c50109a00b014184c1180141d4100100786c0c40d42d0030f450f0701000207822480d000700008112a941c041c003960040340c40e0f100912044181003002480d24440e2414003061004200030801104046021a03181c9014246690b42c0c5194803841601d0301d010ba0031000398046000f40d90a0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 520374991 1250 520373741 520373743
    0x1103070801200711010e03031306050309120301080a030c0c050d0b070e0a0b040303140f03010303090306050703150302190b0f0703021b030307140a080403150534020a0203070602 78
    0x11842c035109200b5041c0541031085051118421410003d0010120150f098160340c060b200b859015040582035078a40b0305000314040c11f5040c1c42d00440013290700030080c0038009038100202c181400f0182081d80c959414200f140d030f59200040c500600700300c60400380c1d030200080700c0001801003070b000c1c228400000040c6060742204504a41d43c9000810040d031900481c03401c142410300300d5805600d174a02c0c10741503460440d40461000417031269843c04214011404e804a801503009502984da42c51180d419072420406550340984002d00701170508003202606410340701d0502c105c07a41201c80c8a840030700c1829a0a075442507a1240e0408540419040da000000300b000300142c511a5081d1807001c00582c40842d10b8031084121a03425500c01d0110b403001a00b00300340b040784080c1c99001c07941060030f42e658445050b4440d0b0001c03180c40a0070b030001135042070300d03002e8143c20203086088800303000d480314a2140003004410304240b0b0303250741c21100071800e80280181038283c0d030040c00355550980c0323411010b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 520376241 1250 520374991 520375001
    0x30c07060510050a050f0a120b07140f0d230403180b03160e1c05010615020c010e09100e0a06060f050307050403020f01050c01020309160f060207121103070801 70
    0x1a103549042200042216210010580984000400c0f241c541821700043c0f2490301e40541c9003a0b00802c8801d808540340c0301061200d06500d1003001605050310b0004070060210251219605680030103000c8243d980d69544142e0302c0890701e24000048004a19841814105001200510010240c0240000c3c5580000341046032403500c3c06400c11240d5079000f010151200706c46080380c400104560240141c4502031740d07005d451008040e64000300c0d080e00c3c00c0740c8092900d10115080c1e91f4428082010620200c0740034400081c40c000781000860100000c1e14080b60b00d22100d11079020342c00011100d40441c58404007030060160721182e1403400b210010028003481c010000421400036015100511034400c0ba07115124650700e6505051031030b4240810b8600c501d00c014180002031049003501d0600f440550302c603100c1071004000356a914440c0803110301403500001c3c1e0507402400144145030f0000783e448104c0340303078a0b043c030f03007160003400c041c040082c0220040b58140175100d00040c00f00815080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 520377491 1250 520376241 520376243
    0x607080423031e07090504021809011e0e0d0f021908120a090f06020d0b090a020a031d070b0309010603060c02030d05071d060c0a0615030b1317070305040803030c07 72
    0x3103885104090a480c0c1d070f8003107040d07281a6240e005072001c5c0049806508a56006440641708001411100c41d9800d02a5011103213540790f40e41d9a651152004485002e1404010000340100b00d181c4d01c43c4802a100d0841205203820311018070b00002d4440d200b0060458660850700030250f040845103082626603000803035103604549600d000c2802034100d031181c42c0501d588002c00078051110343d9200d80281d0014081075a0a6542d4170240207a0344070740f0011440741c1d078400310060b40d0310644a0058205c5148900140700c8200a81801901140000b1160240c44009258a0300d0b640c81c0d0091901501140e000240b029080403600c25405030008050610b00302059001c0c040c41c0c0c0d410a04641c040060301088201c528041480303411030820790018a0440c2101c2c054800200780d036118a13054480300642c40094401c030300002c005000078061000e40118104001c403d40c0001c58640d404410903042441515000c00246042014014030442c0e0040c01070b20305681c0c82e4031340000302d40203540000e80 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 520378741 1250 520377491 520377493
    0x606091703121b070b010609030b0a06062705060408030a02120f04031e0615081902030703290a0606030506060a080a0f0f140601020c1806060708042303 67
    0x1003618900ca40401030701c07440c40c0ea60070605007542c0d56800c80304030202041d820340415081000000082124041c209000c0d00e555142c04c1450392035868502c1881c0c00080440c0f4003030f450002c00344511544941c070303d4902034403081070088950b840d01c0c1c08c0140c2c910310740c0700d594824400100040d40140120291440d40304d5078095410300c00c012500d13001c5910032201d0700740d12042c013000180b0000701619021000d4201e02154035280348115a5460300b00c030800c2503500310a80d500001001140d2041007158fc03106010f80c510702ca898003030b034003080e65a00180401001c5008000942960308410b00218000402044088070a41404c692040c0141150301503040040d050200044490030030304121150020030390b4800d813055883c0b8010074000c2800304480701c0301a44814110b0060345907401804900b468415011005080980c000b925008581a1450144840079010700301440c102c1041940103d0a840080d130320825450aaa480c0c89240c01c00003c0500c0e0b00700c2032545007890050080d005409034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 520379991 1250 520378741 520378769
    0x6190315030c050d030e0415030605010501020d05030f060d0503070807110a0b071101020c103203070e0414040506070e04050c04091104030f0b10050406050a0b070c09060609 76
    0x40c50080d82420603000c00b40c03102e01901c400b0841820b00081044031a40640f8119280304026400a004c0c1c0d082c0e0282429001c40c0c0c18010301c140305891145600401c000d00050418003490500038106002c000c020f280d032001c40c1c0000880d25102c41d120b041c04543e00000f503030703a0740c211803400414980090398241ca0721042d8243d42442c0f4142840800242c070700204015041c82c074150b42d9a03102c207088411f41c6045000d07560002c034031901e50707885c7e03080c900c4240c0d2980a602205c0750000003031040030380941046042542640860010390344222600000c4501d800e40251000401040180c0503090101034a0300300301c0304000601001040b070364019034175555030002c816504010003050350f01c151405640b98104100400c85030360b0079406089400102000907061a56a85501e6a81d0400b644250b50b54050b020401030400b203032124100c0074020440d410031403141014042a004030050141c0442c048000030104144405000f0144c001e004041c4180312541d04c03400d00400782000c0d44074000c0020020 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 520381241 1250 520379991 520380011
    0x6030512120a050c030a0911030304080102071e02010c1202010b060f040608150a261c02071203080c07031b0302030415030504050616053604051b0d0209061903 70
    0x140160f5028044580545007980c95144207900246100e01d0212610100c4600408042c0ca040c006800100030308000181c41362154107040144580c0543c43c81011540e00c4503030380042c0e81100e104128180c01000511802845900a074014940d10400c80e034030000201c0d1010303007804002d0081c8280e940b10340c2c907450113482d124686a2980c1c400300035103612901101045c82011740280c0400811001801a035401c6609004424100034048102141c480c071a4030a03900807079010000540141640c0c04806411011910004c10501003e003408070b00c0e43d400500d55052510800d0110f00034003052001458041991501039660b070b10901c510b0140d21185029a50540c0c06817081138800c90b00000a4861a80c0329032408a81a49900100c2c003404401d0085010602c44d480c03003100c52221141b2f0640c07200e151150a207454884107403483e032007181400c1c00c10403d1040b082c1001d85035042108966215800c0702141d1000c2c0c01210000741d006040442c40c3c2c880c410b08036048082d2440c9549040050321a5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 520382491 1250 520381241 520381261
    0xc0f030818030d0c12051b0601030203060708070807080a021903090308100b031801090f0b01030c0b25050f0a0609060b0d030503011e170c13020415120603051212 71
    0x80701c0140c00121350304101190100300704e03a6500307885070b445280041c80d1882c0e6a00039203a0140d0190208400d5000f080103200314101042440d40081c2c8034100b05502e481c1c0004000c003c2000100080d04125128010600d40c0111741c050300c80401c60384031444a480b400326002801006181c03c16030001c1d0001c1c0104010001c4000e42070103481040310007034070b980d5a440c4007440c039000040002d06959a108001b45c0495111242950b0452042094031465455410500c15801d5150086010341d84200420011000007104451001200d4a40240010100e0600d54207244000303420020f0750162a90309410065980d000400e003903c640780030401258000140a402e9200070710081c042202000113000c04402114240b04103d08852420152500c2d012a0032041501c08102e182035444100b154085191003100d400b203080301038101314101032030401c0104a41c01d5110400e800d100c9005020b4860202c81d82008003d160880c04840c03036200d600b4903000c81d5a00506803440070440d60b10100e403039016 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 520383741 1250 520382491 520382503
    0x102f0c01051614030603070906121103010510050d0201090305030a03020d050a0902060702150415090302010305060909061801091403040f080d0f05090f1806030c040e060703090c0f03081803 83
    0xc2c0350b0f942c02c3c01c0e581c07016002c1407480e40042d103103a0340762281c0c0d1000641c4c0c410600910019010081c1e0300d111881c0300e480c2c0302e00d07000c0145540d1403280c0d04220801280e050988455002c40740c0448850110140500060b5003904164102510324040010050346c880c0e05074004210b0359407042010006030303680356100b03411666420300095101100704083c1c2c0c05071801c11007560410381c4010307182d45400c1e0303150074256200e0720388001c01c0049500220f081040d507030180f007400d5100074107460765400d6142c0074420390749615008046031348804600f2414106e0107001d520a410250344465581140d00c1400b407641da0301c2d00030b4440c0d440202590100840d00510108001c070805009480d601400c000040d002d0710103420a00596801420000e40c0c00083ea803044440c0c001c8a035502004111414820245410405007081d100c0c059400d1510351050048000345480e80310b68980b600103416136141c50035400240c0603a00029070000b040202005100740c0d040100301a120300110000e0001c0c41c4010715450345 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 520384991 1250 520383741 520383781
    0x181f080a03050a0203040f030516090b15160c0f0f0f08030a1b0b0a0c0809030408120c07030f03181a090f060904020703030605100908102f0c0105 64
    0x900308052200020b4001e5025000c8071100340180c2c1d06182c2c9600075010810815402603075140d21241407000c000c40e040c54641e0280008c0c610902203e40301e540071038440c0e80039000000075440c0c005880c0c141c4070004002ca082c01d40e03004005081c1c50f40c0c0c4030401a2010141c0c040d50210041440c0009040c3d0001101c0004840900002e98205490030130140c80b003840c0a0404102002c82c0400c0707200040401080301e109180718980003075420000c0070000c1000c680100140c0e000d42c020002031142c48000100c120300004a203200c40c0e603546108001600386010b41c1e100603c0c140c4883c40100800d038020100c40144001080d2480c4160f03520b202036140441545440b86c0794180801006e4201c2c1000f100706590410060300e21450040c28101040032680009400c0d00040c0d50780c10248802e20f040341c1030607a01241403600700d07400b03801d04110b95100e00178044110710307555070f41e05601c2040704000c0740c020b02945050201e400c040c2042d48209010350244480645652030a1300050100302085034901110f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 520386241 1250 520384991 520384993
    0x40b010201090f0605040206070803160908161e0f0e071103090a0608060d0510150504021e1803071508070c05060601050f16030c050d08070509130b181f08 68
    0x155455144c1a0040c1000f41c0140d0308030f0002c1103a000403c10340402140142c003000850050705030440002018850950006a640d404c111107140c10020000030f4041913034681000c6c07503400507411209030b003441d4290348071510410680500280580c18421401d01c907408984501c0f001031414516642c03244103c50a00b580488414000d0010382d1203000031b00e502c4240900700b401214542c0e2200da240143c000006c4860070303240d10810b0740208940c14041c0090409813025401c2c00e0b00f1000200d02410300948101e00742e9400706101c60810350b0f5155134108040058240c1d01029107410300c03011f413880a070b14007001162a044c085058a072050b05003050194005d4084c24807a221714004460f03543c02101d1041e007641c010300449000a0100c50181120741c82520380341e052003a546807a60821001110a0052012041c03c00c425582c0000482d85045412600d608407130303030008050b400511000e1449500005e00c0d1201c0b0780c01035030507107600e4013514002040c5a12050703e0750780e00d071000c805801a050a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 520387491 1250 520386241 520386263
    0x140705270a02161406060a0e09060c07080f07080403021e09061507061b08010f0609050f120d0804170c1c0e13060311060a0507150b0a14040b01020109 66
    0x41501e030398040e10050704024001110300071551585210b10403420503006854120500b4017082e0316014071040003c200c02520348199141480740d19403188401013810441d0312001400c1d01c204000b050441d0a2001407518943d200d10b140e09100589170401e0004038000c6404c10490340003094a0702d0301000c411001000300e2807179a1002c050140c41220380ca4204e241d00700c14051107000508502030620f40c00100c1035420064903d00d0002480c03980c06070303c0340101211071042806255402210704064400507102110301d4a0410007080f0f01046840300d003411405050313510022150b20001d02c41c02540910740c11445005801c0301d203112440340408011003030f480101050040188034503002c02d012a241030a10402d80c4c2c12000c504a5008000c0303d4030395a0381d940c01403040001d1a04200c1040c0382c10389005003003e200d42c0c4003508512546001422101c1d000d8181001001e0503000b8803001c00001d040890030640d41d940390718000d8180c02c0c007144240c0c00c0c0004210b65510502c1444c904d40c1c0c1007004801 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 520388741 1250 520387491 520387501
    0x1d03030d0b0609100c0210030c080f0705040b04080a020a051002030702010e150703170f04030c15110a0e12060c0313060615080f0708040c1503020714070527 69
    0x100140100c0d42d412000502c02481030342c1da410b00006081209880c0c000010340c540c03041154080c08201098103043c60a41002c142a83c01603103690f020511104102c0c543d1600d0a00381ca881c0102d900c00106130310002030110f44030002064000045109545089000d9251002c014500001040441c01a8401d00080700590311401c03905030006809400c282d0341c0700d401c100310300c030303c0e4458001a0f01207a007074054808810358aa045590028000800c001d0310700301603a008084000301c15001d0140c5409400f44140059942d0103003483e0508005c4041d0b40c0d01c1044030103070851210300813061040c0e90342c5460a02d0030b40003140e42031141581b40580c1e0318565580c0800b4001e82c2d04040140c898a07620300010608040c0075603082e4010700c0c10344030003005107008a0841503100c1c005020004000d83c0800303000000d4900e0405800341c4030307054102242403401103411002402a21005080c401d1214100c007841440070a1640070ba0b8000e5030072039070040302d0810608072146011402d07c410740ba180c00081e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 520389991 1250 520388741 520388767
    0x9150f1e05040f270e06070c0311060423060c19050418090c0501020c01020606400b0d110405041e0605060108182109030a05010c1d0303 60
    0x444030400c18103100b400e150311984210700126198100444a12010303094070f1300e44c03001818100701940c00340e130244804802a00700d640c40c0d480250040c800e0000d000855005c0500800094082a040348100c4840f8a07060030206603950720122004003050000b030184c02000e4011500354451001c10b02400c0c84d0040d1100c100200044881c400c10420400380000b140031700c00328400750303014101080c0201e05c4035643d04000f0449176195200c48d06550180861000e20f036000728140e60300c880102c8070038059450320050809001c4015410640703800e0f100390700c4075002c90007008620940d0b00c02c170410000101d05074140f016185407448042c00100555a00408030b20341a00416070262049000d104520007207079808030202c403480f0003180d9149c1c94400f04520b43d60b0148a49a000c4004445c01c3c031340f50010001130740c4820340c03110052071010051100307803410542c001c11240d40030300103800c840e001c0707006007061402013241c148401d00046280c0340c0b82d05040b81c1251795a0001c030009004d10725182f5009078074 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 520391241 1250 520389991 520390037
    0x1b011803020102061b040f0e27060f1b0a050d0c080103050a0f0602041809030e01030c0903060902030309120a0c0b040b030a0e0c10020705090109051303080403050c030a09150f 77
    0x1d04108000700408074107007130185103d01c0100064410811241483c10351150010941034045509041c22200b5000d0140001380b2b150300035115040024075926912940d0714101646009415440400100b0310450b40c1c0c001d00618226146040410505002c1d1404551010080c4806842503002d50020b00200d420740c5c461800c0a07204650052501d60f40b814031100071040c200100190664170380c51041411380020f40d885030010700340307400c01618000f076034064107100c0a80006801e107036460030301c0411501c04004071a25641c0082100450044804a040d41c64030500800c4460034a2800b0006035001c5081c2505c0a543c84004000d04694482e0382c0480200071030780c0348503150b100f541c01d107080076200c100000c0740d01480381d405000320300c0c1031005008008030182e1205205a24010400c081c0d240d10000c109941949481c3c04041601c1d42c1c282100e89000c0c03180c4550a44c000096241200754201403110304868402040d40c42107444c081040d50214440110400800c600c1102d040c240650321601d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 520392491 1250 520391241 520391281
    0xc3012070903120509040f0e030a0516150207050f0a020607060e1f0c02150405070522050109021305121b1507080c162d081b01180302010206 62
    0x3158038002c1d626111044400010300718000403031000101030480c2d00705405900704000b624141841035031148802607940384910301d510700400101041c0482030300c00c0340900c4103005410414001100d0710000e1280b00950100700101e03514810000340340282403000c14920f4040e600140400d013401560740310100608002d511001032801140c500344402c0949030b03240903840a003048001506100280d010f4544100e005072005550300c050308200015000040040aa60701a03a0217003116403e00d410030002108810182c903030170f0400c07002107004a199400780034594600301d5415104c07a03a42c0244400c03803c0c41120f0304602c0c2c001e80000a40c1c400100070b00480b02401400444490189551511094100c5a030446071120002500006d010042115410a041c4845000100b07403a00f08007070040401d5011b50481511a83c0c1101703800c0d41c80030555401401200240c621100c07000031080101000d4a04a5010070264203c022520b030070030703500c1402d40f035068009210f69182e840c0c02c2c400111a00700 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 520393741 1250 520392491 520392497
    0x32b0e0a0306050a0c020c040b06070f141b180609060909030d0207030c050105010503061312032304030305010e060f09130210090f050d08040603050601090b0c301207 73
    0x6030001c00103a40780300b02845280e0303403040002c00e510100d50003402c000d584403025218a003080c0c0022a00d0f42d600b81100c901940c00000c00030800310324544421145070303030846102030740182c0303c04460046200c440409508000c88900d40c0d0281c1e182c0703000081450546586803c00e0062000911900b010308456801c0303845c0d0b0044a042c4054204000203a0f1711000f412800144a01040750400c902405140d014240403005480301c1c1c0382280703944002c5441081c0207000c1154280c0c080e60407d0084e442520002a02002038003511510300701103059903c240d500300d00007840c000c00022001d066198440c0030307501c020242452000b01c030082148680024002d04007242c0303651458030040c1e0304d003041250134407800c2c2c1f284070302e051812007040a4850780d540124000e0b0030078204000040c4940b0119410780d020303818009243d454420048800101940141e460841c00040100b180000000c00d15220200d41ca42462810014046180c9403032a01803e244421000d0055442c04034110300e20b01c0e801000b0345 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 520394991 1250 520393741 520393759
    0x60f050d021f0e04060902121306150608071716050c031b070305150408030a0e150a020d06050f0f04020f0f030c0d05090102090f010e01030608060a0b032b0e 69
    0x1c0e201a40c2c0b682d190010404102040c44503106401c180c06000020003021a0850910303040c50302c00d09642d40c0050001e407040c4029071030740080006a911620720005035945441d0180c0d01e0b510080d00b481401e403902c40218042e641000360602035222410f2207003142e140e00d540440c05090b001d4906801000c01a43e550100f4804015401c19185003804e6035000080281912841c50070644e04042c404c1000000e4503c0b03000400c40454841e1086a40200984d0000118000b00b0b2036400c0c104400e1050240d9400300e0b24092000c3e02c0303a1a000791200c4509450108405981c44040061880302c0548690700140c4103040b0f070407149003c2e07000d070600d07211b500d9009140100d00d03120399070642d008851000c020140400c8044001c0d20501c00c0d20b034040781d5140218503003481b40c40020858400000d0040c1000761210344e1045d582d11a400c8038009007d0030382121501c1c00c1c400c1040000e001044521402442042220a012070710101005c11101d030071318130f004090115000456442c1c2440700f00760340001c190 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 520396241 1250 520394991 520395019
    0x1407141b0a060209040506031603020f0612041a160c0813121a15180c0f040602070311031204090b030a021806040f020301080309010305060316170d03060f050d02 71
    0x74030008500c580b00e9100140d44500240c20070007103a070007904850003a80001c285a4002801c4a0580241c940407036a440a407403030400040d55621980e10240070507403c840900080210710403404c0d018036099020003000759506440031440c1c4101d55400030000c0c000d01d80200120307178048000c141107484165404070054a4a2030100b42c50210710341141c0d0090030403000280c060202c032100740c200003003040c41e200860b4200c00003a1207620b50841c510922403040082805840c0070320440c0c1118072034020043d119a41e030b9001070340714501071100751441804006680011f140c0810900701c2d070071019240500f4036081810082c014070140d2038490f0544164009a40580c2e1350180440c1800b605082e43e800c20314095040c4420ba8911400315070030540140300500c507414011058a0f482c541c2840d001034a50344200000f0325010904000c4140d08420581c00b1600495a1066401101104084481004d0b94600490444000384600d0044121009040c0310600d845484141d030300380010000d805112170 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 520397491 1250 520396241 520396243
    0xb12030a090305070e161d0915090a020306010203040e040318261b04230a0c020d0507020a0302060304080c070902091219030305061503090d031407141b 67
    0x1008102202103186000e0402c01c202c0c08000c44009085510342d81d40352800d2000300480c0060558142200f4082d084d4142014140c24103104111150b00501508a0703040c00394034208114101e000701c901a2162000261281b420360080303d00646045e4011441c144c078012201d4000d00c0090811001c0082d01410b00713500c40d24601c3c140000d080303e28030380d1504000b070f0881f00220000300e0710b0745c001e02d4204009480c1e400135020301e08a290141035901044041483d88480301038602a581c1200181c840828048440c8895000d80551880c94085800d0b90302141d41c281d5941c080c2c0040254000c80201d4140700508000002c0d6400c46d220ba41c800341400b501d5003440b402e0031201d800004119030301240c00c0c031307a629245218100301426840908000c09040d10f81a082c900808409000d042d00d480208440d0745480364820b40130140000c485d601d0b0b050200416484218448800b00024202030404012025a60030b40303002e490180c9514841c000031102503280c5402540c9400b00c02d4a403c4241140050 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 520398741 1250 520397491 520397497
    0x170307090e07050409180308041e021806010323040f0204020c030a031b03020708030a0207030e03070b0325170718030b01090509031e0c010207151505031f0b1203 71
    0x82c1d075894030340c2c840d8200150a01150340c4d2920707800308070700f5060429001c60b800c55203e40d04079800c41102c814200300031103d11003003805030500a40101003005100c048460b602c2d016400f0300d009a03030074802a4034dd0940c10b00b0421000d4607810304904038a01046c0060000d40004e52003510140c0003600b41240340841600710340002c2030701400306c0d44a0010080c12000500030304a001c507076040842c1400c10380c1e02c036500540002005410010b40c009103480074036009084580c0301240043c1251403d5480e40789818064009561031603148104034022401903205603c1c0c0e1502d61855580c054410001d40582840c1c0c03c400f41020701801035144200000c01400712161b80a10b0154200c80000e501d000418011144000c0030b45405400510618580301e902c1c02040c02900c04548040d91546907141c051402071103407640040ca4a42681d1104010300700c19080035010f500f880000d0790b0655a680e0074181c43d01009480b82640f11210b41c2041e0003904158003403a0f503d00098454840c0d0940c084030245164 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 520399991 1250 520398741 520398751
    0x8100b04090b01080c0301200a030b0604080102040b040e060d080a030216020a0f050111030306031207051c120b0d0c050103020c0111040308030f070906021c3018170307090e 76
    0x38024102152070390400340141c040505004120300c1c0d02001c441c988e40340e82d019200200f801c154840311180c8691781c48001fa60044c0425000846d99690303152128021544070740f051000070380c00c04000401518081008108044d000385e0300300e00d013492200703044000798441c0e014203030260348801d40d8802685038182030802602c000719400c8801b5043c20005810308400210900b030070361003007042000640b008a0b2010944140c08030b102d40b50b800c0392070103c0c10804400d000514202d0001904c00c482d680c040c030340b1610440503583c1017040c2c529590074041070603407910010789035807810b45d010052544681d0060071103032050400015640c103412241c2000b60b105500c196004075000c01408103035010802c41d80d41002c86410040c0e4810324102d0081d44412226008034034642d0048481411680030351040c2d80b298042a2500c0701001a40e0040d4000d240c0444469400030314100d2018480c0d0001105102c00366003081d01c600c020500e61b0905003069100034005030410540440006640c401c03060803d01503 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 520401241 1250 520399991 520399993
    0x507060201060906050d050309010f120929040b2d16030509030412080a03140906090d031a10090b03040308090d030218090702011e0e061008100b04090b0108 69
    0xc1d40c0340101d500c044d510150001e502c80e21079100a4000038500000304c420081081c20111440692500140d0300f00180b40788a0240b00e00f050390000c104000701c40111a00d1103007045840d4408205c0c0039180002c4412079000300041c02e0b40740481e1104a400d20042650689041e10001c4032000440b0159413185c19104010f421502001c0400c0194240c00344c40d030711400b688029820185045141100c14110340c10160040301d00069050000b0710039000b42c0c2c43d0003485000560b45042c4140d80700d5640104841c9034502b80500a0300d81030a40c031a0080301180c002d4001140404e04d05007003001501000e2402aa00303000403004001a1103080c000903600c1240282c079440840e1800740d044030700f42041200300c101090301c10402e84c514140c883d5803000c01c0d610107a52510faa5501c411082e0700400302d40400081c05111b01d650345ca003504058100380900c4c02c94405440700d580725442107840405090080829607007107031404490880c0183e00c12a21401c2c001d0001c109814161288000842d0a801c84d4082e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 520402491 1250 520401241 520401251
    0x80603070b12150d020603010605090105090918060a02091e12060c0307030608030f0403080d0f050a020a120614060a0509090c09091302150a0314150913050a060b0d0507060201 77
    0xc00d54020429104a04261840c00c4e043e445503002030320354070050040c1001d0220119030320003684d1065050ba16181c50150940d01c441c180030055545858000400000d60b02c98440029a20728050098030000500940b001001400c14200b40000c03121707800b2056004400d07941d03200e01e5502c0c03c1040600a01c900d1106940e40c0c107040c0e600034107503403054100c3ca071070394010001003015001120458048075001540706449031400d0b031a24003d07260015510721258101018413070b01022a40c02403518100d2515043c040030503018075442540c90314420003007051400104031005003840401848400d0040c90301910342070304080041c0c01124141c0d0054101d0501180c020392500b411038007180c000206e600d1048828a095002039032400d00c0d40040c7e01c09c4440403e40540040c060b40168441e0700b1240c0c845d001c1ca1400144c1c10449005005100d44101c00b000080b13160801116200d102080c4c0240145c1ba400314981c40d44005004141c00503908403160004110120b90144254000b40c6420b03400803d07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 520403741 1250 520402491 520402501
    0x11030a0c09080706021009080c06070f17010b0301090b27010608010b0c070506090a030c031a07110309041503080c010c02071e0e06060708030c07020907030902030d080603070b12 78
    0x440c40d4400d03005840720380e1180c0f01c18821560006102040f035004410b0128003482e42c1d240001c00d50040290070707001d84c0700b4142480802a00200e60b90f000c51680ea81d24421072007400d540a584080c01c5c0308103e0103a4040005100041e02034116091070000a041c400791182e905d00b14104250055185034403e031036940040c001b0590100d080c600405007685013a0038181d1080700b00352150344510481d4460200007170300028540b1104110002950003c0d401c079140c66690030003440c1c20b85604040c6d525907071080d0015052902503907030b20b03142d641c025004600b0899200c044c04014541034500356080985508000002010900200404507004001080f645c03a00000030385030420755040980d4188298140f0382030709125003010001c40700034100c0b0444035120403010071124419a02c010300401000401c001e101051600100480c1d84244c0b144d01e1141d175186011001c4400c0c8103002507140d0003000c2c2d0441d40521800300d490300000c0040c00e6500003580c0d50714204680e4003401c4564031810149041207 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 520404991 1250 520403741 520403747
    0x21c02030a051014220501061a03090c01020a0f0308040c05040e0f010507020c13020d140721060e011806051e12161e1d0105040b0a0503070909020411030a0c 69
    0x1400580c901c510381c42e10b4200681e208500c811700b6100421014060702400d03051100035080703803006150149100c1041c950104114219500448030600f840c0320300030303501090b035100154014285400c0b90464500800b00d98085601c3c00006d041907a0040c40300354080b40a0b138a5200d420041c15401b0020f001d11003040b0315403801d640c3c004111909641010b41c4400517a00ca00c003004c1c080800c00e00d030050355155405140d5000f00038099500c18140e43c802e0412044541040d907c0f81030b01c0c3c020118164a04000b40d0713190644e01c150080c02c040341d101c5801000003038600100d0245085050102140c0c1707549400106140b072070000c03100040d490b191800c200c52410640c8040341100f480d14050045060305600c0030720b03940d859228000e00c44084071020860103151242c0e00002c1d0103a400441c07001100005201d803801400c1c040d21748a01d107081103100c0075203003456041d003c03280d020740a040d01500e0f244000d00180960041a6080b0b91100304400560741c001000318481c410403007001959540b0044c0c02 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 520406241 1250 520404991 520405001
    0x8040308090a11011206080a080c15072a170306190e060613210b010618091a0909161d0a05100305010e0c0f060a0804021c02030a0510 59
    0xc40082d00001c6025020440d0212a20410031080c00c20f11095546103804200500d1a40e100030b01c28000d01209004015007c00102218495203040318143c1c11200e045035407101d026501080403441c490800b0355420f1b130040441c02c0b034418032803000c48070b10083c1d240d2210364000a554010300b03103800000c006013840e00402d5152003030000c0d070703540100f24104881e0460f1107801821484c804d150200d40068159000c4940c04090014004442c40202c100c650010820109003811584642043c1c00410624424222102d040000c9000c4e010b4943c84c0800342002810a44e000081c0001e10912603042621601845401034008c03900821400ca040760301d00c0b410714017a80101003032a1080d1403107500b0b00b0350980c00e950070035548174000410307440d02020201e17005541c3d80f00511035400c28500000010010034410403c52080d1401ca81e031103040b00030086148100c10349000425109400706000d030418a8150100ca0000c0c151000303250300c981c0003c0c1c604110344500b224281d100c5040a00510418014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 520407491 1250 520406241 520406251
    0x519030501240e09090106150201020c0c09090c1002030c0109080c0c0925030b0d080306030c03030a02120318011514060412300f090b07260d060608040308 68
    0xc007102c1580410030091161503d001078512440e110000b040d002e000039071103c3c000b441c000c4e0100360203010040010f8042e41160114001c03a01500603159114142040c09038819000705000d4010f58500400f04200d0311403641a036011440141312a0011810034400c02d0810350082d000e142d00c41154103100303842c101038042030f28016044d040c00d10104011041c24008a01c040856107240f40c0b0890070200c0003069a0b51819500c0240e601095092101ca000150b024101c15000d940520130004241544e070f01c80c92801000582c4030310061100051075a003d5a0048140c10800c481c06298010060a68152644c0a003007030562020030031000c071060541c860068001e03220142003d1800b0700d095400b0f5100d2001914401e5400200700c15003c5440c4c0144101860f84d0341030b007240d0b2443c04000d00f412550000c0d200820741030f14000c0ba030b030000c040544070010b42c040351900d0314004011440f103020007401c40e0384010b07410a01c03507404d100c280740c051480944520355818000345000d003402081d426010704 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 520408741 1250 520407491 520407539
    0x2030d0e0c0603160e1c0204050703090203120a020a0c060512090111041401030207060f0203060a14030c101b060b0103050a0e1513080c07060f08150108070519030501 73
    0x441d100396070310340800352540321100c40c0c1c11840068446030309036852031000f501d20368410600c0d11030360a50700100500080440c02681c04000690703400d032054040f02c1c40844041c2d0305501120915200c040000024019040b03684180c6080045a80e140c007110807254000c2004a000480e000074291503243c1c60380e130300002c200c009116190600500004030301c102d0168500358402074101c400c059010350101c071079040e80401d080091034206040704c0000e400c151b500520581400c80c00082502c03282c0c800780d071000030050260424000200c00c214400100030103602c18014070610050345c0c0c0c2c40501400507c207000310008030f01645242c00041c204c0724001c140540252070070001103003c10000a501c22083e82d9071840d5540790311a0140010709043c10782004146850019807000d00300008615042101e82c55182c0e00040401e140090394405001c5070540010034108850035101d604c69040550090b1450401d00c0c0b8116a0407081403245210348030358030100b521000100100c400003000c4d0400c03801541c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 520409991 1250 520408741 520408753
    0x5120303070320040303260916061d090a0b150d1503030507030e010e030703050f0607031407050d1b020109050c120705041d15010f0806062209050d02030d0e 69
    0x40554035050013140006010044580340b942504c0340c9642039202c540d51540301c01c018500e00007410640d214110302440406404143c0d0010302d00d8010300c80390403851010706c114020b0700c1c0b040c0140070020030024440f070082500d03003411440640b2840e48803201e50381e013104659540c0d00f520302c83d003050f1000e0302c0d034080140c40d010204101080d4484c0c260740c1c413180d05190410481c030000004a6a44824089150341402800000020440c0009442080d103948009990090340c8101040e411102c1070b04049070038031003140000344a60311070700c0241040100801c000070b941c0b03041441e050302e01061422000140c1c3d03641d61400c05104040040700365046003281e81d010703079841c035642c4591103601620409006644401c008030300130000a200b0004000c000048440c030421007802115018801e10484c100c010143c1d4000c1030611010540030712450b00038118078000d1200e1003130011016070700031f912100f0b507542c0c80600c000220107000f64070501c40d180c2d00441d00c9071450001581201c0c101d01011300701c0d500003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 520411241 1250 520409991 520410041
    0x501080f060603060406080303010b0a170105060f0a050f0f0d0e0f191a0c03011703210402010c05010606020f100608060402010c03091706070f02010b030a060213051203030703 77
    0x5800107944000141c030b11a0700c0b0b031203000c0480c018110344d400070845400040000b0900180100151007800301aa50300c06080d4511001a0039004d402c0c0101c940010040103a54507040c14036005041100141c40d00303a1802c1d18000c01d55049030041e60312000321900020b840c003c074160500404d0100c030b03071150242003c2e080140c5c4141d03682c5202e20041c1103840e00003520380c042c44001030f111046d412150310680f03018640200050529442406220700c3d5090705490150994000819a2010b44126280a10346040000c0305842c080009108a040043c100180e400055080c0103000c0101426002040ea00310390f174280e01d09000d020840c0030303286454048200f00c401000607490303400035020708119074a000c03036040403140000c050300100b845024198030310580010015100c2d1107031040782d8414075901c0c0803a20490a07101c070000500d5040c1e010310441000300b0341c291b00515800300c1c003980d4865102ea5032000b040000e468480995090380011081105098141c0107ea006480800781d02c0d22058030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 520412491 1250 520411241 520411261
    0x90606120b18061201060302181b030c120a0227090105010c02060403060b030309100c03021915050c0c01090b01030b1e070804030512090a02180709031434050108 71
    0x2c000d18140c030070040000304907482d442c00c4d031009014540103401c00316520705404468040600540c2c0509403240d1259004021617400c00649000341400c6200301c1ca840080060300c8082d400151900040b203a003084230341d6580030810045101a00228000a000c0149404102d21564140d2100c0c0c184080720000100694601c0201c0b8160b80d40810005400c070103480100c1d145000c1d41d00700540010860010761740c62074100342c000c01058426400c031041080c5089407200001c003601001005461741c09084d0b40200384941000768016406090541401d803403011190030b40d280307110161088240203006109015101e500d0035071080b0031000c04060480c12050f8600c208800504190030026914045801c15124100301c0303418180955515245042c03001001d1b46803d0b070700e10102c3c4502000640c0707580401060789021b11414040c0c942c0711006265442d1f000300385004103a01d180e140126494482c400300300c085540391564890740580381200041448500d20380c1c003900094140105d0000304401c07040c4e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 520413741 1250 520412491 520412539
    0x40b09060a0c020c011214090a151a1216060905120a030e01080411060301030309080c010f08011401050c121c02070c0b0d14010314071a040519090606120b 68
    0x40c02c0c80e114490081d2a210a0028403400d80507424036080d050900101041c0042c010884500414110080c070a41800ad841151805505a210703606d49010f1480701d07103880c806c9001001c103200280c1d02d9400d03c1d00010105c1c6e1021350040408219010b81c24002814170b80c4044240359942801000600707240d4402038660700e050006141049141ca0024040041c0018048006040a4503807a100e584a25014101c2441c901030311801d0b20a07508046100c0d2b01c99601d00750001c0d660b07141d12605900308034901d640e20000840d024140301c010850340500782801c03c801251419000352494440e8482070384500f189c41d02958000d200c41c010310070f00010601d02480d0204480100718400d540303000d01c2600b400a0030715400391300c580c0b920801c000824080c20742060f0660450300d40c282c80340c880d1907520001020801c000c144a03086424072080c001030909211603048504110400c0f40810f5680b005401600d1441d0044c40005800e04039241c1010014003652490a408413001110a0f070760307078441201d0034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 520414991 1250 520413741 520413763
    0xb0408031b0a1203050a05070302070b01050f03030f03010f1a040f0902030601110109030e010e1903110301020c0a141216110a050d0b250c030302070218040b09060a0c02 74
    0x54801e034204240c00204000110303501d5807200d01900a5601d048014004040031a00340d13000ca41082c00103001e03240301c0c0c0700711070280e40d002c800b030300103642131209115010004058198140c80300300704004501e040b52001e14000c02c42507510303042103401d01070030700c0c46c0d00a036402100c1c0b10081440103100700311458827480305070b1f1003100005840e6902c4000407103a110b0502c3c0c2406482d440c1c210b10310305141d482002030f50510001e80300c11030f0b28100351061080e074500f03503500481189001039051000440d4030b0517904140400500241c205281c803480706080142d90002104d0008402c43e0403589218184684c41803424000c2059040215000d0300d1250007440d2079000b820410a800380d40c0440e0364043c003203005000080c1581204804920304100900c0090b10318008544c06d600746481501406100341d04490038aa8070044500384903a01640a50032082d0126801010101000144c812101000c0c4c8030b5030140d04030f91801e0a00100d42801c3c00006800203001e281820f04180302d1680010350703100701d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 520416241 1250 520414991 520415017
    0x11010314041b0504060e24060f1b03043011010e0310050a09030314010614070611030a050430210207080910030b091306181b0b040803 59
    0x8882e200c0841c2c800b41c112500401c0e8424541040402c911041d564028462880b03118240442c012118090310b800707840750545a48a0401c00001c905010114080c04032900c201420582c108404805a81140c000d504089101c98850940c02000c003400403004228004409401070f81014070344807912a8407403a40b4140c1804413200d540320f0350b6141048142003481400078108042c0c2801d450306400381a0740c020980010741448074000540c1400e600321030480380c0980310081403020903003508015400000c0261030007603456181d03580040c1030300c0045100d68400f5000060340d1406d444c0002c1c2103200e080c100d00c40b000c180303038801c0a042007201c0e034080c42c0d90642c28107404032000c8014280c407400901880d102d1490000c00c0310010040c14601801e070110b0229401d1442d0440444210b08130390b10418142d038041007880100e59001102c000d10741c0524054040882c40743c600514211541070301c01d90444103070528040110001910810304409054102916450145400c46a035aa809516540720701 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 520417491 1250 520416241 520416263
    0xb030c030f06030a021918020c0309040e070306021602120a12030b1c080403020925030f020708180306010f05030a121106010b120709080a15060f0b071101031404 71
    0x8695400c100010120745d004150040b243c1c10303140c0002c000200c620aa03c40d00e16190200c075a001c00500035120098a01c0c40110300300300f510300400001c0c007043c7c00304c52083e008451020010174250b0004050b0007480400e0f8040144452040c421003a070300e507104510036045562607034009860b02480c00d22520342450041440048040050f000e481c14003d10401d4031038400d0480100500840079104032802101c2c604055658000c091607442848121941b0740700e042d03040000003502a034410f840100c850740e00181848400d5540010035485040b1504841c40d401d008003906240400c0254090002d0440500c0d05a10740808a543c3d00f110450041c00b45040348984980d2900c22034018800100680c00c9070269607513901d42d410154050811225000d000400184505015002c001c003100e50440080c4480146902c8036807481c1c140c481c000e0603558507000001900041c84801c400078040d4030700043d90720580342c0b8015400713120741400b0a040c1800d00407500320b48084540a5a072164106940383c034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 520418741 1250 520417491 520417501
    0x90105010309113a12020706080403050a170106020105460b0612040c080607090909030e0306010b250201171b070f1b031203110910180b030c030f 64
    0x7650701444c1d60754169100d04606480001c0e1900310352200898010000303200c41c0030070795404030707220503540c010540450400d602040c00030703209100420f180001d80c90000100c1900701f450480c100b030207a00501c0141c1d10f480c14040d00a011520900901200c0c11591054000030581c2c1008407031240502d0740d245031542c036940c0810015800100c45d0803001406144d84125000880c090110150741c02d8865481054000c0764075040026007502840d8181c4a90b601c1e945420100400342c030712000c007101040b603503070b600e51450f0300e04020542c003a04c40003a82a4460141182900380071042041c10384610760110003a0025036041442d40700e000b2158402050700e41d0300c2048242c019440595030341540c001c0050841c003800078140141003414894528241540280348450100742c120f030001804890500040c0c2c00da00b802548441d21088103000d0b910f052421800005103052490170f000300101e01d40c0d40205140c5c80301c021a00c0060030490100d10b041d41003a4000e4805408000c11500380c1001e0580424 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 520419991 1250 520418741 520418779
    0xc010516080301121509030c060b040b0a080319090e0a0207081303030504090e010e1221090102040e01061d06070201121b0206090c011d06040512030909010501030911 73
    0x60041c0c008088075942d5968070042c03062414019800c0d14040b038401301a038226491800344000e4140c01d0382d03a4001d11581601c43e41300400b401020b0301d0344960b8424010700303039480e03052050004081540c003840d219800c5202410b8181d01e5032680e171041040c4090f00303205800300e4500c8250000c180f01300c010380340c0086141a4050788100c0090302800e2002410000801d0b62003001401600c0d00958144141c090712425079090700c038500844c20640e041000c03040380c24111070002d01139002c0044124a0b0803000c040300c506107240b0680d00d61940c0e0750002030520558404071707601c0d8010292440c00801d01402d050141400046604095201c0e5030001250b0096a01ca0041001484e1544400b00302000c86080843d0b10034503400070030800b5000d041c1c0081c1005102241c0400c5010040e1550545064455040415003c10759011540690180800b24031521000000304c1d8280d100e80c001c541d500d0480003001050f03d0164005810181000c00c4080003842c0348015114a1805413642420301130007203291 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 520421241 1250 520419991 520420027
    0x61701090b010b030a0e0f010b030d050a05030a09050c100c060e0705060a03050c090616021302130302040e030c150405060907030206121b0c012f03040b0702010f050a0b03060f090c0105 81
    0x3c6d5028403d0940b030b10394840c4190f00c0400c40010071000c40d441c0c0780440c101501c0e103008035514803000c243d041c40098060500750708800b48191049040c1c900040d079050008207001e4913808540001603540b00410304001081c4100618005403000030050b040c83c00b80080c8081c0f00d11144c2e441015107510109601d40e411209441d4545001415162101010449050f0012011740240d1042c030303107106070110303d61545c0300b00c0c0c080386602d82044200509640070311000d0950140c1c001c0d580c1c48100319550303a03254103000d1448241184802c00c546400d15003015440c1c09000f80050760560424282000140d44610850303901d440c2c59000c240e12596801040c4020114a54000c010b81c900010030b400e0041065216069468420b03440e10341951050107142c1a1700c004c40d50b0840a42003c0010130041a019203000b50b0125540c4004506880016203410650b84162104c122264441000142c949402c1c480e50f503020343e2003503a400d000c0ca003c020550343d41c1081e404250600c2800038440c84e00081a81c49 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 520422491 1250 520421241 520421261
    0x712020a0609030c03030f0b030c01030b0f0402040303051c051e070c0f0309091404020604090519090b0601030f020910200f1e0a0f020f0f0405040501061701090b010b030a 75
    0x2c00007802203081c0600f4070140c00350118000b07490312400c000c00031214498070304100f401400403d040406c034070040d8018a40207204591094403c140003101e41d48500042c00654400d0313540315241c070b541c0b83d105410a0258003001120038281010443d40e54440c110102400742c88401d240043d4444010070380d4103685488001c1c10a9811900003018160800c03c002c0481d0102c407401c005c0708110a0400b48614006d60300298010410401004484216013146030000d99280001c59500c0800003442c0031100e10402c115118043e21003044015a050310510040d51300c60503041d4900b030003040000f030340009003d1240062041c0015001046020400c3d01a041d02280049a90200c5101201f564034001440508201c4010780090404028086541c054055000782d900441d414540d007003102000e1081c030040e030010700143c25882a40d403070707001d454040c80c015800010610f0a00480d91401900d2a80d00f48507030b0f05000490001441020000d811074901d851580d031291505240d203405420034181e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 520423741 1250 520422491 520422503
    0x50c190b07051c020f030708030702010b1e0a090209091f231e03030d05071e0507050105010501050f090609040902060408160603090c0510030e071e080309060712020a 73
    0x81c1802000400100b1030902903a0030240c91590891881c1240c1d40c014218500340d45400500c454400900548065900301c5c18900010584011000104401070703901c10380c8050303010710b4408100070f07401d01000c1c030000b510880c0e406601d0180608007150040c00054034071081008c5419002140319140000c110150200e50150f2240160002d6100c001111a61002d4414200032100b906000c00c1e07290041c0b020070004c0c01540c144800103a00c1401408010150002e1081d69520542c0101100b002880e18100795101c0b2900c54031241070060031104160400381c140042041010350794220281525000c0d01c0403030b1481e544801050200b800b508400ba0300940004010501094861022034003507820310300c0c0110070444554840040b404e6968030303600a02891881801845141041c0100c00500720b80d50a000c107000b20b101281d85d19000e0300b45d0000c140c1c0e080c080384903802c0f10301701d143d024002e00c0f00000541c1000b00c440e0000d0303028402c0321401010311b82d43d41c0800301c640d40288500116260010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 520424991 1250 520423741 520423747
    0xc0203010b22050a0501060f0809070807030605012d150e04061410081302040b0d0f0b07030e030f091c080c060f071b0b130b01090902150403050c190b 66
    0x840b144041560288101c40c03007420b290003e074002c041c6200c4c16040307405540e03402c4004419100705595600002e01441400e001c0c000000c500c00c113040080303000961261100040c650302d080030300f03014807000d0403507541c85c0481c0d038103647c3c070b8036000314686001d442c0c50180340003030201c0c034210988880020406d056085130810f031000880206542c640f0f02c424106899142c0401030421040f98004011a5240140c01c0040c9406015013401d0b4030031001c640000c2e02c2d031b0042c40300720b40340c6030841c1403602001c4681c01c804008102e200c43c6e040c0034581c1d60304c4c5601c00030b42c184a0310b00c40c4508a8007074070701600d00130180c01d0440100305107405403000078540c011645079600c0841e84411a221035040b150409030f00111000314080380d1042d40d01342801c0810140c03030841700ca82d941c0d41c400c40150190403c035006a0300700070800481c03122031000d4001e0050f0f82c00000c440c102481409080e0b602408070744000c19042c8401c00200700e0204112050540403640000c0440c03e0300b40c610442001c642040070342c0c00c804 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 520426241 1250 520424991 520425019
    0x6080610080d022e0e030d09050106140307150201110d0c090621050604020c0d0305040506130b0109020c031c1a0907050702062109150c03010f060c0203010b 69
    0x44030014090720901402e541000a502106a030344410034482040d102d11090180703d044103e00c00000484021500040742810f01a400e1342e10316004202d240b495142d60305e4201e0708100c0309100d11401030030144a0705a2481c201c20000f40c8030440d901c1141d00002c107104000400c01d10079441103035080c05102d0041e0b200c02e4a188658002c00d044400c21021650420b00030079694050040103503010815008081c1c0b2f2000c0c4242c1d20041c04002d048582c1054081c401880045000d01c10f01c4528412560f001802c1c0c905803c00030b01e45000030b42414034400c00d43c4c03803e4000c10a034001c1c42d819074003514005130f521440b82400318690700c24241c10400d0780c42d007903c0e411890130094105d0340c2501d2039205401303191a485420094500001d480b4040404c2080140b0b40050a0a5004d0503140d146201d0070112130514a2803441c00070011900d91020390450f04103000c540061009180d0002a8074080ca03007198100003821036001900d020350740030722024801c08821540c007504640140200030700488661095 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 520427491 1250 520426241 520426261
    0x20307060b0604050a150329011707050306010c05070b12071d031c120905010c170f0c1b070f0f08190b1b18090105030105090c01050d060806 62
    0x11588044511500703012166640340b901030306a50560304010815200710b4501b20300080300c2c00b5500841002d058445445141118903005031040701480440004d40c07500c01030000404079120600c46040c41c01d100d5041c01251680300054951100080c203100e11002c0c01d60801902d00740e503d0340b0078100361000051000e83c00717044008071402048107850300c2c410320400c001070380326040c50000c000d5099802085075403501407114245241200150502c044140140e101107410782d0341846094071260345a4022000d400d07404112448040d00020071603a0504001d42c40d84009030000c0c02c0c6500d41040407600c41c0e400d01d480000c000c281020075040b01c0302c06554551000344000389208030419030341256400191008041820088480440d0590b610240955a0f85402c00c4000d07000c02e607524014140c199648221000500c6180c0c6c088903d4800040300c40100060540f050b08081d02076414002444a060b0000a4032510b10070709090a44e111078500121000404070303948048070b248107c0302448040c0e51 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 520428741 1250 520427491 520427497
    0xe1902040e25052e030c21090b0f041e030521040201020c0301020f03161704060203010509060a0531140a1b020a1103010f14091501061b0606030803070203 68
    0x2903d09144c55114030240310100180245a016480146500d035083c0500c00d90190781c0708145130502c61203206103029555440554541d0f1200d201d6550070380c840c02d00000240143d0b12907200190101c940c5003a5450b18014200200035050180c83c800b01d4034100341c042d03c2921084c80c07044402c204a104050300b800741e03401d400d59041c1c0c09030050341420400f40c2018021180072a503500c0740d0624544400324140c20705d1541201d03000c1003000c810350341a85409052a01c5000d1070103a4400b58895051804100703220784003a103054403c4040b4402040607496050007a00c1e01604884038800030081d44405e459620b504e20740e0182401d03e044041840304140010050195107000c0701009009030402945441f0124210004d01603885400d151000561040c600c1c80d01240c081c0004c1050b0603500010302c1074428020f43c003540203000c0420020344c1351081010341c1502814008011195140c034a000e0201c80000f034000c4035100001d1180428040160060360040d90721114540c0c1d2864940b100030744030b070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 520429991 1250 520428741 520428749
    0x2a0e06070b0604050708060d1106040504050907090b0604050f01030903030b030d050711060421060f0213030317072a0c03061506020f06280507120e1902040e25 70
    0x1900c0c100224505500c105000d501c5070001501401d231240150300c60b0506201c1d00400342e0f81c812800c210105503500c840c02814009c0203076400610402d410610000240d4040c08841c80c090307181400f00300a00d07503031144c00d90960705d001e0030005a5003000c0e04045018000e40380c031785030701482500c203c1c1800740d6111005002d501d0007000d00c0e41c0340301c0001042058a00c114422994042240300714804200c03a50380f0b17050285449403000140000c0c44120280991308020a922601814004100149070301b007298120008c5881c0034154441c0b0b0080000340860350035540c860092160280001601807000001c0024150412143c10400b0303903910346000940302542c040f0719200d05d00800090b1043c00022004d04a001540c0941103907034422030300c0b0700c000744586072600f08070f1140c116a01e1441038038420107000d000c143c0d0315003403c81070149188064402c46480c00070254849910b521010040018118a080c3d044401142c0156000b80c07040c900741d2851404180411507010700101c038001c00840c0011a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 520431241 1250 520429991 520429999
    0x1a0102070e01031709010c0519020a0509041a1024090e0717070912150c0212033409081204030302060a090c0f03030801182a0e06070b06 60
    0x40c1d16041145a4080c003840700038920358002c3c0589900c0d00d00c00020300840c4406140115516046454641c58400c0712001c9191201000480e202507007800c0b00a0400381c2001c1e140b40c030b0b0700d003403607517a01540c2c104595080c01c076118071201003580f558940a40000521001104079600c081560b91404c2501003010176801090916100248a012480400307101d4602074940c40f0801c810101c52402c104001400034007045000312012070891203500384040f20f10302a51981100304240541082102d41c1003102005550003942820350303403200b070801c803648000459682c0340503480d080c0a0b4500c441001100d000340311000d010000703005500010500132140b400f400c5a040072a5103400e6803840c442c034000500143c05c020009141251203400030324111388078801c010401c035074074010101d01030f449400c00c8000612200c0108108117409a03c108407a074040b034204a080080c1620305000664544074040924a440311044003901405211a11384006270010740c2e25050342c50a0b440504044405130301c2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 520432491 1250 520431241 520431253
    0x606050913060b0a180509070309030f0801081207080c0105130c0f0315020310080f15090706020303040b041103070306141e010b0702030a1e050717030307030c11011a0102 75
    0x340c100c82c2c081c0c40110b54030305410624204a030390084800d4014241071031055104400005820345440e05d600340310340c00d41ea0300054031800e589001014104480c00500c00c00200400602038400e0110310b4102c0f0f0120300480a540f070350b032440c2030350702da0103215480d02d4a035180c04200140070024980b80320704c0754481c050031ba4585890b80300085400740d550001424001100c01c1c007020800d06030740219004110b615592030041c2d070341e0310a645003600d420440740c00da800400c0702401050010b4884d40d00302020001402c8450b041010080d40d070f002c001d201030000c5050001142c01c0c048920040b4480c41c0002d0113844120b5241e042a2018120141104c9100c00e14100042c82c3c40400808100402141c4402060107034640740c803030039040e08866401e9903d40509403d040001c2e10008050400103240b25a400262095007404c60070010305034400c0f170080f00f1100c3c0d00d4980b54000f00403a42d1000607404d001504480c0c00500f240c0c000b02c080342c46101980b0b40000c0801000c7c100d81015840b00d003d0f821680 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 520433741 1250 520432491 520432519
    0x2030f0703020111010e030f030c091f030e010501050d170c010507091d0702060a0e0708030315030d0c0b04022704050a0b0c090d0b04050a0b04120f03090206071103070906060509 78
    0x10884406c0d005850070b580080c04160f0b07c0101c044010340d0000d043d500c0c09411300740820005142c0100c81c081e0340c41c0c1d585880700038210781501070041c3c1c08a108110000c000030361400340410030031841007600900380d0456584802c00c003048142a560b030072500200800030703450318071805032210300c1d5030098042c0c00e80380d500341a00b461911409a442111540c3c080c00f16600c58011783c2001d031044265102c0c0500414002081c41e10040010358410b88405440f02d41510781038041c0760821816259003001c11913070f210240c01050745a9452038019905840c110300550201e00c40492000307070440c21a200c0c503040350078001072000010705580300710b000f205040041c0d01c407000c4606040c410404025001500f224003e404125145021307a400383c00780003a1405035016a0311091229403c0f60102c402501100e20040c180358007030103601c80c8440d1411300700310b91745554000591a00400000500003120320b1428219621705012001c0280001c5805200c019212000900b19811260000d40100c00b0f8a071180 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 520434991 1250 520433741 520433743
    0x9030e060304081e033112050d240905060306041401090209041a07030b010c031d0901060f110c01090314120a02150c0901081603060b0703050d140103050309041802030f0703020111 79
    0x460205203031b03d41c3c422000043ea26444041d10110b0820240801840803030310100444c0910a4603141c41a2503005614090321031811000041d046043e06c24500010003446440c0060380941264015800f4041c600c0760391078080c090445410000d400c44c03066418042040041101082d8201c00c28691000035940c0b01012800c8829024200b400a030229030080c000c030780245000600040011002540c1c400d003c004150030200c00c2e4080303000500e045801c072040b280e20601026070340c00d02e8000b0703285203402100000c0c0290242e00014103010740d0010751252045080040c00c44402c107203480c82c0e07100d05601d200a0345460010200034504207150f0009060006d00008a03002010161244100c90729107600c644d00b002502d4031410285560b602d4007042e44201c1d480642005c0344603940d802d40c0c0348d1110110b0010365240c0011940701081040c014000150040140c8108140a990009005042d0882d010140030039041c06500b41c01510403030640398401040e1141500c3c004e88500d10540c000d003c0315 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 520436241 1250 520434991 520435051
    0x30b01080901090c05130b04050c0403020a06081506180306040b01090b01080103020d03080414150106090510090306051003211416030c0c1d1909030e060304081e03 72
    0x2020800850f4092280e8034001d078840d20246d2085d41e000491060340350100c0c045138020364200c0250680460308104525100558002030146880c005040b0704200301c400300e243e001e11030080d00c218408600001c030b40340e200703036071080504000b01222414105814802d5440c40c003805040415414200782000c254019010b04c1d040300e80c054184040c8a1840c2c40840b400d15001d84110b403070440b1000e124115500800c22002d909950015080c0d15500d8810081c020f11103a901c00d9002c0c0c00700028120716150040040c00071290400000700b855614128403001c1034185030401803420b0161100c0c5600035440d01c0b9480c222400548402c448000b80114201040c006d4420b8844011200c03032169001910498040780927502ca00f510881d8152244017401110a40d152030034200c4c035a0b04200030b50b008107081c08000680300a0420016455180c6004000f01c000c0107105d806520b000011408102c40202141e042c0000c03a880d030200b406002d541800345500c1520011054488081c030100030811103849 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 520437491 1250 520436241 520436243
    0xc12030b0109050411070b040b07090632040b04140a0902131503021209030d06151211042105150f041509020303130303111c0c050109080703030b0108090109 69
    0x6a0b0340050b150008100c06494030108032010b1200034407030310000981e1610164010742c862445240145041c140003001c0b51200e502007020030003c0001e102610000403130150000d8404007540842081d040e00892291280350301680840c1d0001038006418101030b00d0094120030100d543c80f0210f80e84285d010300b0b038020503100c4c040c4d448004004004019002203441c0d0041d520341400740c140007000c6d055540b104011210390b082070704001017418843c056441644054050310610b90309140803080010946400390103411800c0d552183d08000031408001034400070058082140035245038076007400b000c51541c00040701c4a11400030101800030800070070728810000711201c001c2c00c0d03885454800303089031200b69901c0c0c240c3d03445c0200740150300c2c01e00040090740001064241480d28501c3c00528910a0025032007a0f80c000941c43d0a854000d508a9840e400c240d00d05440c8500050901c036005203600000100781960001d041e408050705a0004040d0b2202602ca02072590741d42c50030b96007030780d0580d00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 520438741 1250 520437491 520437497
    0x2090f0a180e1b060c1507050d0e0d3501080f060a2702010e0a090e0d0305060303040e0711060f010e090a0201170a06031e02090c071e080d05070c12030b01 68
    0x15903513410900c010704a02c0030841c044900b4850f03049400100600d058580e100003601c00a281c0000051030302404c80b003020b1400080803900103103003000302142014803080d44200c0c010210003240d210024911040c0c41041002c43d50f80356558080280e64800e0b0300c4d01c1d0101801500300040440c1101d11841c004410342c46e20803186c2044807002903100b0403c01404134140b120103a41c5a8454031004015005854051000902d040911400d03038074010700c40001c00c08141c180f104000070b1343c5001c0b082d0341c1142d401d00044030380794807a4035060382c400034a6181a20184110000c01551400b500843e9040341c20042e640e52071502c0e0000100c0d1508001343c40070b030100d8198071510380d6a400119082d40d001c241074100089184d2030350780b40218825211415101403512182140c150f20f04091803d4104640241162516000f40e844040481e061800300b48040543c0c01030030b0034003510500300e40d4010400001040355203400c9001500007034800805441050802406d10902c82c0684039400360351005031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 520439991 1250 520438741 520438783
    0xd14031b120d1d0604031d042f1c020d050106082e05060a0201090606050108190203130f0609030207050406180e01090609030903060b031f02090f0a180e 67
    0x864194043c1183c0c01602e5548003000012480741c40003031100c00d00440c400c0c0e0701c41c0e44045185611021b46000e074200103108a01c0c0550341540c1400440584d125415180f2200c12030200c0c00b600702800340500901076035030000000c010b0100307000c5079000708400c4401c04010481c90b43c0301e20f011590410201c2d032003200306146050002c2c4080b1004906054404140c006a40c07107170303c0e00e020462a801c1240e0744400f60391101090703010020700c0e0003610090402881c0c0701001c0e18000712800b02c00180c0340c0405a031141d00002052200c100c070284442c0280c0c1150711150702d64118985800100180c2c60181c0050241c00030104443c6414010750084900ea40c4071644242d1154505030010300341004519219960340c15501c0c0003c08900a40c15250b000e44c940c00f81182c0345042c42c005032212552114030a4201c4428603010a0300c0b82c0345002c09011900c00143c50740702250104060007496503050341d10031010f40300000c40c3c81a08000d0144000c540d9001c1c002507107909a59607880c00401d442500e041743c21 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 520441241 1250 520439991 520440007
    0xb07020a150f1d01060603060503010207020f090723070b070e060a0f110f03120903090a091d12180901050904030c02220506040606020a1a060d14031b12 67
    0x10b410403128800c01030790000e0036491189145282036082d151900d180d94450200300b1030345403d441850020700080d40207604c0c1043d5640024450500155139a11079000080403544170f6204a020016840340c21745074000341c150748901c1c0481a0018541100c0c103102c1c1c140011403092180a0716070000c440034160b103081401401060350001d4440720081c0400c1844078086000e540c0030800f641400100c0406556a024031601d6104852402000034016500400000b803242d224915460100c41c808100001e01109204002c1211840c0340d010075450300c111102c403625946144000c1c081d040340c00c020032240240d280c082c0609407400f44521517101d10304030001b07800b00e8050b0036400f284074401800c1c46411b51075610b12200c00c000410b1070b0b440a540e210b0070410700303050030300c52000540710900042020384150703076a1074180c098000b01410f464a0540100320151200c0c03030b010b05d80382d500191030a038102c040c0e61116907071342108408200810418081030724010011403919984912800402e28107601 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 520442491 1250 520441241 520441283
    0x180721141e01090518190302060c1201031106090607050706022118060c06040c0f0e040503190509060c0102090406090204030201140c15010b0904060b0a1b020a030501090f0b07020a 79
    0x100800600c058034640e035892010100034801040325081c00c0605042440381410b000b031170404014582b0106600c104105040c2c1c40001006e0750440e1792081090704100e15000225405004030202e450700074074045244010807501080c03140503200b07241c1c00ca403034803014045a014440e01d2090040c0d81004208551540014140903035820282d010f44494500341c0842d03443d9140840485041e51924500d81c1c0502040c0f4440b840c1e540241118000c102c410705050712aa138a9200e48210015803071078400700001c041d8064019036002c00b00007020241c5402d81c07007030b20074081d42c00741e48064400c900d082c501007010011032003643d0540c1d4069444040303201c804a2420480da0084550366840d200b558000505002c03540c0105010300b21500a00d40c80700c09240c240419a0300301c0c1c02a41c442c403014411040c040b64045580014000e03403014105103504903001040f81d0f40c12030f400152895003030050003030502001d1603070240440d2060aaa9a0a603500030080f6245c42110354010b0011240c1c070105945d03454 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 520443741 1250 520442491 520442501
    0x40b0a0e010516050f120c04060305011d0a1d030a110f030c0c0d060b09040311060708090c0d0303150609032a090e0309130b0f090105180721141e0109 66
    0x11704904100e140c40344a0000d081c61807002c030750302c460017400000c00f4030083d0380c180100390041c004250624414080045000c454040c0105602c0c91302e5501c004c4e6100c1c44210300702c40d01d803400580c02a42da542483d041c0003404006800b84003282ca1241d15803032040500000200c44084240c50003800c1e0105250003007190704401d00205a6002d501d4039000481c0e82c0c1c8122541c0c0c041c61081e114a1821065031422904103e8014010014004510104011080042460405241e003160341c2c40c42000f031464250000c160110030f01c500c04114000102d003850700504020103030384c0541d115411008512240c0e9031503c3d42280701004154803403604002940c0c0c00c0c2c012500440c00001640e090002d0000070070207407410404818159511482c080c083c6c0e0515107017003e03002744281c1d00800c1c00d604180100e401041848040d4041c00d84010008284901ca08012960142c110084446110003682ca03000a0001c81021400101d020000f00d044040100c4c0c5c05086004142c0034203495030318000040d80245 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 520444991 1250 520443741 520443757
    0x602090a06020a2d050106231926070e060a0503030415180b03270a02030a0b0702010b0a0e07121a010e0a1d0406050112050307200603040b0a0e01051605 67
    0x544d0007128200014000e000e40b401400405000c283c1d035083e20320044e4041c0391105074160046d6103601c4c00041200c101041801554030480c1c1440c0c08007026240c3c0c6215580e6030701074a49c01e0260303940101c0d686280c0c101003801400200c0346131040544503002c05840c0c0c45203100303480c0030707840c3c054003000100e01401c0740308462003040305a402616510750541150740e02c00c9802000341d603c3c4245222100340d00c00c6182c0c0300104010001c00c04207645074082540d40c044118054101506d0034002070305c0f14400d41080104000142c120f02020b641c2c0e50412080400903120a00410301c100d0321241254214840c02141c1d219901d400003260031641e0055600c4c0421021490700911030b01e801103004203400378201140308169005080c185814282303d0121b41040e0055400006c00c4681d04010840010550308103603041000b0415105507252400c55004520548640101c00030042006103c460208e40d881403032141700502110105245090888101701c0d0713074100074064440d50034074848c840c4d030240a401d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 520446241 1250 520444991 520445063
    0x3040f05100207051c110706050f0c0706090602060703050f01120614013b0105120a06050f190902010906050d0f0204030f1704030809091509040602090a06020a 70
    0x40c0074030728100c02a40d0040100307030781d00c0d4045800d02a4820a151130416040c40903d003821020605105031a1110703a40e1181108003c40480d0071071003043c3c0d95049a140b0005042100c05840c2d454001800300d00e01c610505001d0b000d0140010304844c0a0b004080c030604850b0a2640d6a0f03080052500c0311441299054409907039400c00c445000e92034000e194040d01020000307011140e078070014081002c4002905001040408031040e903010f00c1d0102c1c003815101c0850b040b03805a44503045032450056415005044c1c24208014000d1460750340c01401d00420340c004032a1801380301d002002c1d095554215000303000481000c000c006203071013440905240f188600c00400c7ca1414154644140e802a4000341c401010382e2010f0700401900b5000607009a142d10407803401e051840c2c07515205802803ca09a01480204001805d00c0b49500418441d0020013052500c8508082c140b8200079040060100c4c013440022002180103400021021191507002d000e000e003a9401a100d68490200301004c1181 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 520447491 1250 520446241 520446253
    0xa09090303020c0d0e0a08030c060109181209091103060d120302131401111605040906090501090b09060106020102090f130608120705010b060403050a12121508060105040209010503040f05 82
    0x40d80700f09100100756044180d48480c40b01d884031080040002c40c0341e1021203107900410003006a0350000c60380b181180c12100001400451080c002c0781b150710744500080040085000101080e07420100c000c065507002c4c1d404005048018a91480502c0140d0b8550f80c0104040c031400009600400c1342c001d99100e82ca40541400030a00369840c082400d5004051449000b1142d0041c039644100480043e20142c0000c005102e40f00c48641b0004000d4041e49018a407503004190600006070070591000b07502c90001c111642a81c1003400420300140d030f601d112030086a00029000b4414000d44401c01c4000300100075084500c03003004500450415040040750712414001001941440100028804a1116580c40c110b52414908552146d40542e204210521050001c00c44c00145c1006199011400c5d01c441500e12100b40c07a51001240000c030140e09005004407120080c0311071008440303a070380803a1213690b2210100426800764100c0729000610600000700420b840180c07070404140650141c50f0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 520448741 1250 520447491 520447507
    0x204050612040c080a050c09100e0f060d0c0b07050c040b15030a0b09090a03110109030801060507060e0105180c0a03021f110129010f02100b03010605031606020d09050a0909030302 79
    0x170806400780d0302650b054101100031911410030303050f031a5001561141e0070340380c1820803220b46040c40000d08128000d038900c00004007a503c03130700707a40c01003180c0200e220740c00550b503000762120544c030240b800c966074010004101244d0805000f10810a0402030591404040c038074260040d60b000140b0400c29035440c0c2d01c110001d0303100c001c0030034055580c0320f02501b0803824905000d40707580528017020f01c184e0714021226020a030f002d143c01e41076405501e016a912500b40c02c050380078250b40080b042007035203444103010305100304881403604503418005840fa0707609000100803111200d42320294104840304181c0c403220a400b000100c2c0104141040013a40c048454460300311140c0706046800c41052185a81d0780150241160030107040900c2d08003982400c1d80350007512200702c1d682141c0c50716210f849421060f0750a401c490050440641141c0f00740754030702c4003050a801180b090001502800940c6c2c581148248035202c242c60010301940d041a2420600800400c4400801d8003095800d00400c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 520449991 1250 520448741 520448743
    0x705070f02100302040501081003020112050903071b0f060525020109030b0c0306130207110609030712050312010f06090501050f0f070606060e1206060f24030a050a0204050612040c08 80
    0x1c0c0159142c0e40060310741d0700b886c0005d0008000908112044801c10b401000140e900204d00d001481c1041300206141e151000743c2d82c610f0284a10040000c180401d107891180c05650f500710489018003c01da01c000e0b580c0d40180c59078451400c01c10355018203280c1c4111008807400824550a1040c501f202c003081c4e0781e40312084503007419200351004c1c80002080c0300040c50610031880361104e40e0441140303444202e64441c2d101c068101c40050141c9404540c2c000d4595013408200c00a20030603004110f90318252404a031240e028078140c0c41c40c18003e40c00842c141d8121000e41d800e82c2c8054a807080300300d0400c1c0040d1515000074400031181c072002c010003254941c8560207044c0d103512501001c0382e1141000809000210780b205818015004200b49168480700080c202d5004001500d41395a10b03104c100c04540c1032b410f03125444082404000c1907000240d2590011071054501c00004c1050341c40d4480048141d01c40c5100303c0d984220180400031a0350014196950803903ca00460380c18141d0320521a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 520451241 1250 520449991 520450009
    0xf060501024b2e0504080c01020a05191103030c0d1805010b1003021606050405070503030a17060d150b1906180509041e05030c03030a0c260705070f02 66
    0x800b07007410b00365600040e0850208901841a088800081400c1000051002210f11441e000808036a250008038040c440170b1000c07a000f11140200075559a00c0c0f07004042d229070311100c4044c8001481c108412030b00340c0305881e411070038402c00e8055840c2d611281d0000025801840c12094101d03039404100c0401c1c1d884820014203244140004100729942804200583d01220310360001d05004000300b9000010000f60000502c3d802000010241c5980c10542c1c81c2041503002030350144000541c56003602d4100c00242900d002e0351404800da903131503e083c45804400e00c8001072580c0c003a001400b00610094214041202000d808a410401d40307000c080c48c08426640884d003c260302510424003245e000d01e1240c090b25043e00d030045c150529035115807004c490164042c040c101250301030410032100780100e42d0b514500700c088a07101c0c1400302401004120064110022681c43c80341c1c102c3c6400101d140101e1052450925100d0382c1d1002c10945299110a40c21a580c0d40b90400c02030040e40c4603001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 520452491 1250 520451241 520451353
    0x30c0c0518190606080604020a02030f0f190309081206010e0a06030e01060902210601140c011a01030e060109180203030f03010608060102120a12020714100f06050102 73
    0xa800342410150051625900d15030000c070b0300e0904110701449915040a00c445d002542500d0040e41d59905200803411070003219409940a60b002504440303142900001c0d00b008803030307807003d020040101c0102341c2c1122120b64000f001075209001481440822a0402c0c1e4041d90604082500841303500010383c0100c02c940091010980d29100f000040c08240b00e5034000e01800752007189001c1c814070b61108130303081c0f000d18100c16403949000503100b039100c2c0305885151400c6052858491158440d5580030b071110800380d9440b2130004c0f03009100d07903229020720603150018801425069003048004400b818100320829080d40c03990140c0801a1001c000811950078140c610719129410190b0081084c14050821350441d03000400e200e5810a89204807510030342642899140440c04a1405020740914030026040c0c411b030340070340c0006000206101c016035600e88401c1010700090001e48013118894003459005030f20010300ba244c014102014031481c40d0010b01d80a00002c412403c1039513000c0f520070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 520453741 1250 520452491 520452529
    0x2091c050114130308010b071a1524030a1a030312010f062c1c03030207110901150806130c23040b12100b030a060f170703030c0c05 58
    0x2001d0b1803541428001240c10510085091000001c0c0ba00c0080c20810103008100d40e1510000c0d0213020450804041507140d1000707140d15000d403600070800307600e103a00e01120300d00032456005004000c10940c4200e003064581000340a045888880000c4000c040740217440c0f1841070000020219a03500f0030240201e95030781003c0d41c3c0d5940c14089543d0000000341c5c0642c0c00c3c40748000803455080000101060010700c000f0141c2e03a03022a0b6400a0f1940600700351f41d000300c109000c810000e00d41d06400400a050041c3c42080810b01d42e5428413510101c00d1190035400c00d503003113402000c1485944169003001004014180c141c051300701200440344503c200b100410810101444407048000014503094103240d00300d0300300f600d000000c08241c0320f50f03903905014410701c0340003400d000c1140c0d61080c0074003488454192640380c030707413110350003000540070303004503c90314100000b001200c1c4022640c150b49500c0203000c40b14519541074483d00d4900104854010701e8010105082e25165185104001411 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 520454991 1250 520453741 520453751
    0x1101020f1305030a110d171309140103020a050f0103060e13151401090c05070f120306171009030504080d12050c0306031f090c0b04050a170a030302091c0501 69
    0x503010422032aa81c2e446503000b41c0011840502081a00150031a605000d03642403139010720501e0a11425000800042201340021036a5000190031220981c00d950400008000d401c820710711320b200080d424032000b50b021880d410309002a0424980c0040c1046043c1004101c080c0c0310310000f600207801300d0301c43c10340c1c8440802c0d5106202140700c01201001c0c1081041214240c0c04142e070050300310502071801d02586a0444107281c5204604450100c0e8100b4090598a825490200002c0d803d0711420b1000a05108000c100d000c440400c10040e03107500001080324040038141c00700074016030355058062250510000800000c140111088100304c0ea5494030892031a8040307808480001d401584000030a004000494500280e0b103000100350680c00ca59201c2d190002e41d001c2c008401d00100580300d0801c0010720406600054000d4807412221403d01e030361903003003900040d8201212011070354840005400442d029500510210401501c18104000c90621050300d24880000803941c41c1c0d075a07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 520456241 1250 520454991 520455007
    0x80f1312021014071b031b050907050a02032703030d0b010210050c0304320f0d0f09090506040b10050307120b2214090a03020607030b060f0a1101020f 66
    0x30008003914030449040c1080c0f203012041c200f040d240140240180300488200314405200d4800112800650740540707105141034001a010280340c1e1603108040c06001e980300031550a03801003003907642d13208e42940210b0501403c4540341004c0d06031090841c148189206400005850610092084e101880400b05d028034506000928002c5800b416040084c038240134414000c082d18116034000d6040f540d695542d505101d410303a041ca0301c0d0f0b13070301d041050311281c590b020281000c04c1141004403500c040e00d251144000e000c1d1000f41500c0c000c03030001044048280315810960340300941224001e803000480c2070182d40422252020300c149040881c1c404070803c44803da000001070a4840c1480701408940f44141c08920000540e08400d04a644050b070720403130300390441d400700d1140614014518902e060030240503880f03400310102500140500f130f0020310030902a0246042154001d00611f01c1d000c824041c9108035080010740000b04011503034030b409902c0c024009050801e00580102d5900d20607 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 520457491 1250 520456241 520456249
    0x3051213050301110a120b0603151c0c03140307050601090204080f0c091302040908070b16030e120307020a150e0f1606050f0d1404020f030a020d080f131202 69
    0xe070703400380d8482d030f060070a01c0f0500d010120540e2140444d41c2440c401102a200d1450041c08100c038036190001c0c4007008000954611203085d0002d00026100e6120b60310100310802125406110060701d55101900c0400000b10f80c803114040107040e0506503428140039a440604100081e841400566004241401006020701c0a1010f0350781c0800140068103c200206145a00081c0001c84040d000d0b20400d00703545072504821161640012000d55030801480c1140c0350350410340700f03040c800203000c0510740264000d22440320b0325003c12004140f03421001124643c240e10040c00001180038200d2408000f502441c0c201641039550300011a0006001e8411450b19120580000480d0300c48116001000140f11640c01a02c54524140f99140c48a02840805101d800c81040b03405103010b0a0606242c5103104060041c2d02c00c0b10803e09100c426810550f40d0064000040d601c003079103c28510014000c00e004242d80c135800c54805003002d100d07410035140b100c020b50180b01c1d84110101c80004620b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 520458741 1250 520457491 520457527
    0xf031201080309031e03040b042d03080d020f07140106080f070f050d0303060509070f080c0f0306010e0103150315050106020601080a1e020a0315050106020f030a0c020a030512 77
    0x3904100031403c119500000aa4900010030750f0b02e00245030300c454880c000343c14411030b0040d01040003020380e0f45968901d6402841c2c11086003403a41c00002c0d00341d200528488c6d11541c1103a8000c0f1405003064040700380e1030000e6000c0803204006120410401001981e02504800011150b00000400d5807600c007a4034100410030340d54041641003604180840382e00d20560b0303070649005542c02010384031a49810b40090880e500815400001c1604015030950b010325600138440c1165204075554135800001e007036500603404000f00a078418000100d080d442100e0f51010001c051402044040d580300d02e5144e0614907420a407400c68605d141e80c0e014000328003e142c0141403910050442d58904944103890b400e448000400381c0000080004002081480d902c03041350b0000e0035801c9080d0741e0b00d00500003000c2145c1c0c2110303032401c00f80000740080c004909d030a242502c243c040c52038003542c440103e400f0351701c800049a00c40315452012002c900c040200303140c0180c81004442d40d5010040c2c160104407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 520459991 1250 520458741 520458749
    0x13060e0f090d050d0506030f071511160302090a060302040c0c050c060a080601230d050603010c0305010501050a051c050a0e060a06031707060e0f0c0f03010510260f031201 75
    0x160142c600010410340c00f078125042d107001440001415110040000c0c145003642094032040e01c503078030002c60086021040f402110f1080d40712800b001280024154481211420481113008508801c00c0503003810200d01d64421145800016265102e60024045600d140c41040000f028a400481008800c11196240c028115031880c205600100010442c04c0010460360400c807484200c840300c8030b407115501503040450301206403a1110402c000005280c00c03030b0124030039030900f0b080d280160f01900c18207050300c10683da0347d407601c404040c082d0344a5001c8006c1823480500701540180b007403200d00c111401103810550100e01c48000014a62600300b000c0c01c079000145c0740800400c0084d13480009400b2413000c240c145511240b15041c00780c01800e00c0302c03450030a4000c00f0300441c42c020020429110007501181c00c1c8840ba420481032500701c3e08110340e980b100014001052009441000303240801086501101482000342c80f040c50402c100030f00e1380c42c5507070b002040010001200d40c2c00c480c050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 520461241 1250 520459991 520459993
    0x90c0d051b090402030d1b120c0c050103020a020c010e120106080c0405010e0f06090c09190302131e090203011e0509520602030c010c02010204032013060e0f09 70
    0x5401c3c5a00080e172200b03884281c000034020868050703041c541e1810318480100d03030021400030075100b0f640740241c0345014018007101c4110041d0808255513009109031400302809a00400410503410015203051a8240d80d00e94080c0c20426aa42d05082c24080c0001809080c2c0103095040041c10070710041c0c0e18180c0010203e900c001c01003001581c2e04a000c15802038084510030465202e02e80b0802d501c0c801c4860454212869034419078404909101040840c0e01c2503031074940e495690500d80c82260084225805502140f0000104154272600604178050008000144d04a03502030a45060780716000c1c130714030387c2c0c2d00c943c100001d04806110b8220280c046041d0295803402e6580700d05428180da9486544082d034405860040c280400a036200145070300800040f042c1c0c80301e60181d40d03900700080c3c441c0d0542c200351303111a0a034418001d4908a07503202d1503130710355030b803015407400c0c4c1c3d101c100b5030f0050b000441d150103104d006405014410003480c9082001800d4208006010b414460060401120b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 520462491 1250 520461241 520461259
    0xf3f010f150909050d0c030c120206060111030c0a0206070c24090e1005060d0b060406030207060516020d120b1c051b0901091d0d0f2a030503090c0d051b 67
    0x21070070110304160044070728070b006c08a4404e507280507101d0074107282e400b80c1001d50034000307203e190780c00054046c0111700c01d88032019a00381d240d007000e5891090101110356504008a10350041c00c000c80a4403855110342d440c000b0329034a5042d61004451840c1d1440d021100c021403100043c0d40011400c400717403e045030480310511348025500309401152051502915001820342c0322540190b02400504030300400f6140d82e566201c8000300030f900603640681e08146080e001c5198203e81e101d200e5600d0b0f09a401030820b9010f030050076620000146014481103441c7c400b00700b00741da25043d138000c0d000f140c8141421000041d090042c40c05e851801d1546180721004042c0d4699621040211f04450003c60080351908040c068107074175207880c0d841e8541c6442100000741e9003035041003440c0d0b03480c4d80070740d21031484150b5100e900c403088541c010341250b1154544050070109100e8001107034842d074044100c90391202d030b450100c0c00c103160640c0252030316044a0711150302c0303542e41040014030680c1201c030101e07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 520463741 1250 520462491 520462493
    0x2001050907150f1d0d0c030503030a06051206011403070e0702240f0a020c0a020603040f02030610060c0204020307110a05150129070c12060b0f3f010f150909 69
    0x81803c030500c40f04807104e030003202d81d04010380d100805222a81d60040410030800d03502d14000c2d95941054994407080e41c2400000b185906044000003000309015009000991809020000708424001041d03050b00a4202c04141030040540c060b0045145500a0868012400b030801d01003c0164224030421010414000c40c22845540c0940002c80381e41c005940b07085406106180c52055940250440808410003080c400102607041032039000b60309032207143e55044400214204140108008107181e803103108090304007503010f1030380070145080c0504403001c81c0b9070a6107006000c0c2c5080354940e00c08800614000c031180e00706801000c4990031a81c170401c90605254501c1c400c0f00740706a1844010540c6000c0c0005001c0840040107136200031442c0404d203080078009056950b00550254a00701c00715060350401009540450b044a407042c540c00400998028046007926003c01f0b0304032641440c0000c05100f07106694480700758071030001d86503612500d80740c496201079020003440351400742448 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 520464991 1250 520463741 520463747
    0xc100503061e04020c0f1f05160305041a0a0209040c18180b040c020f2e020a0e091602190f170706060b04031b152001050907150f 57
    0xb40d02000e420548582607840200400c000340140c10100c0958416019140001140880d1071041e10078070154032403041a000011009441c020780b28803071031004900c01264042d1290784040c2d0042d00c5806203e056001600744502100f005031803009060340d000412a05a00d440e2180c0d020801c3e2905001da44c150b16400120910902d80c03090340ca40f24180074400d143d88000303600401c02181d00800c2007101e503548420081d03858510700c52440840c414034182d2650964400c05d003445c09264050440480419030a81c08041c1d0031200c29082446404290b040d0603170b5075820460b200e0030b454446c3d0305100f01003240080c900a41007400c05140103450040901168a0021150105422110140b000d2910200d804c1c4188076002d00900180e10b00f28001c20140603e030014003c0b60b00404008110640340d145940c0000718a22414500b42000c401d4000c1c024050744809019214011180c1001038400707030304e03034251602240d104a940d0071040043c400e100c0000d010141100342c0d868011101c48481d0409 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 520466241 1250 520464991 520465009
    0x120a090f2607030804050609061e1e030c03010612090b04080c071d0f040f0b0f0414030c0706030b030a140105071b030906031a03010e070501080a0e03030a1802030f0c10050306 77
    0x11a010341c4000841c1130041d03e598044070f1801c0d1800c0b21040b4104030900d8541c01d150002f60324040ca0f80480354a100c1c3d100ca0380c0d429640603c003280106071859103068002d0714481ca009801030705098461a4050100310300400c0c15100d80d004044455642c250501c81d1810030340c5a4003d0507021004001c140c0d040704809210540c81030290511791380d59222424845513084c030010008020007800c00401100c0100204002d00592003a01003500d04041c0020090310f074090300031a841c50b40e01000c01085018400d400c01040607001905407225081141c0718408041599590711100c0da4452003402002903200703817105c2c0d00003a0222a4290401740340c0e00240340a0b400d11a440c05c25490300c280d1000c90020b14156180540d0040082145240c000940c507100c403450300c20580401c0050000441a0310107010b805241702212014500c0d607a039003070f007102c010100c0040c81803c43c01941780c00c20041c0c03010000003c01103002c1008100300e12034041040f0411003400f205004020041c014801c1c00d445030020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 520467491 1250 520466241 520466249
    0x3040b060a1212020d0e0d03120609020d06080712021f1202070f02030c0901050a031b1203390b090c03012c0304030302120a090f2607030804 62
    0x4111151948400620150741603041207005044404081081101c0101c402507081070329020b84828040102e820b4075000e480520858124070044d04c4d040010348a07000044440c071484400184140e150070340c09040f81c00203040c620700300780d03920f00c103104140c0d013005090000e00031411000d10400050340030801000c2c444e000d003140403003030000c0d030303c0424080e580616190f078141104545809150404141c0418290b0059020b40540380c5100c01c942000b1b22200d06a441c0540342c07080301e81c0746940398001d00e1000341004401004004012680307109520010352214001d0f074807043c58540022000d850810325850704240141d442001100b40b01a24460301f10b6181c0180b84950700f5505c144e1050b042c42c54100c2c82907495440d0860711108081204c444122603046502416110f03c0b201820a0343e0344140d01000c1c0140c3d024803100c0412050100080040103224540325003040d58840241014141513003110ba0708006e42080c0c0c2490724004034170140d944402d040102a074501d551164001c0b8880c0d405 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 520468741 1250 520467491 520467503
    0xa0c021c0c260f0d0612030504090b0909031602030c0a320f0114160c1412070509060a0e240f0d0303020a18030b010602060603030307090524120108120a050304 70
    0x144000c220440c40c3c0c003a6000b0700c0c103c85d015058041b18030f0001c200b40e0060140c1e01403d880d00c0801000740c00c180002500c19001c840c025890400c1c031100109036104507801c120703171501c50103c83c5409034072100c19450040c40c1c2a120754011001050202024480507903810003031034190750140d030180d5a000e102c02900d10080c2454080e110302184000410f1003850f40c500c801c030000d0070904c03081000d405c203100d0880e168104a40307c24400c5604000803003140015820080c0d01180041c080382c64241001500810003d01001e41c1c1641d4079541c01065400b12501c000601051028010310769a00b08a030b0000c002c221002070340d04003040001456070b03240040c0036040545c0403e0031641640910082c1c0042200e0760100310f9207035641e14040440783c10034020880140648804103505080c004283ea0160310389445051902d810201030042d006000c1044400f203003201e56100700310303410100007001140f052043d10141c1d0343c10900c01620385000140100e0407414100001c00c1c4c3d846d40641070b00e0308180d00031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 520469991 1250 520468741 520468747
    0x80f0a021e040c0c06060f0501050702060307030204080a060203090d050a080f0703020c07030f0515010308030f04020102160e04170301210f0503040b0d0b0a06080a0c021c0c260f 78
    0x40010107425a0118480c2c0c02c40c0c42e2009070210107400041202820780326880902c5540e4598410a0003a0903510070503001c114244082801403810501960744449186801801c06136188581c52410002140a03981316500000b44a6820002c0c00b00740008029828103a1500d090300340010040c420042500200c2d0031020040f0708241e11030f804030360702c40d55120116000c1644a0818074414451048d0403070b01072044107164045680d07000038180c12660440106419950b92078060103015100810032070440c0038140d150030741030320300208403030181005c1d805081c0185814a4013401c1086c00d503039240c08984c424401040062442c040c2c406032064001c00107005001d484ca4440c030042ea00c0369000307145000104010039841e036540f010b48400c40301c0200c00d0091030071a40a01c902e10405018550019541500040010020380c01248207016039204842046080d0031038038542262390380490f400600304850400910040e0f070326a601c103104007400024941c4100812400c3e40c4a01c4820102c014008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 520471241 1250 520469991 520470019
    0x20f0a120608120406030b1e0d15090f1a04050601120807020a0636090209010c052a04050105030a030804050304080d020c0a120f11060405150d06080f0a02 68
    0x68100000402c000350465400403660105104190864010325001030329014140c1e54500d04103c250f02c0668200004000b030121400900ca1101c500d094243d0f0581170000d81c1d170101c0803051242c01c1c5860300810049452200910700742d01c9400039550032001070101c070028000800c80c04a01a81111071b184110100030710f00f0319090526004042c0d002e036000090400000d841d94020b400d8a41101d90101c8841c03800241d1404e01d0490021080e4042c40f0454035401480880829801442c0001050600364003e40c0b542e41d03000e20f444942d4140a2580c48245a0074002100e80e00030300100b06c100b1182408258102000f2950fa6450150061304100268003c03c040c03180500496000d00030b540c0070744000c00d1040ca8043e549807001c03944d95000d0100e01e08000342c80b02d1000d440c0030300c00350310101107444040341ea10360801c420890320006a1002c0200000500d55071072200d2a2601501c00c038026031101481c03003455048800a44c0109090b4100d00c107400360403100403500ca03e40b03d5049840e01c102c0326030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 520472491 1250 520471241 520471277
    0x2010b090a0515040e01050708010f08100507140d0912260403170a0608070e0411010320160b0c0f040e0901060f080604171912020c0105180709020f0a 66
    0x50314000e0b04903107845c030380040c008010b40201d0f10078030240d2140b0b07056036610603428129841d40d109034022030704400000700980505800c40b68000741d6a140500300c480c0401300d10f00c400d5210084c003403001c1e69142405400c00100b036010583c00c0350b207030401c400d219800c14000c402910003403031000c0d110001400051b04040c0600d80e103421526142e00d80e00300030b140024152000f844d0074001c0901074030942c100003a8201146011034415580155100102c100d54001035019004071590f0300c1140c442032420f40c880c02008000350041c414038450460b139031810b60610741000507001d000c046541000b00400b50301c54801c0411603040b100d5080095110780d032850503882c0104540c0d00b00219500c144070300000e901c400020706900881c0144034041e03015101d2849046184144692000036070300a05080c80c59034003c40c4a4004000301e11405403034030000c1c3c0b0496085170070407112450880c010460050341c80c103080008601500d8064011842d00010f4010103446028a01c140d10410010540703c0c200343d04 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 520473741 1250 520472491 520472521
    0x1103060a1a072307090b010504050d15050702010f0605030313051c080a0c021003050103051905030c07060f09060318170d0504050c0f0f1c05030f0d0603030f02010b090a05 75
    0xa00320741440030f42c620815048140c02140c0c0c0031035a107486500408540300000d48622190400e0503101e251800385880148004041031510a580c1e42401c1c0c8046908501180506442000241e000107180e410161403542100c0f11500428000e50061107070700e4040307244c2003148050b948200c40345120030009580344444100140d0005000f601c1c0400c80d10400c9400820b0400c0052003241c20304d0a0302421031049040303400c00d00c800f0b02260300c05500c0050300052440e01c0c480440c00b45041d64503080081c00101e103030000c16401040000c4081200c182c4480d442120b407070152100c0d25090011f841030f6860140c5030302c55280301520b40e9115000903607442140c5000c890158a03582c505004501d024100141c03101d03c0782d400d4a000b2900601c14010628185c041e00c2c0c41603000415820344c0c03d005100c51070a20400d007108072110b01c020440380540d5100703003004e014982c04640011550505614000b414070710071541c4a02960306140c0c034400213984890209501c82141c850003c0d00d40d80381007030101885 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 520474991 1250 520473741 520473743
    0xf0b0c03070f2f0d081b010911010e01090e01210209070917030f12130f08090a0b04050102100b04060b0406030203040506060904050316020114040602101103060a1a07 73
    0x16030a50780728420888545051200700b0381510720000c00080c0080d0b41c100340390340c0056503070f130080b42020035400044502014121103801d80403400c5107203c10444041c00c6406414003960b1071a000c1c941442150303406191300307060031801e2030f103403144600d8041c506000303006c107008200031051010034002441c0320314001070903815001400c005690805c02405003c0c0d2450b401500c1101d206584140c2c40c0c40c1000003210100f815041d441d07480d00c0c2e00c000a011808502030609412401c0038403915020234628600f00030304602402000d03680d56040c2040041d080695030224a405409010802035a80c001c9030120b484454250082114803070080098020701365030700324802885000c40c000c2005a4550b0107140300d64422400c440c0ea6848080802ca900c8400703c0d0003c0c855172040043c1c1c1c641e6424000c1c04081d00d0310604000c40ca404162510201c1c60b000398003e8001a03220b00d04003d52000240645922400403001d003c0c034600780640898031040d2580194000310340c0602d41024804410022aa03101d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 520476241 1250 520474991 520475003
    0x10504060f27051204270e030913090203030708031905011a09010915030c110c0a03080d11030f150d0b01060f0509131515050d0504020102010e01140604060f0f0b0c0307 74
    0x17468860b566030101c0361941001e04210441c0e41c2600c990300000348100c412607509940154102808a0200301d02e405218103200c00c69500d8100c03c1c001614100003420b01d151040c002291a841d00708004003101c060340c50100000c605002c01041010041601c400e0b107d4020140603960748020801a00c083d400f5921000b10306031030074032a50002c1d60507402030441e00c48641c3c88413004184500440e40d12907083d04c56942c8400d0282080002818510092056214907000880c00a1001c048440c19400072503102c10160320b00010000700e01d01551704001401d05c00c9941504404c8182c54481002c001401900d09001801185100c0640114140c0e40c5002000f001907441041040284020f0145039200c50254900d041c00821460020380840f070260f58140d03542401c00799a0030104014241c050010380c155540d03100f41200821003809003507074030f540741c4000500b84e08101040c0000c03181c1d254003007984014900c038284042004450301100302c409000c05503454101c501205030961107210703001419 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 520477491 1250 520476241 520476247
    0x10b16020907030e0706030213060806030708010c020c1203180108060a03060e030a0207080607300c0305100501020106051807140304050a06061a09010f0e12010504060f270512 77
    0x1803585600900e0841d450141605d20b4a0780d00c500990613401000c500c401c40845c4140107129143c842c40100e40d01102c001e0864001680c1c0d1928039007180c0c007948580e00140c0090b00000400e042c0740c03082111842c2c0d0440194500359001d810381288071050301c4941d042186601c0410442d0381c86100e5040a1a00420708000040c04007684940d00e5000b0464100503000d0a4000a6000b4022071054402d0725592600400c1112420f880c24000400700007041c013854403200030041c400804e20034064507040c0760305c0014403428a4401c40c032070303411580d10441c1103a0400c070301401540c0340c10810046440c2240c000204a4840410644541113a41d000d01644800401004117205001a40c0000030380a0340302000180d403a44501f542ba1100c0061425840800b000f00c48140e52103070f500d11f00e22041c9880d00300407402a91000640c0000e4016800c0d505039121814041404494481c40760b100181c6802000f20390007101c02240d400d03001d9540c9050071401100e1002c20302c078044c0506400d40d11f1042070182c3d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 520478741 1250 520477491 520477501
    0x1020f030a050705040302031b0414010605030709080d0f0e06071e2a171f0605041817031009050c0c01200301090f0905032107090e010b160209 63
    0x124540040360890407560400c0d0104545a02400865065079001f401410141c440d44141c0300c1070102c1c81c007071035400c540c0d20302506e80310840f41c0300694041c101c0750f902d00c0c0d034070300b0540b40040025140360002101900250070a480c003980040c018010a5001d0601d0302c0d05a21003400209235005000c405030400310010326805100355200c44240b135030f910548644c3c08034030201007600e0b680300404041100c1c1058080c021301221040f4604a80380800e4001182c01000d040342c2e09007001504219807841e030548407101031043e403802d40502200b400c0018a08007402126071500c203200412140c0704c0c100d00a000010410103800c00b4072100282c4940c420501450412a1054202c1c0d8482054000030b03510b0281c400e07180843c4000c16401d14600c1c0f003040383c116401c3c05107410081403003601545240b43e4404c00440010800e0000d44190180c02d072100c01110400305081e500a04010303c101c0c10040c24080520201a4921909054030444a11075846084c2e150792156100c01c081d1020f903000803d501002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 520479991 1250 520478741 520478767
    0x92b020f010e010504021914040b0609120616051606090302120a090e01050d050a14010b09181c0c030507060b0607150b0f13230c030f060d020d0b0a0204080102 70
    0x343c0a14421b5501241031f401e00b80040715141864002c004199030840031400f140d141c980c02204900200521041c61711400400003140482c0455084545800107800c001c1500184114441610807905100d45041010700c00140c140401d500d0041091b40d40742c80d0703002410b02c2041504590f112850507a5035500c1058405030005d81507204020180c842a00041480c0c1003128110141c10f0f030120007401042c601d03540748081c0c2c62020305482802d41d40c0310154082583c90340d107070500801c0320115424042c002601c03028200710551046d040760b4080c518555400a0303003c140301100c1034240c540740b5103078600c514140001d08001403403e644224046010707420300c0310304510600341c07100000f020001041c06100340b2000fa071503284401d0b03010f482c68031011014069500891020302821140216803403101400c94850501a54000c80300300d004001c02041154081d20a6080380c0120b0782c01c103525205034000350b01c841482c2401040d401410b4040f6140e10b0150f019940680007101c0290b44950000d8050 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 520481241 1250 520479991 520480001
    0x818010219031b1b060906020d06061d010e062b0f0c0f03111b150f041a060a140a0306022212081b0a02060304031106092b020f010e01 59
    0x10400040c2003c1c05025424040c1c0ca4031041ca0402c00c000c0c2d4885565522400010a04030f03500790313140c039000c00698030103c0300c503c80c2801814503900c0c0d8425642501244188d80c22403101d0315410320884244090f072966451041d1400c00883d2060294030440d140d0a614010084520a400003802c28503509502c81254100008a08043e6280b90603140b00210803000d88060311745811521004100c1242d0410b2140400521555201d045420401c0c448110326000602103500f0840c2082d0301c0e041c8010001003c0014540038040028003c00e0f0038080c0004440308404e12138014003003910058542c00791140444240219005041107403100b0044071101c420801c60314030f22103484821301c070100d901240707580120703d115000805507042c03983c0007200820110740071004e010944030f8405260010307a110002184a20702c0b03075a4955075403440c180d0183c0741c950054800413040e0014200c0401030b08020007040c80d04c3c005074280701e841c05c03851b0105030f0a01c409800117014a5080404ca460105015000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 520482491 1250 520481241 520481261
    0xe0102010f1119020705060f090306090c090c21040302031806070807020f01051e0706050a09050628090b010503061b0306010c0c050d0b0a1a01081801021903 69
    0x80c0140c140003800e0408554566821640d400d005211000c40700407840e01d03c40d002007541c01290b189648840c00900250466542800040c20024252440d070409000c1950480c0b5010020010710340410001020310000a02c3c0c1382e89031001150500707209600810600f41120018120011400c1905009490348e00c14003042c00203034500c4001d050903040000c2151590740e040345540c0c1c140326080d800c025140d1611041281004170510078130074090500c102a100c40245030307003042d035150110315120055030001010b2401c032510b40781402022075408262141e000ba000161804180c100b002d0039100241891070090555151440c407004200701000402d050300c80c110200d404070740d207210702a400c1c1030b01102c03040101c05051020072007550103480c0300c0524510914404444640316004103030300112101c030940d036000011060040702001d03846200ca490b42c6510400b07402c1c1101e04006840b1b500007400c0c0c070341c0d07001c0c46078041004a40b0079415104013f2035102401c0009894401c0200a480d00800b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 520483741 1250 520482491 520482493
    0x18060108060d0b040b0903090a090606080105010507031215150c064502060a080708012c04051009050708070801061802090a08031c0e0606150c070f060e0102 69
    0xc03070190310b424a490490070780e010340c014a05959595800304200009001d078122840103000346140c0d5502c0f40b40d03080151a15010000c1c0d60340c60302c18014132210040c0d201e01e040c0301041003000007003903000520f541108050b279004104071043c460003c540310b15a0348801c000e2000291402c0701c00da0b00a0020030386c2c501501040c8016001c2c508a00c080c8c4041014080001440403581c0c813858606801000200762500c950145084507900416041c5c2d0000c1224400940c521003002491034200c0c00305800b40c0780b03d402018440c150031844980d080000c486426040401800080800404000da036680c0d816804040c00003c8040c540341703a541d2650300641d440f45c0600c0c5808505684144249400c4500c100810541b5a401c0d0f00890f00941c00601055000a174624000c21b142600700000d05400c1490030302403035070300301000c3c06404654840c502a0728035085141804003070380d02c4080130b0070311081100102e956014600c90140c50322520350b01858481c079001100040c407075001410b403020043e080e0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 520484991 1250 520483741 520483757
    0x1302030709020405090f1e0f0718050a0506070501020426100504150507021608030406020706090302060f16061802010813030903150e060a05010f0605040303050a050d0b180601 77
    0x1c0c1200d040e030149002d0290000710f0f0070000381d00c0040c4c1410f5690429261a002441d610907822126442c0c40200c5100445821440c00c2c408500d0380150300004110161420881a5060000040c205009441690700c0b400010500c0024030400b98100c80082400303420340b08418004070710800d000b175800f0300e820303031035024020004180003541c2c0035a42c8104d502c0340d041c810401c242c40c031250061001401c0e040852044084407071907855090050300141040380c0040d43c440e4940000240341c5001900803104000d640c1c541080107031200030584080d03440c1c0070403664964840c80d0000051503032076000500020705210508074480411204c28080d21b000b82e030b400e1003c0d0b03a4640f10103002d2000043c0200043c1152000b080842c13a920f48502c0c1003400040302284003c26004082e181c1a002d807147c0704001d90300c500400c1101010036019004000909100781410f1175a14054420b0103884c000b10240480050032020642d140c1d4016911510020701d4180d088040c400341f034100c0b22044a45501282c649 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 520486241 1250 520484991 520484999
    0xc03030a0f180b13150f09020f1909020307032306030105070e03060601030c0e03010608014107020307060606030f151505070503070209041202061e0117070b0313020307 74
    0x31800d12000d050304803103c007140d500c640071070003207510891006540c801c03c0d0001000d00d00c0e203d8090203c0d46096410085030380a00c90041020035080c90b034005100b0542340440c00f03168034110002c0002c5a020b00c0d00143c1300e5884800a030007034000300b480b581007400c030f0030032000c0441c00d034940321401280150006c22155480007401d0341c0e4030349030801f25541a407200d00007900f13540c42a00a212540e682e407034183d080000b0900800c9c02d50315950032080303a50751030744954060280c40f090411100c036610700c0301428480c1044108018240380d0400c288040f0b00d564006841c2074000c00403646a1540217030100151695180d000f4024050745000e46a01d40c242100700c40382d8031810f80000291404032040070903903031040d4000d40303240e80440f40c11966400b003880b0701005a500c1c80755061045014010050b0441110040241050801002070585100020003c0503c50401000b14151007005101007140c2c0d118038003042c5000b910303601c4400d8521001041042c100c14403844a003080f8400d40460786401e440b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 520487491 1250 520486241 520486271
    0x7030c03090806070e0913060203010f050312250f17030a05060406050616060f020c070e130507050d060914010b010306090605150304080d020a0e01320307050c03030a0f 74
    0x82d10444001080908032440c60b1908500307807034004207240e2900ba2188219948c40b0103a8009a002d500c6e80d03c4140300400030b604003400b5070180f101089a04a19100d00c1c4034001c001c200d40103110030f95094400c1c04d1142081008040e41c02c5e6650084000e02081d12881e08450003984121138950489040101140b1a400d05001d82010340da00100501d0411901c03524000d403840303d0b2401a03408a48617a44c182060205100401359205610080c1050f00e0803c21034002e00200505072140e611511256540800c0c07022480000341c6008496042551409080c124041c02800303e0150000400401c0c0341c2ca86403055100040403070b4207881c2400301036604e104500486045102e0190082c0107074848441e00782a01c002540d0080c0b241c0c0c00c050078180c80b185000c0490700545003a10104900000042e002d6801100300110710a810341c031030b000c0745512041e00745240e44140000b90b18a0022000c6103007140120152041e040441c02280d4591620714840b40280040101d03d061140c40c040f20503200e001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 520488741 1250 520487491 520487503
    0x14030307211d10080a270605070507052e0203090105010503070504060803030609070201060b0406050d1503120c111203130f050607110307330908120304110607030c030908 75
    0x200200700300035940a203c025a8480310080002124650314081c00131281e04810f01082c07400c01000030700e840c00d1400c1c9404800c6400162011080c0300c0180481310001e440001d4060031140202202c508040f0741c0074440081599074603140e42d0450021042180443d4150b012a040310f40032070440b200155140140011070320a13000d02602c130b07001000001c090342041d01400345c0094403440009a9150307600900070284c0c0142d00300b940050ba00045510100d40c5074020320300110b06840e499000700c2c4c035503500c01c1104000040f0310760502081a81c100207110034808502049280501070216450301203240c2614ad610248044032442c6c0b0b50040800c0d000c00400d0004265900544210301e032404985030400c0c001d03400b400e803950500c0348d5500418502203a8038203841d0100c24018005001c08450500303160100b6240c0c00400304242c090003000701240009035140400014102c1c1c030394030744803414100d01405c0c180031202d8106900007506000c26a000990300c8000d4082c1c0d1701d07070400e1902c410700305840794 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 520489991 1250 520488741 520488797
    0xf0606010f050403110a03080a0f08150105030a05061302040f0e10260732090610261f0e060907030509030c0a030908070902040b03011403030721 64
    0x2c0080c4028130008040f50182d01d980303030001301014400d0b0f0b580c2d62030010303541c011018100012402c00080d038209402440342504120302e04d1030000070002480008050740401880c0d164100d88030404100ca5403900f603260100792031104001c2d559245c07200001c8550410318400c1e00305045440002a403050380144031001a201251440540c11909580c0d0400450b0709150700802d07405040c0b00000e44954082c61520030902030951343c2d4031043ca08007001740620800c003660380070b04074503c10404680d80d1120484070751003003420300b03c41070a0700c1250400741041190140b9851807400062001c00d0950300107400001c03d214000300d5078241c551140c0040010159030b0641c004103c40302242440b4000d4020030f070700100080450b0700b0b014955043c2850022442070a801103140b4240501100d4070a01030840a0180ca0342c0541c9058a440d20032200f5110512a0204008d6565068100c80e074050040303964144c2c01494101248903000b03000c800002c50f94070068003240d0084407210034203048000d010b02103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 520491241 1250 520489991 520489997
    0xb030f0d09230d031707020c0a051816051b0601090e070e13110d0b060915090103060c05130b1c05010509071818020315030a080a0f0210020301080f0606010f 69
    0xa940c0310018060203e101c07210440500c180d0304001c09080c091080190300c10140c40d8020505941c614090020201083c1c00c4540601d02d034007015903e80031044422904500c002035000e07109020b09104a90900504100080061800030041c80b03c840004039035060760f4040c041000050360501b00181e440c2898400c011203000d49000142038000d511404500d0240106644100e041148000402441c45210122005440301040c03055905160b5a900d0340001c680a55003801c40a42d800560060414400148420703119200806a98030410a96410070000c0c100c0c58069038a41030380e5030313580d0400d40c10811403941c881c0d050400031140e40140381c125a009015120540ca4a14046503005040280b0140c0d080d4050000070b8640f1604000c04a103501209006032030741000c0140d000554040001c442c0719038070010011020800000c120380c04c00e541401c04850702900498141e0400b2520900c04100070f20200002561182c0070440005c00001c00301079400340c2c3d41d140d0042d84c1d080c0c1080104400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 520492491 1250 520491241 520491299
    0x1b0203042102010504031509030f020c01021b06071202030705010b0406030c0e270c0901050405040201020309100306120c0305010b01031a12011e0c0f0507051c030b030f0d09 76
    0x1103040c080ca00e1503001c60040c50001c2c50180c5a45078134000041194019048954903c0c403401030546c05130b10000f6100303080c400340554404020000707541d40e4406140e2004444a6074401c9403079580c0794200c2d0120340e803022600003215000c2c04003949030b0300550015100e0707500380000c4401c44e04d8940326030010369034000c800f891550308051381e82240c1d180081104025507149801d040460142c15408010a074803e0024910040b2950902901500c103a010134003503400c1c0400d000040c0c1c1c001c0292009110155110500c1401c2c0c688102c010348940d40c00041500741c001951000c3c07083c1c1513008030540340550003d00a01c0e0000e0011022680d0745021110650309503929507040d45000c0e03d1071202001c0348800414041020101104d0540110240b40e0382156109414540f003500105458a0612141806c0e41041142c0c3c07142501c451301010f401c40c1454020700a103418a01075407110002030009070885441104105410703580740d88400400c80804e48001000401c003a0000e0301c0c4165001034606546 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 520493741 1250 520492491 520492529
    0x11a040305070b0307110105190e07180c17011509061d01030e01020906032a0c030f03060414040c170a051b031e0c04050c070f021e1002011b020304 65
    0x2c1030340c002170300d0142005007841150003503910901495004a4840f82d2141e0181e004003070440480e0500220550b003504489e50400c44071440d400311040b0300c1d40c2d20601040c00c4c522500102d541c4140100d00d03411100c040c0c400802e6107000c3d41c14045c8041126141c420100d51907840c1524045200004000403980c091490802c55109401412021005400143c03c050714200007500a40003180c400300c2804648505c0700c02c5a0911000b031407084220687c1d245001611907030107484e4032813410690b031022030001c04a82e090303c6e582c2c002c00c0500c50401c280c41e06805c06242403000c014491144101c0401a07020f15031240902080150000780d002c2c00614a40c1c4040a00a1032414820220f80d814000c403008036107441031050400107060f040101921900051404100403104064141072441c4007e014020005440155100c091501240e55400c44901c1c40f00a24020303228448140e00014a81c054064030740d01500700081c4d507010760200f183c3c400389d803034400c0744c0e240581d100d0300b83d00900c000c20f03d203 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 520494991 1250 520493741 520493759
    0x120403020d020d032309040c030203070903060519020c010c032a0c05010b1c0b0c031b03180115030209011208040b0f04081e0d0c21030b04050a05011a04030507 70
    0x1c001d502c81e0034801049508418826011030040302444082917000a60122615013807040541c01103460030300314254240a103008001c0b244030b02006003441e580f20081101c07561007661f0729942c1d407102e0000755641d40890110307074040d2803171071201d0000c0790506405c0184107100700c425415400c0d440c06011012002c0309012202032008010a80e030075517a42c2e141140d15103271904420a101e02078001c0c045c440c1818588200203c10013032000000000c00d1003800f0107400b151010410800c5901090383c0c403502e84d40f10300c6522940c3e161034900198600101c021495148030190350859000303c0302100c190703a0381e2407415080c02c84a83c00602002007040140150b860540141ca0301103001c52049042030b4450070920b14010041349082c030300319a42058042888010420184161824036005114403441d030f480d0010389912501b140403174084586500b60552180d400754024402c0104140400d060a10801c00105028014060027075944440e241d000304000003100c003100e920400812446107020740309 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 520496241 1250 520494991 520495009
    0xb0f0f0615071209050a060201060605070807030210060906081216030318080406030906051609030201031e090f0507170601060305060109170606030c040c080406020315130e120403020d02 82
    0x100c88040002c0c081000802d040c2e02452056500b5070b1166036006040800f000310b40300017988003030110382c10008180700032a0f01405880d81c3d560702411030f9440d130415250031f90400a803001d11200c0b05151400000706034100c0e8000b5000c07210218141d500d00444190502268402d550441c140c1c1c420030000000020311130307400901e0740c0d01042e803481680d904a5031001c000360300c564000e0002a4171a5809818449603100c0d690700141180010180c0d603200f2200580850021322001e81490346d01d4a1401c500d08200d2002154000c942a003000308440918040ea5001c8400303038203072071921a0350008554a0b060500302c1c82c031704e00c160005106076860424100c0140400410407410090072110002d082030a240d0b1029080000402400c0986090030905151000ca40e40281c8903034140b1200402c6e00e0b410803c0c2e55045a080a4003594035900e817410000c41001d10403146800071810760500c1c03007a0700315034400390030548410b003078600e21820300341c0e00b0000d809a800040d61003032140761344c1c100502d414284 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 520497491 1250 520496241 520496269
    0xf010603030e0f01201c0201021903050402090609090f0709061e180e070e040501090204050c16060e010e030a2105150d110a0602070602070807030506180f0d0c0b0f0f06 74
    0x407114004864015959504603400346c1c200982e40208100c1116202c07030011a42036165031a041005203010f03000152040005024103005680101c08650303280d2085c0b2007203070511410402c444000d42d030380780130030020022440391101d800c0c5414144480700c0d14454081c2c08555054070102c80240b48003c0c10001404509072504d510f00c1060130010b00041d030850010b1013907010340000034543e800e900502c420340b00010400c0d14810701c10868000c0c1f12a0702044949240e81010f030004d1000c1c00780141500414148601e8401444045801031034281c0c4011010070002e414442140c0408149a406d01076450660b45044003404103d60701c021070a20701d41c030440a600500c80725910400800205111024603001080140c0100d030090004680402c5408010300e107500040103468170b1926020f07251040601071140011840b50a410b01500401c40082040084400d40b400b1714590100540102604602281c041080d403002071001d07a2050300c45845440165028481681c85d101004960304505003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 520498741 1250 520497491 520497493
    0x20f03041b08100506130507020d0c02010905060d02030709082803050904060906090b060304020f04090302160e0a051305060c090d050703062406021b0103020c0f010603030e0f0120 79
    0x41c000907001800c10007640c0304002e01c9400186405c0100a200011019004a0007020300704030500021590000341070380b5540c0d80b1700d848041301c000d6100484003d1060362100e0350146022982d070030380c40ea00354000e5000d1545503c0b4802c407140d4550741c045d00d078000440c401c40b50907207070001c961540c805250300d5a1418400e00c1c10502c1e00302100c001900700c1e007503900003203001607a0710400d0088884034840c0e00340414040380c0450852030103030f002542c0414442d2010707016580703c00100040600800c8103015411184000725600790710741900032000c040031103019000504210100d442401000c150a000c01d03045400343c11660b5465580340300d1584884125508252046040c1000c510b041c030418001d075200700d030042800900305141d401c904e480c40c82010b600b48015041000419000038906140d0024030340302d141e04640e20740058009014695095500d0300030311900c079142c080103500070340c1039a00c030303469a101d440c4e180303030602c004184198101e0b404102c24a2500d8141108200400c1c86441e00c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 520499991 1250 520498741 520498793
    0x6240804030e0303031503010e16031b0308070b060906010c03120b2422050303040e060d0f030804030f0906120e1e03070c0e0f070804231f020f0304 65
    0x101080c0b1350390045881800003020034032488a0b9103002e0103580c845501460003490400b01d01c400c201010245840700800e19002c5000140c0e07140745201c1500020744d002520340d0744440030b07070400808900c01140c4445c0309107071000006440758003030360940d28056050790742c0d440c000d412204850000e140240e0041e81c0004620032a50000020b0030350800ca1446034500b00f511903260b95030020303954544104650b2070005146041c003080c1c90010a075822107a518a1203900d94861f02d02082c010301e5005c102402d0010384540b86024950810101801070340f196441c105072085090003211112118059400040e02c0c200003d862580c064210700011056801640d003441c110b080d00c880a800641615140c03500045120010300000c0d4a090004120345514886940707400d8110100e503803070080500060003034240110301440b5481c241301c665000c10041d111030b40c4a8000d01e09545941c0460b82100000820071084113900b403e0080c1d403a40038042d01d40c181151600e5940003648643c0101c0084880104 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 520501241 1250 520499991 520500017
    0x703030b0a05130e1e0c150d05041101021e030415170a060f080c03030304030503070c0c090b0f0103020c0606010c3306091802060309120d0509010624080403 69
    0x7070060f60300301c0d481500043c4a950702a09039080c105007014442c42c502d141c0c030741160440c1c008600c2000c80f11007160900354003100402001803600844050002e50752034030301044100320300c48d07040000b028026000c480907049010714402c0700c2c0e40c0c0702c02e01c010550400d00c030802c00598042c200e11016001814aa00003036586050345150510407248001c1070380d01d034841044941104505200a446003a01401510090502207030b40c0744000380004003002800070002e0400c512803020b02030519401203842c1c0b00c403582c40d103c080103003101040135845582c07642083e07400c560280c4201d8505001940142c401c540d200c000554a004d40351409a9130310f5030594800005100b4092081d80009411040c00c140c0624400118201c4020380c00c01c1400c00d00e03100c00b4180043c0d04942201841e541180c020741e0700d0707680c4c00000e400c1c15100041c10000103004101c1032290740301d07904150702c6858403000810626a40d0072043e0850150003040c81e500320144509a0307412441074404541c0a030103810f10000c41029 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 520502491 1250 520501241 520501249
    0x3060a05040f0605040b010906050316090b122706040809120316030e06070305120c0906070f2604060c030c0209040506090708011e0b0d0f081c09080703030b0a05 71
    0x11142d814a009556100f05000300e1070f0902c03400030a10300038039102803418100700d0003918a1001810b2088188030860001c202a40718800b07050141c991280040c0d11280c00e140d18440f41c02c402d42e801c40d59100d49191002d200340a0501450701c0b01380d400010001611261210361655002030b0780581c1141d5541d070b0301c404c00347c400c01c0200b06003906586940015030072400d008141a0800f0b282c98800c0ba801c05ca2000820390040584c1c610346028010008245c0b640400005d151041444540d080030300810003a00b071040d819061120140210600c04440070341506d81504660802c2e004170028000f48014444d0704c0c800c400c001200b61003402d004612001c203030002141800c003102d00321442e9003e04c040009045003800043d00404e05400244440108000c10400901c240208480c229079126001090703551800c80910840c5e0b08001c200464400f1401d01d40c03115400808681c020b268024003900a803111440344000c0e143d0041462420404556000c0300944103c4020550142820502060b20b0791 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 520503597 1106 520502491 520502501
    0x50114041220010c0f03051509010e07030f0219020f2b170f04021f080403050c01201305010912260a020d0809010504020a090203060a0504 61
    0x51001038141d615842d0100a1150341c00c3c40040c407003080d00311240345011728140e03078207000d00d64940740c0d0541003550131002582c100031910010001b002c42c2c00402a0030132101c0c40c010882d4008c600c115030982e006115148030b03a4445454410078950100b04041104070864058045100313055600661150282040100304c41d2101c0c40f400b00d030f80f250f640400403a04101c19120a4108000010142d55007254200c0c00381211102c0002100c504114100c0484003a950303a20f42503403942c0d411141c1d038000c440403011541d241c40980d5400c510700380e0340350619030300001010b4907454541100f10210030282d00250511030480b00500401400ca0022010b16800c1030400e59040580c820305560896803110b00d034000c50020520800e4142c1c041840a60207a140d5900d01081d00d03044c1d0190b007244c2c019034000754804000c901c01c010003092a0051507111800803d480c00956891000c1307400e4070 = true := by decide +kernel

theorem cover : BRFrame.Cov 520323741 520503597 := by
  have h0 := BRFrame.cov_init 520323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 520323741 ≤ n) (h2 : n < 520503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
