-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0779
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:44:13.097946+00:00
-- url     : https://prove2.me/submissions/2f065203-6ae7-42db-bfae-58c51f50eb39

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 139928057 ≤ n < 140107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 139929307 1250 139928057 139928077
    0x12071101060801051b0c10050a0f02030109050405370c0504091a06040b061b0106082508030a090302060f13260106051c0f0803130312090c0306020a0e04060902 70
    0x202404000b17640c9024040d11107943c001030081c0815000c0149100103840b01600807501c45e59661800c44200c411400114080d0810100c0401d040c107103443c00c1e600d0260607203403212000300045c0c4450b5081510302e8a1886e000314110301e883c01c05a01e030501014a14081c0c0c41075a105240c20100d00c02c001c50b240f400300c0b001c001444040101c1c4d9426050000f5648420b02d005e6101030200b28420311218201e41003d1501c0890300002806504d0b5038003503207403028040e16510041d0b42c81241d03000084202590b10b020b42141c4000c0c6003040406d1201400244090000a11483d804180c445a00394800141c40084a560011500c1c1071b03900d40d102c001241c515141c813101100f5001c0d5081c0c014405000d40b43c2164000b8000490304071a04010b18180100f0709011141c40341c4440d46117020500c4640a50300079000880105825540d6140c0600401e00148400903a2418003021402080c2d5080d07120b412a600418050f0340c03a80c100404076a03111740b0302251a4050302d07203a0081018421a07002d4807507644 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 139930557 1250 139929307 139929331
    0x114040603051f0b16110d0501020309010e010603020a0303050c0a150204050f180705030901090b0109051609080604020907050c030703090806100326090607060f0507090305031207110106080105 85
    0x95000c02c04010300224050126840300401202545041d00141140034a0113038605038280f030201c00016590744450f031fa00396a01d079000300c10b00c0b210703050a20411041d00e40980c0200079080ca140d0129038012228480074041c40004101c412a15500784040050a0380c448030001c0c02245c2492198001c0d0000e000d554003800300c1400c4d026840c242514400403101c910115008140d80300340b8110744650001f000030481d5502c2e8110500000d403140e00044c080e002c507100104051508003103070a01100f501841c50304004909000704040c0ba408038507a90025010b48087c6150f81c2c1350b920646403440f46c217035034240c248400148007042c182d100032040256500a0150b88013a2078104885c0032042d01400054201300e080091100e4214403682241d540d995024221030400c0b0301000003410540102e4000d88885441d4400300070a00c01030301c40c07240d2090711070034604030ba241540c994580d07d003d89080308200d40e01c000d01141c50070b401030700c203040142c00308070081c40029200c0d40280d0181c001a10b91804000d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 139931807 1250 139930557 139930591
    0xb011403130302060c0c1009021516140105130f0201170112060608010e030904021804061e210f0302010b060a02011508030c0a15020f1801170411010e011404060305 72
    0x11282c5c1c2140c0c2c6202c0040001c5c440300900c4840c1100820030b038074040b0382c800e401e6150020203030b05600151410b02c400000410710300505050200000949001603d2240d01d0f103010440d80e03180b6001c507041825040301da4965074000910040e1500344100f1640c0742010042c200002d4502d805c41c00b4140c1c250321521003070000750742e14250142682c11600b507600483d0424010710103542020b50140071500010072000c01061003c00c04602103549e60b40128290240c0c0102400b04000e030b01203090300503c110890042d6201022455514842d84000c005041a40d80503440d03042c14800d4201d1450b212009000c0c0769100c004100180c020120801d00c584070040a850000703c403500401650800b4003100003a00100005179526044a00300203141038845500388000707409071200c08054080001c1031044081d00d04480307030002d0445082940800600741c24641000002580001110500202802e200f0400c00d000310059032402e03007000070849498800b081c0020103a5068204500510340602e0b00c401c80 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 139933057 1250 139931807 139931821
    0x405010f030621020310050a05060102070609030503030103020609040f05090c03010606020106050307120804080a05030405040e0303070e040e0c0d06050109050105060c120f0d0e2116060b01140313030206 89
    0x591441c0c0f00310505a205000c81010700100009007030030305480101542c60078035405100d401100d2003503c078404034580e100100606542c04101080250540e03003031400c005031555480555038441408024020b090201c0c42203416203882c0c000004044541c00d040c0494039200d0300135a510000340c842c1b5032096092680c0000c0d0940188100003e60f003002d0060b040c42c5e42020350f0403450040c40384040303900390020440000d030301c0002e204104031648075074081e56407140342c1400c00003552504000200c5580080060103a201e400c1806401d10801c1681c02140a80001c00040d00300110346003010f070803a003100000c40800c842503101038140d486800c400c1205d80d8941003130013001e00905010004580c048440c0900c0f1411417409040019010030450b807420103140a04420f50381c000c00c03d802c095000010f11400802c0c02c1c941c0d4040c00c0c03000d109071414604003411000318122090b40103800709607030301c11100305a4840c0203402451a104c60141e540da04000c161501070078200300e01680107000d04030100f045 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 139934307 1250 139933057 139933061
    0xf060b07020d020f030f12070605070815040c0207120803010e0a0c0c03050702030a0f03050711041107020f0a031b08060601020606010507110315070201021210050108070c060e0703080405010f03 85
    0x1000c0d402812070300c5001c5003582131000f503859840c1300340d90610030100e05180c00c450802164901c0300e00441203e032120b03014038107803041c0c0350044d040c2d100f0300400030100800f96400c41405400001c00b03c4000c940d03e141842d0030380c200300071307034206030b60107002d4034810028045401b000718101e86100001a07c959141841c140403180300c1c0801600245810300507a000c41c1c0304502030f0082c0c030b000500755400700c512a0707a20690080c0c00308080300807a40128088040c004038848d004034643c0c054906000e00b856000444880d440342c0720303000740700d50800c3c000c40c10207883d094560f101071a070052850780000c0034074440c80994141c501c43c8088900c02e110000c0d400d9440414840d0080c581a16a50700300f6506d0f0750b5400c00407440d503190a405104864102400046401c0d8840c081c403107540005988600d0644402140200140011310240079100104a0369a100112546c04951481c0c68101b20300b2a19250000d0807440000d62a41e200c3d002c001300a00228100410896000740c907415036600400b402902 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 139935557 1250 139934307 139934317
    0x10501021509031c05040231110408010501060c140c0a0308071103060708070e15070305031b0f09130b0a030212030c0a0c031a0f0604020703110d030f060b 68
    0x40140c100201031076004408145a50708402c2c031005403410b25903d540303600344074900c50312034042c01c4e500c5609000541c02c250310348502c2c11080464a1070007d40242012444111100720000420b90f40c04d03501d411030180800703640c041c1c2031400c0288041e50303441d0030007040e0b101032a00607581c480c02c40d02c0241000c64000f5000031203c0d006884c042225103544c44400c0b080d0000c010a940c0c155000d41001c2c91a50140034840c41000c1c140c4440840381000500281f170801c0201d05c00b405541500940040c1407580810f031031410b50b0501d081070f40c983d90000c85142c11201424600345c0301f00302050120b0194001c0c4c01500d401c80080d5042c101007980c4003159001d07243c500e070b03400390022040c80c400e101508208889100c3c540c203500c1182e00d00904504502d25012040d481940c030700d14000e00c07c1c0100b1404c0054000348400515400416007050070105180a8000d09400c1c4601d600003119010036000744801241698043d00f030394074107284241c019000d031845c81c0070312100074503014000ca03601404e841555 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 139936807 1250 139935557 139935559
    0x60b0301060c03180b070c15030605010215060307050a0e0702010f0203060d021e0a0e0a06090b011e0c02090415050105030f0c010e130501031a0702011811012708150105 74
    0x5891841940307054418182604411090060a50000c0303810366601000703010b2540b1071201c00c58200d141000b5180d401c020500c8c04d208050901c40b040082c0c1c1e0b0300091315814030215110340096601ca01c07001914115076a4460b6410440030fa0000402002c000743d8544124090f400038412000030b41142c038100d01c02111000d034080c42c015049405420203c06030841c90580340240b00d480380350040000c041b0f000c03c0e440212842c15010807c01401c140740a00801403a038070300240015901200040e0074907480d8200c055903400345000d011000c0740301325880705800da00502120807a04042c18812a0703000c49401c02c40c1d03154140000069942400185441b032100103070302a10010790504011112014040b04003588043c0848414450b4249445050300071407282c4c9071050451140701140800c1c8000034000e00c02e5914100707205190504200342540f020340c2c0038101401542c0841c00680d4129003079104441c1801185028074908914607a1140035100d1000c00c507064500c0032140c01003d180b09008603 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 139938057 1250 139936807 139936817
    0x9040e03211306050a0f0203100504060503060c0301051c120c051c0519020307120e01171e0402041b080117120a05030c07080a2c01020a11040612050304050301060b030106 75
    0x410204000c2d44c0410340100300072030080382043c0e034249007100f03903082980c1076425030251210801c000c0c40d00703128500061105801402c21071400c400c8040d89400148501c1b40940c0c1104d02c2c2d41c114203108083c80b0740d919404014140e40c1825107000800301c160a010032507071403081d0031102e90546240d5403c101c40c14826904c56103010072950102801035900f00c60b000951006028240000d1480c81c0b03000103000143e5120000c00d24400d00040500d19000a0862002140c0c014440c1d401e190f041c042181e018155250f00c01a1524804074000f050507200300c00561995103da4050582c0c4081c0c00d604940c003404e0304a4400b82041c440f40d854908022078980c004808001c1825580e0060001c0c40e4007821090140b070900f819034a54803116804030b44114000380c0941450304c9800110700020038031050b108000308010340f05030000f030343d03030690040e014000c005808014501a5a240c1000307000c0c101010843e1040785091801c036039681c000d401014480c2d420503801251400e2444203881c1254429928 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 139939307 1250 139938057 139938091
    0x40609021302091e0406170102182b0305040306050405010c0809030f12091204030c05010305010f060804060b1c0506011406070209011206060b1204050124050906040209040e0321 78
    0x1a802d440d00c0e030b44c031034015840e004001802819402e4020004408138005691030140c422a040b00348200483c1a100310340260210184107030031804001010180303201c00407801018101034600313000b26800104503904040802041007c190422030200b045511a03c1c41621000412a00c1780103851991505110030f0100c104178149025942d0340110305201940d5020704d500404001a5020b40c100741c6102c0707081402003159507030610441e4014914016a41885810200020040000540040d000300e17101c0740c1d44002941c4840210000d02c80d034490ba0741a114191a2158603034509100b0350314101d4210400701102c1c01c0400443e22490707401090004980c0c02e050003000120b2102e501603030b0749a0f403a54042550359140d0300504c81e0100940e01d0900c0d610b010b00e13045007503500d03074100c0200c0022020030401040c451b22010b10180e480849440e05160307180000702e0024014203503030356072050a011404800307602c0440202707859124000011201d1074581c155003a55081507039005580c0c0c01641c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 139940557 1250 139939307 139939339
    0x4090203181c050d020306040902060a020303220b010b0d06150905090a05100b0c100504110f0d05070b0703140708071505040506061519050c070e0108030304111804060902130209 78
    0x10085510087c02480042c184134140c0105036103811000c10000980e0001060120001c020412440b030007400c400f143d883d05215a6504408441c1803040541505010510741062007103600950017900c21070064941441036004024207024140c89002d0182e480c0c074001c182201050b02569101d584801c40b0420081e141c40207400d0796900008151410703016040c00c028849a01c0e01455000358080c20aa007607100d18101000086002c14000c2072060b00c0a06201c000640d0201d10a070481d6224610180c49071002e0800740c0304401812000c0e0040000010362000b00700f9040080c0010368000c2d40031081a41c07036803440c1001c49030140ea02615a42c002d20006c1e070302e8079241004134065440142140c2c01c00081c0340c02d6007603203032000c207000700460000706910b00302440420000c0010100e0303000101d07140d4588041c59403079200107000900760701404608040b02c1e48480500390000300170121440d109140500385080141000041288a80c40c240e252929400080c001e5403403049000f4070140f0045c1c2075070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 139941807 1250 139940557 139940561
    0x318062c03070201081e010308070209061c02040b01050f040f0e09031204080d090203030c15100303090302090907080706030603021906081911072a08030a120204090203181c050d 78
    0x24000e0715020206c0140c110b00c00b8140046034000c0d0310030400071b5150041841000180207009000d0f60140070081a000c0b03101e030000108859494056500080c2404800c004032258428813454840c9040c0010340000c009145000041c00c5504844803030205450b0b070f190942d141d118264018840201d410013240100c0c6000c002000d94501c81100000d441301b443e8007190558001c01c05600d0290000c0f1542414005c650812590200044ca00862910b0450ba4058034100d0b6a000190017035082130006610303544104083d0303021300f04340021140499640d94004000e040b181c0412030113004080e8003a02c2030241c2c00c007984252003840d210320055945403070a00180c0074024600b095010b0b02c40e46482e800c03514003001402410b00a400080c1d0400b508003240c00e4005075000c1d582d02d00d0825980400458070040251840d070b05240ca409412950621104000381c0039a0f00300107000d40c400000d10200c054a0300103d1805c200c41400d441134001c00c00ca0140c5198800004080800d104012403000c0038a0380d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 139943057 1250 139941807 139941811
    0x402060706021303141b04020301050a0909060902030303090d02070518061017070512010b0405100804030c1e14060615070303060f090905060112020607020609010318062c0307020108 80
    0xa00c81801807a542c0e031701c17001090742c1c4c680051200303034009004140c1802c0711862200c1080c0300c29142949507514002c04114451420b01ca5802e16035641e04891040000396000859415001400c4075242d05006a04a840312506c103030100151241040006076820910000356269850381c240007020f039512802d00c290184100030100c20001d26500d12000341c0107000c0700742d0007588550b840649910b4034102032400070006800080c07845c9010301040040d0340e070382c400c0d10a00d1031041c58851002c0d211481c00f9030b044d82001c1030082103c02c4043c22109078400358000300740000c0c0186403140c00342a45c0d00c03d29072610300a81d05142c0018ac10901ca0100c10001ca0040110512900d800680640c2d55240d5600c031980b40e801c00e030041a101c0114006105041140b640941540e074400f640040141c0e000a01d10320805400034003568002c039003000030380e00940c0718001c5e50b0035208000010846a14000d002000f944240545a00f0280e1520191034400070a01c4287d1070322500840c6814020b40040d9195400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 139944307 1250 139943057 139943077
    0x3020703062304060b0a09061a09060409020309010506041103040b1501140d0605011e05071b050409050607030c0212030c0304080c030c01020a020c0411030f0a0e15150306040206070602 81
    0x214910207900400e08071403a880745000d0640024041c09171000c02c64000d505503c00c0c4003503818007400340302007440c0d59080c0d031040a00c03c4285654440c0000030610078051359000c4000c01d0301c04802c1200300b42040d0000f9108070b40c112001c0044480d410007800c41404155009040a0300790300c001014420301810540516071705041140700c10341c102d681e410103603004801506241d522110b040210356005410118040d42e0f04042c03189285518600819038020100301030410340340d001c4021505000040e00b14050040031b0000e0221810b00e003403045d0b40e684140c1c1c0701400a80b6091600b2801071000c6401c1c04045131924005140d174454079401101070300301500540f41e008042116100c1c0c801c04000a210500107100090384030070010034040c2c205012107101e20300940c24610110040b10001741141d50101000b112171559446820245006203400c1480605610401e480d90a0620510074041e120390240701c1080e4031080d15505058980d1000d8400a4011009000d117000244041d0090800307800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 139945557 1250 139944307 139944341
    0x11070b090c031e0c011e0c020411030412180501090e0a0221250522090c111002040e18160312020105070305010303020c0d020f060706050708130302070306 68
    0x4840040d0800703c2070801503100720001c01d041910070105100b440c05150090801c070000e400440910780038915500207500800203c1540c440855840390700200b0091020b6000d40e46030f20705460b11850400407541076a001c1001820300c58000f22028250805991041e982c1c1c1030264a80400c5c0c1c94160405802910182c3d024010010104618014000c607400541e10440c124200172406103a281c03440c2542160416524454001080d001800c50720002030550030505c1c0309400e000c880c401250540c021800b91810400324805140d4064100340c04900305909a038104100085100124843c0c3c1c031504007039940490020f0070b103d10a001a0b00001c0320041943c61488481e80c080100d00f400f60800c45684250b4482440c0240d824814036038814050b0604102c02d50460705c0195607004213082c51885000f03c0c185040840d2907603035141c200c000c4050040780c0c5481c003d107030031005050111005000100201e0000c3e08401c8245801c03202d0a030140c028010300c170706544480002d480c440c050314080803 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 139946807 1250 139945557 139945573
    0xa1515030803041a10030b070806030f010f0b0a0e090a021207030b090a0b010e060a15030209150a30050a090f0302070603060510080f06030a0203030c06010e010911070b09 75
    0x8440e68001c5106a10407040e51848181c1220600c41d4560040e01c034007081c5c13035510b03020310000c1c4491512541040490619042136642d4030300003407400500c045600401d500b414610381c1076204641140d01c23080411101040100c0e01e55154072240f0b10112008403507a031211000720054185030b020010b0080340304040c1c42c403e41c0c40e525400030501c01620854442e034855400b900505c01081c3e4105e01509818181451a040c8a00001e01c2c040e450b004a40c0c8000c0c1c207120039046a4020340c111038908401a005890f8040d1284000c0c2c543e40043c1e03151004240c0e20a01c00505041d02100382500700a0182459140e4482c18424402841c0052156aa0503aa10243c801103009401c1801e802ca2080e03009015040c2071501c020141c5400781c1c80035000d14603040038414266040080c25502501c1001c201c0f405550301c1001a103000d4091001075050f00000890039400c10020900605032042e105004032940d0b0b9070b038842c038102c4010614001002406104a4001803281c190854020034442c01704da030302c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 139948057 1250 139946807 139946813
    0xf040f08030304150e030a030b0a0f0609150e010c08090105040f1202031507050d021614030a030e03040b0f0304020a09050901020705010501080c0108060d2a06110a151503 75
    0x51440d410103000c550020040104002a2108810b0311a2081d00140000c1d0a02003079a580c82c001d42c0c0026081c0b549590700d400454803803151f200300800100c25000c929903625074014001044a029005040f401c480c004510b444c0511210507050030184c0d50614241c80ca901c0d488820b4100550303047c1003010030000000d20791f049450180280c000f11074212404402031040514003a0340c001c40c003482c40001da04110640e5040000e60700c1e07000c04610301680d03d881806d90f00340710b20070820004064901c04407000200601c00005050502e00544042143ca015042d01e00d503640034a200d030303002036001041105c80701140000a503800034805030000c10f4441d12a850f580030f840c4121605c1900d42c1d07000c14503606020090040c04d00500310440542429281400000c1410800520b0746008000b0750090100700003031444205010318240c42d10481d10741d061050030304c404a1074492540024214840c5140740c0b040415038100c1594804428030f4105080420180900503c07601107141440d00c1c8400404 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 139949307 1250 139948057 139948079
    0x60504140702120f0705100606030c0c02060a0309020604030602030f04030f03051005010f030f0f150605040e010b0705100c0c0309050910031704050d0804050102070e01080c01140702040906050609130302060a020f04 94
    0x41d40403201008688c050030810300808030b940d126504c00401c4030425101000d612a03204a411a03100e91502043c011390900200c1e10310712032984014440380c8000100701ca4501800500381c0128407a54641240d880071041c11020f40700c041c0e86134000f641e03110108000642c041c0881c01c0a045007410003242c03e5150f0804e02048035825601003170721584903001047c0001c082100440a84080d080031408e06040010034585421305000d00d014801c400111941801010483e0196142403da01070220080072400185103481000c4100e010611302c1101003004c0c60480c0e0f850303104044c2c1080b5401e800e4a1504c40080c000b41c2281100d41410040201080c1c5444055030490814002c01900d590f40345000002440c24140b90f00042003003900348018000c210300400c080540758800d00e003450310510b849416000c03512842400a60062820255004200d01a00f1081c8100011944588960b4400843c004000c00c40040140181c0040001908070307100b95003e403ca220100354064286901c900701046 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 139950557 1250 139949307 139949323
    0x3030905151b0f030105060a02030403020901031b0504110702010e01210603150902060711030c0a08100509121605031b030301080d02030906040b03071809060504140702120f0705 78
    0x414100401c04000e040061026400c194100100e02c0030f250207920064034106000600560f0700c0303500e001500c0381e030300c030303c00c205481c0550b030003c06204295075203141c1000c0f9550f8251501d580c00c2c030510390018080c0f41602c40d40c0051b02460009602d000d03450f500458956503000b940c5814406100c0c0c0000d4903134464a940400e50080800000e401411070a00701e00c940044042c0090301420b10210800580341e080c140e642d1141e00107613181c02100c140001a0401100c030300d1058100502060014062200117001e402211b0440e0b000c200c1a10b42c0303d81c440d10303141d80d840c40d0315401c0030030401c0e1840b5114081421040d1809041502c2c24a611424a2a09072192406190300b6510100052046142c14000301c445010a40011070cc0c10305484041440c0d8001d6118841d103903000800000c6055020700920228200841612014251920000300050085019890003585010401624110491051806000103030010440001018100c21182e848019101f140380d000340f124a00180080061705 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 139951807 1250 139950557 139950583
    0x5011815020c0108151c21030207200a05100309060203040503030718150806030c12010f0f11120619060807080c030f0613110c0a1a010305030d0903030905 68
    0xc0010702c2a000400300c120203004207000e85070800d5039003a181c1e28054065000c00800b07010900098160800410981d0b0800e1900c03081440500901301007503050740140602849108842140704200d1318800891020000c503a03002040003d052205152902e00740102d030b0003d1602140e80c072260394500f000d98005540403901a80003005011541c0d4103c440c6140ea100c400c02e110880301d02d00400000c0810f280b8654034203010800340400c0958900b88403802e80401e014288140220304016210300030008070122985082c81d0005481c1d100c9000c3c007e0400306101a22194140103106a0501e03d1010180805501203000420f8000011040790a10020724031615081c90910302000080d08240c4c1c01016401302000400c104500302480d608590340054040d607072105141001c10303180b80100103403d4042e10242020450070140040050782e0010244250781d03c0030780140c43e030f00403000034000780001881508180401030350b8190301d0f0311202c00301d406417501051150194681c0f500b080480c104c05 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 139953057 1250 139951807 139951813
    0xf0310090c08030a020a110a170d09051002120a0302130e040510021c0b0310020403050102091c0308010b0703050f030403050901180f0e060a030615060311070c0501181502 75
    0x410140040041c07518010400c4401840c41c120005500944500b2003080c02030559414a8110403107496101006000c0c243e180c510301d101b40d1009000c1d50340e510101d240040010000e130f1011880341080301211144450540042c003521042203444809070b04100045010941e090204103446000080c0440040840d8800200c43e42070a0410303904021151600070031850041203403418400311100e5031032803507901c01000640c0b07002c1200002d042160704480103003000e001113008018004190b000b0035020b00221082064441811940f200d4185841301c040d0104e0f1031040100462905d880003060940c0c440d203441807a00041030619415604151016400218007141c1582c0d59608502c02c031040001c2c461140aa0f1450f203511440034240f5800340b1030290819002142184e154007068038003460348143c00b031090001d101e045014a90300384c800c0800290518a0071003c02d101e9804030ec0005402c81c1c1784e07a01a03801c00f001510b440303451859848080052200c002641241740203220001c01c01917000d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 139954307 1250 139953057 139953071
    0x4050f120a180302090a0c0e03010e0d020f06010b03070f0c0602070b040302190506060d02150d090b01150207050105090f030601060807030b06090a03020906270106110c031b0f0310 79
    0xc02002c2c003002d0300100399504203040d4144090b9950154042e40250540c0011924466030381c806ca90303c05400f21056015130a00303d03450300c4000007250f0340708000c009071308440c241082a00c085584680a2040b82001c050400208500610031005d03c10403101e42c0c10250a04030981e5a07001c200d074000c1c0f00036030392a480c52042c08201030381401903001c007440d165004103003c081c81d15401c5d02e03400080c100500c50303c11180c1c501c04640320440302103060144a200c440e107401d61001c0100261101941c22a080d401e200000b040d8071301e5501080740520780941c000c203a040d04007030054402d82c2c0082c2410381c3c01455165084800d9404000041c0178100581e110761071810400d4015081d5250b55078000c0c8606c800340004074098644080c0c9d00100d82d01214045400c0c0c0303c940100341c00d036200e0a03071802008491350b10f181c5150003d414040c12204282d60b40d280602c040500d03162598800d141042d4942c0000f105520f50010300800790340400e0000b8080b850007840329000034030744030702080c0d0401220740750a4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 139955557 1250 139954307 139954327
    0x1509020a080a050604061d070e070e1f0e010c0c120f021f0e010203070b0c03101203020105010501120516210612120e031005090102130905060a1403030f0304050f12 72
    0xb80f21054845032047c10000c254041803a070711125640224144c000074000080c49462045030004007208018119000c0c90f00045840d0002041c1c201c0c0e1600442c4811070b4880c0994070881d403460700c46800c00d09034540700d41002010002c04081075000c2c0d0b80060040405030140e9100e540c041c0c1d0702d16a07104000e407152292080502150044051700b4150f4009010b00008262400c1520358000c5904160726580c3d507946031000b842030a981c00030020740c0607201c01b1008068056000f40c1c141c5809889130070403001001d03c1c1c0000e03644221032031210b05969010140c00359001c2c0c0c0307041114000c40240740d580e4400900034041218001c2d8070401000a0798262a030500031500401e2190348228a4034a0081c100e0002181c0c3d10b0010100507280c243e9280001401070200394150707103011011001c00e0b60707240c1c0d851400c480a46030030b5644c1807083d280342c940007a0100074141c05801440d005000b450038070001c019071140f140c00090065525004105403054400400e12040100020408016440b801102 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 139956807 1250 139955557 139955561
    0x100c030e0c0a0b0d0510090e07060e0a050a1401030905030c07050901090c080f04030201060801050a0501061205190b060c060106050403140705090c0705010e120c0c030a1509020a080a05060406 84
    0xa401030180c03510503c80d5030380340b6007128600ea03500340b004903031501c03541c17800c4d905200340e0343c00301d15003a02c0d085030301026020105070369045424560714000000390540800c00401054403880350b001000b01002c03c02e49100c50164400c000c014140040c0308495070300d41c07038110741c4000508009508118820302c83ea141c00d51a45000d030000180400605c503020344003502e40f08014140c083d030118504006401c140c404d40110028000c0c031b50090219090901444018000c207000e40000f1403540114054540c0d92403040603c904110740c0322042a1108a194400401044403605d41001041041c86102442002110700a00c1c2a582c0c2340d541d40d03c1d40c2050f40241c40c04804081030b541101030700f005640c1d170302d03090150405403902c1056520301d1203181203030050007e2180c1082500a1012424442c081c04014051580103041651a4040c0c0c0c80105619100c00d6000140402d000b406481109600c541c03007850560300c040d00142c0300d180c5030f0303c109290041c0140215041e5212100f0802080818 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 139958057 1250 139956807 139956823
    0xe06090f060c0307081f180507020f061b13030f02030f16051003020c0607020a02011107060c06020d180b070912050a14070906080703060614090f0405100c030e 70
    0x440182045080c8000105400d101c0545075204000058000c6406000c44000106c2c80c0680460608081c070760b86d0b00403a03103454025854801103407a103800121030f9400811004e00a00440002d090760340d070342c808480001c6101c1c03a881180e0001c1407002c00c641c00310385069a40030750301851040781d01c3c0071a481050f107010b40c000c0f8014520b0b007095880d400301a03504400380c0d00f030f1903040b1594158080c00784400c8000303004800303214a0f14031422060202050300801c401d58003030b0003a61004410090240b803a43d032911184078810000740d450b084040800d929501411030a0202e19000c03a644d01c00c0c1c05d0b240b41d240c58a800c1a81da920801050100b402c0d0440c141e04020403607081c0d0155440903d48030140c0f00d94114401030942084864180f011f03200502910010f004012800c21440340c640c0c00d603965803842400308603505440d12502050032510411081c7c80341c10020301c00315059a070b240c0001c5c44000040c0c4110b0f040d124440346210260100d0082c19990501d41c1e400040d14240c0051244c40c000344 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 139959307 1250 139958057 139958083
    0x6050a05060a03090201020313032402040b0d23070801060e040c05091210060605070201031a0303190513140f010e0f0103020a090302060325030510050d030309060e0609 74
    0x18420810040e241d003001d840d0080164100025810001d000503800d51113071100c200c030f4210104601204200c000d1000e40e1420240c0090b030a1007007561a4210224403650056416501080c006a40118200d8010b0300844582d800303a24a41003000000952810060311064003103009a801884516070100c0c501c0040d6200300d0301031120314200800903015114618546014440070030003088442400c02c144103c0c40051282007003c517a03510b03030082c010b4020080c124002820b02043d842039104a8501d540c2c6140300074061446c0a0040f5100c01c4180c0740030700302d041270000500401407130016480800c00107101e40200c1d40c0c48000c50034104000c1a040003a0030741480160200c0c20450348620307000403204030003070a005035964581c4030190380c4244140e00007503100100000f000001d00c803804043e68010044899004007881301001501902d808032524400c2415040080000389050800000518000e0a00080000442c1c0b2454261250b070700c81040b0507071011040c850364100802520040884d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 139960557 1250 139959307 139959319
    0xa061b0810140f0f2d0a0e0c0705070e0112021f020a0305030606041809020306090607082a031005030d02010c0903020603060a0503030d140f01050d230a060608010605 73
    0x3050080c0d20000c406200b0b080c9020701402d010041c402d403510000301400c0400203165000b4140c51403807410001c110b51084c0603408150401d4803c0c075060246081043c1c50008461840540c2d842c01140e44a412490058415100304e800c0007842c0003000c01d03007a02030444200d00300c80403031842c0103000d10920800c02c54034004a103c1e000c491410344c0482c1d80d010031941403503d04d6403a1900b00014106008503000803001703540c901c1c1f4450a4041c0d0ba4803102c0110302c00c0e420780e05159656014151581d4003159500e010034446070000d607209803181ca11759403007004100000d02c041005840c3e0059a04116003d03080d00c20311742c0041c401450100025424150307a0f100902c1a0804024000e01e013440c44d21000380107074004070109002e0b550b0074174003501414008d0200c3e174880c0c2041014030060400403c07506e42080820340810a111001d81c00346060300c0703010f001d04030b081149076038041030110710020030003605040b0528114070749030500402d020316000c7c07180498182d081404907400c40345541e00c458400c0c0307 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 139961807 1250 139960557 139960559
    0x60114010c1109040809271006140306011b11150408190606030204050f0a15050108060603100506030123060a1421040605041203050609060d03020a061b0810 69
    0xb0581c1212000400040e00e03070321107684852504001314003410800580c4012403030500103447c1000381c0c0d06414800800039002c2c80f07403584141d081280b49103010308030005001c40c5891403221a004011a0403030410715195124695400f4160000745058038210f480c441c07100644801450044001600000d1010700c1038903040c9054001d695074507044d1401a81070b81c0281003c001d004541c2d00c58001560042c0090084e407804110b1714500c11000c0f40c0c1d040f5100d1074407000d031036081082e030116000c1d140181c440d03600c6901c585041001542000340044199883c034200441e25895030400355000f03000310000103880c81d0448211a141c1112502100e0169070180304000d00b1175840802c01c0e681203151400103030380b01c0d0b5041e9540500c480542d03e03a082c0310f88400074801040510390295102e0380c050220104644001501101a42c105541c2142e2103100b01000c22410301c2d0070108094828842d0040b5030000205503a00300a0b5002d024102c00b10070641070648040c160000f1050b984041410000f410203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 139963057 1250 139961807 139961813
    0x30708100f06141306080121030509040504050c0d05100608060c040302010c03050c0601080c0405360c190f06090b0406050313052505120309040506010c14060114010c 73
    0x5005a4410780042000100303d0400800024088402c40f810568405400e40d0f00d42c5c8000e440281c0a120b803c80741c900340036070004126003442900d110b40d54503940b0a0301d441d11031070400025002c0948140c800380142901c81102d80d030f94443d00c0308040d20800141401c4c103821f01047d01180c00bd0341c00585c50b500304004000b176040e401c1d021941540c0d42424880701c0306071541401c075201e000e80010b80c1202d01c030f01400418228000141c1010382c00048409200d45d40d102c02000d120301000000f01080b488140f10b0418008941d27854001c4110004070450b0914045c0780e00040c4001c20b40002034003001c2c10b24809001220a880c644000341806007010440c1602d0000300b4a1b0a202d140b003410104600440807441380c0030400820301061360000111041d0044441d40110406a413440e11398024081c0341c40019079040055039030024a05640145052200d403005000290500038030280c10401c00410384000614a484184000f90343c0c04001c08c481d604168060800e211100d02181c1400328400c0d8203400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 139964307 1250 139963057 139963079
    0x20307090c02030415080f16200c031009050c040506100f020c060309010f050702190605040f020904050d1b2001020a080d0f1802010e01201203070810 66
    0x45810328040020041d0701d0031800c90640c01190081e51000340c01180e034405050344800603900650845031010407545070003001e0192801051031800120b92503583c4a039004048011031110480300c1800c2d2910001020300181c1046085070030304207000d42d80c1642c83c09110703041015601c56034080d43c00f00801d08003180000c0d280c01203581e1000030025081d40240c481c9109100744001108082c000c19103a0801802d4640a0400342e050421590303c0e0070000303161a84001510b114100e54559000b0240b0303c0354461101500c0014002c0d6441019840c48600680b2003120035403085000e00081c0c40c00c100c500500402079001d4045049a0011507070260011480380c1c0c1d4000703101c0180020a08801c42040700603414410115805051b041010411b4404040c082e04260340c0c004140c101001800354032424810001144003010780011510740350a0390550007440d64a0244d10f400c5038403031aa9030380744400d915080c220b0f000da1450500202c02d00c00404d0300900303001d03003220302d81541ca1101810403103070f444 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 139965557 1250 139964307 139964309
    0x1082b09030816020414061e010f0f03060e0103051e03040303050f030402040e060a0b0a050102030c1209010c0609030207090c0305040213020a030f05090a0b0603030301080c0f120a1208010b0403020307 88
    0x1500002814108003d803074944043c1d45502500a015156604082110013602141c001e0300886040240c03100a1424203002d0b000100140c50354013075884213000c1210505c50012180e41856901c40000c9078110352268814000d610610045c00300e03100da0000d042d00c00500c0ca400d04010703801841b003800003980000a84d044503860320041503d1303a442d400024050a400146550240611014020343e00803175007140a42d4801540d40e6a103887e074031001243c0e00d1141c9d180990558214000b0303240c12080c2c200040200b04014513050403840c140717440c0c0c14110380c1c0c2d000e403c1740541d1001078200b00750011400399004211180c00c0411480c81c054010400031000c0c0c2808020382c50f4001403190305039000ba03100d0b00c240e0a10400030407403841c0c4020120396a1005500580d03016001c1c6000402074940081220705844800c400f0b81520702a01c01444401c100c0f010300150f2154111000406132001009503448d081d006c0d43d901c0180001d00400035007142c1c2c0603003184007142c0c1d04000510143e100010703010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 139966807 1250 139965557 139965563
    0xa0218060a060219170d020304060b090106020304060c020d06090206040905040b15010e0d0501020f0708030f0a02070f110a030b1603050a0e120f0f130305010f0c0f0503100e01082b0903 81
    0x1928268000d0911002c41c4074180f04654070f1b42c404428002030084940c0140b0192005665566543c0d89850013a81d880c0a0340c03003074600145c215004003005081c1811078070040752080c0c4000c2018001c40d400030722140c00640003110f291395902c04200038800441802504001105c200700300701c3c41081c0000f0714580d03401044a004656030b4030301000b0000254111901e942103800b5081c0c030b03040b06242040190f07000b030798954001c1c0b550401041641c01c40f403003111607181e4409802c0707000000a50f00e1120494141d0b04c03941d4003682145000010039003004009100e07030142010646d031703410001d030080c0441c1c070064a001c655615240a010540c000019400601500f0701c1d81c89449441025001c7c0d114030903102c1c070880741840440c5030700034450220203800607607110700300900c42c181c00c0c026890200d8910361560350004020100d48015580180000d541040c1d01850124000d03442e40c001e4180c0d00c00c203910001080c1d00101d44500c022030440f00f141d842d10705102c02c107101c000107a8801480081940006 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 139968057 1250 139966807 139966823
    0x50106120228090e0c09010e0c04150504090f050915060a06030b040902061b100e030301060804020d05061f1d01061103070b0108011512020d0809030a0218060a060219 73
    0x15908451074a4108000c00f8084028000300c0d82418030680c0b0703000159505405003413010000705640c2268030510307108290b010010b508003407424044440840c034400d68002030010801001c0348104150043d170094103c54000440d0905088444900e82603d00c210f07160085030900900032550381d41c080100444003a49004140d010700c00c1c001030000c0c00071280003940088009181503030704180303500c105850751200d0181c035203606908003050b00355180311020340e003281c100b00010300005000341400c640141c0041d0005000c454030b40c0e00c1c0e9103840016100c0c000101c0703540350314080780107080d2043d03005403841805807000c400c0800c10f0420400010b00580040c0007421a0000c4420010403d890b0784a8010001e185203503915139609000340f103580d141034050002c4582c045011589c0000b9080c105034083c08806088105483e00200764010790355840e403602451562801507510448420025100c21076058424200682003010000d29580200c007550000d050907403442103e040a01d400503040900 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 139969307 1250 139968057 139968109
    0x1a09030711040e07081c09170c06070c0b0c0105150609130506120303041104050106050f0304150f020a12050708010305060f06060712120c0305060f0103020d02070f030c0501061202 79
    0x81642031542c945c114070308074400c0805250003120b07520340c00040c2000c1500c41802c05622140e078412488100c0c8401a0b95070710085840405003007000040224074026583c0b01d000035200d0843d080307140d1040c0c0240002d82c1d161020302628030a59105145035940454600d031500000f080481e600c040c5100c02169401d40c0d4800260345a00c80c1030410326039501d5030080c0c0e030b520b00c2d140c82c00c490742140c91503840380151300c0d2200201c2c0180c001d20407640101c03501140c103411070b81ca83d40d4241c0350902c3c00a1441c0c1d00d544440c0100b420344244c0c00642202c0c1e0980d01c66810301400065440304440000304010f003000280c000400100748049400d64000e00a210f4800c00c1d0381da44404603c4500c00c01308010000324001c549410180e40c02a402c418a6440e1581484289000a01142903c0c010b070f40d0f19911140e00200703865035600990041a032440c0440c0b0250a0511585405132208400041540807441c0702000d03c0c01c0110030301c1602e02130a0300d443c0d91880d80c0c14035004955011030062510618078281c02e0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 139970557 1250 139969307 139969331
    0x2040e010203040b01060306060c0807120e0a08150c0304021813020303130509060a0b0d0b041b030b010908010603030207050d030509030a0507150e0d02040b06070804031a0903071104 80
    0x61061040a580250359070b09180c58031070300440d005d100f190700080c80d1010110f001d07403140005540454014640324280565600c40300260100e6440700800d200e40b0740b4030b64000382c89000c804002486084041c201c20030050782440d403011300007008000303241010001c2100590302d1941d40d41d40c96280702001280d9655521010b01104c4011001a606100200796030350301c41c1c2640a07c4007642c6c400d40e4812000d8841400b4000b181070140603a40d006a000c2c4075800744d810f02c585c801460913034010004540b03150144000083c26001104d24800aa1130b03030051190713940c024000e4001020740c0002000211320715100251200500e00030144903004900ca4042070510400c03d8a00d1054020140c40c0700300214a03001e0740d00c0c0442d1194084424200f0072180103140122004109880090582c044c0d40350541e003000020311703105444503800340051009202041c092406000a140314275026003121100d0500703410130900c0201480034a5004000f400006401000710a11a83c019640400c00c00c07080d803 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 139971807 1250 139970557 139970561
    0x303041205031314040c0807020c0f010e060c030405040c0f0c080f07050303090a1205040303172d0613060302101805060f1201060828060f140901060516020d0204 71
    0x200f9040d12403000001d0100340b07a09070710140e1080140864040043d4400e03041e00741c2e03c00344200c5440003da0018141940795007880414900302400c145817801d503c001d40800218160040030064005501c00314007808181010f21950003001c070a418001c50070503011100420511071880e00600d4581d0204111100784111000e0710001e070752001c140ca03185c2c0b90044201703075960350840c400d4402c0004103502407211800b6004540907240c0654911038400b03a80000c00380120409010341508403980315140e42108002000240c40022481148c0000e0601c2030800282071820b00e0380da01c0e40351421408000503a40c601e00055000301074105141c02e4001308201c0d2402c403145901c4260496000181f0808510040008000c0100042c03102c5074166210802154042d40c103c401000d0303140d1301403c0713000101600d003124460f0030352650040b40041e00d900d481c030382c0c9040c1940020b40b60850304500c44000d03c2e0449d4070302d0141c4418a030a0b400c254000955801002200030081d025036043c104030401c1d500c646d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 139973057 1250 139971807 139971817
    0x90f01031707061a041a0303040e0915040b070e040c05030f0403020a051209130b0604030825140609010c270801020304080c060708010303050d02220305031314030304120503 76
    0x4600c04004c80e451141c0c4403054544a944240e205916081e14104080c0b00c1500300482c142e0058025402c050401c50003803d0440007400c10902c6101e0b41d502894207a0714511a60311031403244480000508042c0400340c00c00b1050542c09210700d050414141860703a021042d2a0711180c01012000203071518142039040a440060140040c080d040038140402043d10052040000640b075401a4955400200080b1141441da0741d41c49031040004001141c0302c0d401405c0700303008802d81c0415035808680b2001400d11842411128041180c0d0155400d0340d0030f00105905c41103100092120000c00031000303008140800103040c031160509144d80174200000c031904003520915000b1503581c03c00382084141078110040c180060301c50600000c1e90349124100c124100d0fa450b0b15400d00b0a490000018003940003940a40480542c88034284400030884400320b0095002308007450740e8100c40e000c40410240700b50450306404003682d41500c601c2d1000421907003100c0078280200141075071450704605511072 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 139974307 1250 139973057 139973063
    0xa0914060a0c020d031104050d0c08061005011b0f03270b0702040e1501060507020d0503070b06040f0614040e0712110f1005030402041d01090c080c090f01031707 71
    0x6100c104a80200039510158207040309400701c454032800d082017141940ea0302c90b640001c516041c0400c019504209411185c51031040c1e188a01441e11914100d20f0501d0031101410026054442000070303507040340f4801079403860340d40013080244494903000700c4004541d10041c208240000c3d01c1820524140f0729010a910341c484d0380035001c1d030b00e09100185400018040c0e21492502c9000c151041c0000303484020b010b45071204452a81ca01030007a219600314100c140e07040700103010000300064080c0010121280300d01e0304030f112030408105110444485030b1b10411054581241441003034504101c0c0c41c3e0107072003240c0100302020914071513414003126910882c9078001c1425501d0402c00007058003c880082542e400303080041e04c10401800d030b01d5001e52500450030400124026007456080742d0400c1118408a46108a40c0103403182150812081513a07040301100301844000c000303000385031300d130141112010403e0804081c1c58085050603c03000307004090700c010030300310441000c090b07600d0075030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 139975557 1250 139974307 139974313
    0x1140603190e15040c0602010606080c030705040e0f0f280510030c0308031801020301260a02060406090e010806040203150411030a030903051608100902190f051509090a0914 76
    0x1091500303200b01d002c015a802c1700c0d031140b03107030000c65005e1051143ca0116100c0f5079031b041072a2034800c000107180d4030141003802013000c200800319620405151407406803035009200c07061841d090341203440301207010b41b022032107000710103001e80c005100200107401091101400561601d441503050034100e10340c1d2000303005802200d000406e21045d04099842a00d0881002890100c84044d49080344004d000315446210031111081840260300b000f1304c0c4c5000c552007203440387c00701c0b5000034002d9041a8429000620002010300c00034000103036107801404518020101400e1030350000f07441d10440d4580c80680000a030015080c40243c800013081d00300c02a01b5a0304160013420018a904445d01065805101300502151003055424840d0202d1f01c40c00301030040b2003110740782d50014189207a410b17030344400f440306201c9a9507841960071f0020440350101c00c0b5202c0c03034902409000f1000f1580b00e08100014400d4243c1c54540c0684143d00c0102c203100041c20603024a8080000c840c0c510b13602c40948 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 139976807 1250 139975557 139975573
    0xa170406091703010509040b060d0614011418010306051f0e07080f0402090601050d0605040f091a01030f08030c0c0604050105010501140406091511190b01140603190e 73
    0x48603848410300034002e4461991202d500700c01841c0510080c400c09030040c1c0c8010001e40841e15201c6d0346a040300b401072503000380590b039850700408e0744d42d0907600a05500055004100040020045243c0e4241c00d032424009a03103204035291400e10140f0001e4401e940300c80c0003a110b182c0040c4541c0f440c040710100c001c0300340e8940491140c0700b01e0845070400403a140e000881c3c0c00c110b400400a1081740d00514100f9136903950401102c903500003180000b000d50f120500814140d8503400345840840c040c1000107907040c3e04d801c003107600b8480c100b0f50002c146480e01c01480410810000404a40d07000001d02c0d940307446280d6140d0702881104003c110700d00412003400100103042d0010384c102e4a090340c80c1d00c0445070444050500707115a02c5810089480d074442003058241030090107208c00b03440c2c1400140b01c941c291026083c10070303032203c50040b020841a50000c02c20520230240c058881050300202002400300407814030b00c000f40510700c40010703e241855401c3c0c9030341c10945000d00840d050700c03c40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 139978057 1250 139976807 139976813
    0x20408030c010b0a05041b0f030b0d0b06130c140724020c100606020a060f0b060307020703120504050109050103050910020c0114132303090a181d070b0a1704 69
    0xb00f0382800220310808504000103041d05c0c10340180700b0000e5a880703260703100e250140307015607410072080c01000c241030b15490b5085043c2e0381e2017401d907a03039401500c0c0702d8403c2c5401c1080285042450352030500e900d1500c210b40c0c140640c000580d6018170196920155070b4486400d10007100740c0210f400b03072f00f6606d0010003200e09817019000340203002203007011500d81c0100700000606554041c010303100160310a0603a100840c00c640c12640990403081c0001400740c400b04c0101d08158400c80341d0307002581c840f02d401c104009108046018405452401c5818141481c00091111065120f0b4a04040c0c80f1004034520403002c0c404e01040800172182156203054602e413080c041e1003e541d502c8100d291040000d4502840e280305105d506501020b00c4407041c10b0035000102c0440003c80b8200e0a101c01d014108007511041c0d040d0b4060181740c1c2c1c4551040d00702e50b1000068580d15060f103422108414680810310302d0018010303080d106030010264545007038510484081d5100d00c0c0d50780c2c541007000140818 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 139979307 1250 139978057 139978061
    0x1303120f0903020d02070302010e2707110706020610091a0d14070909020d0b0c1c0902090610020a1509020a090504060b0109240c120305061309080409020d020408030c01 74
    0x1105100f50241c40310350300d1203c4140d8951803035202c0a80412207084d20304032140f411003400080c00b00a544195a1074600e1080618034690440d4881c0c0840d1400c5180c182c1c00000300140002413000384000d000c0ea00c0e100e0710548445c421842002c00c01c0791920304828412215062564210340003a254204a2956040c0384910b0015444840d0040c00380500104d043d42540c0503400030a60040d1102e696000d5a50740e0030702500380200240590001440550588411071034001d10720315210b41c0200d00e0014030700400240315000b501c114410082d2000c88044543c02084507680c050300108020401ca03071010705980503040e454402980503500399004540300000f9403140b40164029841007162100c02801075504070000d000d02c426091342c0d0031000d00d840000f0290401000c0d11440c090709140b0700740d0b483d078403c0417011409c8000b0030380742d1042011905200c444a18110f0034207400740540700e036903110440715200d02d000d60345940d9000a80e21001103581c1d01108e000705941c404a070303a02c912958003940 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 139980557 1250 139979307 139979321
    0x606041d040c06030c08181c030b03010b010309120e0307260d0c03020319140f18040507050d1a0901030812150a060c060905100b03160e1303120f 64
    0xb628610803500420310070b20a2080180c1c07000503880d20046034880040107914030094104550440c030502c1c40d281d040c1c801d054402d40001b002602c0c04180c80039003100301400c0d110301081e4981014507105642012611408201d45603045c582800740c050740c00384000c00e042c501c041d0462942014100a02c81909822011960001c0c2d160000c0e20f5504074400030845400072640c0c0d0290059009001b141c074450b4800201c2040c0100354100150b040040e160340501c560088541c007486200b02052031a100715022400c0e1020700e0301141d04120078038042d10098038601179107079030356a02030390307802040c40e524030040c0383d841c60310700040c00e4412960f501e180c03000c21980f00f4400e0084d040c0e1b00c000810040e01a9060f56500c1510040c240300910341084402c8849000501c07003030315800c0d1940c9049000c120107004110500108140200c1c1d8260408107042c50003028800e01e000b01100c0c09410040c29440390000d1340c2200c02d4042001d24100c0d11b080c1220401094030b00c154030079140100c1076604140702d9200c1c3c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 139981807 1250 139980557 139980563
    0x20907021b1c02090703020408070b0702091b0d0b031203040f120c080715200a090509130308040302150109060f0b0a0807080603010906091104060b041d0606041d04 72
    0x2407400031003402140d0501125401002003815900d200603e0702c150303059800310721441d005091507903c0c05110b14203011540111300d41c0070f0000c0c01500b9410007004095004c0301c1940030410a241c0910304a9091159204088455070340304400c0482e941d0901140081d64001c00d1903580780e0901d401c0844100d21020400c6681e4006202c450424500a411021a00d80c020302200d04015032354541d0190780d0500b6a0b19800aa40d90000c88001c06102000c5007441445880300c98907480e20210203818009140c010b50b03c540320350b004010b0301c2d002089400702c10343d5040c54440c5c01b68031546000e91621200080012041d0b091400100c0c0d185107a6000c40c045480564560000c569558006000d1b4880c40b2160000140204002002d1500900780590401405000050001515168101140c07d04241102e080d00c2800403140d003071409004100103054001490341c81c19141c5154418401e44081940701c1c0c000658002400e6070340c5e0101a0350013400c90f418500c04c030780c00c0b950051403e41c01c02c440403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 139983057 1250 139981807 139981843
    0x4060503011418060f0402061305062106040207020a090207110d1101020c042309031b030d0b010207050102211c0c030c020303060d0311010e0d020610050102011a09060301060302090702 81
    0x910182480062450301980b04c140984e0146d4032140c081c455551302007051390010415603c030003d05515290000e103950030801c01c0004441032111260941c5050141c00ea40c420390041c0443c00141e0707100034017803084400c496001a0380390310700d00c1c0059031006205d0920b07900500501015060124200c11007060a10917400d8894420b0b0310003c0004880301c00c0c40c280000c0d4040400c2d001c800300100800c40c2c00401110860382009600300c2c09200e0180c04010140c1c0c01e40001c203416100c1400d0b805032000c0e5000900141c40c2050070000002e5907035040350401403450440c0c0c0c894a515010b224103c0e21022440fa55403404e491810301e014000e8400c100c034040c00a072800d40da50394650b00c0031050700d00824005084035071100d000e46007152900c9607440c10403915546c03500e01e070108180801102d002e800164018010307926140c21256060809071340f11074190390401e06074401c0c4048054405515101c2115101207036110316022a00401031908000d400802c00741c14041055000a004142c0d07000201403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 139984307 1250 139983057 139983091
    0x204060f03050606120406090201030603080a0917030f03040b072c1e030309041109090103030305101502030d02032701020301210b01061103070b040c03020a060314060609040605030114 81
    0x511680340f04100e149110390420310003082c005641fa4009240e20ba00503d800320392107440340c0307407405603610404041010504810041011000381d0403500004854440550700300500040440c0c0035100c0240010521464500003070030060050042410700c05210a10038690291145213886203001c40340114444d042e40344080401085044d82040c107a54003070051410225248113100c0a03005402e587c21200805000c0703840c407070300ca00e01640c0c0210702903134020850b030400740740e01c030822000c0e40c0007205850500714117041d043e42c0000032914200642e060050f540c2e600d100712103869544124848000e070203d030800080d624030540156040c2c401c1d03103500a0420b50b90700328002c940b464072540100199490001000705e103014459442c8580c64410540e40341501e150f41e15a4188000c50301101c08210141c01441542001d5900001801a90408000614445005006da044001c048620418000a4503405038807140c100100a00024000303004212400c907066460400494080341001804c1d11 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 139985557 1250 139984307 139984309
    0x5100f1107050a060c09050402030f0106110a0c030f020105040e0405011a01181802070b010909051c0225270f06030213020d1503050a0201020106060e010917100204060f030506 77
    0x2003140c1d00355a0060041416a04640d588006410b43c0818a010301160190005041d1124001144a1818585800595810040c0c0031b40504401aa8070009074048103041b000620484100300c04d80e81c1141d4820800c0031320344012519485141c100e0314181c12001c0a0004000b0150043c142c5c030143d00d0f20f0010a40750301c50044500410a0b003a41101e86885442004402522030440200d8412400d015251804a0720384200c0b664003030340844a19039481c0c1c0701d03605106040c8664801d0003900c5403052998164030750001e50310140343e8140c8890300ba00c4100710350742c007881620810050104800d4030321704e4141c40c0800d001d0f9011041000b1449802c05080c509070300010f11520302900d50082580400002249140b402500807040740c50400769102c4c81d10f010303412000907050046104000a041c0c0035202c0c8002800d56600f42d01190900088c01240400c9a801486110a403842c10400d07400c20140010030901d40b48082000781c0030749100240100303000e0391100c080061403089e92028003103915004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 139986807 1250 139985557 139985591
    0x6030c010513170a060c120f05060904020f13050a0903090803030f0c031e04060618060e0105060a090302100203041d0105010c12020307060f02091008010b07021c05100f 74
    0x10400055040d000c80c091202caa11504040d40034003c2da8121016003c2640c4c5003012607540500200100310803851900f0758900c1c9000c0e404800350528014011414104007045002c2405000240306400c0910b0741811910390f44402c500c03c039500b104c00d00c01c60402501100040c00e14410030740000302d80b404086011071000049a0080e10030502c41189903441c0c28581000c1c2d04081e001d401c03856105903072180e46080c0c46480034020740c0039090008585181c1010620403910740344000111a003080d100308030a5111104d06411610b00b5100f065030f81e11205030403210f001c29a04020350181007140c54a012560000c0a04195100e041c20b54051a18060b074806001030240309441c002130300c8000900020305462008401e00300d071401240e0038051280c2c1c40302c0556144081d282c3c000d036070214401c105441d0030400500c603034030a41000b642035410001c00e05010310400c80d003e03001382d0141c0c4259555004c3d8180e94135001c0d170048241da1141d011030451401402a10800c0882107007001d82c1900c03804140 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 139988057 1250 139986807 139986817
    0x11106090715051b1506040902090a021309090b010501140c1c050c010513121106060904020607140d08070906050d0c021e0c090106020d0903060b04110f0306030c0105 73
    0x49030082404501d081d440c40c8070000010301c1101009010301c00c024140d21150000314007420a0b00c003030303ca0130001500f031203141c14000b00140e1140e41098403d1b405078032480011074201d520b402d80540c0da03c0e0b0f11030203420035100c264000e03140a403a042005040c0005000c0d101d069403000d0703862120700091030a83d00000d000349142c660b11a0040a045490340308100c120107425511410002d0400701c5440c006402c40b5012a10b0820141000035503404000594841500c0140c05080c0713820300080ca07101e80d41c1e541c07600030301e000d006001d0a00810f06640da500c05464403d98405059810002c0890105494040c0c0c1452000032034008c1c40403030600c80c0a000b518042c0c0b50581d880c0c0e82400085142200500664003140084d401031110083c00000d0761041ca20004800308010701c00342e0308007070900400350780c1644460115001250042c00c5668810711741001c0303a030081000309145100d03a0015000f80062110341c403048400042c0c0c0301900354008061882100102c0943e071030380400100654a0b8860 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 139989307 1250 139988057 139988071
    0x3020702030d030f0f020c010e0f060937080406110105060904031b050f030909011401020307030507060e0d0903110102060f06040e0708161a07020d020904020616060b011106 76
    0x9001c03104880e51003940f0014801340010000b20b82d1011380c0705040100c0c0e01c8040c100640e03944803148551590802c02007044599040d800034509403500105a45d195043d08004440801e500310032406044001800b000074108200381c0410380340d80e2403420380265489442040c000c9118416801d00c202d9046c41240d2180c0f90180c81c002d81c6d07503503d55084510f0340950074254643c001d005981004260202701000604854500440c1d07501c0d41d1904200354020164402c4030007003292000100941da010094648099060506648403a02d500e0064054121110300c502c5500c00e0000c13958503194080b5030175048038041d081c0e020038020103200498031068116164080462407002083c0281481d074001a204039201c0160344400d0f0300c0d141c55a0501040490007401c440d84114180306800c1d4001c10400c0f800950002c40f0314210007680812002460070350017074400c100540004065446070412a45103229640c0c00781c0103030949203172100c014201d002c03480b03002500100a50000c02e0f4002001c40c01840 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 139990557 1250 139989307 139989313
    0xf07080a03120c0513060522080c10050408030c0d1103132606010b123405040510020a03180b0412050a0209040b04111c0b0a230f070302070203 63
    0x242d0303030306000035008449005040080812000c020b40c001103407000007030b010075950181d0751001805601c101c54220041c03a50310107604601006008000200040c56400c00d0719400100c01802c18150f0b418042c982c03156071f06010014030411102404500c580c142415a152400f5041d4000c81c03480da24060030101030f002c04c0c035101c014082051101d080c001e041400b0f03a001d036a21580b00c035800c1e081410a0340301c41a0400e0225031070000740c2d82d04a803075034403010060b83d50396403040d0a90350582c104131501e05801d40342c42d8503c0d4840501e214004480c040c21001d03040300024001400c2c000d50324080b44034260009054107103800310200c90783c2c0c1c043d0100c60004104034103180c28600030000c0101400c004469520500c03d070280103848084c4800d200314081cad031a400d0140380a0400b00101c3d280408058030074036282d4400002c240413500b250b0030072078221072402981c0c0da400441100404580034001002044803164500254100c1c3c0c1080c0b041002d0312000130240c5503000260264000c008000f585a0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 139991807 1250 139990557 139990577
    0x121b04030503090f15070606050f0306070807050702040207020d15060b04050609060d150b0309070603090b0703020304030c170703020f0c0109051504050604030807020f0f010e120313080f07080a03 86
    0x131415074084040880002d1140a040c0d00f54032100b0311540c044441114074940f0341c03404000c5850711094010003000d05502806403841c190100420540e002400c0105001012401e80d065481e558103881e645c960140c4155076070070b414102195800380c40e8a811a080c0d04006001c151032003c1c4096608440002d046a03041000715020860241c21101000900daa514850318610455046082000b094441103c1daa43d00303007610010b0074580c280d00a4000d0509003207551001031440055a0b500407254a80143c8984452400b201c640140400c080c01714070303c2490703c100c3c1034800c40041070318521030740840340034102d110b02041d110f03403041001501090303030200200000d01709500700300d00340e8481c00015850b168448000642681080c2c20556442c3c00100340c8100710b091240102900510072102082c00c9195280005e01881c0d80980490042c440329841d00d0304968100250340402d913280703030001c601c0c5440e200d0081c0e403003100500c0030401f4454000001801c0001040c0b814a045e01a501d4607158 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 139993057 1250 139991807 139991809
    0x53006010f030f020d050115020d020c040b03100f051609080316140115090513020a05040c020703060e010e06010501050a080a05220311101811060f121b0403050309 72
    0x24114030740c03801e16460304011082c0b141a44014040c441c0440c0001410354108202d401c0d02c100d400c40c400c029035003c4840358241c99000211a10001800c035404181c0700c2343c0c400440e040030044800f6079a0181450340b40c10b492456a0401d0f8440c01c0801d01c00d840ca04a605d10490740a8414030920540383c1041201c001590310400056203041e014030080c1c884550310704220341c00c651040e01000d1012207c1c0c282401005098000d594102d54582d0121500c1501600061107105151241c0e502c2540d9601c3c0010b203050007440307060002c54000a0401503c010711800c140071f00384070070754400e46008035000890303250b002e41c0950740c1c0c2c0d1603141c0e20340c801c540d0741740000c0c002820050000d2110080b4181940da081008003040d8540d076220f0b0703a40208645901702c0c521303d410540c00b03600b00c1c400d00742441c0b982190380001e800b6140b5500700100541804000010454038420b45410070204a80060420303008040c1405003801065100c00904212440000e0780d9014021804010541e810400c80c0c6401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 139994307 1250 139993057 139993067
    0x60e06042a0207120c05240a0c14190209060a06051801300c0801060c0206070213051f060513090c09090204150e0f0f100e0402030705300601 62
    0x6081c0758011544881d894421181681848410441741c09660103014001ca080801200c0d00f4101d4000c112030000f44d11114910742409100c003500b0400c0898181c03001486420340042c0720703d140c55030550310007a0f42040041182040110300f40e02409200b404640d13075007000c0d6000c008460b6550340701c600b0040c482282243c8000541d00b55410044074440c4001d40408511008400c841eaa131440c0c00701c060104440c4041d60079400c0b4005c1441f40c00b4004028264228001d00866603045540c956100f51038030000f03065010980c603480320b8916140820803242c1584a4001144014200401e0b91660702d0f9000c039038910403001d0440c02c0742500d002c00c002a0303445410400740d552090802402d91516103100703101300c3c0c0190b8404d0901d060601001502c940c1c1099085040b21010744130081c0441145c0301013041e42e402442c2480c010810211400d00591042c16000151003004000759640e04240c20000c040c6c0e04100350401607120200c8080e6101203008803e1107a0148420381094150340d01030041d11 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 139995557 1250 139994307 139994381
    0x1d180408030c04090203010608070305090a030504090f06090608150903070c0b09030c03060405030901090506160b0601050705010606050a0e01050c0604080f0d050406060e060901060905041e02030406060e0604 91
    0xb104200c280004520820303140041c502911442e562000c50f46004070300142078400c09440b00d18503030442c0c000480825030041c101d40c03e41303074221804135060b035110003134400030300c0c2c02e62000c84090301d04440459007060109060405034140a05210300740c0303864180e541c8a103d1542c0080c480349400808103d0380d0309810140034641c5c0b008054540403260440403e04144c011101140c407a000040d5008003980c01400050160a00780c40075030410f0031400300d020004001c11070140c452801000010100da2040301203601141c0e00070001d02610f40c1e26803020f05140c21800080003c11a806030a401d00c0d442042614448141e42e0024842c60325603032103000b010b07880b94007410b07104e240c00c00c0790a894420f140541401a4410340d400509903141c502c6a4441140160921348624203000041203003981c8503042e02c080e664111800900360700c1d4280c40c0b494034140308909007002400030041005001995100308100d80b000704840c44140d8910301048220350403840e401800003111441d03110500e100200130b074 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 139996807 1250 139995557 139995571
    0xd03030e060403090905010f05010e09040224040609050409020618042c07080c0901090b0a0905040b19020f071b0801020c0d1701050a0b0702150a1d18040803 69
    0x2040d00c14018a50309081084600b54086201d0b10010020030019100b500c0c01000d0134011401120304100c0021700800c3c04d9072000307200300403d4000c01c0c00d642d104031100843c0a00007508040810645072000f83c541c115118140105071990310004041c2000e000702c404030340d801880c4500e4038801e03040420240c0300c4a810341d90820754a0000c5444c880b5402515420751139203818654441c40114003082c9000307055080425540c20401d001c950740c2e202e4000003410f403035880c80f01194042e00f1202141c00803025901064075a42450284010b0142d41404e65001e00c411071540130395403090013450b8041e0711410054015a807401c108203804103007080002010780c040380c0b00805010350f941d60402d0990700034108500141e040301c0c0d80c000e034880e00b001100c003100c00e0f0b2010648080d89440000341d00e540b2248140c2001120001c1d0340004c550f2801c2680f151024450034480c2c41e8621040000c0107019024000b03034104407048003c500c28900140441c89910244d42104501c0e5544d540700b00854001500030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 139998057 1250 139996807 139996811
    0x8070807060b0901061805040606080c0d0f020a050702010e090907140301020702060408011e150515130f1802132702030106031406060307230c120d0c050c030301050d0303 75
    0x10300c02d142d0340c00810b58000c0520356591016002285d408002118103540007500c00d51601e4010840150040140d9030300895a40c04240c42c1c0c1c040016000c080d265a0384200981840060380900d9182c008002c0c0610394000ea03070b00d40d8140290703414480d24030b9040d10b1280c003a41c01480b0400146006000b22083c5110140016040480030303808545160403035007040c2d600342d44991004002030768104c0300040444c2819014416040541045041c040362800360500603541c24000c4006100c1440c1259084002050481038092399005081e615000901070b80c800040c111103129581c0d0f505000341c074030380708003d403403250440d1400d100030b80b003c510b0760a5031800036400a628401d006c0648042e5008002945010812142c8011400140e040041c80c49125560520038000d40ca40d0103205d031040700b1407114204401b46851500e40c4980c0c080c8610440700e5105e10002070384c1c40c000d840003515032202c102c074050000d1101031505480324042c041003582d0b142e00c24401040a442c104610744c0e0042c4c041e081c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 139999307 1250 139998057 139998071
    0x606030a1b08070e01140118050603071704150501091137031b0c051b0f060f180a0608130f17090f04021903050c1b0a030215040807080706 61
    0x2280d0030403290707601c52001345801d0300042004803040d204030700903a2803d2a0002c0d400d440d0410300031680c10342c1d0141c1801108044001480300380035489140d0368007440c2e031b00303100c692074589400740d40c420045401d404150f0804c00002580e00d503601406071414805540d05007030420142c040f40c00c0082000071200030f440850081c00c64000040149814504166004a044006003032105003600d8903002c02002c014000700240d010603c0860710112030810700d140070054400392000a1202d0040003001d03a80001e002404501c20140c601c000e25801e0000d03422940701d9243c0c0b004002e0001356510416011991120019165104003c11010910300c01c42c4000010ba0650b1504240d03181070004e00004504005102040c070b2500740031262400304c0480301540f80131441138203030f000b0a5401e01c0000605032524085490b0000c0c3e4403d42c0e0030041e41d1100388504040318074020781d642805803021340241c0501c00717007c40882a01503a1511454000d60007600e0454940d40701c0009600810040d0741c0c03182e41d052 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 140000557 1250 139999307 139999319
    0xc0f0d060b300d090501080c0a090801020406020d0e040204120210030f060f050f0306190903050d0509011e3803010504050304060f02010506030d051605100603060e0606030a1b 77
    0x4590004140900c02c600558504080381e2501d00782031250014090389490401590313078404038060303105201c00105c0380c4a2100f5182a0313840c080340c1c0c010300a15400820301140055000070300360441902c503079601d55075041e80e4050004922580c022003c040d0803514042c000750a02e8100007030b4039406480d0001e003034440603860380308680040c1c005c2c44d81070384440010080e40c54440c010700c0c9840c004902500243c1446600515090b80d02d11030703032040541b200e4015041c94020420f50305001c64070030043c00320b4581000114000c0c4035041d221a030700180b0901c20f0825140510803041c07546000e20408000110707000b0902042d10036440c0340d21100e00340d1a42642151130a0044a015500c01d900540e01da90900f04090070b101884172421086a251804002d00c0743c0c1c2c0021048114040d5042241d501c2490014140030007d0251024200f841141002c001d0342a07143c2c040c4080341e0044404104500480340041d0301c451042e102140c0c540c2c007210512010074a0794680e04800d2070441a207003541750342c43c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 140001807 1250 140000557 140000599
    0x30a05210415050f0f040311120309031233060d15051f1b0501060b1b070605040305150910060803210c0304031809020d020703020c0f0d060b 62
    0x4904945a800703108a0a001c0b074100d000b90f036080403001200c550a4905504e03401e540050040000e402c101d10300454604020007403100419503400340c45110765a1a004002903640d80c054044103503220241c1d000a1500100313000d030704070307075400d20502c400080c02d00301c4086c4c01401403c042139621800030090184d03001d0303680c13003080b12000e050f01081e8070a600d05010040001141001d5003010041a440d0b881019408040400e04a8401c2103280c400c51541c01d0050041846d5084040c10751000200701640d0080302c540c9242f104000310850710a1911440c003200c50f80240d02c0006d0640c0d00c0400c21000780040b020000354055a080304403003d40301d201034410203076445580828804e4000082d11824206054040b480d1005007082542407810048070308091441b00502c05820822001c003c00800021780c2a4040101520300b800c0d521921301c1d8007403000035405420b040300036100c2c101c03410809003440480b000700564028a0710514204c0b64440350b028011a4402d2940028182c407803040c1e00c0888 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 140003057 1250 140001807 140001811
    0x406051c0c0c0308071806050d02090307060207080706030207031416060501090b0406050423092505040e060f07030207030c0f0602041a2703160b0c01060501030905030a0521 76
    0x6942c454100341d01e1400c018098184c050280342c00c00590401c5e03907035000c042c003000758121411b43c54655540c01943c00c0c010000d0281d24492681401448000100b25600040281c00e0340d50303540a903111a55940015000c9200b6074400501089840300208881c0c002d040141c51250b07201c5110003e1480c00d42d039800704441d001d07000000603954448180c40b95003803d10034071018000035a420070004c0900000c0b0001038074401051000350150303100103000b0103c1448500e42100c0747c0316210011880310f00b80500e0002003406081e02840ca02001c2050300d0000190050288000349680f83c071a444182c07040740690f111000980034018807503031641c009404566000c040c58090480107031201d00b080401c42d0701e040486055a020301c024842c5c81c0c2d440d51250344406150b0140c00140030040c02200c0440c0c148400c1c1641540c21100e440000290f001601c80241080190304001700041c2d916400150100d466144c4081c0c66640180700e07040d2507601440c007c090600c50284501d0500902c1c080078040040301b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 140004307 1250 140003057 140003081
    0x110a0905100801020412110d0602030c190e010f0f020304030512030703180b07031d011a0f12031c0b0a06170112080d0c05090409060212060d05030406051c 68
    0x625401c001c045111000711401802000000f50303d4a440c1c00246450302c43c1000d0050514803801080c6402640d0340704071104180c1c0e001c0000d5440c1d1a110030700350b01a411103035204989241c80141500543c2c0b1801c03000075013242c140c60305030302003901c2c6074100c07103490703402c0d60b60801c0d41700800002c00402c50406c08260140c11040f585030380c078904070b00024203568a45007031416079a5584107400014840c100b2940c1d0005451034001110328641c10000c5000c42e00b910200540d500e01400004600d43e120341441001009541c0c0c91000e0705204140305040c8140703084480660428040080c5040403007120b140d050003010b00124203904148000303119022240c4c0400e01148000d940e00441241c103041c0c0b1401403540c50190040d41a858898102c148240785510304150741e2522000003140c0a0002d0ba100550007400401c40d403107581ca00b0740020340c000d5204078000c800f40b50015640745424101e070091590310501540c2031910b481c030141d600350825002ea08500041002c02d85002003e03205d1050340e030f60 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 140005557 1250 140004307 140004311
    0xb0a080712020c010e15100603150e0a0903110c0a05010804061d06010305010516080126060c07020f03010b0105120711060717070804030203041419080d08010605030402030a0f110a09 80
    0x10b10b002503d00b80c00e8404000c54102e032003040213920030b80740000c7d1003141c066080208841c0c0c0400801c41c40341044d50003070150f1a0b40f10040c131449003443e07880040b440703102c1d46915011010340e2030b203e966808080c0000e82e104007501f00c00d01c010f510aa0102e83c0241c4900c5000c00c045581100a60f400358007100c00b400190702850040080c08003d01480b50071000c40c03003101c221744949000c01400c40d1814042e81140e03401c0d407000d01400e0020b4104c00742203084c180080d50000e0916582084042c0e00c001c00a0344100005215944186070600c504d000070070b01615164503000c4034054803117121100130840414446200880482071205121092240c4400d89e201d03207a419001d0b199046c20078000d4007000801c074010080000281d000801c80d01901c5281006000318005500024007101c407841c2d01a031071840d10800001c52540010300c0700001d881c0c54442c8007460ba01c6800440b11b03400200c034041d5055101306000c40c007050307002d042c2c40f9450313004500e00240e19000c1c201045105c041a8041c0380419 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 140006807 1250 140005557 140005571
    0xb01030f020a02010504150e0c0f030a140d030b0108061305090a080706050612060f04030815130b0a0e041709010e030f0a03020d0f120e0c0d05010203010302190b0a080712020c01 78
    0x16a400003000346441080408c100d94007181026544c41442668030f000b501e5582c070b0b243c035681c0c04010010328190f10040071445840e0100e2641d407141e9010030081c001c681040100c802030760040442501c5244040c0011a11500306040080a810003a02111060142e09440350210300058001c05445003e00e00c04130311810440107020030240001c80c20401c5811510500c990402c1221090313422980610384828a51039040d0110b551368280c1d004664484010b484040b41c80d5620b41240c29038a400320b4a040c0c1c0155980c59682140c50100c4000f05140010700001c3d024a508002420001e24185030281e010702604022031310b40010b00643c8002540851198410954108034010a07851941b404d920808031518010348140d000812038007403251035030002c130411002040fa8008415000b407000c00300d0499410014000d603c00e003c10b1340503802040c1c41401241d4981554000c07121040d94a41c07800001d000216801d100103460002040a186412012001c0c00d002900754619540b000090075 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 140008057 1250 140006807 140006813
    0x10020c061b1c09090c0c0311070f06020a020a1403060406020d02041214010b01050901051204060e0601030803010315110702010f0909050c0405010306080a051c09080628060b09040b01030f020a02010504 88
    0x80c3d0707800d40c0a00649420403401100695102400c62660341d4907040102e48400c030042c1c00c0341400d02c070782c000700d00b804039009000036403541c0020041d28490003030303079401380d0103032aa0b41c0c0060003625160000d8166000c50040390000f031341c0754010194800944001030505448070000c98010b01c806209403029070aa0000c0040d00300d080c403402d1040c0c6000d083c4245400b48d0080068924001c10500044c41e0507104002000d00c2625000003841340020001d90f9665a140e140c059442d40003804155040326850690080e580914440c0b007203001c00d00781c055030410b02c96138011030358924690300c02c40402000901c002655450703400b503a8055450a001103885500b070100040480358207502c50190341d0300107560360010800c042411000c0444148640310300c0d40104100f03480c154069400180d045c0304403010080c3d694201c40705105c01010081c00c03010010307200c1c0d0000c800c1d11550702484d0380c200c000308241d011601e8a940500c181c0c040c107044c045080905840810200e070441900a40540d466401700020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 140009307 1250 140008057 140008067
    0x50a021c0f02100504031409030106080319081003080d050910050103050714010302090d0809031f0b09070c03170a2003072006010306092a1410020c061b1c 68
    0xc810000000700021702d00750304c0081c10309030140500a01120005034400c8181c80c29007043d0007414800c0110707a070381c0b03035084d40c0c482680742e4000e41711002901d2600030032001401800107108881e080f1241c503040c01603010105004160140100704103104085e00705218038058090180294010781c082e110707041c901402071801c003030444041410540304000c0c0381c1e201c1d034400540c61100b5402042040c0c884001001080c54900d540c0683c4040c0a00c1010282107092560461803684505aa0080380e03a1140341003507807206100c0e8801008110070318154405c51400350032103503100341c0610020a88401e481107081d9402c040c00c9500c042c00000004100c0b603140c0020a4440c0d254400d10000780301080e0a40c42d41d1110070602008010680701c014000600144c06440c0c081e14480c101e06c41e040340c056074102201524180b1802d1040c0d44071200340b1005241040d044a054442a0040c0c4100c0b489402042640d5000c810501d80c0307070b00e503e0b41c41005080200007000c00f4071f00018845050304119030006d00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 140010557 1250 140009307 140009323
    0x15060905181b06031302011704060b0f0609060d050a060f0902040801060f08030a030911090906060a052209080f0403120206090d090b1e0c0c090f040c030201050a021c0f02 75
    0x1400d5035180c41000382e00c3d0354044a40c01910600c2e40310400d000d910048130701e2541902075141ba050403500740300920138186d12070010480110f03030380140d08242c0e100340003983c020b0914182e07001d903040c44201c802000d9900f00355801035504d00d00049041d1555081c0d50180303581e0308540d61055000c50305020342c1038248071301c001070016207018040b0030b407500c034040d50f40f849855100c104150701c0e81c000c18100b003000308242c2410100100030741414504008035654800c0101d604c1445040510000111420a605446607842844007070803560f12103410010050084150b0031034182e03508020201e1100c03c00030103070003d180b2403844101c4554041c50003e10b810f00250507036140350041d08807049069000783c03004044450322802240c880b4240020100368441c2110548090b013000907002c10041800700b9250f440c44021103c0c02a181c44501c410400760904880080240c82202c05c2400550f020340c0107011074849500c122072400190030b01d40c2c000031350046100404650307182c0203100380c107030140310740c034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 140011807 1250 140010557 140010583
    0xc13150515030105010c05010f023403080c0702010c02060a0e0306090c03030414040b0d050102030a11040e0a0222080a12080f0c0306030a05060907062006041506090518 74
    0x1540c00c8812422180c0c1880b0611074075040c0040081104c0401a0a40107403402c600d00100464643c04581c0c10101c4070380349410080001c03103042c40c1c4d40746240c820100b1a046070380c05655031062507480c01d210880360707481010140e0610010749007000040c0c3c2c40000600c6141403641d124410091540c041c186014805000c07048160441d16080d81542c41c0001079404442824168a9280048102040007090680c03942e87c0c01c060030710301043c14030070b054008500400c0300c00c1041003035510791070049865010b0740c0100041076030150302003a003103a442c0d0040d01c0c6032000055020145c282c010f58000004000e03901442040c1c01482c13400c002d21000010b54030221001d0f080480781d43c0f03840e00507960b480074002c16400c0d415101102190440e20200f103030303080300c5501030200c500c98100308a00c3ca0340d82c0040c0c425900011030a9001d071200e15500c281c1c10410314502c100034a1251211340c0c0b41040030010300d040850040d900c583c006500d14550296500515001c0080309a6100c8d20422500b8030050000c48 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 140013057 1250 140011807 140011819
    0x501050c03130f06140f180304050a0308030601140c060402040b01030507020d0c03091706010503120c0a0b040807080706020315012c060c1204080f0106030308070806030c131505 78
    0x10b54148000540705005500a68500d60708000e0b04d00980103002c0150100043e20f00d103c00c03c48480140b41c1518050030020075490b500781780c1d040d201ca56a1040e409401c1d0001c100d61400c2001449060286800c030744141840d944406900c041d42c2d4803600301d6401460944c2c0a0400d010942c20640b250605034202840d082c01a03240c4440065507440c0c0012016003001201152030040c91701c9500031802500c44040700f41c041000c00c0711401d0340d40e0320a020716807190103103150000d4551001c3d401c582010403280047c00740f02c200e5480d210040c0d00010004d440410082112200042101d002001d606100380e80050f100d042054070146e19840c07600501c0e05000b0005000c20581c0803e43c400c008501c00020481600d42d907000128480b8010003d000c40c3c9032290000e62004d40707058101800036074050700111280c0d0060f041e0480e0030395166100c0a00464540408624901e11404501d507000c500602240d04154400012031180510030504092540d070f980521703502d003842028200010721040346c80c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 140014307 1250 140013057 140013061
    0x6070f0303050a061a1e130303080907150f020309061603030506090606030a1e020706060303020d0203030106090b070206070c060201060f05030309030d050a0219030c1403032a040801050c070501050c03 88
    0x15800c0001c1c100c0d40d14035144401140080300d1880f1005c2000b02c6c4000e09207010740342c1045002d0130b05142003034002100030800c0140005e008180000c0d601080b64800a4013180714000c0d90410b83d81e020a60900d242180400c03c00448c050320740000504190b0007219200e1000e51141c18000c003281c81c050507a61245c1090700030b100700d03a40c03108141c2e40c0010010741d000460f08103c1180e140c148005502c0c8445007800803c14030103008140c1e1151040b61300a07001d50341c1303010410404036140d120901503140800d590070028070844076482f0181140301d101410003481d140c142c1d102c080305400240d000c400180c0d156042400000074040c0544002d01c010b80083d130800400c6800280c4603074583c0c0201c01040030114172652000d200b00182c910420002e0180c2c841d000031801c00038000c05200c2c0c3c040c0d4540c512490300124900002048070f00c140e07a00c0c1006e40e24185840640b4100d01940d41401507500b074240b00c04a80d051003071040c90b0007100000c80c000c0c0d9500b00e51034201d0941e48010003001d909103092003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 140015557 1250 140014307 140014319
    0x6040c12020307030204020d020706060806011d1306050709122f0f09040204090c0e0708072604080409060b0414030607020709090f0b040305130e06030c0103091106070f0303050a06 79
    0xa0300c0c4050f20b071704580160b241c442c6c1c50040c000a000d411405080706090400000d400701e07000c51078174181c3c0c80043c0041801c6400006007014680d05458015502480a00681c00b0905c10b03444260440103a2400c1d8405a582c0c6061401440f1000700c1542c0c8440c4605c428401d403403044a041035180600360300700c41d8008a00d40022040040c584009000c0c480c1a4002030441d9602d40c000702019a0000040030311645440101c5040f517400c8030940007250060020034402c5005000140c55800c1c11000f2412940d041c1c03811514942c2c1c042c0c401c07590740360309000100c0d001c41e0303500450010303149144007540c41300d1420315107500c00a01c000d04c0d02c1c000d0300400240048180d01013000010341d098400042005140b80c0303000c0b220200c5210000c1c000c1004041407100301070380440140402000740d01047c24141e25081404800141981d20f0b07076040d405a40d40710b901d54001e4100241640c0100c021940c40350b0041d000c120b03594401c1c201110341e000310005040c01c06405104140e000407030090200026400c00d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 140016807 1250 140015557 140015563
    0x2e090509060105120a0615020601030501060506041206090219060e09060a0308190e10030b01110106060e0409150c0c1205031003080f0d06030b101a030c090a0e040506040c120203 78
    0x51007001400071207000111181c103560014002000040c1030038500a07c10200251601c41c20700040340c0c0d9500700000006c3c240381c844142c6042d900c07041c40f4a4203c80c0d095550400502e240001240c12040c0284c2c07103000f0b0601c0d011a00000c0001e51a80325141c08043c00701724510100800132880303181c4014051002c62102d40503940c0b000103d0300032070203086650a050761102c02c0780500340d900201c41c1400c91300d0203515400c214004803007a201c41a80e55010f421243c00e072403180c0101e0000400718200c03d0410324094001e4000180a40d0b801003180c0701c0c0360080000e8421014412010030554642c1a0402150a401443c0030b006454680e041d070900d16001c002c6c1080a2001500e41c00020514000a0300c280084404140c641c0d0b00400c07626690749071000004404030b4407603a442c024250000359501038000c10320041c03c6141401c1e0315559820050603000e422964201e42c000580c2440414506042081c05001e140210018092854145845050200d554001c2001507040c0409803005803000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 140018057 1250 140016807 140016817
    0x10216020103150905090309100c0b0408090415260d020607081b0a020705030717070524070f060510080a0609210306030b011a0403112e090509060105 66
    0x2481c2c04a103a03001000080324045954110b490745518250030701c1248880007006250050099941400340031100c401a51100c0c4050809000d5940701c800240009000000030001c281005000140d0101c146840c0c0c504600f032a08003500c41c00e07100030301c4a000740c143d40254a01808100091400410700e010003900c40c08060030344000d000303110340891400004010021410b00310002d4082d165480903030003cbd5102e07800d01c142c0c1d0180c0505c107008603681196505414805500c1c1d00100081484c0100b030100316844680140e500a501800f400c214910748001040194054455920003403164284a0100c03a001340c104a5403903400358007001100c0000c01e041702e100d80c010030000780d001050f05005180c0b103d494400e445100c8680724507041203070113901c002c09403400342c901c8034a66a05c503002d074035a100d44906040c070010014481000001c1446425003031854001c0d1040070710848580e184a80c1240014140e00d40c0c030807858600780f80e0340d07003e05460003c106c21500c1c1000f80c104100040c202d8030403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 140019307 1250 140018057 140018059
    0x1c0305030402151c020f160f02010801052b110301050c07060b060403030c0b090703120207080f0c01210b06040603020c01050901110306100c08040e0718050a0608040f0c080c030f01021602 82
    0x204100300d41824800c1500e10041c0400c84180c05150700d850002405c5402c0313232040b40421071040010072b960030b100c2c0301d0482012000c1c4841c586084e00000c030300b010141860040710b00c0d11110291b030040d03890a0040c81e00580e8030950ac41c0d01c60982d40f4000c01900c6103c1e0880f03004120034030080000c07a038070809400e18941c102d42c001803152140400706050040d550800740c03a81c0a00f0b0044800300740c1c00030341c140c110f46208041d83c40e2915059074817070b12201c002d00c12a0002e24803400480c400484203280e07049090420310005440c00300e900c04250340342c00c1540f186000c680e0106072200411402e002e5181d00400c802e00800c0103e04a04c010f062038000035144501a0498068074407615001b1909141d20541066447c1d4460783e0320074030303c2a0000b041b1010000902e090318403203905034042c2e107001d0aa82c0014024000c3e2414000101c900c07000040082d519005a502c01c00c0110316060303c0900a0004400600350f50105c000130305140c046181040e4915030b204000102d0018040c00c00440d44680c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 140020557 1250 140019307 140019311
    0x3100b030d03050606070b01060f030b060711060f1c0506040b03150f130b0a2f070303050c190e24030c070503041802030103020315040506070e1c0305030402151c 71
    0x3ca180110304031b4011443c0c010a026241400440d5803a081040a006552559001d0040030314090901140b402070300300007802002c06040c0d41e082c500c6c100014080549166103684c0c00c080384401000c001159500e400c0a040b6520002d000c1e9609060254240c0500e080d0000d0400d1315401715581030000000301000407a042003008500c07070041d503110003142160403114101403410b0107141100104502d0741c0301500d03101412003040305076130110010359a0708041d903070071410a2510784003a0044d1a0003043c4625075141000541c02048540c111a14800300c1517030340c0c6071050249418882406002413001040026404080c080100c2820840360b0040382e0782d11564484110b0721341145140a603821401070f0b261822032003c28456a41e000d0760403207008800319142c101501c0c010018103c019039015081da0071417400144d1032030113132429100070900502806500310030312010003280c04018070708078009407001042c4000c1d460b108030282c5c48460240003070786c075000c0001020f000071210b803103283c880c0d26 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 140021807 1250 140020557 140020561
    0x2401080c19050f0c0c0913120c05031204151103060d06020c010605090f04110f010c03110a080f2a0a030c05030d060f03020102100b0105220b0703020c03100b030d0305 73
    0x1e4401c000380d40d48801c2c507100071519080460306450b22401d18544c03150094000400040140b06c0303012401c0e8400703400c10390321000b91950543c1102c030b05181034403d450300d110411542c2c01c1040525121032140340150101c4009480c00825841558010944043c00743c17000d1051200a43d00c020101035140c0e80082c0040e0b80b03500c43c552040c090090340d4070003507220f08440c00304040741e0591040148100d100c0c2d0010a40c046803007041002403200c0c01102c2c2e0014500400b800002030041011141d007010500498103101d40e141d8030b8840c603511081c0c0303024201c00041100318000440340a6100c10301c0310f01070320209009079446140d50341c0c0b041110103003c00442290030f6050100520884440101c20002032240b280c03200880c1c014046648412070041c031600d0101e85076821588038200075518160340f09481d00d1320860403c100c4032907103154034000b03c44840c4002002e4907400d0040030024840d80181c00d0022a02c0300305030400a0050550301c0403418403000000c10303070740421a07894544490400080315 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 140023057 1250 140021807 140021857
    0x5090d02190609210f020109380702031b0a050a0204110f0703021f0b0109140402090306100504050106050703050304080a0912110f0a0f1511062401080c 67
    0x43c06038090301814907011501504059107043d002c1c00040d83e4680c40d190f144e5540c91030308a00700d4200c031310042c1c00003402038844200a20f445074085141524000c42a40b01560001103201c094400d441003030140c2d100160b040100b21100400c410907101d00d1029044200031030b12081c0c0c481d010248028422940e440848442000003410b032488014906101c80d00c4001368507010755507040465051540300300c0d2103440b03171740b40e840c5016005901d10180d503030600161408100a0050070300000c565401034081c000c05c0c01c1514104100384c0b20f0b1b104c0c0650301c1c1e002482c0c0300034041150410b03000001005070801c0010046500203044a42190b0f0204005a0f0f42d140c10b90221280044c030b8110004061070b003003510050002034200d243c0314200440320065021040804c202d03514040d0f22813000000c600d030200b08080c005041c4020041681c60800c0d0716500070400f21141004403c039030103040403610025010600545c0c414048074400f0a0030500c2d0709007032034410a4500d0141000768254801035142d04405 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 140024307 1250 140023057 140023061
    0x11070602070c1e0e16020c0d050705030111091008060303070803060a0f080a03020105150102120702030118050321040c05040911100306050301051b09010807051c050402030105090d021906 82
    0x800480e41c0b08109003000b00307882001c400d0244503d01804c5041c40c042000c5442d00c0361210800e401c82c2d0000c040701d58903201800048200340d1410760301030203514800030300ba403420b0003803020000c407110286503252540c000700700e40c0c1124000014200140c0508220507074400204440a40c0d4018081039200d0741c40e034000074001703403042e0001c0420001240e40007440715000506141914806d070002d00c42680e13103c02494140c004a01c103140140d00c503807221403859040000400c0894000760011504000740c0009480010801500311110b60000440e185411103501030210300740b20003c5105003605007500e0701c1201019a0041c42e11440d510100041004013164400390720880c0074200c03040f1101001d10150081605104030390180d420000081d221491059000008001d400d21807403e1000c02401107442035002444030041c420200705440d0008400340b8200300e000d4002c0000700f0b940c0380c00e2042c5401e4800107000b44816034064100702e01156000320703001a01d654001412000790034a401e00b000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 140025557 1250 140024307 140024309
    0x3051e070c0603020702030c1e061c15030b0a060b030402091302030610170609070b0f07081303200d2415030203152e03050607020c0a080111070602070c 67
    0xc0a41c40400000c5854140c0c001d801902d00032001e481780480c0306828019005216a140620b2071054840005145010009095a5404240400307901c0794041100c5c0101e445010194040c040707151001c00800c0110705009070b0101826409018451803c40100c40c14000540028030907503415001484c0116448030030745801c1d03001412900e16080c40c00d400000b00c0b91901132081401004040041d0340240007031468001c1003004000c0030587c0ca0002c2c1c114294110058500040d002040381c1004956901d025143e0302d03610000c2c03148200e245161146a4102c540d44c501c01c4c00001c00480c52650380c0b480703030641510f40c1042016001c18100c080400d10101180c03450403200b40341034691030b544500034a181c0d064910a070100c8503000314008044900c0f071422103000c242010030840c00c1401208528864801030740b140602c9412a8907070340d46500b0114100d4440e001a80701d040c6a28103454001000300041c045a0003c101140d08822000c040348140e0401400090300050303010b00300080461004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 140026807 1250 140025557 140025563
    0x40b0306040c05070b070c1115090603130209010f0e0604062303030d060e0f0106021c111608030d060504061d04080f1306110d0e0904021302041e0e0403051e07 70
    0x20019103440349028041d031980c4102613803188c403410048605801c00d101c141c8000110b46040d182010f03503000400c006070b480141901861541100e81c2030041c0c40e081e0b40140617000881162240790308140e00f03e03c58004c0204414491030030b0450810541011700c0c1490283c0d840b01b082440270172146800b003859803080120030180d0524004001036100140f4042500944011404080c82d07640c46c04202c0e5078410340129088070f01c00c00750a010751580181006a00d5404000644501d00ca0108d6400d02496460b4071501c001d420004000b42407000520602000d0b19044034100000c9007400c0c030030b00f064040064586c9512641d440460180324400c815186040f030120692662541044850480780030544164408624440b228071580780c2d021039130420082d03260360303210740280c00d2108006862401402c06d9800029a4070344060703540050000b00050310030f81000d030303c45059400d80304030324422942c0801e408200404c24803000039403020899441c0c01a0340701140d89251808882401c42c4a030403802 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 140028057 1250 140026807 140026823
    0xa050a0e04061b0e0310050c0f0c0a0816021206040b0106050c03090d06060509070309021807050903010e06061c0b0f04032a021315090c0504030f080706050c040b0306040c0507 77
    0x100c3e03005540300c403d8480d140001d9090743c1560184401c010706807041a6a0002e481e4818410101085444400f42c94440c075042c00b1114094543e458100c02d03035000c031826181800c00c40c1030000950030258480d8504821000003041e17240341c075840c0c0203002007041c010074040120000d10000b0030a0304000351601a40000c000c25154032441c5014002441c00b44103441c0168040300002c1c800341d0184c410710240540152103070030900402441d2080c2d0301802000d03401400424403240c4190b440c00d20941905d803c00074001c094a0418208010102c03006580c040e452000000c00100068410204150405507160780c416440d2201d2400b610700540014518001c840304240001501c4038044074980d4081c02614284545038140001c041680c005000b41e400c030118003d01000164002c0d80841450035691600604003a100d0b690b41c001d11030b0014060350240b401042410912605110b040d4000d000c400155280900d40603045415000003000c1034401c1d41e8811031541034a000f0030449003100da100c150 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 140029307 1250 140028057 140028101
    0x42316090905010c2a06110c07030311160e130b0403080106030f271104230606030601090b0c03070803010e07031a01090302040f0f020a0f0e0a050a0e0406 68
    0x600c0c00820380058107440319804d25441194090040e0040e200c030045050101d020201d070041808004061402d044440c40c0da514401e180181001001e4908010500040c00c001c614505000380b402c0040e240ea00c0c6035401c4103505040540c1c0120460040740d440c501042c20aa036801400320f010401841d000e400c54070300750104820168403056450590300151000c00516445c1c2003041d084500420b130143c1c035032611001c04410f0190b58880002131600c0380e0b10a140c0c91a8201c08a41a10742035088140701d80c14034080e4650311030400f80c0b42c942c0f00106a41450661815030002801c07004a449560018030700000c00640c400414400c840125401c007501c942c0c2d95960314550900d91400b100d2842c0000e05e000c188800130546081d440321034010503566407141500395001c0000070400c005180500540e00e0310300c0041c0020703500180400145a41382c0c48000c261f03060000d04040f1311241c1213445811400c03020301c003942d280001300041d103019840d001d206588070300d824002000001020402c1c0046000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 140030557 1250 140029307 140029319
    0x2205030109031707050a051b16080309040f050402060f031b0403030e0306070c0b010b09010201061d01030209010f0b070303020a0201140f1f0e04021005040306060b040f0b03042316 79
    0x100b81d1060fa0040401c0500613900c1d14404c0360940203107080b5000144040004d03203940c08400c40d0000d00300b0380310001c3d1080703800e41c03c0301c00c6107000b42d0742c1c00780302e4907000460b043c00d407450907206040480c001000d0500062800e580002e4052164120800c202000030020440c8140340450002504000301142580c40c3e499003030207030030320908201e240e20a00c20000011005442030744201d80c5e040c0e10a961000603400d08800e40c080c2c0c1c0043c0541ca04541d81c070040000d403103941d080c20502d0081070310586500d65055005014080704140c20004c682840701c601008001d00031004c4a0b0016058500103031900b00b60542240588500c1e0b15040f2861010400e1024070718035111031a0094414240e440c04262018560b900c50900a20410301c0c2c402c440b0000402509081d0440035000100f8902107240c039850f40e8482d0110f82c01d9030042980904089400d20811280c641e0300e40140c800349800d50308515040d40c0b8413404242d0481802115041159940129201003003222a00001f01c58118151504d441d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 140031807 1250 140030557 140030567
    0x50417030714160504230103060b040506060a090603050406110c151303020a1209030b0c0406030c050408030d1104050d03020c041406130c1701080109020a0806010605220503010903 79
    0x180c0c05888586002da56004910030015070304030307040812a205280c1038644404c0000030410765424095841c4595803188508a101c40d55038081c0d40b05150008610550130140300031180014409809a0f20401070403d05070b4100040030f007140d009160109155803940f07030010203084010308450300c3e12400304007a0002c01307021500008008520304035620f107a407541061010540c0d11079015015800141d029004522100200480c000c41d40c24101940b542da541c0d814080001201d40320601e2101180500926506005140010b01507282040c24641040d0f0340c1070700c034483c44429000d025075604950400803020b005407002400000d0000f4092a0b1078180a510b42606194040c802c5103080084507020313180045442c040c58019090300385d0080c040c0c0e8814018a94400c01105004051502c80c0801601e0303c003640c00790204100104007200d003403050089030045a00201400d420810041c040303658044182c1e80c5400340310b00400b031544050a038203041c111454100a416500340b5148030b06058001c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 140033057 1250 140031807 140031817
    0x40615030507090f0308160507030b15090c0d050a0f0203090a1703270703051f0f0b011b0f080403210207030b04030509040b031519020301210305041703 67
    0x98030140300e240c2d165241165550240e0003a00c4507207404920610100c2c03d01000f400d40c40c0c4460074803c02d10070301382d22045d2801c1070f00c0e401180d203100c1010400201c900ca503115054050420344844125051100d1241e041d4040c5400c5612480d0343c500c0000c1c1619a41c2cbc03c01d008581c14480c0840d41c90070710444075900c9802c016801e9074880c01c402007101c000325804085900c01c020054003801c030781200d5800b048140c004031a0055241c40b64140c0030000c0b82060020541a92465000240810024000b00c040c8d44503a1480000c113481e02442c591940d81100e04071220001d12020400318001c02d2030aa660300081180141c2654001315001c0b0410401d014009418004070141104511000f04103d03906c000e1800300402c1c4011030070101c1d00003070250780070780b90f43d090041010814909440c00303c0c1c038207101c000103601c0c111010b105100c440551420140d05c0c03503100c1582075145605000e07000708003c1c50045000262503600040b48203152184050318054014248120721800c242d4161a03625004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 140034307 1250 140033057 140033099
    0x71b08090f06040f0e10031a010e0702010509070302090606040e0a0203011412030d230406090201030c030e150903040b0309031206010c0f11010203191106060f0307090e0c0406 77
    0x648100309891502c0000d0340c0482d5002ca2400400d103040000d100744010307018001e102d0720240740602100003403803146051824402e524005040303624019140c1c01803034011b4070150669140c41e040c48000d40c0081140b000b940e8069a0b485000d446100101d10b2621030341c0d224004c2c00200d441444030075841b58008604903040c20400303030a415040030400201d0004e81000d00d11a6104200c203807e100b40a81001456108484011020100380d40700d88a40c0907003154121112030769660040110742e0103103d801c140c00c11928041041c020302045ca1941e40f1448440045005070030030000e42070a10400441e00070f071034000845a12402e000c0c0100d27940303400101c18107402041c0c0780e00145041d40326049078580190042000d03180d4080a880718420f1080d040c88150460104010041c859000820b080314120600c0d991300c1c1e610018801035609205002c2d20303581c4144900a4100e256680c001030030010365007201d1000418448103410300340b03003680040f083d5801c282444000a12884a41d40c03520340014 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 140035557 1250 140034307 140034319
    0xc080c0f1b0108071e03020702040c0203070605010801060f0b07020d060e0d030c020c0a0b0c01060e070c0c050d0308041203060519080c0d021509040216060c020d020303040c0e071b0809 81
    0x1c941005403426034089443c0800a640b007600c3d90400c0c4403019820907894103078140140342403a00d80114050b030702d10b0448400541d1000941e80e04100c0f5600c90b06004082c0c02008001c1c030f600709013400d9448101c7c6c4c0304006210a01041c50019075580384070095641e680260302b04100f00080207425180c0c200a01c001010a1400e4021074015001150810940c000240078999075400c0405407030700b40d0410710413900030750360328500410164803140e41c00740504260380b42c00e0443c04042c9840c540c24a01d9030440c0d0302031000a0540300001f900b22070402e8016500482c81d41250540c0c8008400a03c1e55500180d8031450050b104c2c8480100c40600c1800d8801c1d43c4d0135a0312200d05c920600c941d090015000941100c0c00c1d00b20203032540060b4014105580e4001d0001d403500d42c0803807c054142c040304d001640ca250340c60042c030302000d804005a0a8880c1309002075829450282c41c0d0150f00292442219441001070002444c0306115036000808081c0d8540c280302d41d50114140074607150812894140215 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 140036807 1250 140035557 140035603
    0x30307030e150f2205060c04050a0603090c03032102040b0a080a150506031803070c05030c01080f13060906020a0c030305010f08060411010e03030d02030609010506030603030a0c080c0f 81
    0x480e007081000d109198480301c200c0b0b9520b13015100840c0c1030f071802140c1d8454107032242c1040054000e100f81c9025140496130075072101e040408001310340245500010074146400c51590014036950b03e8181141c1c0c040c01e0070352018868030107801000d817003425030760020351001902244c43e15001e0080d00741c02c052076454014543c1e4010100c0112140000d103800440d800702800c03c00c03440c3c02e000543e4408098020740722080806113146285801041c3e00b10741d5a48103030001d21544c1070400c80c50b80c5400007441d202070141031100043e030f000c12028007c20202913848450071f00f0301005170044115964846021582d41c40300d500f004200100d68041100000c1c200303400094800b08106840c0190358001c405010f49880d0399541100c880d01507140c0301d0600020035514042c90b9014005002c0c503482c241e40c0581e50780780a108210803420141c12892003244203005000e0242c5000003a2028092203007440020746031907091001e0203020385014000c0f01d20414030102c16651020485014840341c1d82e6194000c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 140038057 1250 140036807 140036833
    0x60a02041e030b16050904060b03011d070807050a02120406050904050105100e011d09070801081501030c0603050915100e0901111e0c0a0b0702191e080408030307030e 73
    0x5515140320141000304020f0104e854100010140b2510080710b01300607242900000105080e604554004408140084010403c4240b507255003280000c00c41c17000c0086207000711015003000005040003040000104000f105180204244202103c900c242d154485035a104000d0003a07010741750250055040c01c0000816040890a007546005aa08c41116003c288401114450703c10748240707503c0765406a80d00e04a4907107c4002d4007540d900ea40b40a001d40c1081e10107460003170000b20303d10704004448010808030ba07560401c5000e0b140e251902066544440f00068900181c9161400501c41c880c4140f1402c51048540081154048507501e800c0d40d0f112031050303080b10051080d002c4010010495080545805104a028541f4448082d803c1c00550300007540342a0012100b22100100c08040c0485a0780411400908050b007208405064000d276503a001c1c0320b0301141c0d80f140c440400c0c030002c0b0100311900d400e23200503101103c00c903a2240381002005000d481c0205820003540640262a003503 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 140039307 1250 140038057 140038109
    0x30e010501050303030112020f0a090504030219030203120403111b01020d03061a0c0307060504030c03270603020f0403020d050c040612050c1e130603030905030106210c08060a0204 79
    0x40702c070010302441c2140c0c0303868111041c1d20207101c822a0710561302030822100d56622000d5402420841000051034689450080e00e80b60495400341c5010125800410000b54000203c40e145e107000250040152514034050351880c0d4401c0302649503000d09908440d058240141c034241096090f400c80c4c0240940b0102502201c4190180d500c000406040c403d00c142c083c00000c1c039001c1e5544003143d240440640f501821290241d40440000303560000c04000c2c107620111000c001140c0b001c42c11400d005001040c1c1803905248a03c000b0f146e0085070b0108080d2070041070302d005640183c0b25200d140100d280942c0c079140302c1f5a48a1180307150180c085890381601c4415110700d94000c0003050746001c00e0040101100d0070841c80e000351519038009d2005529150540c0020812140d4085049400e52402070001c01c0c143c2c00040c0242e151120811100710500245c03081d41400d280303012610f032068102031105401c2a0807a034401e220314010720601c114194000d01c21204c1c5041c24400c0e000c3c0148400340 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 140040557 1250 140039307 140039309
    0x1080a0c020601051002120a0c02031002040b030a0c030e150f090304031703040c0b040e040b0609060a230d03090906050f01050d15050a06020a050c040207050a081c050109020307030e010501 83
    0x5074400c82c011300c604e007420b144520b54500280104c807000e00f8241c0325040c0c9580000c041d10300203191041d070401141802c210000320160b0780b480a43c18203040071840d1840d800700500703890310342d5202ca206c000300900070740c40709039880d20500581c1c5504140700b042c085c50440507100440e280807a5000241c40b01380100591707003038983c00384018103100203610350107078181c1000d00250351605a010f40041c14510280c0140b008142d0040c24105500c0c250814586e22a070060640b4007551005081100c01da4030240004280e0b01107900303012056001c828400c020b501000b10060b001100c50321600241a007020301e42c004c441c5007040c107103c56070300d501c00d01401d08000c55000e40820001c3c08801400c9803140c001250320880c6082d20400700380e403400000c102540b16801705025070807440070751040c081c0c20f11211002400556041d450881540e40d0555030b1007400c50041c0210700301042c258092a1a0660100740310102c00007800596101d00a85009510a48e00c0d240440e01c0d19180c06610401802154 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 140041807 1250 140040557 140040581
    0xf06070c02060304110409031d0a14130f020a030b1c021008060d02040c0306090c0512040f0f0b01080601150f020c011d04060b030103060e0f060106030b04230601080a 73
    0xc400450035a0030320800b0381000d0310446030540b484001d801d25484a11603102c9140c005e540e208240e8840c1c05241040e1000000014081e030070070001442207201c035a03001d42c5c1d01403041d505452a0034811982c0d500508900c2d0180c00d840d03000041d600340442e4140c100160481007103c45011030f403566902c5002805c003e41c802500100c45010300130b061801180d03201c0c4c0c0400040d0014810000590000d005c480f0149481030101356100f0050240c010644120003c2040717034100b071f5181101f0401c100c2e242c110010001003007291800940000c02000281c0212a00d031306c124562043d5071544096621820b0034003075040c02800c080c00340c400161046010702444411070f009011004000d10044600c10104404226079500f203440c1080e040d140c1d0300c02c2c02c0c014030422a0494036541145050005c3d944820265015540103c5401810f0070020a00504640b154203000400300010350110b03014051001c0b2018020780380d8003a502c94100a03107011486403409984c1c00c042da503584a10282160b1100c034080c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 140043057 1250 140041807 140041817
    0xc0102030a02120307030608060405011505060f07140a0c090e0d0302030610031a061c050a0915050703150305010c110706020a080d1506180605091e040608011107050f0607 75
    0x14605a456030b43c002c42d0000c0161a01150302905d4805041c90220103440c00c1340d45d80c0d594400003954ae6103840c400303c0584000c41d00c0c03d24202c0720356003100460069100181511410002541c003034030040240c950758a51090000074178a94a09640000b08071203104000d190117026801180f1a219100310780c8540d400501011900309c3d0320381c04074001c100c4210301410000140e5070404c070382c0d5916000340c12a0303000343c030040300481c0c1c2c0005014183c41001d030071003002c507040c4010400010144c084049034600540d000040c0c690310100d080b4040c0031b40c039501220001c0105000f02c07e010040d0040d00c230707170000f54940e10180c94050754a6075031100315104503401608036147d502c0014400600030b0182c80280400400d80352403010069611540550200002c92181202c000c10f5a641e81c0d03240f0020501d501700607007805210300c00320318801e440801001c200380310f68118480c81e03136555200c07802901c2c030b41e4007c0088180098444e86541d00c0782d40240d4261290004441d150280050b10a12514180d912 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 140044307 1250 140043057 140043073
    0x60c03080103061e020c0d0e030a0201021e2104050f01080402030706030b0f06040e06010210020406020c280e0a061e0b0306060d0507050d06060f080606130305120c0c0102030a02 78
    0x1d00802040e031242201020000f64400c101031581c980003800140d50b80b1400b87c00382ca03074a0f0340094401c103521203496001c1d0f0009840e600250780c020810200c010005400880c3c1c00400c03c03c99030419494040710036844400305d44018003d40f034440980309a520a44144c42010380c980019511110110b8000358941c0c400e4406210082c4030740c000b0194800050621409801444000b03459078000d500031940704140c500c1002041c6d0703410008a8810000124114501818000020b4488000c4020b1030b00489840740c2c114041c1c4081d00e1a0006c4a8542580d24421621082e00007010b10055034070701e141c03a040150202c2c003207200d80040031045503524031018086250201d103003501c2d0002001180d000d00d06001051215941e801200e2040310265035865031155100c81950407583d05801c004104580c0e241c1000083d50425405504483d0454080340c84100f800740c00e03800e45030b450b000240f1074058103030f07100340d60f04c0302c400900002031100d0b0036110740b5400840126524090703485c0032001a030100b0701c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 140045557 1250 140044307 140044313
    0x4050a1a10120c0315060504020d020c06130305040303030b0a080a03080703050709060801120f0b010b0d1406010e130f021b010b0102030c030f340b06040605030a0311070f03051501060c03080103 85
    0x40d140205e45a15000c1034041c4d4980000b8126040011801001030b0002031172103070300c80180b0490358000303844201c043c0c4142660318004d04a010b03600000b81403503541d507800462aa40d031030503240207009007422190850201c2c50004d104110944640740441c2c00c3c240440d61060040b040ca00c181d8032141e0703d1840e40d038a00382e615210340c0d49003641510344000302e101400110300c4a00900b03000c0d201075000c1d941e98107e0803103080708441d003210700c480b000030001d801d00032283e9000180240b907901c216451401125401e411900400c11410aa04001d02c00203460341c000e0000c03201c442c402c0c0d1031070300200501c050740300041e07842c0e210300d0710310510540082002102d8802d6582c0509030f080d186a41e800e52900d400200c411607d11442082c08030380316420310352002c214a0000282e8454000c2d135080c0012450710012a54035080100c0040034003882001d07a90b482c41e401c0001000074450781c60040f1409591f404c02030b4440783c0351500403110403032220000c00c0d01030040c030700400742c4e0354156a0300455a01e161 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 140046807 1250 140045557 140045573
    0x7051003050a0905010c020f060105010306050f090a1103161101050f0105010f020f061e13121103091005031e01050906060703030902030607030219030e0a080304050a1a10120c03 78
    0x20b0103407203016943c040300d0020910034070030300407600b07000d400078100500002081850508164031040c101401c0c030340d06014a40703980c5420f074010312041e2103848481c2c03076038550000a8020b6000c4000c40410100030004202605241d1204000d507945404222803c004150350a90300112a0107a014010700300410865104070b000a1400c2000c0c03050f40c0e2805441500d5600f800307019614440c2e043c6010300040c5401c00c030f412915403c65010307101001d2144066542040c12406400c083c818042488802850180144100c03107104030001d013803000e07540d0f80c410050b06a810541d6902d220007450340c803c16a040c1240a0700703040c0c817402010001c3c51358038103040040903881441c2c120b04260310fa06509006131030400ca420f008138901e0f200981c84580340301d056085918990012001c05040c00c0902c4001540070803c0100340390450115641ca954500b441441d041400038020807040d070591068035403206100c0d00c030303008050130b00c80042456900c40000002940707084018201049880041000401031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 140048057 1250 140046807 140046811
    0x4050f011b0f021302030a0501050a080c03121309140906061206160909020a02100b04140c07060905031b0601090614010c03200f0633010504090c031d0705100305 71
    0x800210006034081580d106a8209480b0087e2840c0c884c0c005200e00d24001d1412400303050140014214040c4800010b560761304802c20b207070021200010b203100c0b806403007c0d800c00a400180010701c4690340342c103100000b409003120740c0145d500444010400a14085801503d111030880003418251140c50309140782e084031f4016032081c090f0860000580060a0000c5c10209506401a007030041d00359814006641c5a02d8802e440740d031030714001c406401144203240d6001510b082502d525815149002d0004100c1c00c1800362030b600c00403400110542c4840c1e0110044c407520703070942e081a680c41c084034050f54040d0044501c0a01800c88200055114000b401843ca0191030444c0d504080c0f0b03645140b0085241800c112a07070049820005824020000b050b044040036200300e504003075058000d4000b4440548903001c0141100d01d078a16680b00d142034501900384a04100441ca140c504c01030018600145030381a00c000e0202c540044240125450049900140016680540e011800c5000f4800 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 140049307 1250 140048057 140048059
    0x50903031603020105090c032a04060e04080430060b01090e090f070e060d12030f050c04030b0f070e040b150412150621021c060204050f011b0f02 64
    0x50203203401400d940141a401c09000f03400008150411050340c600300403800840d01c0c000d0740804814080100030f062080420503030035003140c81800394100001c1c054083d0f680700c503200001e11401c5c0310900c5083c03c001c20803681e1950f012900c01c403000b04446030396406607012240c841c042040f10710105900780c00188041d03a052500703008890300d402c41080e49260a5071050b5003544980d4006070000010080c5e0000390008103000ea0903842c0040014420032210440185003e40e00f0191800284c002e070010a00e40c40700c02402d2099280080c402681500b16100c26102840c00030080340c800b454000300740707004050641d01c1a21071005003040c0400762007083c3c00c06400c4403c6903045040f82400350040d001070254813001030a461010700305002004070340d8508401951414504001e00c1410305a001c1d004c4180c0000f4803011005800010032005180e90548080101c001100c1c0070031050351b00a00c00c0d0743c000c80b10101e94080b03407001100c0c07580c84002c2c1d400480c0f04151148001c01e408003108803d40344 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 140050557 1250 140049307 140049313
    0x203130815010b2d0a2c151201060203130e0405060708091203010e10061103030402010f03060504020c0106030506130b0f04050a020d0f060b01050c1c02030904110705010606030203010506040303050903 88
    0x11109645068103820040340d030313101d0f0b440401c13981c030301c150722a40114541d99110b15010300329110051a00501208071007562182211064070107051580b0826981985d105d03460100311513030343d144065120b80c850681681c40030600074003c50440c1c82140d903940190740000007081c1540c4c80c035200b6511510083e0103ca9648204000c6008040a04c4019070190814107411b055a041003140c00e03000e1030550700010144a00d80c1940030500900000740d0394015024602402039100440050300144019000140c10500000d801c0b0001d10054110900303c921440c02c54a45a642d4001504070380c0680d03034003c1c000942c4074042040d5103115074109803c0340c016820748100402603400988145600c038402c072880c40d8040601400c0c002c1c0d40c882c03c60580820300300b07181381c4503002240c2500c40340d040400d5a10284682d0400d01614070810039249521409081005402c0d68020700c180250004002202c00e582020008500702d8400c0c000c0d02d0490b0006071100e824681103550569960f0008076045802d44 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 140051807 1250 140050557 140050597
    0x90c121b1107080a05250b030a02070602040f060c02030708011107032001060e04150b011b140303010b1206060c030a0c05010209090109020a0836070b0a0203130815010b 74
    0x32109000744810540b00b82e00031b00d07801c4444500304030050b080b400c04c0c103841010210100040b40a40c000c0300d901c15800000144c1c2c81d1014074101009000d030360080d00103a01c035220040741d800e411400780301409008400300ea002c0c507540c4139814240d45141c1d440c3c440000091140500203801080200b10302960850340a0101d820010703207900f101c14583c0015152601e07041170000344540305040301003007924594184880f81c46400007070803055894807401c0800c01c80407050303828840c054007601500a1400280c9940b569107952400c0c040d004121041e0403070070410080741c81c0d403800804403200088408041c1d820809000300a88818501d840e0655465400b00980c00d000d99071a40668007030aa072600040c2c135244e0401c00200469802800c100c00200300150350341a00c2c401400310b01c0d42c00c0000b0460120820f4282c1c82500b001002c1d440124921000307d11041c5194001c0040c007903031f1074000c1d4400c0d0040d540d03180e03199668600703514280c8180c4011006100505840c002000813000c030b03200d400408 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 140053057 1250 140051807 140051819
    0x603110f0105071401021b1203180a0b01090b040b091005010809100513060c050717030702010609020712080705030106090b1602060a0305060a050402073207090c121b1107 75
    0x1355140d4090314140d5002030b100d940082507186c1c1300d080300f0301040104400000d1941c80d000705d22000c1e0200d8020018036280a0100d42c0401c03407181400c0e40110800042d5940c1c58664015200064119104034103082d4110000e040885080e40300c0c40032004001c0e01c062400d401952040c070094000c1c2000c0c00b400f405843e0440e12130061500600d11244150100c1015040180490b4505c10500782040410042000440d42454081d030340801c091b00041c2d40d9880380b001c2640100001e41c07081c1c0c942400810444103028141d90741071000c141c1d6443c1c1142947d1a0002120144024023340d80816107070307001440690301c484042d084a00400030040050744441c1c0000b0860380181c0e0f40314001a8440d020001c50b4109503004500a040070340e815030078640e5640c0c50801080c1805003c542c010004941c071104801807003040f0a054140d0001e84841d69261112030340a0300000250402084c00340100c007050039154070a08a00190103904014100d0040104a90031803115002c50718902c030f450004102 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 140054307 1250 140053057 140053073
    0x3030b0d030c0303050f0c0304061d07030c050f010c0b0c07050a08040e04060c020708030714010902062a03070c121103060106170a060803070b070908060709030203010f0603110f010507 81
    0x304a001c1d4552640002080c078000381034910042541c1800c0f94504248071081000900b625002039000201194029110b5110560818104000c54040c0304141d00042401500c400c0714003981d10913100b040341c0707088900054a41416145000b0503064400000550707e0f00c400c006001d025200d41e0a1314903012031500c0f1000380350800d4010f042180b0541050008003c1c0034819032448030a14009022030519141043d46c4034003d804c0d000d8850b074100a150303ea0b0340350a41c061403445034020704440d03c0304941000012075100030030403100c0d040c1142030300f90f407520000070696122a6001691803178590070b1800006400407101411a0708a80c21003030307007055540901c1518040c2806070b44106000c00f1126486079000005094181c48601c3c04101340708425000c0704a03103d00d40c00c4054403006451f8008100c0c0c500c103465015005501401060140441e440b201c82000c4a008034005e1113841e40c450519400c66000307200080002020054600480c1001e222540c1ca20034141055801d10340e594443e240c0f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 140055557 1250 140054307 140054329
    0x40801020f031618091505040504060209090705030408071104021b01050907050a0302090109050601120f050708150a1502010207023609030f1309020a0905040e030711090403030b 78
    0x28031801c010081005150107481c40349141c070444d00c1c20010f214095400109890405d02940c6102c50f01c650365201106803406c5103030010180a0003c02844c6044d042440094101d00c94041c82828100f001c06c1c02e081c8688141c0340565001000030f0319000071a5140d081c0d4807841c400d5581c110b40c003030207510200808244c20707881021440c000171440e031520602c854288001a04100d108108092003403000d616001c4a0070705540c2e000074000303895100c010047c0c4000e2201c1d00038000140c108001d040c0c44001c55080207001340f602c0d84070704a0503201c2c000030150404080040c150818680e04080001034204841207030b0b244414000140781060503004a04141d0460341a1040031200e0702c410b04881e825440c0786515103000140310203550600c004400e032a846100e160720260364000c9032420b406401e98521400810003d6811541d0b05000318000d0411061481400d114034034003009940504070101c00c880c0c41903480b00c007031440303140303c041042481740300a0019002c16039681b000398850b407128041c100b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 140056807 1250 140055557 140055577
    0xc050904110a05041802090a09020603130b0c03010815062107030b010605030f0a1113060e09011509030f17030c0d0c020a020a0b16170403060f06060504050d0804080102 74
    0x89500398a107014442d0810150b4016401036103404d80500000d5513003120205401d9045901601640350110395102410023084065070204000003403110300024400140308062255909480e1036488144a4a003400244071710001600b100030755010181107169420761042000b03200485080c1088420074001d14031b00e001c00403d9000c180148180545050316900502c01d030f180c000e140d85020300410070801c0014001881075a102d0342e0020741009000252296000d024503541007150b51600002d01404c2445c124038040c42e078040012665840d080c002c403102d00da82d900d903000d800d8515526844054940f040c184c5040c41da01072450380301c184c034000450081f550308000381d8460020307442100846281c1543c9405660040d1101001a10350080000485121081c2551194411117954024030001c82d0004c144144245c4e00920910070b0801402c1603e000c0c900c1005503840c9205502c04640f03650140c00045035040c0000c00481c03420b900c5880348140300d2041d02e402c00b40d44030703405401e90308651109 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 140058057 1250 140056807 140056823
    0x7060504080111030402180406090503030a02030f0702070803031b0403020d030c020319380103140d02030304230a0c0e0103030e09070801030201181e08010e0d0504060c0c050904 78
    0xc0000d50800d00408000700b43c03010f491441c41c10142d0014002004511040c4801e401841c0041e0500c01180e0007115855040780a8941d2442c005603604002c1d4001c54100c41d440b440d0102103004c803880020300340140c403481d03001149551034844a8035021858604175010182c8100008401078548540310523005100e81c441403d880302a10401d418007109c12000301c06d41050800380404a0104082c203000c050403030b034000c160031501c80081c4a04280080c200c4902c5403c2c1c02c0000100424a0000c50034480c5040c10385d488015460000c0fa101d01c010380d0042c00c0c076030039202c00c120001d050351400a00c0701211811504072544980d0f51600d08605948504030091003103004006168211000e0070340040222208c4400303181000b409400722006000c06410481c541c070f11140e00040c0789800402900780804108401001c0380200c40c203860b0f1070f0041c461194208201d8105608000a0044115040e92505ea0801d03081c038508075210f9031300b400180c071521803a00c800170792601c440d07100600482c014004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 140059307 1250 140058057 140058059
    0xb0a03060f05010e0c090d02060403062405030d051902030705070605030901050a0207080a030b0622080c100c0b06030a0b011418073203011211190510090807060504 72
    0xc2021280164081083c1013040700800035080c0c001e100b2a00d1400085030031038a0081c40740003045142c0500d404c018145441c100e2102076500f04080225800d04c5c030003d50150384c58071402859103800303010380b0f00320118400703000110000020b14800a00307100b8600c1142e003842d056495840c90400e242e84943c0100d80000709110301440280149a400400c0810940c5003129035641c401c001d00c5007110346020140e036000306000380d6031000e08807248003803001c2c541218010410482141d80502e0710840015102c1e4021085c41d60074510110768440c1c4850b101d035200451251070346111114000d19096241c040d07200e910000494945840d4040e0201da040d00c0021b0391a141841008190311b924000c84034807500c03c0026117644190032010358035181050b00403400e12040354182c1c1c1107410f82c070b43c6581c2c6004400841c40a01c1c80b122800e440c0d0041d80518180c3d80d25505100007a883c1d0745c0c041c4038494240c80148121700b054101d1350099100c619040380c0050b43c9010841c140340d02074101200007040020 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 140060557 1250 140059307 140059331
    0xc0807020d140723030f04050112050103080702060d09050a030f0e03070f061206150c0b13390e090f010605060d09020127090513020d080306040b0a0306 67
    0x35030314103600e0341000e0b110048082c042022500442e00000c0c01103200c1d044150300c1080c41400560f48059040c03c8907201c1c01803c12580d015042401454000344214280c038243c44040c0c0103d038100d84d0031603503092625405409114540d4800e6280d88803003a181c40d11440014020841903e9050080e42c6100801e500001c000b01207446082c0346074480e034003806061104c5801010300004440300341c2040070000398800014006809581d010340e2070800305a684070b03241d0350000c1c0300c0403016100d01c1442c480c642d100b0b5680384880442e40e02c042c2c031006591f40360721030a035451031400440a6104050546140380c1001e6568403c0e0b0542000300400c1003a0203001308084100114901800d150b0000d001c002e0030f0101060080c080c06031840042521980d0702401d69008010051603003d071300040d0345148880219440707410015101d01d00d020791400700005d6110300810105107880da0b0080000e00034801c140c450740c00c0c0d41c00186c1400e500c203503140c0040609030b41c1e00d04e00c0f6004601c66440421052101c41c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 140061807 1250 140060557 140060563
    0x80403080f090a06030903021548160201050d06030203010903020a1709030a0b0a2a14040305060604090606050d050a1202150f0a0204092a020309060403061a040c080702 74
    0x90310041c1494213201078040000e8002c203027180c40b140b4540f90441c85d0b40d03800d103501613149042189680b01c0008a02c0081c000a201500b41e80221a50188072000082e040d90703001c0750b44114010f00d10318420300800c500056100700010441040b403a003001c0741d4a5100c3e00000d0841c0c4101c60200d0140e441200b800742082036034441d006c050031202c60210300f8242c001f40803070384550030704000030000c10282000890a480a078482e01d960f25015403031161300d0035105a070406034048220303503170040744022191500b00710b0900101c5003540c0e80700700a000e07107072a050103000c05802d0303c500c212a03d5444840100300c98840c156000702e1140110300a020300208d038100311520b565050124811034000803007001e1000280000242c00c900c956032038140d29030348c5010090090282e5002040d030300d401c1084c02e00148a8003e004001d101e008070740300c0c14041d6103000503603032481803281c05504000c00348420400f00d8440d030b111103036102c000e071221074140d4040c40003c0c08541c1a00380100c082014401448036043e410 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 140063057 1250 140061807 140061809
    0x80703080c0106230f0f030c0f060d05090a031803080901030b01020127110301020307020304050913050d0c050105090708071a070605011e06020307050c060d18031d0405060d030309080403080f090a 86
    0x1940e14444000340c86e40071a446810b880c81c400c0c01244003140b14244e540380c0104030b600c02e04c58000100070f0341c180406610b803141001003055001503940043d03107001314141303150030085907031282d603a03842e01e103401c0010f6024104030202e440c1503540e20702c113030510f41c8801d0044600d901061240c26882d54820b2402c500c0a01e411158103009a2041c03081000f1190000201c0b8140c400850b004c0840d41ea0303806182c0d00e6482e650390002d00c0f074040c4150303084800e5004000c0740c01c00e0344148002e100c079681c0c0150b46a540d00c0f0b60311511000d684080410441d0714800005110402c1450340700c0d903c0c100c1035403650015070b02c0a034400364003100510740c1c40003e0511102282e015111703600c0510300e0b10049844160b621106070601c41c1c03054000080c00e80c6209039980c0851174081280325800e0a05440d030030302620300c22214440000800c1502c1c00080d80d0715051060720320410001300211040405500d00b103004062203181162104010000480071641110207407241a0b2034800701552111000d0a0014000d95 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 140064307 1250 140063057 140063059
    0xa06020312040204091401060602011e0203040209010e090102040308030c0a1404030b400201030b04110301090e0c0619030b010806010e0d080d0c0903050601060207080703080c0106230f 81
    0x4107002950030080010380d4203030060b804490100300100c0900b07014402060a01e4a00810b41c68031000041c450b406400503001c24450529541481e040e400c5603400340c1c40100c4001798000b80314001404040f07003032944c20f504580395200041c140394803aa98044968000d0760501541140868840001ca50141d2502d0300366000302141402c01d407460355264000c2101900001e5001e0030b11034074400d00c0e0700c407038000070610300e00b02c401e181d01c0400301050015180403140103a000a0424103c00e005080c00e000c0c80e040710b24440c0704103107075a1901021400400c0c2c100c0814107a4011800c0c00c0d11a075840801400c1c40c0c003030a03a03007800300600d01c4801078100d039030000310f05050081580c208511a03810106e40c502820040d1916019500140780450b0148250700e00da03117109250a40309046554092480000d4030303c108120340259803900020f076581e500901c01e030140303507100c2841800043c031254040e11036000385500124159448266101c10070106c00c00341110340321640031244c0185400c1282944401c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 140065557 1250 140064307 140064313
    0xe10181103070807060503040203010f11070215040612020313060501080601090f0501060503070f0903020405180106050607021c0c0803030a020a200304061803140604031709150c070f0803060a0602 86
    0x40340440a13901d4002600c030360028010003000090542d202908016051000b1400400c115200103001501d80d070003070341081c3d00840c10410707988120703c01d0700c0c00c48047d5441c545440300d0000c2c90700b03a410080e40c402081928032808240c50000083e01a0040d2400713440c003131018007065818440c1c00c0040714010f82d03601c00703914140701c010481c86401c1421070790800303d10b01d00107022540c40c0070241c885da01242d0000790007603d00300802c402405c01d0800d0141442e400002803219644d0740c0c08002d287e0241c900c010790f000c1c41e04d0144044102c8034603212002030f03208840e514151030355041400c2c1035420488010011903000150500c02c0c41c0e000e04240c9072658400c10712060b231417940107a030340c1e41d0103280585024402d908450f0242c20340c80c4081440115484241c2e00038180d0b85417222515000c080d54102c02051a400100c803a4040f0424824800d15000005010101d070306440d0700c3c5141000b404d03003190108108128804942412001c4440e207004030381e816520b00f002c806100c0161410f41c400c1c41150 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 140066807 1250 140065557 140065559
    0xf07030506011b0203031b01050601090506030907050f0d050703030203090f1816140705010c0906080408090d11090f040b07140d020d1506030b030615030d030e1018110307 75
    0x103a001903c026002c0c0c2d20711010a070080b4940b020074a14400d40403c50440000c1c43e840b025015015003080340318101c20303a50000b00654440a0092600046d2508034080d004080144500d0507c8200d40c1510740000f4489080b02e01143c8446090100a42080d0700503000041c5200c00c9040c0302108042c0c030030b003d4480d103a540303a451000003016400549561800c14082c40320f008803a1044080d840604e50302e020040d0b9800c0c19180481c002e094115881c1c010800c8013400190050081110b140320b960012565403504081408002c070000c0382480172903540408101c0c103013107521100d80e0240f02d0480c6441d510207504180c1030000d90b0300c00c000e10f050108184c3e120b5040d8610034050544510f400329090243e1034005443c11340f40601038001c0e10f2503058030001000919280d15400030440d81c0019000c0e51a03603201e506424100303140d8001e080e81c043d485441203003125031003980900031155854041d03070003a4044000b01016620800447c0c121000c0340c2100c1c1e418031100100801c02070900f02c000300005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 140068057 1250 140066807 140066809
    0x601030b060c0a0213020d062403052502100f0920030d030b210a0b01060203160b13080f040806090d2a0203100c0206070c0305030c0a0908060a02030f07030506 70
    0x20742d040207002070180070200e01751405c442e410b8040e10f2400002080c180910f64483d01144a480c0000711100d85803201030003131580c51070107403151034020303076140642c0c000e00a07000012489008640101108502c2902c0c80061040340c14891029541120310300402d080c01c290030058280041005031013683d801c2c0414440c603d0350b00050406400049050115940045100145242119100515002021300c844400340320010034190080c80c401c506001090340c0740c100881c0d4070f0180c090740d13401403043c40c074032080424104c90001da0722a0603413880e04001d020940c5c4142440d08242c250381030001020a007440980014800300c0e9100130315000074075400910032350040007001125010200c6000c4022100101c4000360f0300000704503000703000c80381c40e41524030103070000f400c0c4401400014012640401c0d40d0343c5c81800b500319559015600c160854a404001241660203006884c0c18026000340003c2c2a0030107002941c41510702007001030f00ca1500b200752030070745c85c0010001d17030405243c5000c108113 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 140069307 1250 140068057 140068063
    0x7030f0f06141504080a0303091203050601140706020904110d061a04050f0102030c03130f080c10120603020d050a0204061710050402060f030f090c0607110d0303090c0e0601030b060c 80
    0xc60034202c3d1086404030085843d1101841203821050607401002d0f1403000303040d0590049a0744512403505401206a280001c030102e80095600034001210800246c2d55100c5942c0540810b5008c0d1100624159694000808903030222102c02403030540401c0743d220300009441040010402d50340f4a50070b86480d8080c11059108a0203008d00c107403580f04000001d03910810030749064510300c408907562180c02001301042210b5030706c900303d20f504092102140149011440081c0540c0c06044840c141841c18005c1d54070202401151041c641d0320310001016a0303e031151942c0450040d00900720306141350040c04150380f40754002441e1800842d48007064654000740c2180c2000041800080e191142d200180c054400e14011f80000c28004c0240495503071044c2d60326028503648011144800407113011700513607014101d406068207100c900d01e00104c2c1404508507103040d10030b140005074048142d0f1680380320359440c1c01c407440c03561000c0200401544c0500c41d41c15025001c0710b800342403940005100b55 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 140070557 1250 140069307 140069339
    0x10207170102091914010e030a03080a1509090c08061b0a03020708031501230702040e07080106060906111209041e06091a0901030c0b0304080f0307030f0f06 69
    0x303200e00d2203881140c0100001c2d4140e44a05000a141005007800b444041c060507555004280003403a54045880ea10740c010310b000b0040034006806031169004984040e2041c40c4020301c625491615160054200d039201c0410304080c3c9100701002400c0d0fa86e07401c045504e6085500904c484e503125405001d8015450800100018045007002c0e0361410020411400380c0a4480c004000302c07004011700000c20740c140c440b100a09020f0340c41501223960510a00b0b20f0707401c00b1441e18039002080007070740007500b01070300300b00d58140c1440104c0702500d0b0350301c02982c01c4910707561088000a0131980288201c5034021000d0800000c8540100114540c8203000342444c032860f40d443c1d00c01d80d80d400c070780c640030380d80c3c0314101c071401e44800d1041000fa9070f91508880540b580003042e03804021482c020042c1c0b03240080411f4180ca4200120b907004900b420020b2205038409001680c100c2c07014003440c25459000303001584a08000d60380825020b040c44040703002d4805510340c0390341c032a042030720031b2010350040c1641c40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 140071807 1250 140070557 140070569
    0x14010602060f07050c160806090606011b050c1e0a1d01090c0c0c0f06030f052502030c0609010615051215010e0d0615050a120305180306070917010209010207 69
    0x1466030301d50340804e6549226400e400c0b01e26001d2800240c52020043c00d54508aa2038041a01c0c195540c001c0f50300d442c2e1804658090101e01c810358000342080c589401c07242414031420403985580c5c1000c1c0054958082200b00d100c21451507005c1c01c58504062414000506504081c2e04056041c06ca41480c00d140c1402501ca185680342c1401d80800d10980450700e90b81c4c1c010f01d202c1d0b48a52603264900c0b4928441c010304000c61300308644e50f010081d40b481410711461240001030703c01e8031400904600003006d1080d104c114442807150721010309082c800319025804903000041d01c203142c25206d441400d0145810402d0140602c007005130351400c0d1107416400100549007004901c0e40d80d00585d0805446004203801005002503030701040903a500c075076078401e0b03480214080070341e94404009103880c2c0350095160f40300ba010607180c00240100c000d04484a01258519020141c00c40031900c1d0a000b00c039000c0c00240d080354200111110800e02e80301c0381002d10020b52902c1e40703440000c1c1d84d9061600c140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 140073057 1250 140071807 140071831
    0x209010e1608161b08030421020c0f060a090b04090b010207050909030d0504050f15100504060b34030503060907110c06031015120e0105040f020d111c061401060206 72
    0x600d0134210943c021080884e4041e1403c0c1c0c4904103030401c2c120381d5003041110210b00221064402040340001080000301000400e2200501c076000d0500005030454807594040c4020240301154501e091009003010b04a04d607000030b80c0451190009252000991009005210170030900820050200443e41c00150b01c1d00041015211803800614055400c1c40c03c02c40d40c007409800f00030311040322000f5401901c1880000f400191940100400c40f08030b0303c6040503424042000f641c1003001e004001c00485903503c03c41e1060012075600701c00c0d20494a00403400144004200021850026507040c0c00044518217007900f259045855540c40301d03c90500351164a0101c009940340b50300c42c001c3c40c06081c20520071000d110702c10034040d20fa00d01410310fa582140c100150340311445814071495128942014400340310041303c1c0c01380026100318920a54210054040c07040300382c0c4440302c41c05035800c00d040606020002c582440800c449140d11101401102c003001040300c9940080c2854002c3c8100c2c0b60 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 140074307 1250 140073057 140073077
    0x80f040f03020c03190204140f04170906071401201b0102130e0f130b150d0f0503040f0801090807140307050a0f06050703020c0a03030b0a030209010e160816 69
    0x1042e440c010032030400c20b505210340110800e45404a491519456100350350030710202810000380110780f002102c00d50403450b4604002000300e4004400103807004190003500749030840c448007185250b0301103001641d0b141c2003001d0351501503d09200da07461140c0c0414407604e003041210800c190030301c04c08088484038044807505180c00c420a50444406802c5541c8100d0300940e1643c04484e0314000b140d401c2c281000d10b4000608030b5021a42c110422a48414050107640c1d5461748089040e54451081e9001402901184000fa1105054446544c040d41c010350b100d516210601468a01507004241d840c0d04055580d000640300400b5a0481a480415540c882400507440c5187d070184a4010b41244181c441010500c140078922a92303080c012a003c1c03040c2c0d91002000d6081c0e01c1030004001141d40080403140210388640e1000c101118010020b1403419501d4001601c1d810342030300000304000a40060040c4806102001d0350b20b8282420004800d14101d00e5410030040400200b400380044c800d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 140075557 1250 140074307 140074313
    0x306150b0903330f06010f050c0d08040c1d01050916021207021203040e07030506041a010c0219081006090c091802120a0504020a080c0a06052113030807080f040f 71
    0x940100c3c07030209107504000d80c90000310707036030506805442a9012410102d0000021880380040303c004a15000040c400d407016404100c0d09190001d00548412200304004942c2d9607500b4640f286031002c5100000203541003000b00a12408081c16012054030405000761032280c0200790103004445030180213440351074034004070302d0681108020034028000003c021486914012285000780740c281e408200740d603924420b00c07040313401040f052003403a42140000e41e0258811903560302d000d0b2000c1c00300303150000b900010700041061900310410341e8000e0306003d5001401c9205000c01051516014445800d100c18003808890003405200c00000f41903900b0a44461340d0380490703040240c0f5401201d290b24080b0b4030000201000da90403880389002000000d02413000141700c2c40151001001f00c400740f450f1030825a4513622941e50140304c0303400310040303003000061030075024443c213080c01140904600c03a00d40108030420041c079074401d01c0400d0050100821300703600c0c00783d0301035800500811500d806007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 140076807 1250 140075557 140075623
    0x3110f0613060225030c0510110306060921010b031908030106180b070305030106110109030203040b09190305030909070318020d0f020307090608010606090b0708090d0503040306150b0903 82
    0x201c00313030840450349454205584000721250960142042d22024000d500c0e2403000c0d268100041c0180c018240080761261178010020003019030010002074000c2846000c04610b1540c094044860f659203000e41750749400c05204000144030f03504010340d10803900d640c4194482c08180941c0d010894652440160b07600c494403150040d0041000c169222090fa240080c010b41c801d0181d08001414411059208901401851025607040e00514205418418848500d40004c8510b0781e1200f071460b6280d0a20070100c4505000d1070050010759a0b4184170030a2018030030025004c0340415207014046229100140d41c865550f940c126100c68244c0410700306140700481000e0044d6050080c910000740c61245c0341e00a400300c4a02e000207025486e0b5a11045c0c440011074800c5400201c0708014004c000307807840c2c00410f103a200003800d258580e01c16454003031954120b42c104466056a039411501c1903240c0c1303030300b81c0e0080228030b00c164a01800b90300031030b4848902d405026a4040c21220310743c40c561141e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 140078057 1250 140076807 140076847
    0xb0103060e0f0f0705120c090103110f13092114160b0f0106020705030d0e06030604110703080906060a080a120302160c14030a0305070b0a0605060703110f06130602 72
    0x210f40710918440e10b129100c424a00c00c00741b10b02a50070841ca80d00d540461b014650502c0142001c01503861a1918503650701c1e150401507201211010200311642d0b81880c219400030342d0000000ca0890500e0811007401c0c05800c1410540c40d240c110700403050f4044d040c501d0015100036902e44515190951040103800004000d0100741310504008202c40c05999403412285650b084402c000c1d40c40c0145610b8170310cd0040fa00000348440a00c9400e810602d005503008400038200054143c900b5110350240d03007040c0da04400050201041c07181612003001141d030040d400301c410720460341c54110b00c2907440520f4900202030054100070049158000e1713050341c4610010350300800142c0c41902d0040340f2080180a945c4115054881011150a0001e601044698140c94440c60405903455802ca03c2d46c3c001e1a810704070f41c03180c80109094440601910078030784280c85107420400200e8105003040810401e0301170300d0384280d00300644900110103c0c032819402000040e07907800e010209041202007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 140079307 1250 140078057 140078083
    0x9070c060b090a0902031c05041406070204060b13080c09060132220e130507080a0c151706010c050708030a05070506100501051803031c05061c0b0103060e 68
    0x11082c01c00c507030981541c0095002c41d108800f5180d900c002c000d4840d650b104000303240800900b0a00c802d0106580da41184210600c005100c039040502a90018040d14807a811503031747e01401058501141030303003851a07805802004054007401d0b6018010803042034008201c41e04010036a210000741e65500b040d8115448a400320000b002c21020343c07192a20342c0443c1641da0142a03149500c60050342542d501001e50310302c84000041c0361a80071003080c0308850040240c907540200390000441703030b1003003084c9e401c5079105031030a242c49031412001c2c02e20a901c1071083c03402e10184d07611001b038140a01e0074480d449902400c0407400e20b4001e05000d881c0807400d401140e00d903c0300041d1010b0303098000c00030f0030328a40b141d070480b891a55802140601d04d02c1510a00380400e2007031091040c1808040282810b0711406002c41e400c109040300703100101c5200042003220355555038123100f450300b8020000060801e14400402e008001c03a03450408420052201801160351080b05400c480c0d0113008003481016 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 140080557 1250 140079307 140079319
    0xf0601031803080613090c05010509010528110a050703170f04140301062705071101020d0905070f060801030615080a050f1516030b04020c120c0105010902070209070c060b 75
    0x201d15000c1e088060a4813a14400e140c0c0503030f801c541c0d624602a154a04d075001c1c050144a51a005c01074035650400c4403407a044c40402c1c000544090524080c0003c08816070200c0000c1d1455020007138520425244581c002d6000341a0000c04030350700040741c10449501450711540311000d4172100d0094001c05000440303940001800044003259111800c8502804900808c5070a07602eaa0200b2501900e499241003034811648603941d0400c00d501c01640300d003190411341741d0f1224817081d850899102d548030303120050b50b80070443d003032200820030207010300b4808448502050403e00041e180348e205200c020042e5442e42000001501c0700d40c0c4010040903058101c40e0105090301d071040e01c42155002c2010180b0411524103041600c01103c0c502500c0514030b5642d061103107c9046016048070310955400075020401da81041a0806c0416038075403540705041d8030b0f0006249143d083d14810384c85070400c1401481035901680d501c5900c0c1e41c001da40c80c1411251000d00f131500303d000d0301e2005d04081c0c1c059 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 140081807 1250 140080557 140080601
    0x90c1203190e0f0d0b220b0c0c010606020609071202030c03031b010c050304080d020901110706030903080a06050a0b0d0b09010b03071707091403030c01050709050a14090f060103 78
    0x1d402088101e001c4008450303040a900084050018054854602500030503028010962001612141e1b690341105114a0410550780c0d8079541c4c500c11050300d00c6628200c00040d1940380840a10559016003450310180c00c0718284810403a82e02c0050b03000b0030038198045200c1c841155420030010201c280050140c9890794a0800000e20340c002d810b0f803060752942402d105a9850744142c08503446031782e00030760345403c00c000450301c000207412030000503040c0013042d03020003d444010421a401403809650101701d03000d0514004214101c0500302604407420468180626902d01d1101d000f0b40f0300c5003560307030b841d04085c001c46c1010300f54003064240c208018000108409003031a0043d44290000d44a1002e5040c0350015034031407d00c2103403074100183c550503051000e40320480e55011055402000c8031700308101428110f00b16075042d600c1001080544904000509040030041d0050640300c849480007603050012981c06900240402b00404054001031100d0703000361700203032254203e507640510103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 140083057 1250 140081807 140081857
    0x5031005240102071a0c1605030d0c3003200301030f1b03050c0a0501080f010b030901110f090306010501020a0f0308060d140a0303050c130b070f12020607080609090c1203 75
    0x55440081c03000d1b41401095132404211424607184011202c02030010100d408541d20b0890f214095801c0c2110b004101184c0c84000c030a40700c1e04050654500404443e4564001b00084c080311000d42c1d032094200400c0c42c3e8150300010410587e411290041901e2000c0001032070407212a00500c1d4007038841003001c69012007440b40c00960b64001c01016a500c0d207100fa210001510482c40484564070b400000d10018001200320310042c5d81c212001400204d0700d10203403100700140742c0011034442c41000c0d020502406610701000850b0050400b800680b0410180d0f489854071481c041c0d40240030b120303405021901c5612400103002c5501d4002c2140383d40090318402154444070100700a070000b138100000710303044030b00b03410450701c21042c40c50080c000f1a01d803001c100e01d190070410f415984030120480c04404244080321806460905501400b135901e08420040c0001c00702911550003203844070104400000001091140304504031041c4140082c03484840f4030307520500180d0001490164003041071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 140084307 1250 140083057 140083109
    0x1202010c121e020a15050f04020415050a061112040e0c070302160303050c010e010209060a0c110a03050303100b190315150525080a0c06060305010203040b010503100524010207 77
    0x1413900c1040c45102c20641e94810809468060760341000d07080c03080001c50014a0b203035020050600c1035280b14000c560790b0342c1c00102c40094a9100e200880e0b03115603244000c00c0180800700454020043c654141401c0c04801c40055200404c980740ca003e001902c60306050080201c41d0400951400314100a030726441e00a02c01e810507250310030300e903003014007483e40104180203491106401502c00c5080440d409070451b0901104a410303a00c0d60b0041c55400195140e400c040009103001d00c0065031380703007405081c42a0715042c03544103c0e24a00f05002404100d1410304175944401072519011076402c03104e114040f44418540d01c00c42c800250183c04d02d1125400a000e4030782e00b810f90110100c59000d40001448a8407003800082c1540c1042084200c17081c015182402014090b4500040c59600c0351307101402ca07481510103840b18a17001303004005038a010401c280b202d0f001607000707000382e0800240c03041c201459460105000740c0b0200262420364401c0001c17030014a00071072810301c1d5007104120515 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 140085557 1250 140084307 140084323
    0x150c06050f010e190e1009200604090509031b0d200307062c100b01050909071b0501061205071e0909030e0301241202010c121e02 57
    0x11100c0c00c14000460040c14030840034101c800c49111a0031580d92440d4142599104685044030700342d803050040e14018040141e40f02e40c10f52802c00091500d1329083ca042e400c00c00048100722031016010010f059144c0205031030440b410450701042d59114818414154010400602800b04c6400604451280c0007c0c1d240c40100fa2a114215000d01203900c450804050411594140d441086900300080b03590b0f01010503140d515070b03d00907441e1010000702140100070a046455800000014150b14051084a8150500342402e514040e690750101744282c100805807400e20250910040c41d034408800712400031035005000308207481e00d40e19441403640705100141d40e2446011804144500c0c5010390312290310048602191080c6130075080c0000d1b12210600701c04012804e811410300361403d00a82c180794520402555102c0a040c02e1a00d1002e10f9900c1184146a200e800c000940d8000c01d03400c2d10303076030002e0b4900480c01e50100181c501800b1095100c036080382d82c556000b2220383c081542c41e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 140086807 1250 140085557 140085563
    0x11e090519050d0b2d060603090703050303040501060807240c11041d100b0a140118151d010e01080a0908030112050d090317090102070306181b030b0619150c 69
    0x110781c00c41200002c100c024404164902017009401061a500e8884099540300700c029046460140e03d03982c0d141e040d5007003507500700c440d03070345920301480b219005000d480040d207042107841581200c203055042c0c880e242860014240700c0b001c1d81800c10b000c01d50000c28070000c07016000f4810000e010407000d290405101c540c01d500d0080020b030085601160003031b4202d90030010f1074140d441d400c01c0040803070b151116035458140410080c41030641c0800d240c00c00b009000d4203010b6030100c00042e6000e40819009160306400e205a1041006942e81005001035014800c0c609118941d581c98800e00080c4041e01c4080e14118000c000000e400b81203070380241003684100180d80078003821110a840ea04400d002c010310fa0f40b40140098111000b003005418200814030446d0f51440e0b6070348402089406600368031003250f01460104041c410320b601c0482038102204420030b1014503586418401200207010544610558030380c140e116504015140003074424040b15007440303088484050004100a0812 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 140088057 1250 140086807 140086831
    0x406060f020c060405010806090c0702030d03020301140307030305040b0906071509150212040305090609040f06170307080d0203100b04090203061e01020a030503090106030506090606011e090519050d0b 88
    0x455560810f041600d0407a00b06840340c1d0400c7c0c440708100705a603079004124a843c090248049405690304100740703007800d201a14010381d0395043c9006515040a0449214025400b41408000080c3e00c24119800c40354184015a01c803504080000c00e1803040800c0909020025030940310207041c00da0269103c2482948041d29000048126230280d000d29810507a0540da5040010b000c00e0003500205032048004040c00e241c800c0c4040001e044a0107401b64a2055590386024051203590b42803003116400d02100940c10b0240320340d100c890034407c42c15040c04064001c030102e1070f2903080b81103c2019005030341e29151560784030900c10000f9013040f11002d1051208449a400518103a0501c12006006030b0240c03540458603103040c0d5080c0d1000d484803143d50350b10400000811400d000752400f5480c41d4000d815a814001d00040c1000c0004205050300301c050085001e00e5500404540222042643c0003103000100c1513600c1881401741c0d01032900802e075041d251080000640802e845a201003000e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 140089307 1250 140088057 140088073
    0x360303011d09060403022109040510061b0803160504030203030703020607090501090302030c190f08010605030f030c06070f260601120e0304030807050a080412111903080a0e0406060f02 81
    0x2e1541c1e60a42a03c0160251f0010341c5203403e40c07900001106111401d0000c07551521402801007402c0318821a40700c00601c40390031f0207000503940300782d14a40210003906e8001600500d40c030b0382d081910010304940304010711350b03100c2000e250090065800440d001010349803107849901340a505c56004030380000001e0920351001c20a9802410038000740c0f600680200814450b4005000b24203208068000d55030b1880580000c61516013024940984000000410078915203402d00d80303481012090700b07060b900203205014085000141c2164405100e02e8900c615542d04042507138076407099440d0300f803000e00207901c0e074015604045050703008413020390307607580a201000c1e11a02100d81780070005185400400c004c01c0400c3d540381c00b521005004e0000d40d14488250303a5292007a40c41a8031040e01010203120072014002400107000e0411030594015160381503003c45480c0b0703c04c0780e000c01809404045641c2c00b006128091201020710050003c114403625000041c00019515801000500c1903044c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 140090557 1250 140089307 140089321
    0x4050303100f0605180f040c170a050f0402010c11040f1d0f030319151401080a06030503070206070f02090906100906141005070f0309030b01050306360303011d 70
    0x151400c203c030403540d00d00b4107140e070403403c0c00e072440c44900d1400c0e8404c61084d00a205659544916841c8161648039410151444580f01511a000401c407182041c0340a003005680e035128410950b0103582440c2c0030342000114a48650038400c80321500380c029160200343c1480c003929602c00c01810f9401c42c080030000c4804040a560380600d82c02d040101d400c2403000c290501c038007a55550740c80d034403004007044204101000301d1081301c1d02c6d07110361404a104100b10380e041d600302c0701141e0170000c1c80350709228260450b202d0565911510f90000e02804000581c8011710072000d03180041c00ea401001d5000c40c0c18038071086541c4031001e03600d40a03d042c0c00b0300b00061090b2144584002c65000180c014109800c0c007082000385d540480740b00c800d21208002107000107d0b011065440580300b511562440341c19801c2040268005070403450180d03101d0400d2094030060b400c2e01c4241c0c00700d4002145008e05810300c003070401001d190300f0118244800300000c0351a900fa0400f11071205400c503c2c2e51002d598481c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 140091807 1250 140090557 140090579
    0x6040605091905060a05090f060f0d120c0206120f1803090d080304030c05030f03010306060f0602030313020609130b03060702150f2a0a030c02010618050a0f050405030310 75
    0x148103041654080071042c04040c0c003d41186600c01c0c80188907145240e5200c0200c1c0301c0800440303400c8101010752041045901c1c00300344c0c00000d10070940c1e1055406c5410703511110006d840342c0c407000c03d100201c010b02c001c564800f0101e40301ca4280400320311090500c112615020b404c00e44d1070000c0d0700d45001102e00b540f0000410390f10703c00402001c00b811611603032690340036944080c00607010402d1084202e40407400030401442103600c189013140c0e0700e6245003007503011201a0380025003145494141002455400420307613802101704049104103150b144002010f42c41034130400c40d000740401000104400c402e070f00c004101c00c4184d00351580741e6260304089845034444010503191000c29004243c4101c84144425802400e52070301185a2641d180000342c203400e00d054181c040c03200042c414001d44e525000d20742d00070384240000c1c45100d080880401ea05004010f032844102e60300e07000200e06009681110720030401a01e01080a0705050810544980c421117500681d107410b01c800151031000340c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 140093057 1250 140091807 140091811
    0x7030c050c0a06020f22060807020327040603140106030311030c0d1d030a08090102101a1507120c020901060906120911100908100504050709020c03130b030604060509 73
    0x1c600508103026060755403100a40001c02d43c2030b61000c007072181da80318848116141a80700501d40d402c2841c00e1400000070401c03d4002e10305d400310340061024261800749446100f14996945074449881c1d0440d10110380140401d601c060320310103020b12a420884810351104080d60302070754031184d0501a0321855580d0388156041400e8551080d443c0301c400301e2203640c441658804080c0d0303041181c0149030000c0d140198400040d81d6101c00041c0b60000d540e0104402e012a642414041c008658242401e01e0642820034009004c0c801082c00d030040341584004442e61264444006244881c1c4400e00414912011904a00a8810030000b00e00140a901e1100031940181e894400030a601460240580503801048440007803446200405980d003a042040030002580d03240d100514200d60a40f4005107034403c15101c602c0c05081c000450b60219a038010b847d400200540c1e100d80f050000303483c5100d00d500c204080d449000c00410003001b100015070055004450a000454403201000403030501 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 140094307 1250 140093057 140093077
    0x10b0a03060513060c020d0e030c090c0a05120f06100801030c0306020913020a030b01030f0e0a0f170a02010c0e04050705070b04080903031602040c1e11070b0a0807030c05 75
    0x4084080001418030703084035511859200b03400d4600200380d91960155080d400e10203015810181424110f95800702c0015001f40089008020900505c400700e1340c3c804001e405060380b504005400b00003580160111000c1c0201c0c0381548009241020302c1d0031b141001a01d50074481e00e060054035038070324440c00055040c0c2e908a1802141c41c3c0c42c41d555507000b580051a01034101c00b07034032140c101224152000d00094852030320042000002d0b440010b0494044110021889103024440d44c000d10700003400b41400e41e449900040c00c0c8419040070444040080030000d245030780090307801d0340140c0c190450041081d031382d10344046005d1040d003007009461007242c00c4000980d09220380c0000c25070410606802c5070203000e405e4500000080403d065502426540d001c4aa20010200440c00c00388100c2c90100b50310310f080d01e11402d0152020154049410312441008080909040082d03003e2021380300030241c0081050340d2b0b000107030b8054a00141220518042407a000010020078000d00c2100d000c844 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 140095557 1250 140094307 140094319
    0x10504020a081609050402180a080f1002030a141006020d0e010c060b1801090902120106050f010804051f0e010c0c1101030c17040b0103050d02030a09031709130c030608010b 76
    0x3e00c0103640300040da000f42c003500800c900480002050b881e9480204a42c1c22802044061001040e00340100b25450b64405400703640a03c016404031b40c030221304010010719103c0702503540d44602c68080d010f04100c10300603800c05407a40a010210380c2500118080340e82c15002c3d07401c0364003118410780310041315102c1140407070032200302c08000440d02e0780f10089110005004c203030b600d80c01031415201003009804c1190314969030000318055241c540c086001e644115002030103000c1c10040032402c003080380d0101c28180090a001f15041000034440c6452542801744070305c209400c2c60104c00d001c1d01064544004552800c1c1000c8480c610403540c880a045e0042620307600041d22600440c010702402240004000716080d541c02489000042507000d68000c000359016541103080c400c0c2803d015030403035410755000308519170106030801065021290003440c00300d02440198000b80d05882420a00c640c4001000b044441440040c0e018800b84c400654041100c0b689800065007211462018598052 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 140096807 1250 140095557 140095561
    0xf0f1507180e0108070b03011d0417030c090f1e012003030c1201230d0303020d09031101050601090317090102030c1009060507051c11090307060215010504020a08 71
    0x604006145400914030329024444054840d407100001c815604090109009a0010440300b2000c110b03400c00307000310141c5280f9552400102000c08080b900403c000c640440c0006010b2112400304107580d00c204500d8a81d503454030640156280d0320083c481da100302c19800009000d030034441c1c038010510046044800c940b00c41040155080844040070700405c402060a442e06544140041c6000d500b2401d1029110f007109541d420740c61505030080410010b8628044015050702d10041500c1c4070240d4141400c500d072410100e0107440303041c542c6c200b01c6007424260750402d50701c954540b65030007128008006a8403200300440d80034a0901c009058840c03868001400c50031040010480c560050045034a045019038906003880350389101440210b940c0c030a1a000d104c07a9000303059211001e40340041c5084246070280c0c12213200e4140c60992240e45160912846104008446004400a00312084030f80c0e1040c0007507864407512180030601c0b5100000281a0429000391a103031103094076200203036 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 140098057 1250 140096807 140096833
    0x130809090a061208090907030e0d050904201309060501020a061503020d08040806010b0a0f051804020c010209030f0f030a1110020703030506010e0f030606060f130801020a020f0f 78
    0x1030500504181081d542d1854001007207540c001c00b00c0185072054500076150980001003191080c4000c01400a0504100d0010300b442000715a021990741d042c01e00036143c440a00208008100d0302003051040040c04440346e11100240c03002d03110b1068030b006075056554941a10a0a4405603c100d43c0582e00c03141d034400c00078046820190440d298501e0103985582d90b0380000b014001c01800c1540c80c2d100019050204c00014031560740505103440c81245040004000107040c5190380300b1100400c40085034000784610040100b001d920001807080d915180f81c0c07a0030134000c0d800544c00c2c920038070400c0c3d0f411a0804003c140c48680c00c40d004040c6003048c19628040d20302114440c0c6510503800386c40846148030903c0c1c0301404003a4000d07540000c451401800260080350540591842066804040ca5965500041066020506803810703526105440342c0e20043c0d0041c11754190454420382c001107014501540500300200041c1e0803071301d02040300703103031140c64041041d1340a007103400c6086004d80d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 140099307 1250 140098057 140098069
    0xe010b1807230307030902010921020d140601090b01030609060f0902030702100504050102030a0c2c061b030a1403040c0504021605011803080615030f060f0901080114130809 76
    0x16540d0150003458800c035600380c0301900ba0f100300d4240c4007103070341c40c40501c0035541d001341040040c0410320b1180c2e940c40703d030010002880040c83e1000b8400d0200500220400c0302c014000309038210721608032a4656101c1c85500e010385490510b8030f001074a01000001c14407014041e0204a0322555290026a410440390b10040d40c0014401029440f855080c101c0211071880750f40d104600400c001a120304044071a001070718401d148806c100400d44070080284420703040d800c61054201081e440b114060a000300d005d90240c1c00500f521040815034810301080040300401e0103800d584d440c40d400340503c600004c0d00307000035103000d0403000d2500d000307000310706042e0700501081c01003d014410622140e55290700307464030142d00800d881141c516030380405030030915281c1c0111003140e030040224211204140d180c00020185500301900d0400b1880c0c07a103c444403100c1541c2c002e044a4019a1070300d2549010340301c590300c2012562402000186c021951542d02801181c1c130610a43c034081d556020420 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 140100557 1250 140099307 140099327
    0x1c060f02040b0d180503070f06060b09092a0f0301031502250512040312080702191b081212090c090a0507140a030e0c03060103050705010c0302070f090e010b1807 71
    0x50303074100c120800c0106808001401119204940c4240389000502e0274030705a03940c6170b0008024080a1058030001c0e901c140c1096407200b0800800d071031315180c0b845e2240c1c51450044107480e00c0c80f80041c10f44c01060711507009605070fa000700342f0f01206040050101d0102c0c07003402e440111486141240a4940c05c40b0103610707488a020b541101c150100a180100e40b9521607032044408400300c055481040350030002c0c282d4010f51500103865590f884480006081c107203294000c006000040403541001348203c04603000d0604035088980f00c5510304c9a40f452588a4915035083c140444000b460b4140e002480507010400a04200f80c103031034035040079026260140c511018400c1109141100f41070382c202030029005036640101e503103e404442c031030401020203030a9020303402c20307001132001c0b8000284400440e4000c2c41e026210000e90708003203041c25890b811240c881002440000744109131600001c0d02c1440c55402001100c08002c100020030301c0344080040c0b104c3c1070740c00054505020b904550 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 140101807 1250 140100557 140100581
    0x60f181d151906080603010b09150301090f060204063209030f010905070f050a050a060e0d0c0305210c2104051306090e03030c1204111c060f02040b0d 66
    0x100110007000010b4a4980d4001a40d1007070103818004200050f4801507130f64100400394020000420a6004200c0307600c4002c108514080e003e032403088050b10309501c644001e9401281100210300c0034540600a548244038400c005a074820301c56031040c11160001040341c040720b080e0030485200c500500007a4000c42c004c80d40c5801130035400d0001d1402801403c00044c811000341900905011350039040132143e4000c14003807040310006000c191504141036055400302e041412050b402c0f07000144075203e000300018002c501c444400810403400207404a140f0b02c088140c3c1141d948403a080000b1401014610951503011880150000420340c05a0700c507420340c00c507924a480d8031040404e0300805c82060079039403a6134611007007001c9000303441440c150415207009103185081c1200205094011488160701d05c03280d6070b012504001b00340d5112080040c02608040c40822a10100200000c070203009403111401d00380c064682001034422070b015140c0c41e004840c280303109045418020b2610309004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 140103057 1250 140101807 140101831
    0xb0322020f060705010e0d0f050d090f0c08100b010806060702040908210105090901090804061d09010b0702030c0108070917030f0301180b0f010504030201110a020a060f181d 76
    0x4400e15842d02c800405400c1e014100114042c182c400e42d007417030304206c203035910208160f00d041e40f90381c0c50f4440700f1256001c08507140400c022505051150381c0d103900d10f034001c103007804080e00003400c0030340852501710409580e42c4c02c009504555006481c80c0e8402c803102544180200046030040c03038182c0c8910f40080c05504400e0a00d0940d00c80802c1d603c121084c0044403505400041060340380500c0b0155110002c60024040c5d954651341d6094180514000d5206001404480c8200d61382081c002012400008204814659450310094826480080c0c01d0f0b02a01858080c10140e50291610500411459680760102031412104515034503c581c8584411f0004019210310843c1d010043c5010f44010454242001e5811100d201101c5800c880d190107501e00d54211003960380c00005440c2241d4080c01d08140127070b040c42d080e03401c05d000d00700c0c000d501600e0340764003084403503002c0700c814500705903078440c40103003261714a403c403107075120344100503500c052170f000700301d01c207038100e04c45a00205400301c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 140104307 1250 140103057 140103079
    0x1809010603170c0c0a05091b1e0406030f09020f01200601140102060106030501031a0402060d060806010612090210262d090c2205040c030c0b032202 65
    0x150300d1025403180105950714030b0110310700482c16410300c01c0349882d801c1255041c1150307203040042100103500034002c1c0601e03003205800d900030f425580300701c80300c41400000704602810301c0303841c03010190450301952000a00e8590810741565291040c0414203070028040e4264910080c01150b16030709400d00c2440460460b00d2381c0c0580e910030000705019000c0c1c000b00080320311612000a20700b0105038000c8007091706003001003003c914003114190051a40e40c201c2007065031340380042501c0707115507189048443d103003080001d4004004181c49050b5005590f9503070149272454907000075118004006540700f180018050380a034040c011076050a01c500c001c03c2c4001d0510848450540c0003110742480301030700c40d00e286050202ea00550540f00030700c103a41c0e400d541002e4045540e54100002d2050281c000110241c9003000800f8170b502c0c0b00034814000341301c0340c6414609812030740110720044034641c104c884003003409030109041d80c1c41110240c50407429180c2128040d4242422240301380c0e000429030f40 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 140105557 1250 140104307 140104313
    0x20f060409021201210812060d020d03030506040c020c01120b0f0d05060108063d0803041e080f0d051c0501080a110f0a03020112060b03070f030501060c021809010603 73
    0x5083d2140300c556031500f681d03141c5080e08160448188003900c5030f0741c0142090b000581442d00380c6a4110110701c08440c10b907290310209902822a80001e580006000d40741800c040d41074014070b1080030161010700641e070100e00103a9803004a44902d1303011494054105400d29801d070301090061400418210050312103001107502107425030400d54603500a0300060248103401c1010f1070700502c0820251850f814044844ca03840b621342c2520016001c00243c40a00301182c108400d03020388002c1050b0707640ea80e82d50103620800364010300700c2c01e90a5002d00c000513100340c000c200000a100c0000103014862102c0700225015402841292182181880101c044120364403c19028115810041c18440170900301101907842c0c0544140c49400c0042c0c00c0b08040d00c41c00a440b089070340c282072500400c680b4100701c02c007825540c1c00c07800e5080c2012007008443c07648540c0c0501580d1441d2020080c998942c94120f54014401c540690001a000b1400c001303071241241c0e15501c103058400010345c03039441c0e036 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 140106807 1250 140105557 140105561
    0x10110f1b03070215070614100e0402010c06020307021e010212070813080d27050304060c050f01050408091806151b060103061d0730080412060f05040f020f060409 71
    0x1100c0c240c0342c04c045501d0041092920030800300600d0b0740c1a03810140741c21500340524009901901ca140e501c91008202164050b540075291180d10010540d104d20781441c00030b40e1410910030b0f25081543e000c007100c01b061010300c211038900c031075400003094a030740722130007078841ca14003828807110180c0122280f000310300fa10f40584039040c00040003144e40700d00300c9102c040d21041c240301a550040d40004510000324000211400c0765a0f42c2448081c401c82810024202002c6540300081942000b01304002c2012640c01001c0007035003110340d129a4018841c41c1e98081000b00c0d00c1e650494400c200c1900f403070030210080c104040604002411100540100d0ba0030900c00b82c0c03040766080d45a01080890805560300403564980700e0009004140ca40007a0b08110100032400e40700d503030088c03d4411001756610704401c1a00b82c200d0040d48e543c41e80c40d80b0038483c0c0100001c00703951891030041000d41c8a400d40c050140030f03e400c4084120002c0031b80d000c00108402000586500a01c100000101d06030340d4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 140107913 1106 140106807 140106829
    0x706080703271e05061e1815060a09020c0606010207080a0c1806120b06041a030c1005250209011d0412030b040e10110f1b030702 57
    0x1000080070000c01040c40a0058041c2c9410040001008650500030400c0301440a06c40d540e003049200f568441e4801d460004d811441900801c800f040c041c0315049480103044403101695800404101d82c001c00d640c2946401c1101080060b40c0c041c04000010312903500030f840c805065940d0442016818010b020510188542c0c299101c4400d5010704007a26110407028500f118608000000ba00d08440e1a0310450030110900c03562160f0b41042c08a44001a008203c4010144200305c1d24001c91459a410058103004460070700b50340142a4046240001400f80c900030140103012200d20160807880780d8091144c18a0840203011220562068004018444241515004070090403070f0301001c9078804c3c00d03d101405d00c1100441d02c896a02a07840c001c210f10380c60844120514095940413185506040c0014130510065109107030038580d540041da03151501c1680040c1083c880 = true := by decide +kernel

theorem cover : BRFrame.Cov 139928057 140107913 := by
  have h0 := BRFrame.cov_init 139928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 139928057 ≤ n) (h2 : n < 140107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
