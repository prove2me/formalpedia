-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2307
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:18:45.239189+00:00
-- url     : https://prove2.me/submissions/c0bcd224-e0fc-4935-bf95-14e940945212

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 414748201 ≤ n < 414928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 414749451 1250 414748201 414748223
    0xe0105100c05071202030708011a0d03030605100c0605131e081b01020c060c09060702041116030306140d2001090801050112030806030607090314010f02311202010c 72
    0x80d800f4803007940103040b142504400c140451040600301603242d0000da071540c0c07420407403150140203140b11321078080042e11498101040c1c0e0500318007400343c9800a07a00130081d210407180b8241d00100366511b82d80521400c2020345c031781003901c1c0805504100080e001640d221406d4400340321004886807107a11604480b85011a5019804e141c210010340341c00c00d0365804100702d01840400d0100d0f0707a100900c0d03032203030b494146920300040140c080c00001034000c1d40d89108030310060a40008a80501c400ca20040d02d140480703203802405000640a84500795100d1840d41c903090619404049003903a10401da1031a0008180310948103950012a10703042048003900069521001e01c140c0b806011105800c0246402500b40684840c6019001c14041d610560411500b10b81c09100c8006032a4020400c04c0034840428240e030143c0048160303441203503c0040c844080001d080701d00d0f0302c405130b5070000c01d590070341001c03c022021000d4801e003040b030643d200c01c1d080158810b8040c010b04511401c0c0306030f0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 414750701 1250 414749451 414749453
    0x22101021e0703030b15031f0302120105040203160518060406050a0b070326040f02030f030a110606010503071b030507061418010c020a0303020c0f060403050d050c040e0105100c 78
    0x7101e08000c45040036045000801da02490340c10700400345e5490050750740c0802004034500042c42444020110756460321181400281c4442c142003c034020340d0003c00c88000175200440303941c02003001351000c81c0b207440350940c40e500c07400021000304200ca0006005195101c00c4c1700c4000424a40102200d0340310381c0da01c2010801f41d840e4039050001d0040d480d50030f500c2e15960318000c0c0401029404038500000000b0050030781c0c011041a4076132003a445610209110807a00c023003803170204601d14401080c00041168195190b02010f43d002d5004031504690b803e444030001501c40c0c2c48151400400a8248610040c00c800011450543d031407003490014503065090302d80004441e00c00000f00102000031041c0003007142103070381014201c003d2400800416468140103542c8184900d802428541c0202d205141d00c00103020300a14444240281c5e1007030701e03007803030b00410541c070015030b4901d45c0e407600011980d040305c441c003503a040d5500d01100d49a564200020801d045074840e548208200032003007098 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 414751951 1250 414750701 414750727
    0x10305040c0806040c140108041104020a1206171002070327081b1e010207090b12010203040b040317011a0d0e12030108071a1e040801090809040e0a02210102 69
    0x14444d80c0141d0309500041d04020550001c2d0071103645445c10403168409000200fa211908551181012a40160f070340700307850302c1950b00260759000c1485442c07030102c0c00a0200b40c40000d000320b8100b4003003903884980309800448124003901c1320140000e40140420128008592078200742004140103e13404142d44000403031800103403417585019400154a1151281800381d000b102c080c86406006034516a4440000d6550a007803107040d425513100e4001803c41d440f809189240e11643c1e070000c0d0340c5d03460541881c1c01e4000f01520101d0000760500c44404080f410401100d060b15240304810100880c08a500c5e074041d0444480300c045e5136601c3c2524020380d02c00700020740c6089900340085403250b240150040c14401c13a030b0300a50340210700b88103171240752801000710f8a1514a215410400c6985150351803c10302440d00301400035072070071001109100c0c0e100c0c0a446000c00465042c0030784010054055100c0c20001030080d007115a4080c40c512420300c0200a050b07480400700010705110181101e5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 414753201 1250 414751951 414751963
    0x60b16020123090405010501020307032c031911090c0d0c12020a0309020907051206090405031b06040611070206070b04050313032a06090b1e0a0314070e0609010305040c08 75
    0x40c10312440000f140d0784107040501500d0b0042c0001d002450410420b61006000e4090900c00340f0740f59041154003803031007140c40c1400700c3c1c2d0f41406000c0310031300000120015140c1e081c1032800c0e111290740030351220303941c40c0040ea003a104020b034500c25418240b00c1c20307003c0c000c0d10340510182d0600ca418510350340704140903c098101106990741c040351701e1180e03005004ca560400342445040000410050b50b10340e41121140303401030010341d600049c0b0717981c0e13044c05411802107007001100c9140d070041c410250800050b58a004074010740c800c018a1000000203d11486000c0000b90030440901004d03000c614521005607109003d0300a907403400806d148204010413580e00222003124a4a0b8910007411407a40013216054008448084481c02c04101030034074007540c41201030180c4000340e04520048600d0203603964440d41c80003580c441440b080301602a00c2100520803215240030300150032540f003058000d010a070090655881c002c400303801107000d04030050040da820204580e0016002d6420010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 414754451 1250 414753201 414753257
    0x51203090108070e0d0201110304030615061803020a121401020d0c120608150702010f06150f03050c250209090a140114010603051906090b01020c0103060b160201 71
    0x165a540340008005004520043e200744100080d13480104143c1d200d10f0082c800c0e1940908008000ca00d02c400c00d18030314815a080100000c0c1400c0c0102d00101060144100f51b81c3c03c1d85036609044070180789810382400511000e0341c007484400040002c00402a40320b03074864007412000544610201c2121b007a45e00c182151810a582d4807165058650b200c64a2144030500e007505001e99494824851340d21407605404074013185031a00442c580900035482031400040c04c40c2c2c188080c90386d4442141900380c075000d140000c0750310a42d400c3c0303046109220b0584100032800480d070601d0880d00c00c1e0f84085400c140e00810204c80c000030040580e440a859612500343d0100411080b515407404000c1007200354000c207074070380c101080008640c9804809605403800f514000999aa4072240104400345d2041c224400038582200071501c3d45071038010780c0080c202030f02140c900e9141d680045049a2030b80c40345842c0c1c040d007404510a10304018a145012900526140e40594000c250900c1da40e400044 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 414755701 1250 414754451 414754453
    0x304080c0f010606091523160c0608041101030504150b15132405181c140d0212030604091a130203011a010f030c09170307060e0309031c03060512 64
    0x8005c000c2200c00c55505500301105140039a00000b140d501f2004c180704001100d0220b210116000440ba40e0b074212050406030001202c0502903581c51028021010030364090f5007a0030074502825065000380140c50040d54070003040c0c0349920306d01491500400b4000d00c6036500844104144402c03405d000c028160200d2152068140700745030203040c4121a160000c500e038100f510310028407941d070300003056514020b500501034024110a10008000301702000c01c0380c644071600104c0005000034140d000c9020700780d560440310780403802c80e0240e0f03581d02e0840c03682602003020000140d290426400080c03c16103e0a0310a40d8500307000d0180400050440d00c900c0c13011030702c05020081d4542402a00d0b504c4601698442c0141c0110b00001c00c6006000b0a00e002e060f112240c042080c0d1140360420010508400b0300494a9024000240c0703a50080703200f91401d50402980c1800b240f00401116142d003002002403a5484000d103003104580c8070182032809266880304d00290325190700c680c0c0510003803204 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 414756951 1250 414755701 414755717
    0x120c051e1018091a030106050d060b061b01090b0601020f3c0607090b0301050a0504021305030f030903160609030b090705190e0a14010909020d06020705060906070e060304080c0f010606 81
    0x4480b404d11080c039030303140d9442603041290800054480049040f101900148042a0b04802c80040b4006118050840107036540c1c518082c489141d044d8044ca115522450000c10141c8604004903525410340140c03c038250408107841440c00701c80c4800341c142c00c3c240c0100075045642d44000045101040001e860150407400030400c81c0340c0e010407044058510f02803103600f07550420012400310041ca000d41406240c2c0050090f0200103071100321001031000908441c03002281c1580d650f100c0e00003081c420700130720540030300c0c1e0103404151074200243d40781c6aaa46000a2440c0c03141c89030b0410191513001503008010010a460702da18003a0700240103982400c41485181034640703521140300420001c5401d140c5460184508411080d140c11905a000040b80117003950001941d43c083c8120000c080f14800a044801c000b804a600c5205004c4442510700580da030550a4802c0001c46030f02561002d02000000d0000d40c16001a100d0307184da5404580c440100c0102e240d08450b01c1c0d07001503001c03c81300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 414758201 1250 414756951 414756971
    0x3050a02130203040308070e04090501110d0e0a120c02011e0c0b01060e33030a140907150810051207030b010f0803070b04060b0a120c051e101809 64
    0x100e0400001d00e54461001c518500c2e06071401480040040c00302000c00451400700c074200d5035144c0011001a41201c02006501038902035204141e114507440d104007030501410b014141c1c0d02080c41e0404540088060101010494045032984110402207040c40026141001035074030b2a80e82011b46101a10751940b02201810601d0214005174001d131f040100d8424541c1c2c00340c64400c8200c45240206201c05030203030692010000380c4900f151504084400841004030703030341c0940c04c51001003208401000a584420b01c400e600d4054074007038008142d001110390400c4a1250448680c40b0750309141c0c0000958079180041c00075800604035030516407043c28140280700700b114045d401461440701a07000c031417030001c1054803400751910140003070032404009812320929410450078040c00414442c02151170300c0300c01c03940707010500098032240001c2c0c2021406081ca4645071000c161505880e1040540355420400c00070b6140114104201d02e0790742c0c1040d00c0b903215034400086d24010b00040f4081b081 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 414759451 1250 414758201 414758209
    0xd06060e0f06130605010f08070203191d030d0903110310060311040506010f0c02091902031e01060f0c020d030e0301050a0207020f03341503020307030b0f0f010507030c0c03050a02 79
    0x10303078040d84201490003c00f040031b6a0421074041000100d8103000b1104d6843d10b801b40d0450007080032800382d02d01c0300503041350039aa00003800a021600b01e00c454440c0c0340ca034028581d8480a05094501080c541c0c80d0500204840805880c2c80d100001e0859074240f107403000c060291803107a8000c54042104880d03250051825018060340b01c01c1c00e19158101003c081c6000342240b2864a019005119040115505081008803806484010300082d9524200803426800103a0452200c000c481410400415158031480d85486a50010741e2400c00b450055000c2051140251100324144804c01800700d80f280c0302801680e00c81c0c204445c005071103a040740180500c60f02546645442034020000c0050244c03a00c43d104000040d02410462001c290600081010184c0c0c0d0050751441c45030b12040420a50305400442c0f08803640da0301880a1020075081c4006c40c3d20a942c12603000fa540d507441d4400d9441800584801c6010b454002c89c1c041880d1601c0c0e0f10a009900142d9030703030b00b00b40c84420075424 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 414760701 1250 414759451 414759469
    0xf070c03061e0504050304060309050a02090f0711060603030702040b1f0e12060105150702010c1b1d1003021c0602040e041419020409030905031f05090102040302030a020d06060e0f06 80
    0x16142d90b080c401e0b0319003a034540751680724a00070507050554600c5008140b050801c050070741e8a60181c5094000d00f8280c14145d92158211068000140244503c40554101141c06801468054011820020140d00b000040c05492103c6034000140b0107030001222030b2512981010a82074a60004070341020043c80304a00d0b403035240723100680c040c800412117600c0740007415072014004010584c686071584012a80c00380c81c013001400a0040d01350703000a1089000e01d09040b2510040d621603401d04001e036855010b8012220141da0000d4000704001500305045501241c3c83c2082d03040b54a84030b9a500c10b41260007a4224640114079141088208400030102e02c01074401e030070041100703a800d603645d040c0c10703003407201c0003800303543c46c0c400e48000c05000b0000031000e00b40c001d060b030300b0b2002c0407041a400b4040c104090f5840c1403d000104110309418400c90b41900d401401030100d681064091044d01c40ba00c0c0d030121410f0350b441c200000c0410621180c076001e500e504640c1415801c00e082003081c600 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 414761951 1250 414760701 414760751
    0x30b0f0a0f020a0306060f0302071104050a090503040b0a090e090a0b0408090d0503070b061c06020d060b0d0e0606090108030d050c190504030623150f030d090509090102030c0406050f070c0306 84
    0x11309c1045a8000b050448500c414411800c40e400300f880c0c1d95005090019010404005000d40303c0407030049042941240580424145980c0340d60940340d40d038000f0011003006980c120f055400c00c140404c041100070600c035500038050b005c0d562030f21201002203500d070b2144040c04d8901d03400c045040301c10890b00aa44075080441104c107412200b101c524030400700d0701c0c1040005d202590001d0425110f4602d500400020600340a040d92180d206800603405025040000d440c80d000303d8000481906d403004201c2e040c0c4003510001c41c200b183d0500400020040581520700c0c1c0e00c400c0c8105445812907100554401030300b0784e500c0e0788903403461500c0780c00d440345400c4900342100303580702c21524620b00d001201e9005402c0e40c180310520301c86401040540c080105c40541500410301c0e521615504050200d0840300142c9100c44d8a50310403056500302d0109441c201c820031000c001c00c00880744900301904a00300c041006170b00d8881e5603614214495016442251065140c021403092101c3c1104250303801 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 414763201 1250 414761951 414761957
    0x6120209010807120f1505030606100806040c0c0b1e07210c030b0a0801050603070501030b0a140a0f150f020a0c0303210f021210030b0f0a0f020a0306060f 68
    0x1003503a90300081c2c5003100c010400b008004507100e110b4074a01080d00b003003c1007000ca001c02c0107030490030780c540ca42c0301d1000c0c0259406403182d0404500c0c14104075011109401040d43c40e03800940b102d80410001d014603444d040d0030044003400b940d000c0307221490502d0040550840203d200070f140d450a29040200034404824011440c8483e046021700100a00380200e42401c0029154891802540103152400100390020003045011036003100550140d8068070701202101e0f4559034460044055404840029803c1546090100305d055070200180728003100040c4128051a03d400c01c400428070540c0c00046156400f1518000140d001440d40d0038051141c409840e100d201502c6422219020303110090070001000ea904404200c0c00101c0c1501d50035403c0c060240d82c041d445210080e40254140c140e82003452404a0029003690842404480d0310402d81c00c92a5540702000c1c00e0120010f10284c0c0d229112440d080d28546c4d40e00c02041d4a000c19140010b2450800b9002031043c801500b860041c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 414764451 1250 414763201 414763207
    0x151c0507150f02060702070905070302121f0504021c090614040803010906120206120703110f0403061d0a060c0e121f020a120905070801090b0f060612010b220f061202 73
    0x803640415210150348401d000809d05440f8004224024803840c00d03200c0d0f1001c443c0c400c2c0004801154441c43c090307603e1028a1000c903844404102c03c91203507418042000342c1c040500901d07201650043e0202c80c0c050540040e81d010184141c1e81c218108940c1120b0155000006000c12111441454003804000904d1a000115540400c6461180740d1610b00e01d0703ca0303000003410041c40783d00b082448150300d080c3c86840c0c00c3e21f401010b0107a081400704540407070400c40a1001c0340848003829110b0f140e81c000030070b41d1030100d40310b450082c1207901a09081020300c0304405100d0b100c100410a0030b11150004010b03d05240040c0e902681801400400c40340c010001410442c0d8030075100000c4a5140300c0000b640c40700307841e00b245410940d81c00003905500701001002030140c4050003600c00e0703a65091864460b583c140800c81107200c1c1552585082d18980014021042c10401070240b00000003000e20381400304007a50f8909084590203140c90341e54281c030500241f40c2c043c0344003910415140d0b0070740c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 414765701 1250 414764451 414764461
    0x1c0c030c050906030a0603080d1505060c1c02031215090a2f120c2805160f05010608010e0c09130b060105040b0c06041703151c0507150f0206 62
    0x3150b072050140c5140301c1c55000c80400c0e8108510744c000c200540c1d00a0416698030061400720010300b0480c40301607001c4a4482c00000c0ca03080030011540b281c1d14000280603000b0164044107100408480303d8401c62006201002c42840300f56039541c0103920b08442020038200f48400c004203402c0090075200d080b03007400030056444020000400100040c10300600003c076440c240281c40c0d00075100c00c15904207076502801504049180245040c3c821032042c032400603881014908803603240090000025401c0041040100542d002803050f04d01ca99400900c96100351186400c1d988250488403485c0d41d00d24280046090030000790390382d00390540c0c0e00559440d10140c012120441036402400b0100c502d00042e94903885241224041c02803052099181c1c60152503d66807482d00703c0741181c2e504035408070b08000341e151070207481c07050008445468240b26804103001141e1100d09480f000740f51151006800580280101c03009821100c00707600840c41d182130010b0800d100040d208056400c007000b402 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 414766951 1250 414765701 414765707
    0x32d0204020f0702150304052107030315030602070b0a050a09020a140301090b09011a011e030b030c06120f060a05030a0f051504080d06090e0d1d03031c0c030c 70
    0x50115012900162691445a80940544111030000358004045100d8960310903141018500a6000c0c000f140c0000f091810190000c85001901101a2030284410400070340f0940000d044072004c5075849840d02d42d01d91340e282c142c1e0007803803040b82c456540a0030071090340b0140c45107903441110808180700c000c2858001c102e12260300e00403807031907103160240e8542c542c600b500702c40c1801c1d078040044031103464a40d51180c0240b010100194004010903452441d540c840d844003280d5041c0e000265845400707080c1d00307600a1102000c5290580115005031a1039900d0a0281070a4a00c183c8100780c2032400e12148210114000c15080c0b04000c6c542082c441520002043c8040640c8009040607480e8039060180c6402080e02060b000792243c4420003080003441c0000e00034032002c0803000e000103078849015030150b440204803044070b680640d103030420741e078402c607501c0e9500180070503140b20425400c00031038115844030b0210301e1000c1441c2c1c100740e109060b910541d80c44442528003000400b021070401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 414768201 1250 414766951 414767033
    0x30b1f02120310090b040626010f0203070f0804021504080c01020606030307030504051003020f0a0e040506030d02121e1206031209090f04021801060f0201140103020a06140c0109080403 81
    0x400b02155660880344146c0c0701c507130201000e014204c612841d0b402c00c0d80100c1d040c0c001062000c19140d400d00412030904034850094a0240070107440d582003080c200c01c1c0840700006c00a005a81c0941e0036104148081d42c03400052003d046031801170601c42740b1b8040007901e400070150155010b03910801c0a0f00c0440d52150550303099910440f20102c4102c02050124064001d040241060f5100041c9803100c2940100c0c02e1507a1850a40d403c0c070059844400b0942c5440700e00c2d04070000350f08512066008050020002d00800c503501080c40014001813031191459000014001e50040694050142a28007080481840c1180f8502d182ca04484000494054007005d071848009804800c00b083c21995504500c0f1800170409418400d00d6a440d00700900f00010b1500d05409540f030034007200128488a084a8180e81d005000c4040152905c6400c4071050000c3c600002101070902c4075100c400c00030301404c0d180318014a860b5032220306504110994420031240070704421045004141017003400740d45 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 414769451 1250 414768201 414768209
    0xc06030c14030f0907080102041503050a1a06031e040b090f060702121303020603100f0506040302010519030b1903021003020306100309021302040e011a042103030b1f02120310 77
    0x740c41000c0d00d88000d503500c0c04119800041c007e50022801181420482d6803c22100ea0655003c0c00b85d51145001481242c0000c83c140308644000c40f0003446500b040c0f0700654011002003c07a5400b1074094121101059042d00c04441030948401400980182044800b41107403034203019024900f400c120180da500d0301400300d441c0c59440841e400c01c03022140c20f8060300450300900000d6076841d0240c110f1107100800e0166002c0805040c00114513030503c40e0a903016079506031a6946171107140c04110501204643d4080200754568061607119112291a80c184199071403803003511504520412800390700803503540003010301c140100942a900c0070001206900981000135a02c0464000705100002800443c00c4080c00040c0c0010301c01d4417990014122040c2156181600c20360181c6003880d4450340c03080000706807040d01201001c81000c100401f0081c828180015100c44110101c2d00d0395905040d1120f082c01e401002c0c8001d5601403104d1032010710702c1500c807071640c40c0c00c441d0391002c5241405 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 414770701 1250 414769451 414769471
    0x10b060a0c03020a1401050612070f0e060d02101205150906060c01090c06021b0a050a0b03090304030b011508070c021c03050c032809030321090f0c06030c1403 70
    0x545205050013480820b21454002c60040102c8210301072041c0a0310007610f0440c01040d8000c4010585240801c0c1842503544034240b010b151483c140c0101d50038000a08070035444000091008010f07590020b05422013055074450041d256840318001084807002000705140000740f030000400e9a641c20585079000804450050321005a19031050050102c0b107001061201074030000f00d44543c0015094002c040c40b480300e041107101e0801070040c00c14040c03041c40c0c0c1004140800f4406414600302842c8c0c00200b4000300ea051a6594541100309182a405041e40241d0b000400360400e911004031075200070a420312a04a2802e5400708e0a2524140c031107030545001200750f903080506c510201c0d0041aa2081100c0e02d0b1139a99100608101240c1c0d000307161900c0480039402901e00036005a000c490301512048403550900300c5100081511303400540515598448482c001240d104a0a402a0095011b004900e04001003d01120b0481702eaa40610031110302201d80014400200c036880080c0302 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 414771951 1250 414770701 414770717
    0x4030503070311010e0a1103070603060305030301050d03120603030e0109090e060f0709051806030106080d081501050409090b09072102040b01140c0a0b070509031b0105090a140909010b060a 83
    0x280351607004050300c0754001c0840c01500c4009044c0203ca151003034030000101d02703440d0015954030701907040700c41c01d11009026804c1480100b1544c50544005002c480c041d0400ea009621541c000204a5074a60402c4002c0f94a07114004a5568000454005000e00860030050021045003040d0b84803030051251201200c1e8100160700031f88240c07510070040c80050207052030070807001c000c007540400440ea05070196180c483c00007a007480020b2041c600506d103454010740e5440f0714486096803890000d21505105003040001000c002d00c2c421400454040c41003100b0741e0a004c44c40a0030108190b00c402c50040092940c034580388100044d03a210399504980006499100e0001610200f02c41015140900b00c0814022000000850858151031044803c0002c560f200281502c0b10b00500c002c4a4141d440420307114400d4103481c0307014899020504041307041240c1c0c0d03000600c80540c141c11401c40c0740000c0344840d48505141d42d5041c2c210000c0d50082c0810180c41012138618000c0c03a400004002d010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 414773201 1250 414771951 414771977
    0x50d0f03030f0603081b0319050717030a02030411150f1806040611010c030510050d050c1203070303060b07030e090a240311030f0d11010617060106080c040305030703 73
    0xb640415110290001c040c40203541d40c0c00c012840d41c009550851b481c400c00d60f0051040c490200403510940e241b0040d061581001304001c448070342003c4403c481c40c0340442d049400c001c030b0450255215a01e411005607603440d09180001021240c450703000d00035050036000302d001c00662401c0c1e40811480c03011441d240c000030700411076032004404116412120000b4041212076202109214030401e440081c829140c2c00c1c802142211f904803180220200c1c910014802c52a1941c1c54003410360144040301e0004254600003202c00100340c10308090380d400000d01004050709405010024081c05123414100001b0b61000383c605c5080880c4188520708890004128100c0ea07130085610051241c0c52902c407980301700080300381c42c1c000d0005039801000c1400009040c5800200c12248211040280110304415503040c0d41c0642c003a000700d03005548554001c1400040400080d4900818030700030403d95140800140201c4c10140424182c800b04000070b0010800000445000341d40c540b8203050a0541 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 414774451 1250 414773201 414773207
    0xa1e03020102090a03060209090c030f0103061a0a0f06090605160f020307090c0903111c02010806151309150b040b160b09011e0b031905120c01020c06010f050d0f03 72
    0x141507001d1307131002d21900080300784042540903004081e000d840728030540e20744280302013940c08200d60710600c1d804c01d4001800040c1c8103810100c520100748460100c03510b10340000503a400b565400900382280f101c00700f08081d40d0311500040040c0b00608299142c941c00ca4840840c13a4580710010300074103041034400045403002c001300c00c018030011074100031880c0c0d2a03100401800c21440300303032003c08140c8950082c6140980d0a44013040b5280444480084940e006403069140100413591001061900c044018038480c000c00d01c000359442d242e1070302810810b110040318400721880c2019104c0705010b120340040d80040f501520101130300107440d00741d400d0304806550442403008000d0321111040c00481c00054002c82600380b130099400b08002050f01c0503900300c9650b898110f85c1a03000c90a83c0b002c00c64501859441680604180c2785070780480048031845500004003190180e600291109103580c080c01114050225083d001075400d1911703002440e40c514407131000e464000300501100c10980 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 414775701 1250 414774451 414774457
    0x1309020108061519021605040209101808030a03050a15080303010e0912070302030d0609020a140903071e090e030316030b010c0606150230030c0903010501030b16020a1e03020102 78
    0x101c840c84541404c0200d490007502c840005044c03450045054001140f1442c0a000f900c4003600e025142c04c001c074140c071008403900c1d00c050320440074034006803038003044640d4140020074525180762000b0820742041c400c3c600884840142003050403a049000f44203480c008411213044074400480d40080742c42c1c45103014140104284500041d02000544208254010000d441403940b00902008003030b541c0c11008060384a032a001c40006903200612601000c03801024000d20100030b030868080d96203851007140328104003908200e00e440001410412a80240145980d08074a04040d40c1107080450a10180a030749021840c00d05031140b2540078243d200c2d031082c0300d040d908104140103082e070382ea200b03e5203401c20100c0303080140600282d0781c4020b140f1841003807840c20303454625891040081a01d80303c40e04007030884038850b1030412030b00d41d560313801f4052035001e140038609000050820006088240e21503040305001d44d046a1048000f24030b85952098a641400654a90391a40c91508900a00c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 414776951 1250 414775701 414775717
    0x4030503071b0b011503050126031c051801060312050c01091a07030b01090308180607080c0303070e030d021c09030204090506090111070f120309050102031513090201080615 76
    0x88686490b401d00c00310908107412501d19003a821405c0e8110a8114213445090040d01c0e4120740301c002c030701030485040105500d4a50214203580c10150454040314038000510380c09900a62540c00b03100c0700080000429041c0c3c940100200a15803569079202203100b5800c040000303004011a00d544184000e402c10741000303500541851707044200450750031000e5801e1705c410700060b06d4046812855401664000117994210886a052180081c0d202d45407400d031030451a04480305002d0a03000405c5d68001e81049941c04001d941c491078000c1008295108030300003540f1a07030000101010352074000c2510b2000c101c08500d40342200d54214001d407101070003a4402074000d854509068180700020540a0040a5580090101c0c100c4482d420080d4001d000c00580491000c0c2c607100b0010f5807a00300580440101d042c0480c0b41001921080e0898204486150350034080280407141031605024000e01d0000300f0100700010341c52038000805d0b1400003040c540c080d1190842d503140f0082e80c1c0054608007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 414778201 1250 414776951 414776987
    0x3020f04180f03020d1107030212120705100b060f0d0c03020c100906050105030a0302100c0c021002061608010b0d05090a020406060f09091a090a090b01061d03070e0403050307 77
    0x54000d10300300100c007180c04003c0d07006024034180104002d10681001c03420701c0c41c090050a08504540801c400f10000b004035000da8880c01090486001c034500242000c0c074021809409070304290383c12202501d40094066109500820450300713649039220690310400e44a0b030340000d0781c4544003400e030028415200210054810b020f02c100702401590000c070404c0d03100341c0c414400c03642d0b00c0041c036984100c58100240981c00002d079483e03040d40381d42c0c00000465100e04c0d0002e405151500444c1c1c1007148404141c005820072020065440c0d9161505d441c0d0f040300e45000303c030962406080d422140159040540020b8980307020589900013001001e01054000380100442582c4d0304010b8000c00907401100c01207a00c0203800590013020b03120302c9094040341860b241c0304959400802407041c100401c00c0c0101599210340001040c62000014007806454951120320f900b06540803d829021189142c46a440410140800c00ba0704034107035001641803e10544a403035135901500c88611004000e029 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 414779451 1250 414778201 414778241
    0x4150b040f060311030c030d1b0b0f0a05060307030c050d030e04020d020a0809030306031b180a0b040e01020c0d030b0d141b042f130905040c120c03020f04 68
    0x101e1840d5808241202e11403ca416003140940051507181d58925180030341c150400f6005258041c0a0810020600e80c41c0b03541c1d0888034603980d980440c210046d281406400462010000380003450b00c903031904040c00f100200081d9103941e0b0f40b40c00e2840d4034081c03180140300c0c1c80312107003c060281302620450000100195106c0c1c401074507030402900882000340004440307801150052030080212801900c2c0034024044490400400d454121701045000e0340081280140861440d02c6030020307030048500b4000400c0c182940c10803c030503140341d1249918164810041525502030004d08114509014240403540c419030500060a5070240d0601400c16013aa0b0080c80000d123002c145e8990030085545c8020b240305100c2c003480304807009580762448a100c91240c0d0640360284803214024403108031210fa291641c011035840d410303400c1b43e0050020705e45440c1404100300c0442d0014025040080c0304081400007601c90703010040581c400a03000714a6000d040500c0d40783c0c0c0d080b041d05c121031100b003141 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 414780701 1250 414779451 414779471
    0xd0204020d11160308070f05040b03040305040803070308010305070b0a0816050412050c1003050c030712231501080702100908040902030f10080f25050414090714010804150b04 77
    0xf5844190404800040ea100002032185010b954981d142c0740040c0d8807075007090305004200c0126440a00158117004051200080701b1a0420091075168400d64641225501d5807a1140c03070310758a5000b20074a580284104460564040703980e039407140d0100254010901c008006a800d0b200c0d0b47c05c20541c1070706005241c020f00900042c030740301012003560100e00340011140101e080703410a0b074101c03103241c004002140c09540302310b44031601c2401c0c8210000344811812081c1b0b021500103050064000911404c04c0001000b40b45991712210702801e046035103117804400207440360301341c0007148009542c1d070b942c1c0b40500c07820340c09440142007001d0301150780f81010b208a03004040c0c00c5980300304606c452070001c5014500802d00c2240c1090740d00c002c1500080300c060b10750342418855a01001d01c003840340c000545507946d0041d503000b240c101d40483c50a090081c201410714007140c12040200c1c1c40e100c01c580d44c43c3d900a103155031041e088080303a080b045c00184d40e0030141c40c04603225544036080c240607403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 414781951 1250 414780701 414780727
    0x3012c0c030c010f0e040e03130602061015030b031236010206072015220209150f0a0e01031209080d0804020105120903180118060809070906091a0f0d0204020d11 71
    0x89c00d95040740c00b110030542d51a80d02500c1c0503801e0041503540c0320010070804059000390000d44855070010700b500c000079142407c580c40c640000c0c9003695440411448040750400d00300c000c940743e80f26100500d0340d1701070510010f075840401410081c1089515a89803480031040010040785140b03072816a1040040007001214101040d5003881c551028001b030700b100d085100c8046420a40d0143c40d10005940308048100300c2010031050a0f003010444500701003954448403110050315000d403070040caa506600300492450000b071404018040801c030240004140061401c01203429850200b205a54a20040325a8040d003c0d041100e481c2500a01c81030301c4000c000f42081c11529207940d4045c20ba080d00445600c0440500c098080110210034400c480c410710301d05602a52403411604c6d02c580d6984140c01305c0782d03e5400001456514202400c4503d6011018043d0003800ca071800c0c043d500482c0003035091040c1d404000e20540e40082d4100090910380c00031084218241e0500d40c6a5030710365016 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 414783201 1250 414781951 414781987
    0x30206070806090601020d0509060412050601030b130f171c0507080a140109050403020316060204210209061318080915042303012c0c030c010f0e040e03 67
    0xa00302080500c000140c59050105505210381350582c024a440f04060b00c042c2c038680c2c060240f1a8102d1004c000204148d17044001c14150070b48240003c00c125807540c10108840702c0081c18036031401751083c040d01c2c00700b8680201121030341d030000c01952608400c140f520034075101d05814640200491a031440a410003580414803400003501c68588565821a20008840c04c1c00303c99000e14103944014044041d40b0382c401544940b10b401102d00d8a2001812403070115900c0400303c07070300e54000038207025412030180940e0740341c0c2400b0b160070380701c901e84e40c00503841c00300090406001700c40118054207903000c4c0350080d0b0107403020558032024408044c100800158008044980503085082001e501910010210303012189052051400c0d840020074014280b000861615815034035140191550041c0d50301a0640c500f407280850115640da0b488a810302d40c9202c1d5291081d000820549402d03600301460f40510b0540e45400c4070a590600700040040000443c034030494400442c1110618452a42d9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 414784451 1250 414783201 414783211
    0x1b1e0a03020d050a0f0e0312030c0c07090b0604030f0f0b072c090103150603060606050904291320031801060501091511060c0901090636030609030206 66
    0xd03104070800000c802c2c0d405105211034000003405c41c0e45c10904180c4586c4502c01d400d0700040c2941c0d02c540800c600c1c408036800c1650511300c0c076180029803a5100d2020800c030300003084407100900c0f14400c0d80d400074089000d0b42c44064200c048074200c2d40300300304010481c0d11440754002043d080783d04180100401d00090084140d82c0700b600d07450346403002c02000700300002c2030741e0003070110400c1e80c21540c1e4000080a460080c5e183c0582b1000003000046482c01440d01134240703070361125221401d02c4100400d65106c0619a4080301c0346241104200c10000748901710700c007007510710300e242c98014210301004107d40b0ba00b20001c00d13a00d810350b41844140301e0065000e0401c4007a000084006403d0300c03401c9800070712038030380800c9905104000c0c0100c80d80321041c0c03840301400c1c40400700107800503450411504443c521015800040c014401e0342c1c00c00e1084003d00b84d10b00d0115801c1c080842004154020701140d24549003a007584003004500390320040d40a5540714200740450a024900a075a498050314 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 414785701 1250 414784451 414784453
    0x40b0a06030507170906040f0819030902090c03090c0405090313080601090b1e04050c1210030314042601020405150301091409030702400c0809031b1e0a0302 69
    0x32131305004044d51111a801450060042c102079259503550341000c85e1080d07000c44880390f043c0000540c0d5000ba9200b140007019a407000b0642c00340c6481001007102000388003e460103010b00074400f030340340d0000302c0c1044aa1b05613000110381e12592100c034a5402200c07010380303200c50324420114801c840070030101d048409280c0180805c20842041142c000e101a00910401c1c10200314200540360940040c2e8000c0181e840350b5141241c1c40c1d802441a140842c0c4402014501001c10402c040c0e000d600082800c1c107418800341851b0038955058108989050b4a5400700500c16801140136000c0d8100c0c3c3c02402c004004840350703d090114040c40c0d4209220b4040d00350328000195400d10407031610700c0c0c0300d0340e0745601a40c5081d00c02e5081103038040703009503d08080f0440f0310050781c40d88a904e07940700e1a07101300c2403840700445c0141c00304000d41c1c40a407520710800803200c090100765a000001d584078004034810348203405141c3c0340d045140c080761074040307114000e070040c030301d07039200700c0403482602290090f4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 414786951 1250 414785701 414785717
    0x6041707080309010f0302070804090501150f0201061a07080d140a0e1b1c021002010f0e0c060a080702010e120a17010f0b13170705030609060702060411040b0a06030507 74
    0x7161407600c80c020b091029002c502200810032001d403081c2c2c010002648207100981c24180c0340c0e080c1c0f004560098002e11400d10320b007034031030a038650400404c4c0c0c41005c030303880240091810280880024014066200907108011a080040154100950300b400c82d030000d0420408884e80d81ca508400d5094940c0158a07240200811101e000420851002c8000400c1d24400607100424000c4085281703075842419400412490010380c0c4540001c400c0400c980d002148044100c4044401ca504042d100c401a5105180483d50ba456a03000d8035401c01031400d01101c1d41e681d040082e8007400103040903909500400300307000105200b01010b050000360b69a103104d5800705410121144841c02c2c000d04a4202d03002c0c00811038400041c000340700042a03110b0f0040d65698540e003240c4480f40b09110f0f1074140d002b0706002c0c8882d084c100400c070f520902613001442e44d820a034901075181d10025101810300b440d82c1544141c59140e98200055001001e4080305842c1d80e1200b0040003042d060390000c0018070700e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 414788201 1250 414786951 414786959
    0xa0231020c07060e13090321090b070305060a030c0f030b0708070e1003090611030a0c0815040f0608100c03060b0403051513080d09020114030708160e06041707 70
    0x9403003991003800d041401000070300d0a0a030306030303451022100701c143d00c03c10910f4103102282c2c880c05250341a80c0307e038940d60402000720710101210742840b0801100ca524104007800428814840320b60400d8540c100003401e602e411010500054150704064007002c20340034001202100721407210210ba0040b0001440c03610784002c21203d40c03006650302d0000a101001004003031610740d40400e0307801140d00300020300308041e0b61460143e82649000c1a41c1ca203002c820800c10b98040c2c0078101c0000003c2c6002e03c3c0c07074649030660505200004101c42d004a075100b8651006c2c10055001a004e010342c0c00072a08403514203829240031700141c0e06043e001a003003400001e0407201000580d0f064940c054007402e44071800c111400900c0d0030040c20000d200e000c2c00070003004038840038002c00142541d100d011401c4500c40c000036040c0106040040340d100001c2040020055011000580129690f11502c20809035013504645881c1c0d42288582d004400140000e44a10601000da00742d00d01d40c0d090315a86555 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 414789451 1250 414788201 414788299
    0xc17010f091401080a1101030237020d1215090203010311040b01020d090b0705010b060301120506060f010c12270302010e031501180e010207142a0f030a02 68
    0x4c4c8610569036014003131820001e40c81035040501c001d01890014204400381d020400c4142400b811501d030700d020103a801e40c0d00e44048070b00e26401000e84c00100707000100910010416420f40c20b40480701c079034400c00d02c6a903880407582500144041142592256160700381400319a40d5038544600c614508031100159500116901c0e0603444161156104d10b45025000061a4444901152295600c10002a803543c0f140c010307502038800f4000289071001c0e03c0c42c0c618074208002e00018031030311a4a2150350503030380c80317810040510750144800441072840c2c0d40948180c00d1865840204401132607803902501c44450301c500849000341d0310f4105a1200a0070725448000008800c0590004e4200500c0710b84641c40c0710301420340700c080d000036510703a0100c191422a0000b21085844444440b500c488182c01001048800580c48180c0b000c02d8844008401030408a43c84032402103400d03840070105a03605022071410300741c0181241610840011805444030201820107039142030b011001015944 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 414790701 1250 414789451 414789491
    0x60312032a050d020a03090c03141b0307060c060917030a0605060301030f0209070c05100c0f08061e0f040609021216050301030b040f02030f0d030617060a0c17010f09 73
    0x400b41c0355a4600059268007070060b51060f00130000307040e2142510380004011000c00401980101492144110005c0c41d00d814800c400e01407900306a454022802070b950b000c02c201c011103042e818203c00d90006460224054021007402408851010729202d10310280840154403035045e400d82040800d40360000c0010030301007804040c103844071000c1482c0041c1803681151790429405d0801c0f14012003182d031561300e03000c9100907100466484100c03281c504e43d0400381006061340c490412124900c5c2200100b080e056041c0c22010503010000006070703032500c42107040c1d0402c500240080c004031761a00c01044c00717940300c8100003800340080800104104410b1809610320f08144d5200c51540c1d10319164114201400382054a141c4a010314040c0140d0f410010f20f50450b9490b4094114856141000343c21907080c0e501c411b0b4002c1003500024510038001c41d0059100b075505100007a5407550f10000c032458480d0203031850510341c010001081424200070ba13441252800c98050190076113600c201241c0b07130 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 414791951 1250 414790701 414790781
    0xc010b0a060c0515180d050d0c0906020a0b1f0b1207050a09180f0f090201080105010816031104090e0f0c041506261501080a050c0a050304030306031203 67
    0x342107118a00400700405002582028402c0e45c0044010310198846041500c3c09050703501088001071040c951910b00d00544a8076882820305243d550301d0300c4800394903100944401085c01904100091507030420045c0e21419003104598080c41a032a8103108129a0151401403802989440081d0f00e1910035400c8a01c441c40302c2c1d84000000345807040f0104120380c031003040300d4420789905410020601501c102040261546c2c40801c0e041205d00001d0103064043e0042c9040040010810940144242c80849010224940000d844414844207a402d000d40c0d041011120b05207014035440010000c1c56070f800400324400c3d074003800d000b002040212500c0c40c40c000c2c1c0c0b01c881d40f501007000c0d9000381080440d4942902400e18140c2c070342d6240f131300b4102080f11142c4d4000b01c4400400404c0d60b01c600610b03032143c20800c0c04c1106060030042400c10307014882a4104004002001804061003900280e00542e4082007840b040c598410000c2d003c1d118003041c241003201e05070640d00210480306103c24580d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 414793201 1250 414791951 414791953
    0x618070e040515061c0b1c12020105012102012f071502100e0c0a0312030f09111002030f0d1a0d020a03060203180318040b03061005010c0f0501020c010b0a060c05 71
    0x51132154084440c800034469542003039075103003100040c83e121001410181f02039004007903d0210b8902c2c11009194400610200b1689030100500102002e10554843c8150318503001c6d068003031600c012203024481e07400395070080340000b002801c90301c805a140d1030302e00145030031303101003c6e1503038031059501780c0c4840038000580c450070405c240e81d40b0307aa0110494501550079291000a04004140d504a6a034800c036010200007102d12116a41480381e010f55070354800c0207100c0c0703400b59154400600000c08206100304118401b5943d15402001144c803803181514025441d4003c80031214001c0c1030402c2c60100b221a280b0181c0550701d45109040c0c1180c0d0700404100c009030841d15088002e4000401d02400307004401c40082d00703400c1c00c2019280388021a801c84018204220500050b102c1c41c0c90600e029500500500c1140140306035614140c0303001b031174450440849420803e820502e0980050215480003a5802d00c0c4003040d00b100d140801d090b1201c8190594036001290155010b400191403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 414794451 1250 414793201 414793207
    0xc1c1103030705130509070e03190201050d27120215040506070809030c0f0a02040b04090b0f04150f0c0809060702030a180816030c05061903050618070e04051506 71
    0x3900d00840140050050360500c40c944e9030f0304c1e1400724074928415980c4e00085009440a0310300c510b0100000103503011050510400c4c0100c55002801d9030003410150b4110a442d821107022414691190310740048a4400d404d80e040000e007045500690f100040700010b00400c2045540d103086c0701e4401d406141d02c1001820303d5995500b044460071000380801180e40410081c00d8403031001001800566030035180501a5480140304101c101c0b0911071507a40190f041c032001c3c03408115806441580305101d510144640e40c3c86144c1a80682803c9683c520301c1c600c0e0080001c040c1c50581d1004000003030545078554641c4601c981030b036503038200301da2100040c0d1081090ba61010705c5000c0302ca00d000048000b89228648603905682024070109495200007280c0300200140480350348200e00410003075481c40d00c2c01281a020502030701c02400c802082c151924046805d45e103514982c0386d00e41e1861802e1403100d041c8848014070030200d0b6130200e4895400c10b0045000b80901e111403424410004190714a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 414795701 1250 414794451 414794461
    0xf1b070e0c09010903080d021309090c0e04081e09040b0301110406030902030a020d11011407050a030f12060b030105030c19050d03110313051011070b0904020f0c1c110303 75
    0x10720307901851405040254a10f40000040c48220250610261850000da102e1080c4440395400d51603d40c1b00c000000d04068803900031990185000003924044030240600b640c450401c0300c5148a41022120800b45c0103400c90034210b4a40090045050102e03814088802c445003014217903042c83c1e211500c000d10800040203514040e07441402e0f00b500c00f5003500c140c02019000200c900840842c182c40a0304800410605513911100c402c8080d001440c1690030300ca02512110307920148440000c003408100d40300540700d40c1c0110100094400c051109210700707a29511480d103190401c1c0300d0a4082c0c031840c1c086401625102c00400c040d9502c1c1c1d100d60141d113181c02c04100d501d614040042d820310070441e00052000a09100504114401c0c1400002140c0f80500303100d4446441901c0380c08100e1180500200d6a1010950000321517142d00325584a0b601c03d00054001d1160300d5101004007400141420035070f2001c80ca21580110b01b0502d03800f005070111003a5203005685030f80200503081040028 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 414796951 1250 414795701 414795721
    0x5100e0f1201050408030901060501020a080f0f070f060603051006051509040b0603040303050906010b0f120a06080a060504170415080a1d2a01140903010e01020f1b070e 74
    0x52500034008114460702500c1d504481d0841e03605803810f6481400001c208042c0440c24050740d001400c003840144660b80d00c42d140c0031114040c102c00fa000d01c4c007000407000e2880303007101c059840702600014011061003140c50040010052440102c505009015004403e442280328003402c4a00280c440420501c1c48048003400b81d10007661141d2159850341200404e4032402d020707501c11803081e1000512400c00651141c6820016800304000310010044002c1c51110350058580c1c0400301c5209203102e440318540c6402038040d5801c01c28140c800c40d4001014010540c115900503070207052480040f401c40304940c661440359014441c13004a03c203500440c002d100340000c9a00075160328002410301c01401640c3d810480720004400d095101c8840800144100d0310703c00e1400401c0000d8201012582e00082c142900c03c111443d07002402081c1c3c00c070305440a40011581000c888000c55507030321000d080d0351460700440440e80f048113000640070b2074124001803001c242c403010748050085a071004504 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 414798201 1250 414796951 414796969
    0x804020a170609210d02091908031309090305070b040c0504050901021b030901050313080d0f0f0b01020a020102070b0706090b070f0207060203120a0b0d0b0f2d1614040609090605100e 80
    0x2490702300c04500c01024000c45885c0e5030134054444040911340e220b11410307010310300501c2600700040051402040d5400241c0140807940b18951110324000190380303c0c02c0694088215138002508503082c04204842c1190650042c1440340b60310304404020107007980c6190b5240640504a40032030010400324219010325020380070720074400d0820501e880d00c50041d0b94240c4405c01031074407642ea12210840c2130302d1091300403088200828030051500d40a541c000070740c0d40c0003501c100c600303014002996030700340081c0f900440c01c582c3d00440140070500702124010800100e9900c60001405149030200c0e00d40d1010084400441d4200c94a004e2510390310a0507005001d1508456800f1a2007044480000c150002251142c1c464201c000e10500c4c240d078151040a111450a0710048000344181109012041a40d07030015200b00300c001002c01c034040107035001c240c07002c1c04044031a0041030028015038082c1500044d41c4102c40144100c50341c900c00d200e00388c10745c0c0a11401003080020b6158090901401c2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 414799451 1250 414798201 414798217
    0x1d0103050a081e0403030c0b0a05061003050c1b0708070b070b0a0c09170601061b030c200d0b061e0303090f2803020f030c09070804020a170609210d02 66
    0x3100c0f100c000d50070004403a40c0301d40e00c2200450900e10b0098140600c52903402c3d48031b02060400c1c85030385840d40019510380902c0440400f455903500124000f00389081c2640e03454114481e04400408038013801d00d079517400d5807103103201a00c2654000300314020524180c0305503541c041d4651010303445c5c140b240800380c03040b8050403080046101c4c0004117182c0625042025445031005400c495041c0480101013000070012840b100000146480029074045921000c10f030700300b803201d041d6030410702c023801091400c03800d080d51008614000a040c40840042030f070007484103c1c0d0300707a611000300786c280d40108281903210f40e050300300f48800601401c00819010140f503005140030441c10200070354040940c5a103262000311000c040c4180114201403048820403e0300300c0080408001c040002020000001e21050030012102c0c0801c0031034480ca10040041c003100b100c001040c40320a52056510700c02255085140d2140c40d000500304046944880c520504180d00035150910004d0310001a50081e1070b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 414800701 1250 414799451 414799477
    0x61222051e0c040c080f070201060803180607060509100c0206100510030908041214030c060112050715080601030c0f050405040c051213030f020106060504140f03161d0103050a08 78
    0x2400251079a0320700c644259048141c4170206541040070301d0f001a8100140030009580c9080303028425500c002050751361440c0380540c9904031182480c0494094015150010311450414007840140c000100b2000483c0b5144101003150500148040f40c5c0c1700c41c01d80703100c4d1203040030240511160401d9800716081c5900c3e8140440c1019803550703406801e5001d0b47c44103600ea41d80c0940c580030400350480b840c4a0f039152030021340c00c058000c104161541c3d41071240c0a00c500c88503000c4010840d050104a004040c000c01d1480c81d040c45041c0a080c60604840c414000380c900a211900c00d80100d521134100c85250751054101420902440020105110f000060100a005807510700034201403280c4112070321032080c1c0d8101c585140141c010f81d0160f8101c1c040d64103084083c840c0f075a005098408039003d4000f0010303000c400601044c0841690300b5101d07018011102295541849500031000702d48081022035082680d1204805003c802804020b209801100b00305c4007040c00c11024001e4000014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 414801951 1250 414800701 414800713
    0x1c02070203070305070519030803131b060302091512061002070e04050f06091219121d0d09080309100e0a08060709090603051515061222051e 62
    0x340010385450180d6008407010350056906008900f880d120002801400d07103030810701d01341181da13888003a00000341411003110b91101c40c40d05114003980041882602107000c420310640782c0300c00a0180d806895981c2c06a940205601080201c070811551410100d080440d82525402c0c00c0080b16910041844114483d503034000c11801142c406080c0503078404d40007804c1103101d01e900d80341090401491154503801c030101c40550b00092038210b0b16290060088100206d001610541d16011070800e51000c907441c00f103644120001030380060548440e88401c031407030403803160380c220f49404040c000c40c01c0ba600240706608150502003116107801138103040c40509210b4140220b0034102003540f2100990380300070280070009812815140103001a0142031100a0950301c8569803200a50424541158080d00040034940e802083c102038001c000c0419544070384040c4034a4070303c0000da40400010701000f0b078140c540b8442141d400c4445520001400740140c00355002c0c507031000c0b440b034080400c0c0915 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 414803201 1250 414801951 414801953
    0x2031207050c010c0206010504050603031204080903031c020d06091a150403021210051012030c0516090606030b061e0c1903030e06070906081605040f091b141c0207 72
    0xe0060b040300c4d00055005000f150714250400054820150820340260800c004080c1c0700450b400003158403540081d000c035607400301400420305d184141d07040e60340c10003d40c09480c0002c80d042d4000307080c000d2001406220b11612890f001c8211051010300094804e18030024414506026a01442070310b18030013070b00c0c14540d40790049525000ca800c54846e150300900300300d80c0c0741c1e08184070b0319800480a80e40c00905604010100114117074884000d4140b08241071071000b0040c040162000c0038840a0504c541030783e6030000d050140010b130044d880440d041c8040c52109051101c1910a03540180d0700c4a4010580c4c03003004030303480d44802c1000f841e6015982c1c404454034000c000e040c0c26980309540024004403001d08050900802406050402010580400400f41d01c404140e0b0400c00322541182a002603d0707056649200d240e02007020015440400030f5198100e0b0300c849600301561524400c4026109000c54080c80c8651609070340d50700500be810514104e420880b0040880d00d64010b10301092 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 414804451 1250 414803201 414803203
    0x2010e01060308040303080c13060e06070606180e120304020d050a12050d1107051221180c010207230a1e06030615020c1e06030408090a0b0a02031207050c 68
    0x1c41d0000da400003800142001050b0f40626002d901c100d4600a440c00d2495004158240c0486481150104042c50550000f0303030351468229a00c03aa8015010002d456540311210160020549124510751030444e002c0d02002001c0b03540986101003006541c9142e48903402c0201d000301c03031107040d1114404c8850030400503a208030041e519442ea5198107840f801055400d030f0079113000c41c03034140030490140318150000710300240c50000c4408600c244c0342c40704e940800e505049860304010714051407030882071090070580008150050600c0d0000d03100c0c81c80294005981c3c1d0701403403243d84580202c09019119211203003021800c1c50300000c00741000c05607901c42c004441101e549141d4032000c0c0e8603a007000025098800c080040c00554210250f20030340490194a170707030b401303c21036000baa01d24014030b25503003120004141c54103008000d2600da0070f0134100448160004507140340112130040000c00c00280302000d68039a6403040d8025032410350314450401c8010409490481402400c1c082070414401c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 414805701 1250 414804451 414804461
    0x40c1e1404080c2b02040f0b28060c0b19110301080c01090801050c07110a051c0303060f270b130209040617030901051837140f0102010e01 61
    0x14421000b489481c000604205007003141d41c1c40018404082a0552482074000607140c1c4c42c182c04640004a400c0c048100b14003a0518030059580945030126194a0a00c0201c01910703200e548100450700703d4444000340e0f600d030202000542050a01e00010300702c0810418820000da042030320101e03140d103185601048941003a005280250007040e103d1000d541c4c45000c42009001b040024080b0f41000250640c65108080c4080c05151403074000c07982c640c44000d02280144009001d200b12101800c950913545003c1e1001100064101880042c0784000c000b10382d42518032180220486254030504d040400081111b03041c095030f203c8240c03580c1e543d521584c0f001440c00c0e0140c00759464180ca810003045542981100946030005c0c081260405800401e64034104c6081c00d11a550b0080364810400c45210020881d5000301e03600d0744085a01c141c05602030420911120b0502c4905201800c040880814020080b039200c0004014250b4500342251481158042c000080c0c022000e450300b41c2521 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 414806951 1250 414805701 414805709
    0x40f05070e15011d100c0c080d050403050f030712050702040e0a051029040c09120f060c02010911040c090314030307020d110c090a1404050a11040c1e1404 68
    0x6855219800b000d5821115803110450008045481101d45800068404200c50310701010416401446010829140031150103407003284115106120102401403035644540000c031201d008440c1c01505d400000400d0351002c1d64841928110084034400c11540c64026a405983c000d0701c03454900807510341440300c07000c0e40c0e0044024007024022220007400b40c1e001c41903070f042e03103e83c00010f80c01c03107c070039034100d480460040b900840c5004c103841040310380315000d40103001c604201d044103104100c510402d4054651185038248000304030901c05900f02c0e0500074014111506445580401d483d00ba84a8002c03d0500e0405542440c0c694440480d501300003c5024003950001045c00701e400d0f010060708419004030302e040014143e40c3c50345683c41d80000181e17140506d102074089100441940c100703481d06003c40d000c0b584030380707440d003042580c903c0034002c142d4601d601814010303441e003014003940b030542c034072501d6024800201c2c14040740c03403d050301c88c41410042a10801650b008100300140020 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 414808201 1250 414806951 414806971
    0xf031f05030c031c02010b1302090a090b010806040b1203210c1c051909030518190e040f0203010c0903050d020601060906051803060106020a140d08040f05070e 70
    0x9400211150050124680040348268490301814025507000a00e9104003000f1465400200c405810103034050810308946940c40600840906c9416185901800c034800003207655480455980000d03004403050700000f1030008401200003181c606082d084200500300141210100b414180b02071030039500103801d500310f8000150314202c000c0c2c40c1660410b81000c0b0652280e0b20b4681c240f203982d41c0f02410070340302c40751071516840069540200c0d00c10711035140000c044144511030443c600105183d2140c003107281c42c00d03213011714481b660810b400e040101d0a40107400c0444581050340c4084c662000601c2103a10500300308603040107072030a00844c001000262941c41125003189012410107100e00031440c00c640c414401040010b6001c80810210b4140b402c00c1130b91103485540c1c8011480d08007003071a0301480b032000002001a40040d00d95000ba000d021203020385c5642c0442030340c6400440c81103000203500400400d0206001e00d400080d0300c1d01c41c7c0d08a983c080e41d02c3d45000c084c0b5400b01d4522102d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 414809451 1250 414808201 414808231
    0x403020306090f061f0e010f15020606031e030714160902070b070807020c030f100c02030c0c0910090509011b0e220608100f0c09030302030405040906020f03 69
    0x45090400981c1d8111401d04043c01009004007030095803198010000c0e07a69601302d003c040308128000600701e000d8503202c141d0b05070310b68681000c0c0110340c805115800000340c0300c1e006013440c58400328841e0300406004014013503007d011950354114140c0f070b0180407418041040704600040c29111150681c1364640d0280100c0000c0909049908401e40d108006140c01080417500003040c00c00320365071042d13081c2014a05916851412407900c401c0a0303110342c1600c01d0200c5c103100b100c0c0c0015684c074a076600000c140204114020b040341c6a01412180208650106400c0081c40c907010079903d512a070703551804c0140f940d4802c07801050b682c05850880340c9035550061007040c0d040060030589050340c2d80c28888138102d00d4001081e40ca0084078801c501d65082000c03c14080c8816800c000000c1c0384d42c50480c0c03407540550b0852401801098405488c03039240110052500d801107540c4d0003100d4040d0061400c06181c01c040c4030142c403103d002140c41c541c1c00c1000c05040d20700340c005140032340042500105 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 414810701 1250 414809451 414809453
    0x90a0303150f0305010c081e0105060a170a090b16050f0a110a1406010501091d0403261509010f060305040501090c060203070219180e0a0204110a031104120206210c0403 74
    0x194405448401c01c4003420700002c8c4202e190110050450748103076022175850032481d00c21600d0402500c01504466442030603c004201a80c101560941c01a041200d243d00c601542d82c0b082c2d1291000007001c100c1c00c0c8440c40200721828058940c0303d0f05404c000f441e04420f501d80d6401e0000324042183e8036040d040f20512044c01c00c100d0316000d010300382031000d851401c3c402c43c44e103c0d1170007a80329240c080d000e0380010201445008042c582c00c0c00212101100141100c0356604d007003040741c1e1a041c42e114000e880e54070b031400600303041c121907521b0301c0801030505255084005e031400410682e041d640b942440c0740060750000300040102000d901640e250030032441041b0100c80400340c180f4030044400414003502490040310881d1203503d16000601c09919080b82d4140100c010020707500c0340c5030901c24482c0c0c1244800602209546a07810040e81d200d0145110150180d40117000705022908060b50050070042c0040038241e10030613410805054010701c00400080446003180d00c4100490200 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 414811951 1250 414810701 414810707
    0x6010602100c050d150f080a17030f180c03120301180603050c01030b040608030406110d020a0f030c14100b04060f05092a030903120f090a0303150f0305010c 69
    0x604001404020710030b0301e030218002440b90189444658825590740c2130701101d14001c02810f00102139180c40030100700e41e209541c0b078032507440d0f820a69641c020003020803100070080c0e040341e00c030f10030b00160604c0b291100704200c0301d00020b51710021070714401d941c080001507508001001c001d540302c0304400d6407503040c42440b40070340c1d400810501070b076420000c5c180300064020031508176180003071030000760341d00d10600000c01602c81540b150800b40030014000c10440c0d80303c0030808201c0020320813910076203c0e040b8200c0c1d071038440000140007000305c2092400000d01c41c0030240c603528000e0071500c8071440c0d020319982c200001103007400c1046a5178498640c1a003064001e40d0002d2080784051458a803828020900d0440c0091215070811815440da5184c22a0f11005113414101f01581d80d40703074540100415601d0b40f00000701e227803440c40c00703000450940390802180d1241c0365400c00350803e000355680039006028180760030080ba480c0304102162480c001d0801b400150700410001c965000804005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 414813201 1250 414811951 414811963
    0xf1005150d0b15030102090604030c053309060c03030a15080714100302070b01080a020414150d0203030d0e070911030105090c09030703020603010e040c050f0d0f02180906010602 78
    0x1060088404044140202d1000d1202d039900003681c810484a0465600c0024024821070540941c0b0100115010040c81614030840b801e40300700381e0707003844c42c8005d2048411020080354031010b010341085801081c1000004098603031400d002e81524103104c049040c3c0d41c2190002c0314055400c4c0c3d87c1d40030395210458951076000042000c07001810446040c4100031000711030200100c1d000321110202c40584a200703038101c13a60f003078000d0010711042d615180d045480d0107040409a20850070094185000c0c69202c501074010750f11500c4004464030f50009102c12808021016640750000b070003541403107106400307403101007150304015201081c00c1010000440750020b4201000d000705000620580c1c503041d4503542c014400c0c1c58000e0b03c0e80d003200300092a09006410094000c44040000603c912098100c1030042e03118035202c040721521a014041407903652008283d0045901c0c00c20360100e2181180e813400c2e5800500004404060120a89400e52090300c1d016499808040100911641441a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 414814451 1250 414813201 414813241
    0x203011701200d05061f020d0201060801021801030c0e09010f17010204120206031008070626042d0501060e04022806050a051314030c01020a0f060207050f1005 70
    0x80b000110102085080a9000300400c0d003004a90300c01c08074449076034200380785c03d040030107a14240b0b842c0e00c2000000d4a401c11622044003543c20840041603110040c02a0b900c0c0c0c5800e070b0814000b900f49640110040c1031013002001c140181e04030b405c00c0d1034079075031503450191004076200d079000340c5810148881108814541c41c2c050348180401d005d44800c122400344e01c140c044601e01d40340c1d200c200c10b00d400300802e03611100301c0303115501002840c1900f10800f05485d0030821054050f5000c4190401d10460302100c0c000c005c06100b800c2c1e09a0981d2a0350103c0c16109c10b8140740d000010642e0702c0600b1500e15030032200080c001702c000c000843c07520907120099804041700c2c2400151000c6e04065002c880350103203c080c004042098050300e882001600c5084046440c1159010358a501e480c0c500d003212080c041c028065405042159400050303171a0700030f6406041e01c0c041c4449600d50f08000d412444086500d0b00900c011203004000401c0a4414900c07002c500060030304109458058810075050 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 414815701 1250 414814451 414814481
    0x50a030810060e090103080a050c0708061803070308010e070201020706090b0a0e0d020d050f0903011401050103150602060a1d070941060f060a02010609150f09020a030b040203011701 80
    0x140082c0513101d034031100741100d5214000e185c49000010f401d50700350140c7c401100040c4550000081c00903000121507000f0303000322456248e0403800110725520b034031407441c0c0a000f007440c660041000a61841c03000364041400e200040c14482142d403244280d901d200003d8802103160010f1001e070f00814814031726183c8110b00181103110745035001944516a0449000a204011540310f10b001211400c441c00150028003c100d103c41c3c001c4c581840d00c00138007075140000e00d4040384000c43d2464180300000c2d40c81580040145076502c1010b0005046c2543c6103510320418112045c084500401a03036025285916010071030034241d505080750309020b01ca800d0f10882100b070240e81c4103200d08803260029154245001955510440499418800c400784541c010000080007684590f06500c45003d03140115021700895100c0406081d200780680509c0802c0326489100704050541c80d4010107a40c280b40c240442d10305440380010382282c1003613000c11140720106c2c0c071303000844800f8031412164841c1c84c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 414816951 1250 414815701 414815717
    0x180609090f0a03080601090f091b081b090a1508010317040608040b0a090b010803071a07050f0307022e0f05010f090c1101020708190e0d11010c050a03081006 69
    0x60541c03035030b0780626040502404118004280c890740300c0c9031104098034050880032203540d580c5103c00c0081242a242c000841c1c411004a240648280c103014000c64159194080400e01420598040c3c4e010f100c1d11607100c130401d080040e44142100904e40d0000c81030325001e80d250300d181410410350a03c1420b04060700002c000070300040c1c0c2c011100c990890b40101d03248042e50740c0c0c00080030050000b90400b420700d0150400015111800000a0901501c64050030010a04252803841c0c000720640d6680b001c2602480381c0b80d00b80c401c0380c02442d4000030902c1140d180c10715103544c1d9a4a200150f41c8507150030041c400c0c4081e101503d00030900d80b00d000c2c0300100084d614203449098800c405000d888241511854404201d0380710b002c82c80c26260341017008543c2d9030441c1c5002002c0e64808540c0700c1c03030315030000d0311403181d9402600080a903a40191400e00c0c02c0312075541d600e55103080d400083c1c0c148184400d2840102d003041103035038010340c4243c507000c070075007000d014102480340d8903842142041056 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 414818201 1250 414816951 414816973
    0xf0d17010e0f0a1d120a0e03030306030714031504030c1a090a020f130f050a05070c050d0c170a0207060219020f0d2d06061a09010807020c18060909 65
    0x4078400c1c3e40200c032030b000000c201101071659059803001030440c0800784550a0100502d80030788008220001c2d0a0b200d0740350b0b4151180916450307010441c1c030143d054002442c02c1002d50502040007040346801010707541e0000258802000c1707203005503002d60005040030350760020001030f284003582d000e2000d20400924075040084d00ea0344d400c0440d0003030007002c0389101c091964035502c40303005644000c803400b03101d005403070941d800040404941d14400c5d1400e03c0049001903006008c645101c640120150500005200381500e00603240c080031180302c5618511401540c9113000540740e0303134507141c3c06030910914003c0c3c000e1401400c2480c80c040b05008091600059480d0b01c4030301144001581c074004032514905120001700d140c0030101701e087d002d1030884440456940002c00c2c0d80c41c0300380010040951a04480c6244465810310024500070030860441558001c038050f03507102a0500c12035100c0480b100104800c81d0703880f034402c06179081c40f0040c4417981c648051900c1d80001c05c100108210282 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 414819451 1250 414818201 414818221
    0xa020c070b0405011404030f02010c0c0807090b1e0312070804051302070201030b0901051c110d080a09062c0f030102130317070203030301061d0402040b040602060703060e07110f0d17010e 82
    0xe923100a050107031340c1352050100f0104991840c01444000c0c191a041c680d41c60b0080007914245101d1485060b10040c45080d60b081d40b078081c1c4000c00041c000300300c845491440d500196108201c2035a81040c01d004c006400e60741c02030258952801000c0140c1c0b103240c01c3c40050300741c4410003500c9118480450050146860f0700300703610000c48146c1e80c0b10034490710341c0c14403844952200319555003005484c5403038414441c8500c01840098010741e6503040003542c860003100d0b0b03402c143c488050700e081c182008100c1035512035846014150000e050080c003000d82400242241c2c0110209a81c2081c03401c020001e00c4840c0c51000d00d030380400d140341441e2400540c002a02c85c0700501845090044c0c049076a040081c07104201c030080c00020301300719031752515550280e0141c0c0140c401c2030018460301c030005c0d48840c46402600d0856034050048001030b2102041914214a10581c04031300f40705002c0006004201084080079500182c0c44e03945c0802100040525803110581007940700150010511001c040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 414820701 1250 414819451 414819473
    0x806220507120e060628080f060403080f220201110706031d150c070c03150917190806030a08070803040b16090306150806090724170a020c070b040501140403 69
    0x3840003496074010041050003022a07150850329448c42580e40b9140b00883c0003480a0043d8042e0b16562055030b190f000ca411580d000316200840d00f541070b03500442e00340448208101042c8141460090480c1002c5d0f85031400c41981d01c644000b94031111100c4101d0b0f00c21084e2110803042002070000d5034102e00106d2002c05000e407007030a0764040011964244074040c024a405107500c6030400101403503201054029140100c3e090b101c40301c92840b004002e980d02422120a0f010a0100700e08140d4403000c144c51444000700390300c0c0c160103104c524200180705140208540c52040507056141e04142c2000984000000c1c103002e103c403007001c01601030369003196a21045039031003800891850148454201ca9510a81c8140090720403201880b000c40000b1444809854024881025801021284034055950440004080381410a61550140442c14803607400a100e1401600c0c000080c6241031070088141c0c40032120302000701c0d040c4115070b406091083e01741e540c00c400a08140c00c548900d28400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 414821951 1250 414820701 414820729
    0x1e020f07020d020a080a030e10030b310f0609050603070b1c2903060f06100e061909060906091409040302010b09150108090a030806220507120e0606 65
    0x140c042c2100a00310344e40c031204003018003001820390381443c8285c41d0103080800d0400d0ba19104107107400300c51400510034411000c400e00003c119a583c2000c1c14070300e4503603c000d10350100601011401d0f80030f000c1c46074001c240c154400640b0003c1d41a1030302007900708030b4201902d02c40c440c2c0c020800c10042035282d10161100006256503030703000d1940b0003101000502000c1d10007030340620000300250707a074441e008660364030311015000d9409541d503400c2e5640301d07044120380c1070358065290383d07861403003900c41c400b000c0740150007420320361620714403504400d180c8500300d1082313001582d101014001c03180e01501800c0107040600b4007019041c10884100350b14406034110500580d003800000d02414400d4010b8011a02c000d04a40880e0405d03220510003110807418040c0400c0c0e02001050702180005401d0004a402d80d0340c1a4a0303172248420041600480003100e0441851110092801e60071481503d0060406496444c02c14015000000a84804031031114081e00243c0401c2580c4c1c503140202c3d0360b40c03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 414823201 1250 414821951 414821959
    0x41a09090106052203111309080a0c03030608101d010c05041202040b090f0901060602030702060405010305090703051b12011e020f07050105010803070b060306040f0201301e020f0702 80
    0x362807029035040c3c62441c0e84c5055144450314140001408240b101d407091740c02050b21440254004101d880d002d60b004018000c040e210100801a1100e01c18189050218428900440c211380c0c1e034080a40307080b805c00701c00c0c4007407541c940d6000c1a80c04a0b581881141c0c0700000240b080c1d9403540c50150a6004a1040b001c0d040301e07040003101150344075446120b240c5002001d0000030304200290019070001141d00700c00940c07903c0c80c0400d046000006848145500501492a01c0c0c113200044002c0c140240803888a40314131540070002031010f2101d05840b0001d29000415444640c0401c4051600c800188040c0c3c0d141c01082100c5030000d0071444071114081c0c0b40960b1313410400440340e090348128a400713010365107014004500c114001c0010800c06004045000598503414101921307208282e80003408104015195001540aa402070110f400c444c840360401141c004484401101512844061580e0320852124580715400140410b01d040400840c1005c0ba11030f03000580d407103801d50291113 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 414824451 1250 414823201 414823207
    0x61b03030f05042a18020d0603080d05070207050631050301150305060f0108100e0a06020304031707020d02150a0e070303020d0e030114060603130c0b041a0909010605 73
    0x141400307600450a61100e8480810007031a05051101c400902451400f40e15581d10004000601410186500341d0704a021400112000b40b42c01200a500640c8262a0140c6445000001c10352440c00b90440e11444440860145003400740241000169006144144070034071109400c11482c40c0c0040626005140c00b14030300900c03040000d0940099480143d1560074030001c040440052220401100d116034100e8590b41c0b220300e4006e0010f5024090300b00b40d0750140300c11090074842900038a411078000c000381d64a20629481749007d0782c1c8110b9003074010034902134507502c019038008180f940c08100c40c4040e000302044140000d407548000c410704545050009e000c6070390710180f07a004014207074001044802840e900c0c50007944500100d0740c0c2001050100040030b2007420103002c1d00c034000c00f142c40e000100760307114000c0049680014100180103c1e942c041d40c000203107242900e0000c2d01c0040c00c1c05448505d0040700720180000c0c1407410910410621403074a468852401d840c0c10344440e400c045403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 414825701 1250 414824451 414824453
    0xc050307031802031617010603050a171608030613050610030b220b0901170a03031a0a230111060c1605060112020a060e010e04110c060a05090c0307061b 67
    0xc55016003402941c54028000105c10500c40e403041070301201e80400d500585030401d01503841c2224402d11028065030400b1024100051200c010840080310143c030140c1018001020040108c80b000b10440b9140400000d011503403400046500d05400d2685041c44585891408100340d040307513941c60418980c4504000c200b564410240e148a040003070f2440c0700c400d00751014800504404803556001d0048200089518000300c090680501c8144004001c01049a94110300901c60811114215030100c54500356030b0b030790205804010401d5000ca1b502c2911500303c00b094034240e0944d06418001c0300d100c640223002000c94441d9001580c043c00c05d0f21050607401c041c08000c20028000c1031805400c001107003a80c107480b12001c46500075254103002a84445083e0380030080c0c684c0c0a80030510118029049103495007220303d41d1200e2180041c01d1000281c0e0342ca2030414207885140c0295181c030b04000128001308051900031504500a250503407a058001e86000b000080c06491080c00c1070001c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 414826951 1250 414825701 414825731
    0x103020d1e05130c060807110f010c02100b0306010b07020301090812150a03081603120f1a0303030103021c051c0c020102060106020309060d0e0703061e05010503010c05030703 77
    0xc0c410a262103000c1c0007040c448007582660008680585507520b1801000c19459440c400c03c1d44102076001d14550942400c00c00b00b0740342e00500600c0002044001420030048c2c0d2010322400080c40c4841001003035640d000e420107814007524a4449061514000004006980000b2000d04484880c035902c3d694900380c3c00824050b0281380009030542e00c0000b0440084c4400c1c1c02200c0c400c00c3e17007003801c10b018548079041048000c920311016051490034484030684940c044807508501d07101c0e0403c0381d040e000002c4110305454201c0350005005070303601e0043e16142031071802c5031500501103010703624560440c0c1c0050541c0300d43c10903440020b03800c941c5407010040c080100140c60000c0b0b0790710020b07c210b546030060409401540c100d006001d9800005242c500020603a04100c600800c480c0c00c0945240007400200760710b64841002e8840c000c000404140b0350700c2541c2d120300c26403520761004001c0c0e12604c3d00369507061b80114000d03850304030340c0007500ea4800c0070b40b904071295180224074012111441 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 414828201 1250 414826951 414826957
    0x60610090302060919030c080f1c031d0111040e15010503010b03130519030e0901030b2206060b04050114040f05010305040807122109050607030c0212041d0a180809010302 75
    0x45c81e405665400044184a030700f1400d581100d1b20f40044071602842e540f11182c940d840c180c41d0495079000c1d000d1804506000b07801100c0854490480e0504001280007001c0c2900d07040d0044030203241000400307100044414180507485184c06c1c020703403c0c1c00401c0000a01c0c9200c140324480c04c050b404404540c00e801c040e00f00404094200c022280030b9000e5030140c458244950100714089100c8058103e6541084a0303028100c0390030080f10303201a600c4001c00d004038071a904500b100440007920b00000039920b031003260040d16403180040d848a0078600050312055454200c552161424001040041810130428050343c4081c80c01045941741d41c85c02804502403100c00401050340000803071442039102150310901c0d00203018428101049003103035001c9480c04103000d0495009080002d013000d0080c2c100041c5110644100d500ca0964044d1104498006400039919036040c8801c041800c410050166000480080c0400081d88180c4011209042c5030b040103000f50004210324403140e001f5415 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 414829451 1250 414828201 414828229
    0x150f031c030e19050705011b21020c03150f0906190b01031116020405180303010b03100e010303120507050c10110405060412050d020f0a03030f0b130507020606100903020609 76
    0x48181c3e038030a880c29030b40f078001ca8001c8500103048429022a8039800326070840803a500600f0b48001007003401d006070200c0b4045911801540300e9030a5145840d281046100703542e01242400304042c0c00c140443e07a0100c14064007040c0c05920010503c000701d5001d800d001e0340441000c100240e242d00c94001a000740c81038400080410f01d0101301c3d554810510411000c10301e02c201c40410140c7d64180290100c000750040852940c0d20a00045c024a0003400045801c2140d00200018195803003ea0000009c401d0308118001440568a13200c484c006000d6603400505604101e400c001401490a980382c02b502d0741010101e803245152040c00320000201c6024003000f9046070764594031140d03882c20210200c0030490309442175050764480315101107a001d16a5000f030001d04148661603e04070050940d0800b001e001c10b03624014250700b5607600070090140b1b50521000310b0b1601d031142c1c000e8200100200100e015103440c0c1000490300364460184400c3d40d6044030000e4440389548041045050340c0d0ba4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 414830701 1250 414829451 414829483
    0x705250f0303080916120b06190305030408010f0603200a08010f15080604020904081b03070308160e030c0409150203010326040605030109091109150f031c030e 70
    0x100100030305030301c10f106520900e07403d0201c42d1103050340006440009018400e805211590710390010000c2c3c03002c2c900a0b0000c000030502c04540e902502c4408000c141503000700c0f1503900024081200b00402e010714041100c0c40701c2c0c204440d501e107441c6c036009020f0340901c0007004520b080041c1c103107658802c0070802406903a8000c1000c4031070300b03440c00700070800c44440c41103500c40c0c82d0340011058000900544947d902030500c1d00720391107684d1800269000300c950608000141074500c541c450040000d0499a40a0f60b41c03500a03081040c03443c04e00d94240c0400c0020072113a80000700541e100040c2480344c190303054400040001c56818440048806505180341150000000005000102d0b501c0803040f01c184c44903498905a60302c00c1805440b461141d070340440d00600c0104200d00b05644400d0b0310318003450ba04095551890300064480000301c4106028003071412614550b41001d0003842a0000150010000781c1e00e606900c0550309100d5024404058503400c01840c5050705000504840079285 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 414831951 1250 414830701 414830729
    0x50109060f0b0a1a0405090402060c0307030801051c050a120e04060e0601020f19020402090a080a0c0e090d0503152206034101151e0605070525 63
    0xa16240007078042c0708a81c0b403007108005000300b004191000040402c510f28080240341919010501c0700c580c50042050342e0024081c065440e941d1010b0000f4000584a076440041c1c0e5814101005100101c001c051811404800340c0b100c001100081c054041d9900312050803e0000300707003c101c0b510201103072015002820860001400444401d0241c0103640036000e0b6181030300c901441c241c0d210803181000084a07090a407010250034540c0c0142030700340e80500f0000200791940403040ca01a07403040215810408040108540c03070311005032a0308a0501000350030450f50b905801000f43c04003405102d000700e000104055030b5902c82003580400d0312240180d4650f00d4807001c01000070034540c0310070b80796104040c5510b071841c100b0b0743e00c00d01c411040048000202081030704e400e013100c0410012002a66076810026018180c0307109d040b0080107034401b2a81c002030324403041c014038441035002d042809406d00c410000180d02059014a0030340e152144512029140500c4d180509180d02c1000101603039 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 414833201 1250 414831951 414831971
    0xb090405042f090601020607200109060608061f08070303120f05010b1801020a02010f0320180f0a1d041109040606030302011506020d110c0a0608040c06050f0d0905010906 75
    0x707014442d50040710002c072035584040059032104000c81e5548002a0300c00c0c0d420108221a0220703070b03102c6000340f0000034450403584d9414100c030155004107085a01940801000c1c03007110b9801007007040801c034010080352404444950b250900e0100030300340440d55404420031281684130030b450b541c42c25014091965980c25818082d4403420801070b45110504114201e5400042c03003c0c81c259041e0368400b5006140c8108400038a52102e180d00e6070440082405240440c01018103e014600c2c03060b0b02c0c150114200700030006600c0c5003407901aa11700b841c200800c20309090312042901c401040140103903151314000c542175511812441d03121202405120a00241d42c0c011401d0f00d00c030780c0003002100000d080c400300c4c800c03d80c4540300c0180d1020041040075441001c1001c005c9001c0000c495581d20064001a00300700c5079008031000524413010801030242110b000002030420703080841c90301105981280e503038466400402c8045d41c540810604210b000d5200c00071103134000d00204942204 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 414834451 1250 414833201 414833273
    0x50d140a060501080108010605010906050a0516120207210201030905070e0a050609012102011d0901090e12031e46020f0d090f080703030b03160b09040504 68
    0x540030b180d0003d02c8043c0080342941c0148150415504140c454031281340c50300c1011031b8261f200c0301c0c900341040001d0281c141500e0401ca42c10400c14401c010207025601402c5000f441d20704262301142c1120007042d400320503000014507240000d074080c6400b0401a50604180e460003040c1c0c3d000902c1080c2410400c9040c00340750344140d000c0c9070111100074190760307a0703040c0f008061006400d080485052000c400015030150034011509a0301d01d014000040e0f03410005000520268054007240b40c0310300f080c84a1541c03e00450164a984000c0b860440c14801a0582c02210010b4030540481c0c4600220340c002012510008000e401440703010200c0282420ba0003000042070708031005110401044280640a07009031000c07403090000b510300381480c0c5d20701c640241100d01d00680d07050991107219008105c0c140024803050f4000d407030104210701740c042450f241c100d41c0c04203810000d500017024800700d03000f64112150480c0c107c0d008102c035101d6003800000d90401008403010703401070740c40081441c16 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 414835701 1250 414834451 414834461
    0xc0d080709090902061c0f110c10060f0b0f0f1602040507050430080a020d020609030f0d200408010c140c0604022830050d050d140a 58
    0x280369500e24400d541c842c0c0c040c2c00e60307660400003507110505108002094403400e0701e0796510007090201103901c0b1204142501100c1000c0c120080c2c14100240e02141100c040086260b40645108204825450214803200581480c080e5803c0107000141210403d0b610340181d0f054039600b0000d10343d07244d12465604610486040080303009034201000900e002d0301800a1354225443e0410507000350350078240021082400b1090344800300a21204600800d140202515040c031581d00103000d04002690060301e0710200034018805d43e03004000301c81d040d94250742995a01a00e011020481c803c01d14402c103002c0030018900034542c100810005005041500040d0400c0b44644a0355055007607a0300d00344241c0b04100394001c0b130781d01c02008540107090003052506011045600343c10b014100340380c041e42d406000e90004882c400c4007405410464525014601c84000a84e90a0f480800b0b80d80d5494a5103602ea0603841400400309070207480700c01a41201504e4100318200c5132161900d20388a0740100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 414836951 1250 414835701 414835711
    0x2041812020d0e1002070b03010b2107020c04050703140f010603110c0a020d150222050f240f0304050601080d140304021905040207050d120c2001020c0d08 68
    0x3038150091034241c008516115480610758403000350000c0b000c1480301c5880001d141e2403c40c0700c0d450b07000907102da04201440c083e00f8a1314010313a40c0e1325a240404181c0c40205a941c010301c42900c103025050f900000c1c001540c2a05540100e1507035a022010740003842009500207026240d0805c004200b09030001390740c10b8a109480400c4018005c0b480c1c8030032402680000d02190b42301161040252500103001e540341d030311400303900407500040c0c02e00f2000c2c1d800c42c0000010561005110f07800c402140c82050001c2d10040e52010305290003403000548207074103111520512605091014070203180401241d1802e021011810b5070fa0415151050b0f41e444244500615802000c10b9a084a0700c114a08007202140381e600a045031515000c2100002140d01150081c2c0840c02e00040c0b161118006040703d07600420282c9010010808041c0590780310421742caa00c5c2c0d1609004201054200400c944a1040c0c3ca00c0b2103030760b02e2441c100714028454103010f800588100a13002e414594400c900038868 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 414838201 1250 414836951 414836963
    0x3100506010224010e0406020421020f040209010e121903091502060105100e04020910080f06040605030307030302070602090603010f1a03160c0501110c0c09130201050f07060603020418 81
    0x30101e440d0880340c03034500c60503103000e02502030042113204013021290360807600554005152580e00d406240041d104ac514154203c0801708204080d03141c10600140b68a00c25107041d80b401d00c1a4000a209003980c1400c0c40c030500c141a40900105002c1050b03c141000030b640030300500c800f03414044c1a0100510401c40541d003a40e843d030300b4a51000c11064120b0314080d080d0b014145036244192224411040400d4105500b802852040d0f03494140240580f210358440351000e08045014515810700200a2401541001c00400c45e40e1800011101c10135014680140c89100707920346000648501300f5560350148004c4000302c1d0011640000b4011683c54500c1054a480c0c0c005401d503441c04200d41031140040550080341c082c9006100449020b80b01d040002040900680a114250400c100141441e0310485003100e503420010b0616070000448010b01e000b0b9001d940c0020014420408004aa1040400d4540c01c20065400140245034001c0061107506161002d044248400860540e11 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 414839451 1250 414838201 414838213
    0x191e0222060906270e060f07020f0a0210050a0513031b0e36060408040906080c13020a0c060c0503041716020f0613080a030306061106071b02031005060102 68
    0x2100d01d02d4403079103040f5141c00410b48180c0313290070316500740c0390024655040c1c00c0f600c074103d0461206007071100c02d01c07542c51855400c0d00d60520140c02450402445c061f40c0040e0300c0180d8a002690302c0303141040050190340303440c076a5800400c108861500941e83d80c481044003107000442081181d581c0c40d0b0181042e43c00c490707001650b0f240340840c0c1d01016244c8100c420700b00754085001c0104c02c40f0401580c00d0800c160005074900407407a614258040740c2c291038034000402c041c000801d0a0081100402010004202e611411000140310f030340c8403116019100d43c00203c070424140280c0ba00000c054115400700074000ca02c0714003502031340c0102d80c2100c2c140d0500500c1104040324200307598618240c44980120700150794240050003800d0034400b0361110341480000d84c1075081e210741001038804030014028028180c540541a80c034960040300a01142000042c00640b000610983c803c2c0245072200069800032200c08100300e6040c0d02039010f0103220180c21440c51203421083c0510303020307421152 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 414840701 1250 414839451 414839459
    0x709020711090114040506040b06030f04031b0201090b0c01090c15080f091504050f010e07030c08010509030d090c0e0a02070c050a0b180604090507081008191e022206 73
    0x21140b80901400c0740481c61041126880e0420b44d0013503600c514003800001e151007003400000ea0a0700229000e0203480360800401c81019844420304000420007144c0c402e007112643d001801200150140c0da4525202145214083d030003500880c9025410540c251115a100e4040411201d00b104c003640c04110007402203500c04500428442c0f041ca00c5002404081c8250355121142c10800340c01950903118a1100140003c000e100e02c4500c4141c0f2002400b80f2840c1d441c0040d40031085500400d0164540b00030005001c0004c01200c07846c060b00b10001a078050309141442c1624010b410030300000e0751035810400448a2507000b03000103809803004501c505d50750350070804100c40c54040c140400c002880881041d14080102c40200e41c401040745040070740700c08a4504598089805000040100c4144680d00e011014000003401c0204080c0c11207002f0701841c0c64a4030385100d8000c20419041811020b020645820020320396401442c141000851410000c070400074000c11640703003880e03c10002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 414841951 1250 414840701 414840709
    0x30403020f0703082205040501090207021e1804080f0d0605120a0305220b0c06160207030f03050913060605040f060804120305041a0108060717071715030709020711 72
    0x1102c3d8044045445c00e82001c079442e88182c00325441030a403103c168800b140c4e55456028031406000e440200680754030003401000041e04c2508140c400b8064500d10602590300c645150214030014515041181d817113030303d0420302c64070880003080000384000c20280141c8849800005c1101d20403244a102031600c8150941c130703501c0314400240410301c20012107a04038075036002c003500c402c1030342076400c0d0703269440d0411012584a40101441501300f60b040001502c0c02c1610011109410301c0101080e60075a681c00c014007002d010b000e010b010010503e030300d80d0340d10045003d407200000c0300c00380452982c072000504160443e004154a4246c80350002c2084d5201c0ca20031841581c00c812183c2c00e64070420010740060601900030381e1900c640b019044615a440351082d802000920028000f0303282c4800300a01190700135408186441e41002030008040d03002c503038900880c40c420044480d60300e40012111000c14040c042d43c0c3c150195000025000c07015034094104e190154000e4500c0d002100200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 414843201 1250 414841951 414841963
    0xf060e0105121b0a0b04080c270c0f1c0501030210020a11040504020d080a120f0c1e0e030703050f0601270b03150408090a050603010617060420030403020f 68
    0x2d82030700e601503035010800240f80403040c4800c140c0603000954258039050960f240394403036001340c3c54503031000d500c0c0a518142203000e0071024041500101d00021443e241100806000d0505000c07414042414070400e081d45003100c1503103c201c00b12080c030b2501010b0304009040c0911099100c0c0728009218040d00303002040f180541640720706280b441d60300f4a41040020705001e80266081002c245101002481501c02407240c1e00582d1038032203109100000c4e05041e50021b10358191031030300b80f00202403a43d0f080310047c11000c4e10010f207001c6d04c0201ea4004c4514003a0405000c0d490720582c88000144007000c60b0442001d446a4181e40103a038071940010044034000144460700720b90007104412042056015064080c0300070140c80e809220001040c907040c60950b03040c0c0328802d0016040c01da81c50301204140060a050700c00c681550301d000e80140180c452550504100e0001c1c4000a516540355880142c4c0d1418400c0981d61001a0f088038609a07002110214003502c0b904040c086040400240c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 414844451 1250 414843201 414843229
    0xa0e2511190507080607081005150d0207170a0509030c0306010f06050307020f011d100c020309010315090501030819030b03030405060c030c071509050108040c0e190f060e0105 77
    0xc010848110341d00381080c1010300000e455600549401203210f900500205000701d140d5902c0e10301c2130034101d00055804400358440380c40342003c5402c0030440c3c2402420b40f001510810001615208142030000d59889100d41341c41c0c16040001e110b4480c140c110020b030041c16410f8007112040c003590f00603d030341c41c0e01c02c0c0190a802080310303404000c900d102d01c005685c46040e07031040e075002c4501d00800c1402d6442d5001a01205401c9984c02455820204200529140d0300070701072203118080c0d440603445e0b21071a8907582c10142c45e1841e2200100041911200170700790060304025540c0d41c3c0c1007500c000c0d081282c080106040640e01003403210b2282c00f030304507400c200801441c5800d02c3c000c10400d4036403149061204600050040310182d035401c1c0080001042d403150007484056117480700424040841c0c1180d0306200d1003400f808085801c03080800140c0c2c4001c01c0c0100d082d21250a5000d00d004000e00020081341007200116240d60107822000481c1e0000022100c5642c81e03004101c50610300c40030b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 414845701 1250 414844451 414844453
    0x9090f04080d020a1d0d120f18030510050f1608040c0e1008101815090b011e05100c120e0d0b040c14030304140a0e2511 53
    0x4544044050012a50090300c154074031468444114400802c0c1c0e0000100100407030051401c0000103004440e02c0c00f032040c41200c40901242c1c0d5039803869030b51540c1b05c00c11001c0103000d03c0303203c4071203000c1c0ca00c02c03015502c90710440580395520b1920f00d5850043d0700109000f1401c02d4041102e40e00300d254498040d0340c1c605840b031215805007000310382044004205031104104401d0014111214080190080345001201020b003810305284c40e02d403910075080503200700e20b440c680d66054a201c04110311810303800100807444c0d24000341d400010f040b205401502c2002500c00004000c00300392020f2125580c41c041c40551960784004000340307a03158005500100c0d03c206455800107640c9820036081804d0360501c60084240180030441c1e000124008a0319400724400748014012084150001803664100e04404001c882c0046a101c2c011480b034030f0010070414111903c2540c0707454014019102c050050940b034500200300407040c1f010751031907100012070a1941d40d903841c840c40581a08800c040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 414846951 1250 414845701 414845719
    0x705150301090b041b030b1002160b072d05150613051e011401021902011b08160303020a0f0207050105040b07110402030c1314010903060f0b0a06020d090b09 69
    0x128403030083c0201c407604541c425525144001301451070b000040003902207550001d01e04079080c0c288034144907c11801c1c0309540c8201c2c0344000c001c191b1656801a19941118140c441503030345003c480000c5003a09a003100041c05000c2e421803694482040400e40c0614221581145001d02074a82d1107400d840c019000140c103e8403a000e00065041150081d42011010b599103408031501002c801081e001018103201c042c005043d20741c3d040101907966450300071600c4005402d54000b8200311299101111203480c02c0041c0b400307000c011002e680305121003005a45016200d0b1800800960000740c003040424002c41d8000d012600c002280000d66406851f1280b07054100341c0b008415030480711045425402034203940c0b01c203403074034005180030304401802261680e10003180c05204003400c0d08110101d042d504174000050307a00c10282130440783c0204000560f0f401c0d14400801034030069000e9a00b084030910001001640050f5812680781c0e40c0c2e95500c002038481c50761301d640348174070314519034441c01031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 414848201 1250 414846951 414846959
    0x106090602060a09050a0b070306090f0b0303070209060109030515190b130b0a1a0301050406060503090319110327062b02071b090c0507020904200a080f0705150301 72
    0x2548244c00042c0203008030ba800003519138900036414821618400001d44840042000c0c1086001c3d0714881c00e644c50060000c20306180101e07541e4019444064401c01c4840c0110700c450340104240e0000e5a003200c00d0314103240b00e160320003416840c10341d10418118511840d11421707159500c00e110410000401264244000c00f03500c2001d024880318695020314a40300018100b0500c072440e05440302c0c0142d81c2501c07580361404000c07c842c4030340e000c0300601200700200071000202004444510082d90030302d004ca0f003d411b00072180040060039801030340c070001500780044584050b480c00c2c0c0040001c81d4592229105050146c0c030f024141d05884a001c180703400185005003c890031013648401c19005050030030949039850190640c440c44084034442410602c000444d80c0613200301c181803420803510740350803640455400800108041d102c00795042c0c0e0000520014680415040c5005207880c4540d51a890500d80f81c10740d40403401003074807448400184509124940380715010104480c11b05582c07030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 414849451 1250 414848201 414848221
    0x1e06030c120f0d1110061a07060f020c03030f220314090406270203070e24031009180507060f0201060b04090501081009051e01020c030c0114010609060206 68
    0x55601c80c050180078062104100c00001c1004100340302d01681d400d41a4680400080e0601a000b01d00e010200c0c18a81c0601c00d00004050310b00140c1c403224906903a8040b076007040c0004004030403258550b2400051b0300544500c0000c041e60003046d05015200c0f881d00d408601c03010703454076514900c001601005032080401d001d590642032204c40c042d40f861404c110480020200d0f010340d0003816140c0a050354070441100c41a107060b000c51a940001c40c40c5003481c075005040c1c0f0340500f085903c5040510000140b0214403402c0c1e20070000c11943c501d0316805c0a008106a80078176008582c4660300e0210040019001c0d002c107011080d030011301504030f883c00c0c58000c51b086282500d500007950b403500b10000740c208081005100a081c03c0070001415410a03141e81c0c1080d0100b4900700c1d40600b4590320b10040703400411703000d1200100800d03905d89c1210304041d81d40a070113000400a01400041048803440106401c1525400c41d201c2c04000680e803141010b40d0a000e41d8055040140e00100c0082c43e03040c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 414850701 1250 414849451 414849469
    0x90506060f18090703050f010e0c10021f0e160e060405090f070b070309062c010c140c01112a0a050603040309080c040903120902040e060f1e06030c 65
    0x14000d88000b00101000401c2e00c8100400c0e5851031040e071000f10300300240103050000b01064018400248104030758202d03a242c2d1015094992841500e0340b00c550030240d4000c001c50031503905100500344038580c140d03044000510000030120301d203020310818200072582005842054070021089030f46603464840c2030000a000060030080188504105055171810420a90004020303c0040507070381d804a18004254020682c4840306220000d05c64100240d20075420300c0f14074546155102c14509410012034010707419800240020000300600e81210301e000c6208250f401081e00c1e054000707c107001c10310fa03a4003403004c01d900842c2c2a0070311420000c15403c05040d00f242e0000c002101440e1104000b17841ea62041e1011800314885030020880c0c0302040c0039007030100343c08803010080c1d10541d4070050401c494091850441c60b9440307a00e42c046558a51112105071840720480748c1d54901152f6140460800352441607040f0364400c0c1034030400c48260f651038441c2c94090068401403c9420521081c40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 414851951 1250 414850701 414850729
    0x80c0108010e0402120f03090a05120604030f030216050313080c0612073005070207051e06070c0e09070e0c040608040510020c0703020a0b0406140705010e030409020304140109050606 80
    0x1c03400c07401d08001c40c0304206c4030850480c5200078541d40c010303800400c80b44c0c18150b4003582c01107440c000510300601d0003080c41c640c00340c0c040c02c10340040800000110028402c0d442c00c0c81d410b0300c00702400c0d01803010020107003010100c1c400030502d1460316070101c1607851a038803010a502001c03c10220b035003419498000345d0400103038140f02c0125040c00d07140c10702d44607003403600344a43c501c804e9640b00325908601a0542010060015005050030840800c110b0000142000d1100901035600c0b4080d484010440716480d800c080d12007480c036281c107240d41070281f05032f40703402c9a0b12940001207007035641d10b401280a002c10100181c5441d01c1c1440c1a503040c1c20003003007506c00340141007a030a050a4603000402c00c0c60000800743c4044c5041d0302c1045040f181581000300e0411041c0300611803607801441c002507803071401149580b0768425181c080e002d81212485030401c0e000102d40080e10b2409500518000c602c220311190088160b5400c49080f50960f55000d0000e43c44080401c0e218100090490f05070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 414853201 1250 414851951 414851959
    0x120c01060905102615090d080402030c01030e0a0816051c09050111100f0f0608010203100302010305130f030e0906010509010909020d0207060513030f4e15080c0108010e0402 76
    0x541c0c00071507005c1c18a503081c200583c840304020200480800140700300520080141056503c0d41826000f1944e14000c1c03c400314141983c0e5400c0b4040d505040050610f4290320002e9541d454488007400380b42d4500d0000110781358442e1440c5800034a03107412203201c440a4940d103410119240100440303007800f811464840c64020340c180c58003248054061144018201d5402141d05051101c0560450703500c1c0d8001500d6034070520034010a0701444004c030f81100d40929021503151104149000902241d410003440b031201c0320b40306030804d508a020701040000490b456925a0745180056a01c1d200b110186400190707a070109202e845a10381c0606440e1860400c0142002001c0d0307580c0b0101d8030142c1707114035540001c00e5000101039205040740000303003a600d0020000c01c18a01550b4a00446e042d04075000703001106080c030303600700e50b480d0582000724800c2003883c62001450f031140107040b002c080071207110400d44045081207002031501d80e1a01c040c1e4407445103a191a0900c965018050f10890b44 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 414854451 1250 414853201 414853259
    0xf0801080c15090d0c060807050702132c06160507020d060c0201060503010e0a02090a0b0604060309171b070b190305090c09100905010911070b040311120c0106090510 73
    0x100d03202e00041c1350000f0310868003590001d0800704c0140c001c0c0401400300381041003c00100d00181c6540d803e8405d80d01d0300c03020201d03454610158019181079141ca0000d00140c209103000c0d100d1100080d07842c061000014a440b440100c80780884075807085213406504588000d00d1103001544940c81400d40011510001444503260030000b170030b4800d05075120b001c59100032404002d51405848150700501138820070800780014001103407c90045114040506541d00e9019042c01291030105d0003c07500300c0c6003180c1e12146601c0302403140c600600e12a20350320690002141881e00f213030445100940003044600340d50300a45040340541402071034000103000d40208510300c2d841e10311032a030156000301c040b4508070382007001c10700071100c0580c0040c0b842403c1880c4164408468407c444503144c2064101065680d81d08042d1480c40c010302020403d4803038282c035141c007509407070f02034101c4809400081c06120341e5118048283d9005aa0f80a4084007442c070401800025550750b0504039030004e11550 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 414855701 1250 414854451 414854467
    0x606090c0c080a03150b041e0303020a02190b040320100e042a031b0c030c380718030506061908160609050108070206060402030c0d1b0f0801080c15 65
    0x5e806156004030100d060100c1c0900c50604c06640c11038405020140c00c106131840d6071802951030428040c040e005550300200718a4481d00400e04030007504007560801da031244da900d001c41c1c00710144030f00340c0c2c1403c608241d80d003400d18000c0040c030311401d040ea0342d6000003580001000028500d01c81040f404080030f101c1283c21070428843d406481086440005814500000505050283c00d203c101080300750444000040d40080c0c94040c0d581d042200300391030010694030001c00000d0142241000259030004415050801101600c640956940c0300b44000c94074407548031400391400002c086801030380000746541080c1090100d00c0460952010307119503200f59441c01d010050210041800b1241d07428045107802c4020f42004002c20720704044240b5001c4e000030f448402c0a400d1328841c42e00000420300d1002c25500351501c0d15010351007000203c034030030940404c2d00c07032400e10300f800b0600e84503612000c40e014220b400e0481c4c1c41d910250a106660301d01b0440030800c865800c0c0d01c10281401050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 414856951 1250 414855701 414855731
    0x60b0102150c090307060f020706051b01020d0b10051608090616060e0c060a1707090906121403280c0b04050a150e03040302010c06060b03130606090c0c080a03 70
    0x94000ca100108070b55456280800341814825141c215905004082071640b01c6507034001000c500302d45040c80c14548801c42d0181c0400103000e09800c2a01c15030010621480308140707035201000000c0210741c44514140015000d071010300174181ea25001140b000364244c082000c0c10000d113040d10000302020301c2c10740f99501d034030202145c00405440b62650788107500c090450801c40c640c0e4100701254664140050725200521264201811811100c501c00c04207101034003c040e5140900071501c000c0c00440d459030605c000c10302212009075030000324888400c6076007a0210448048905c66110410608003c6c042c004424565188030b40402c0607005d03105000c100c0c1c00d43d00c00d01892181000c0c0421840b2402c0151a1000c0e802c3c50b041218949124504140e03000011101200d50a082080c07200d4001c2c10310b200100401d50007861003803c0002041000c1c0c80814181103502d1081c00704110841d2108000c1084403000030b00100031400480807000403605000241940d10030341e04d0003060301c2021000b04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 414858201 1250 414856951 414856993
    0xd050903030406111213050f030301090c0e0a151d10030f14010807170111030a1d0604020a0b072301150801110304080a301404020904060b0102 63
    0x4005140c0010052008010040c014050481d00102c4202e09003403941c10340e0071074210702030800380806010b984554104a010302605030588403c006998036503944641c00c00140c0444001c11780050b1180140e402d20b85444045c440949404c580341c4520a0804070017034a842400180b02a42880042c0079840782c0d50381d00804220094041c1d40201c2c10006032032601098620500c804140c00405c10010701186000141040403254040004203041c108548080e0051109400b400c090040000c108100520b154020800c1c0880c44e80704a020b0b00c0722014120307100d040c191002580700705411001c00400d40844007030410580590300c61035001c01070b00700c0d0880884540f10b4205039651101c82d042c0030315103401203510052242034000d110b9990300c8914028603100017000109500b80209203082c205214181650001c1580300000d52404003003851114030040007103070051000d00740000d0280140c801080c290260768050315075101c50700d460340c0743c001400c00410f8180c11403044401d10700200d4990404 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 414859451 1250 414858201 414858211
    0xd0807030302251101030b041503140706090f0905041707150506060c030f0a05190206010503120a05072307120b09120304080310030c03080d0b0a06050f07080d05 71
    0x40c1e40d000008010201540081c00f80000c03591100100300124260302e1004415500918002403030504200004004080301300e42c0c0380d240030710760340d0100070040003190070655418618202e81d0b955681c1d410481e9103500900418801f9140740d041000030f0800b641000b03801ca441030445452444443c1c4141c10190450b0300d0984020800000c0c03031866441c42d100d2740ba0046429240c0ba8a030000f842200c40c1e80e0300c9807800000a0310701c0010007490091040050f03d4074121400c620818411542034025a549400c0c02580e10034000c01c90701d0000000e001c130460350104401d443c0d8508256281d21280c1d20007840d100c0d0200d007500704201d8010070b5101031117050050b19808118880d4040355090601040e20000c20a10345035000000ba094207404050550794800c0c2d029000c25540d80d5403003039050a80d101d5510041940440700c002000704210b141c0548154900103008200d514403a60420203041142d114440100303808014503a1264101002061341d207002d11295803034004100744480c12100c044034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 414860701 1250 414859451 414859457
    0x80c090d060510050102030f0922090f050f031e030702010e0d0903060e06010509010e04060e030f030624030a0f0605130b15031b09031015060e0d200d080703 69
    0x20810489140f140c8140600401e100031401c002c030492003940103128010400303100d194002d82d800c0b04800e0079490003070035040e411800d03c0343e80454604a00350200198044510f07018103d44c03201d410400000f81e1380045009071107260400c01c92080140d040d4000b034164021952115245910810200060610401140d0703132001c1c030b28610300300311040340c0301c8614107000394114030010880d1b80e813513000d00c5066609180e04000345840d40d203080e0004060004a2000078000841c0410079480e486010b10300c05c0c3d1040d6203103015010007503825444210381e8020110448014000316001281513400210108a4005e000440a444a00241800e60f403003000c480a181c035000c0040441c00d1800c1103480a601e200f0103242107080016680502e8a0750402012000102081c540200e95080000c481c02c031a40c01d10810481c0c03040d410131458010107016800205001401500e01c0f410203840e010040c1d50000401c04445151f10103001c00c4103924503001e030740320190843c80300218000d1802040000c3c442d803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 414861951 1250 414860701 414860711
    0x212040c0f09111e1603120e1903080a020c0a0503041d0705031609030b0f0f010803090f0d0203011d0d0801060e0f01030902012a061119080c090d06 65
    0x7000064501c146800c8846041e05000c03c0780c00c003054440036140341442010880c0e00300e11011801009501504000e00400a40c10041c481810340003548003142c1c4620b103105000045170307205442e940b601c40081143d4079960403008040800d1040ca9216003200380a80094a80004812824580b050950081c4d849410006007009400740c0e40c0c032403c05651505000c4d0049141080e00648a4040140b08102c429100e112082c41c1520230001f4101556100000c004941401d1441401c00e0004031200c0b45030f0240340d40049141040001502c03100340e00101451155502c54050100c0d001040c0c1d003ca81544d01c6585412501542c00d1a907248030f48400010195016201030007001800113901050500062070310404c2983c41c6c049a400c2000e000b0308000c03c0d0f81c1da06100480d0190031140600c0169010700c02000c01c50504590b50142e202d000e81800d00109010b07079800703030b09031050780b0800050784408a8030409581c001c0c0c072082d074400f420100003418404220b001ca074000448030b9041f14926911 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 414863201 1250 414861951 414861959
    0x210d0603060506040515030a08030408190e01030f0608030d0b040204090c0c03020d140307030203041103030301171006060e100306090515040c021606180807030302031207180e06040212040c 83
    0xc1c0c401d1301d0340500000280784c1b400c101003000c6602c070a6800c2005e04000b50003c001400d004955046030550042e12018131009482008028035031845120200d0010f07081c022119040c4031140100b809580c0440061440c0c640a40406801490104a5150802d40a1000080e0191180b00d02510301d64551500c1540c00351600e0001c3c00c12401100100501c03d075854804004100e00041c3c1e58406502d0800682c0da440c0c6003004c1040b0424035000c20392622000001056003000d49200c0d900b0380b90400c08544080e008080784e8002c3d5a503c1c061000010140700e086101c030725020726944040a03c50500140e607548ad40f8071207065071011240680c0401003110f00ca20141014413a1284141071480a01415980c68030503041e40300f914031803001042440a08032400d4420345906000804500040310003070340e40ca2070003039104e81000005041030000b00380001d01c0c280c062082e072000c01074400304642425040440c0543c0c0c02e1406040f40d40c10030740c2031101c0c075040b250380307036001e40580d0083c0b4585003c21300e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 414864451 1250 414863201 414863209
    0x2122703161a0408102408070617090d030b0a030c030308011a03090c0603060103060506370903031b0b040c1a0f09090c2205040501050111210d0603060506 68
    0x29402c0b00e5000e00081004000c0e0280104441c100c541400b0008100890b09424001d4a0100048144c92485044100042e07400340014044201c4030180c9481e150145450343c0341c00907402c12030f031440d0700f078100c2e02d16070a600d4880d84c0501d40b0210010020302c4410740b01c1d107079030b03100000c0c0c0e820490224031701e0b9005214000309542400840c1446482c028130798608403050301d4803142e00d045c01a0042d400400442c82d40da010780c0101d0003800001e01025251101885414881d4440004140c00c800265500d1030b102c0040c1c3d00c5442e8a9001600c9000c04680346603030860301600e00d03206580c1090040198400042c0141c407950380524007c000b4851035500703283e07e4240dc035018401045400a08102c0b90303000050401c207a8002c900c0498250040350b0390740c82e0550081c41b420801d05034060b410780b110b500000000c442282a00c90654080080d40c5c0c81d440192050421800f1215083e88030100c1900703041c00cc155800320203012415168106401040c800090740c800340c00c100d402d030b920f070401c02602d414 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 414865701 1250 414864451 414864479
    0xc0f060a0207110a051309080c0a031d0102060c030c28050703030b0a052404030512030114032b0c020a2309040f0b13050a030e030c010212270316 64
    0x203c4d07081d11400e01c1c150000e50038441d8403020044030307500d402d088018450060306580d9801001030940310314207068607009000408006680d0240d4a19204507411541b00203904d034031800e20391a03ca0f00d0340c7c449a04140c22500242040003004205601f007481480c01c0240014400560f03071200f0f07484038030364500541682c02c040c050318001e02d101c1c034007042240c1d20001c1841000380d1a00d044030130001702d10320800c45441250405030241c456542030324030501c401d400543c101c8074000c0000d542072044204254a90525841d0b5180303140c5070441100350b562241c01b080605030310345c1c24243c02441385540420aa0070092380311100048481e506401c0005111030403105080d0704070307546c19952034039540d0058800860f08010b0400302070100007400c80945241070140305034100044a407010000e1500030400c00b00010624003e01640c00440665400000c0200e14a40c003560214141440f01009104000c0c140c200f03000500882550b802c1c242e18140800380340ca0090341401ea110b40e05008940404503 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 414866951 1250 414865701 414865733
    0x1b070e06180910020705070503060403050c0f0309010c030825210216080307020a1406010303090501020f0c0405091608010e07050118050f010504090f051b040e010b0c0f060a0207 78
    0x40125003002058030000c10f1501c001e06821000507220074183c1070403440c02c1619001190144581c001748014560000007038041c3c2c1400e00c2c01c642c010100c0190407501d90146400c000d01003000b115810000074000c1c1c1240b40d208004101071192440501d2524028440b40142a00400c0b91315861840e055000d041254060905400640c5840c202001d05111001c2203200a086080003001140c6680c1c0300344007840d40140c22025800c00021907801441d02c0e20828801100130070101400081c0e15400869600b6102c1a0800603100c0c08203002c041c000034000041020f03e150103035401c0e0641c0c81410400c0040071b04801c1000092861050321114034101450300300d54140000c40c9800c90f00b80b04051940d500341c403000e8913800600d00070f4134016912070140350044100d16003405010000030501e9805584113109203005035000302c142400380c0205106038041d490b12002070a005001c002c03240c0380141040c24000085070007980380400c4032070070000155003100d50316030005422030600a4981a1840318 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 414868201 1250 414866951 414866989
    0x40e01020307110c0f03070b18030f07090615171008030a030510060c02060403110a030c03120f030203060315090f01021315050310210605100906150c081b070e06 71
    0x83d21704000066513445941c400c104130a00c0000719180b40f5448042007944284002d4100c59118405900c00c94960b210f038081c81c000d49280c0f03d40083c00340301c01c66280016242d1500d031409540544c181c01d60001c203000300951070380f1110190000300403c003000103007034030b443e5031f1f800140608184205843d071641e9076008000700b1607102044005a590356048800316507011040d400205100703000f051540e5003681c405000307004142000820b002d41910003000509266560305070f0810b1206059080b400140c9083d078055101e000900c003541300b60880103411040100c2180d43d2501d030240483d080e82d02c41c0c4008861458140820001114500d44401d480c81c254100281145080b20f85542d2042c405c0c441c80d5640d410091410400f80d42c00820303900180c0e0030850a00c00351500d41c0d180940c822041c4181102c041c0742900005d0711a0701000420f5010850380c2c3e0b107000440d0709844183c01a040b0398680120f00b4a06550b0010f00202080640024807140d102c000340e5140c4001000f0049000e4145880344c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 414869451 1250 414868201 414868219
    0x1140a0b0f2502030601030303092a15030b0918071d07141201060e12070308070f0c08011a09070f020a12090305010501090e1e0a0b06040e01020307110c 67
    0x6000180d90503151846104105444601c030107524028902030410b4019401d07014160010040c1507050b00040e082c6802a2000d240401c91090b02409424071071070800b4501080d41c405221030069a070740c0400d01d007106e1601117010121200064001601034030005001e03001c078021500300c044144135840041c21404072560080440700c100d055039500c010403040c01c011728050380a0134000b13200c0a5409070584010040415a1140c2026240c0b40c200c0340118454401d4241031140040000380040070340381e0111245080403c2946d61150320360341140121051000d0250114010703c4c00d1061507000f4940603051a01005d2600c2400078201011b0100004c02042181045601d134000403100103140d80907030000c041e8030603c0c0341140c41102035040103000e5401d1a00025000506821030b050340c44204050b02c8c07a520010941e1701c103c031811b0341c200d0159001009441e02103900d00c450154030003405440818010006014071f400c9030710440e440c201040b21203941703c3d102042080442c91300c0000783c0342100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 414870701 1250 414869451 414869467
    0xa110f0f2e02070305040909030f0212070309030b060a030f051005100b18040b18090c010309150203070203040e09061f061d03010902040617010c0806010921020901140a0b 75
    0x1145a100e80300c030100345900000d43c20100f61180d811200100202d07441040050b0303180c60020300c3c1c841c041d42101300501c100081d02847c0640f0204a505456058640100319851a0389880100302e004081c00da020b071120500201140a03000030300402441a4090a400120a2003450480d0b1019008070030365113000c1003e11102095600b1102d0b601c001e69881c100d1004900009400b0744480c3c0c042ea90003a20404034a0041c0311511003c502550f0b0040a0300d100c084142d004400700d440d01103020b0465040c031345030007004111a44c011030b00400180b050f03914240d20381c0030349803003c80252070300d07811503010b202000b8542d810540350a0368078182e06001c0000710701d448002001383c0d03e0f080f010099850740c2c014440d0a590300350301004c07816501510601125039110319800050074040c03601c00d0300e035003050840c1428a11400c403040c803c40d0305848120b90f550400c405000a010b00d1841c18001301e603024213000241c0c2d03036807403080d000380040141e001120702524140038042149074400c584881080c06010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 414871951 1250 414870701 414870763
    0x20190f0306061b050106090f060906090912080c0c0a080933090a031a06031b0916030f06090605030f0307080d050402130606020a020901170a03050a110f0f 68
    0x802c144074030510f1103112910a080c4940180000c0c5d00c0303100140c0c0f4080c0c01200410407600801c040701c40341c54040000b00da80d440d8680603110415030080c0800404030100f202d181c01a004030380c0101c000e000003410303c0c040140e0989400b805c600c081e03031030300000705038180145031448591101d024030401103502118800308642c1600106c00c4462008000800c60854580741c00710440010340d0840081c0540c0411141e001d50000810b554507402401140c0b402040f00100b41548000280090310049055560304500e80902d0110500705003003544aa0000d0340110050103083c01074020404001101481c00c800c00d031900b0500308070848590001d0003043c010407010310a0300d40e1110221008241c9944510016007104a80e815002d803040c6020004076061f0360000341050040d10980326060642d17224510340307039000b280c11440c0c4041e5016506020010380700e074015003131348606810704510002c54640d24901b815010702600c00154411008600c0308a4204488008d12000040075424020110044 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 414873201 1250 414871951 414871967
    0x160e0c090907080903072913050613020d0204091202071205120a05070803040501050118020306030309120708070608250507060b13050c19140a0320190f030606 70
    0x10814403001d0f40004006032820300444514980c000120503010306102181d0350801e42d40c448040750a5020320004041074001400c1c50311213a08600205601d035102c0c074807401d0000c41141c0890304403200d0001200141c445000751180075104841000d2002c0c15414002c3c9081650b40c0120240b000c3c8145800101d42d01061580c1e403941e401044980d540c102580940d4a0300c00c1520003020300000204201c03d00c00190300c054140c038010f4070301d50100d0001060302c9040c0e0000f6035aa42c0e0642041007103406505d8208a0032156a8a51041e00d003140da50700e50050525107130794000008100f2355810094600000180580814286055100e01c1212144028402d00420500506503036031502010740603610034502400300c510307010b005d2025290003400c60b42c9036007041c2c44a02080a001130b0f403840c403e000b1814906c0d8074100790421410808000c60072006044041121114201d002d104c1c14074042c0c451009002c80d5400c415220b00c0b00c188048020819031140003c41e04143c034028007030101e15072004007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 414874451 1250 414873201 414873211
    0x203090d2a0512040b030a0b0a15080a15060e1306031205030405031c0204050f041a010e0609090406020a0f0914010f110f0c0f04090b18030408160e0c0909 68
    0x10400003509074a0118034003070f02c00c019034401c1c0001003000509a4084402036104800c0000f0601880429000740004080d0f240035200301d80c2600703000c0480c014400c000d8603074440d083c030741c0c003240091040b003041a0422030754100500051410f8882c40d16801c2101d280d858500d41507404116040c910f48500013000580780c840010000004046014420100150344030356008002a00b4901e000300e24040007948248507140c003903c20040b040490b45403e101c2c81e4804840400c0c0b10000140d02c60045494801c050340b22980601c05108400d40e40d102c04507510720841c82a507006a40300400e52028000f88640c2c01d5a008104442106101c0c80702590350800c240700003800e000702c42c000d0282c1c0617602d09000c080180c81511a480303480c40d202000141140318207505031000707070307000c50864140b1054800820001d4036040061020514075020701100858402e400c40540e4206622040340c3c80c1413840a08010261424030b5509100c01042148803681101c038007804145445540c00c0803403000400104 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 414875701 1250 414874451 414874517
    0x1505060705030415021212011a070b060907030e010207060b090c031312050903190201030501060201060e0121020603010f0806130f26040f03150c0207090b21010203090d 74
    0x1811013003003402000407981d01180306010f0340d12a810702001c6086400700348150000310f640900c03030328400c20000e401c40782110b42089681b502960348005000100300c000e40000c00309a502e03041c1c0924408284040c003d0382e80319950116210b0980f03030412440d0340740a000380040726000c00c10b112945600c11030051260341e10001241c4200d00d141d8003512640589090729805000382c0500a81da10011101c60303200c140f00741c03000c121a0342ca82c0c0d0103e0072a141800b81c0d2040e980d0100051103003113280781c04803c03039a0f01d83c100d206500c8007650101c1e81c039810a90055010b00d4070000d040c42082003c0c00495400103090207603045c0c110b0300e03450340440c401e0b6403400a0310000b60510030a001d40300005080081d100994801542c07540d071209050780300c1d40a84000d5807103012445c510000c0c81d900b4040d400d100c0210342c2c0201411410034070007000030505984903c0d40400b0484488400c00c0b0134904034174100360040e00044c1c50713207004c9052a05280028881d40200156680d00020380030b401c4402c00d490606070f00b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 414876951 1250 414875701 414875729
    0x8071502031206010c12020309090f100303050c030409150f06180b031008010e0a11040504052a041e0c08040c27050405070f0b1c02161515050607050304 67
    0x540182c505d00040303100600001c40300f01040d0581c60300040200b0890400360340103c80d59903080d81000c0e11600070740b0708501000300c0c0041000400d00c02d601800e4490104030940b8501a42c80b840c803021540d054801c90030b50a54003004204003618104400000c140c90304002c03620148031075181c90301a0081c05014150703400440400c1800c0c422120410113402c022008004840521341201d030340d81c5060344100e440504074070b1794903001c2c1001d0040e1030190f0303440401403400e0000704c05034040c090418818048100300034030300c0d81b4155441c2d000c0e4070001c40b407203401091891040341080381950f04a1035410306100301d0741d06020010b620328a0b060111440300c0c40203481820140c040c042001034070300b0200c621030f01b84403e00090200105000c000c688031010142d88143d95094010001d00a081e070500380c0b00e00e881080c940c100407d8005011242001d00d000b00f0007605540c03170f0315606081000c03856980b50f0f900084c807064443c03450400c0190604945413801c26420f5a549690f03842640626250200c9003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 414878201 1250 414876951 414876961
    0x70303020d0509060604150e04080903030c01051302120c010e15070503070c05040b0d0b0708071b0308070f02120904020c01020403020d05010203060a090e0a03080709090e0601080715020312 83
    0x69410788000c0010a641801541400c3c0f114540c0c03540140c5031244110324001010210554140403202100c042401002c00d41d82c903030311042c07441d40000030101e030540001c003c0303a8000310007885134900c0b50403680f688401d204141c5c0103214060000c03000c80c05482c0c1c803251448041c1e03038001d501102c14410480c0c1c05000c01c082e809a0030071070300a54000030441d2001185c040108076519980c3e01c1030b142c066500b000414045000c01c80800901240a402e0300501404640398506c030701070841d4001810700b4850483d14407016103403203114114405400085042003480b84603548484141c0c0b007034000d0320080ca0204502c4680e50450310900d280140703d9540080e4100d101d11080d01034600458000300a029008e2540c100725020390320484046100f034001440210b404015840740c59070480002005110154141e68142d58005000c2c1c128424003801c1031001682c2a218020b00c1000b11065014126552400c001a441c11f5100d80000c5c00c00d00c007112501480340d0740001030310005d5200118800b041d840d6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 414879451 1250 414878201 414878207
    0x7083721020c0708060a0b0105040e010909050a0209071106070908071e05090705070c080714060901020c040507030f050c0a0f120209060a030929130203010f02040f060210090c0603020703 82
    0x50654114120f001d40a0300262480000c60309501c15000400144984c4000000440d400d00c9180100028807640d10014018008150701150071684180301b110102011600060107400080b0382100000f030b2291584950411705010990b0009101d080c982415418802040c0c0c454141d8001c000b2420240b142c08418000041070820050001600359a000d0602e1540103141d41d200b03141c10b503071101d10b81b0000102e140002038510116000406007505841d102d40400060f070340090001c42c11803042d8000c2d81d03959500e0f4440e59001c1d02258400083d40040f2042d80020b540c0c0060a1050b5075070103000d1998016045010300384052401d180202c02c0d404801001c0000707000b030b140040d4024101141c0003800d65007582c080070050313014401c2d4141d044400000c1c40155819900c1d2103518280600211304200c40704005650308510040000c00c007103100c8010300c0100d812503840300c8007201c4211403c0100980502c15818914034020042c002c00d1055211018000b8417445024100b50340054004c040c584 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 414880701 1250 414879451 414879457
    0xb1c0b01052b0f050f2d0a0213051902040302060d05090f030301060306170d0e1905060d0c090b1213020d0218011a07020109050907050708372102 64
    0x11020b800214440c55040c40c0074031198480040700c56104215018801010001b125480d200d80e100040d9000004a081c507042115119445041032043d50f80c0480107030f44114010a51509501c400103e62510500c429190200f070b00705465114410001840561a03100c1140c40c001e8160102050070703240c205c00c05140210103081e043c4680404000170504603170640281d41210321400d00c0321011401000d006407500c004100d00404100d200034560b2660504611020180c0d6610f000440c1e0280e58a010840c1d680c050301840d00c0d500e560b5403104611940001d003410281c034107920312908089044040c0402405c0203031814100d1a0455462811135450491400c0c0d46640582100171040e901020003210380301c28001c052410319460010140c04460004cd41c41c4d0130380503914071144610b0041400744900b400350072401004020440b000100340305000070440c0c2d141c14811200a030300c50040b0103161440551300040c0303628104081000e9030754090720360917882c8420010107400f82840d00701580284 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 414881951 1250 414880701 414880759
    0x14060403080a0c020907030b1804111018060206220501090602120711240a150e090705150405060a1707020109020310090302032205130b1c0b0105 64
    0x80c00251140390b042c0c1c0041050000c0f4820b41d4104130b40d0315440c3c0700340c040c1e07401080410340007131590304089a0b4050300d003065600305000720001191a004100401c07171406000000c1004a55105500411181c055100e80001c0170310384083c181d1404c2c002159101d1803031160218146c400c14451240521401307620001d80e85a0114046548520390800c950380044203c1d08007000c0b0344a111003d400c10004561301c00c070100740d00c0c030351000928201000681200094008014940c0e65102c080c12146007800e0100580100408900a481c1241da068942425604002c0c091864500f10443d44011481a01c043d500d0841c7d205032501ca038410b00b11040340c0e81d40c2d0341e081140c62071424031454680641c00b03540e1050094007903c070001c00705884241511489040140181d0041020104c261422003085560444823018041d4079a039640c006040e415012032101c4c0c4607559600780c640546003130040d036003021b942c00309107494072010750310f44c070419120510031103000ea061242400081114890304051135 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 414883201 1250 414881951 414881963
    0x5010c0e212d011a040b030d05030a0207030e06040801021b030c0703020d0813090c020c010302130324020a0503010501030501120b0a0f0b0a03141e280b1f050d080414060403 76
    0xb03043c41301003071050600385040c1d4a0045140c071030b4621240c20042402440e14400b41c60780c40c86c40d00d03a01607800003944411016030402281540326919695403400510044c54031f40005600e603d98003040049610b60b050038402c0c1580200500d4100c51004212001101e0301103841580b902094100004076101d000203441001c7d10042c004201c0387c0780740e07200003000b84ca00c0c1e003118000b4014000650480c850f01010b02107440b80c110341080011885e0030f103454400e8060030700010a00c0708032041e4061303170811640034010402c080018001568144500c17801070032240c48d00400131903039803100c1940d4400980020141612912010040a03450b00148041d050103015204241c0d075905154041c0e10440e9018603840c045c1d1803002a20034820f1500d01d0a9201d40c03005820a05618003031482840030310360445a085607000d55003030220707480700c402510400f0108000080403e1f0784070405002c1c03045801042c8510045010364000c40c10034403d8405407046050141c60315000309002610758002d550004000d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 414884451 1250 414883201 414883211
    0x1803160509192a020d1d0103090f2108070f0305091e0309040c0e03070918120e03060a060f0501050c0106031205120105030309060708030406060305010c0e212d01 71
    0x80c018020602c9504814148043c98200c03a0301c0d20072611040249144400252042d0710f4140c41d00741000441c81c3c03018141400171f0b0710076103544c80e0b80001540c22802d035041803a600c12891f50701c44010640300000094900184640b500301c6c409808a01070103003500415507160005000080d007045502c5500e0340303c503280301003030f0b06041e0100c2e62980010401d90046d420401c0e000c072528040d542c04198400b0040c0079204140c1810002e0005145030b80c484082882501040c402080c041c40303c1c52800c3c81c5036078552280b0310300708050600c0d00b10b000d8440341c10249424004c10071510b0046d810016031300246012a81c4e1210440e841d400340c8019040030302030782d142c4a612071210360088010240d0104502c5600e415030798903402c0549900407540840c0c1c1151041100c0f50000341c4440055901512034800041c1d21616520f40790f00710b408580d01c810201e030b031244811100d85000801b0204019250400028070418108d00720b8403141c20807075102e003c0d8002c0180d200c20365003070300c2d08100030b82e02c1d0300003081 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 414885701 1250 414884451 414884471
    0x3030310060215040203070312050706020f03040b060906210c0a0b0301061803050a030e01050c07094713151401030e0a11060d11180316050919 63
    0x35403422032180710098070815081e43c285500d0301440310700c5250001d000e010442c1c619258201900d0b944881c40c02003010400a02000600794800317402944181c0c0041a00c078a454641107801c40303005003083e40700b01c20301000c011083c4d0395001040208034401d800f00450801d00300841e49400060302a40d980a982c400020a0311101100954103c030b0305136540c000c500030510302d49000301165000261498225000e50f8011030b005000180d905a4180b404500d00311030300320064101406500202c40080c0c0320031074503c000404041176440e080348000070000802403642c5840315180d0b5403041e5030340d0041c00b5402135002d0340c818081c0c0c2191402c81100b406002c00c0a800c407090410140900c0103004548940c10340954428410380d05480c102c1802010041d296803200d50000e0805c1403004d5002c41e042100664510a601034001000220b8003610303200d90141c00c000c000d14200303800140c026071160312140b504003103c99511007102c405030f03030008158842c1c00309449184500c41c4401c150b1810040005 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 414886951 1250 414885701 414885721
    0x90a091e0912031b091a1603020705090a0b0f0d17191e050a1215080109150e1f14040b0601080c0f09040209120d051308010b15090f030303 61
    0x4070003a1019902040450200b20018400c0d020032034014000805980007407100f544d045040c44866240c0145640c28012480c0c05080c41c414000f1f41140140c0001341d0400150604d000c620b9040910307550248022403207280400c1e01715807802c4201f88202401504a4203001c0d00c0000c0501c0b0255210b60180d80b01c0c00e820014124412a00503800090216418803280360340405100c920240c0981da214074151480711308442904026089145503940d0728102d48000000c5401c0c0c00c0104501c0d4004150480c1500300588880d004015910002e1b04009000745080000300b8403141a2900100036001020101c40c0b0500801c01c3c0c004c54910706044409000c01e000421702c0b440e1090400340da8502c140d13500d6405441c1c681c012400600c81e040400e01020302d051510780c000d02948a070107410207110015824042d031819800c4684117012400003e6004803905410131200090b28860000780501c4482d580031940b00d06c100b1140710340c41c0704049540c0320217650b00c46252081c0c01c0c00404403070302c03824882c4582c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 414888201 1250 414886951 414886973
    0x2041a1503041703060a0905060f130b03070515121306050403050712030912050c0a06152103020a02120102090d110126010302010f120203040f0c050402090a091e09 72
    0x90f00d402a800703400d007042208910860b03100c1c50f0090310210a0900c1c11741c1b403001814026200316406041c00c034100b42c00b6111000401d0034004200c0340818190284400d16080507a01c1e00158050003e01c2209901c800c10310049550420001c0c001c032400daa0340001400001403e0000141400c3c01d003010700c07042c1940300002d041250300607002070906098922051b021525a1000141a10081e0015100c240e0249015102c2600c1290540c1d61a00f129601c00080780c40070b00700d40803040040c80c0d0900c812000d000744040c1c00880c0395048109d4840e0b54601a68640001500a12a181340e0200c02d803c44401c1d016030f0343c6840080d02205c42564546040d0000220711855503000a6205d400108513407050302d41540b220745036882500569003560011071f501003000c9030000a20003480e0040301011541e10045d40b00314014920a032500005103800701e035074105a4001882640140101d036141e69415801104849030035100003069804124008002d90f00c000a8020981c98079204e0003d2100400c01d03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 414889451 1250 414888201 414888203
    0x60325090605180106110f24010509040c12021201051005040b040b01050906070c051507120809060601350402120d050f0c0106030f200103020f0702041a150304 70
    0x5000075901c803018060921800c1451061a6224000400c080c4d40118031500c0c8400350501690001d0300160300301c07440c240202031040304c00080e002400e10403010704160b00303000d000c0460f402c03405401d1903110094220024010840719040e0349003003008560340c0302c0411154030007410091040e8038040d00f11318200816841070f54010f5041030710464140c5800d107d034403e60725050311280e090220400604c100c98100c441c4c103c0d00230180c10800309499564103580310b404c40301d038161281c2c1c40803186004400c402040f030009007440b007840c05020001e60081880383e8040e00038039100c4101d05280103200b0040750b403600ca8500410f4034000c0a00002500b01e00244600e00070b440b01c11082e0008801e8541e03070f80441e507030040001c0081c4114401c2d061810001c0c58421900320020902546a8680c3c88801c442c8030804c4920070141c01d82262400a081c500b40126007007405d0850400349090a4100c061140c0c0070000d05c601d9540b010b1160b01c19404003045800c41015006200c01e0824010f5543c1c00e41c01554 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 414890701 1250 414889451 414889469
    0x1c1b0302010b0301200d0f020c0106080d0f0e0109120314040f050307150206071d0a0b070b060915010f091502030a1416060b031009060b0109061404030b060325 70
    0x200040320b01910b1218102c1010140c103c41c50b000c00c28046500400301c59880b07d984507001c001c1c81c07003985024022000540350b088050403c0d45015080640070035000c0204c6010b0001142403100c1c1030782c00c0001801280c0d120700c034504000c0c499240c210342c008855826900b44100100d0049001103042110605803003040c0c045850254441007001d0410b0403480d02280168080701c00641d10522071072100c010016400e101180d204d041500113124600d440d0130a455041c4049008414000b54240c0c1075002103042e40c65098904240064015280044101c0e9040c0f00c038200010b00320340d1254490600402c101e10700400c0c0030b60300d0603000f51640d01424000340012012100c02860030303010400c88142c0104801503149503070081da590006041c1082426030305000740c0980f40007800300e40c043d182d0414840c11002030024241c200162181405801907130410005800c03025043c1c842900703d4054039005111420075940302070009140003000507410500803c04005c0c80088003034200c42e402a51810300b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 414891951 1250 414890701 414890711
    0x302031f030308070f05041a2835010b0c0a061b030617070504111908240114070606150503041707030507200a030b0105211c1b0302010b0301 62
    0x45e004a640d8015409a01149080d0f2902466804401d9000b00748640380c03c6940c000c4014034a204c1c1c10b42c80c850403034090104409841040c4048401c4004ea902c4240030240010040408403c5081c210320502810b000c00f13400003600418103904000c4034141681c0180c061180301004c0100c0045080c0803404080880d081c04804250b0307503401d19601902e0214507004102c02d0740b0340002c200182c0621030b12040e4508040040501c1c24110109071410f000090700c541c1c0780303411706113041000d000b04d2602c03214028901d003d074521180e030f008184021081c02006442d0302d4220b903003007410090425a00c50594900744cc8060000c6a4100c03001e10321650049240d01803144c51400c8209251044020040c0014070400c4524001160040748007080c2c1c11240903400400c0401d0301007100c80085400644850007400b00400142c6000080703203054480d0300301051605588046c0c05c9554542c0c00701c90b05981c002d01900440028800c880010380c0f40301d02d50f0030306034103021418041d008200600b40207009500305 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 414893201 1250 414891951 414891977
    0xa021b0d0b1308120c090a060e13050a060b03012615040308040302120406050c061014090a0b040f05010303081503120a030207021008011d0402090402010302031f03030807 75
    0x348680301580c64016074a60000e80e11000016200410310b901101c2d21001400030028161000c1d880303502c1601103000303030f56840707011204018900ca2580e025000b0040c903002c1c480b0f07842d1941d10b40072040110306503020840340c4400d20140050f00894002d44a008801f00001170035610040b20b002c6c090580440514402c1145100e541c0c40300c5008038052b04052009006c100040c2c85801e40940c042c5c040e105855202409a01441d00c60303102e6400000003800102d04501082030034880240c000c981062000340722460214102d00c1135a0001e1510310a60700c06000074404c8501d03802c8400c000703100600c02c00c0701c1c413041c80040e4000c01081c001540010b07004000102203001c0024040034101d0014020070315081e170100e0414030f592213140000101a000d202020041c2c07070304680c0e0404500541c488601d41d60502192203459080c0c856071003255410702003404003503210b503040d16400540a1034056900e079541d5900d0446100544803810041b080c094000040c10f50004ca86030103815079a4034182c0d41038003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 414894451 1250 414893201 414893209
    0xa05070f0e1807200607020703140a051c0306062d050c060f18031e13031425120201030203040606120c03020901090b010e040e0c10050315061c0507050f0a021b 70
    0xb0480e040c6c005603104007410320100723516038450f003120340400c011900c402103103035501401c040c0380c0c074002d42d41c031001b0140b880c1449415018241c050801850700440b240040c031407000c0c54016170034264107160b1801d654000030911840403146c40312016000c48010f400c018503c0c51003907c044070710700c45155400560308050507002c0300311590640350341003405ca091150f0180321442d41c00345010401d03903010601d002000643d804950140c4000140162080080c0d009042103031440c40040200c1c842e02408048c0706468550040c0301c04e01e9020b1a00584030b90304c6181610041c0500d811200182d59401d102ca801c20a82148804c2600c0c4280c86202013661b07220481c43c2601e0050790300d5404654418600700150410385c0c230101d4004402e03411640040c1c00c4901241c2c04001c4c0180030701c00101c0c00010400e60882e14101c855001000340d46c0342d40750002801c80c2402c240d4a582c10070b910280c40c0c07004100301c00d10645c01e07580c402603c0449240d4824a14001955a01503080161030701c521280110200d4a0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 414895701 1250 414894451 414894463
    0x6060117041211030d060b03090d03060b0708180a080c030f03090f09150402070f06180201090303050a0c05191a090a0201050d0f0204030308040b0a05070f0e180720 72
    0x1a104028a0700c0b11002c810680c1c0e100958120640340740310501280f41002c01500401c0e006003d44680aa070320305213094000e0800e2401c03e680f41c141420160f04000c04060001110107460b08241896210449802c0000404811840039940b19130500380100303400d50f011a040c00c40c10000c030f0885a419810300980b80e120b000e810a040e6010180c1c106031081828242d0405612202090f410000d03d29a08002000c036005042d0503150b20403104255403c2000030300c28108074213009200070020746d9180e07000030110349841c04002c040020101c0c040c0310407401611081c1081d0341c020195aa5000e2010300504400c08241c010386101c0641808a200d60b941c8038280c13406081c82001401801c2c2068005541070743c0203c200e11040e0f60344044580318081c0b1440074001541c8680d5400341d01c3d04081c20b010700c8000d40a42500100b502d04000c0c0711075250004045d50104c030890030203c54000100c3c0028070458001d110010f20782d04860104000117504c6a81c1c640a46410615030200d25040103400d07564003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 414896951 1250 414895701 414895703
    0x709060807030b030c0603040803191b0c021c03180506040b0d18150615030e1b01090905190606090303090b0f0d090302010606030c0f020a020906030a080307020606011704 75
    0x1030040380200d01890700c00d0304900d07103a40001d41110543d5446001050060780111405d0750703400c0c00401444458403003815100459030300d10209004c502d604298249001000d00420010f0115444080782191100c1c1e1505121100050221541080711305010b0032440f80382c10301205881c05205e01103203614020b410340d025141071242c0f65051020300b80d882c0006001608100f00808180403040c00015000e0194200904041e600840d1003031410080c03080361450400307541c06050030a032580c1c20a0b1400039904580000701ca0203502c0c01c0f030001c4010303201c8941a81182c005035003031408100006041e03954562140415040400c92941c1e41c24084520b09058000280050000c00080068145000240002840d1000d0091801d00703004540000ca42c0508011400b50351030f40e2040100640520070030001900d14103042c6102c1d035410300b00035203a501006009201e00146004a0400c0e101089420b0f0103c1d440700d10a950b0341000a40695907610480300315002902001142103501401761100b07003d6 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 414898201 1250 414896951 414896957
    0x14070f02070b070c08070b09010f08061c0c09020c010203040c0b12010b090a0f06030905100b13090512040e1603090803060607050a0c1e051e0121050c040608070906 72
    0x200c1c140b0008141d0395210706030640d1401c00c462404200f03e1010f010314030003080d2540c00540e8880401c400544000000340300001400094802c00445403155154036032000002102100300c0c0c0110f10300041d980005400111000b4404280c40500c62815402540074a0144509170b203c00d80d5041000c0c030a01c1000100407050801c40c004100388a070b008050400285c2c02010311680e90380782c42c5060031024040d4441c0d000a615a4a82820300c5070030301076901c40b00b00014040c80454000f0b404203c88001c400e03203802109030707205500e10500005015a801e95826202d0940c1d44603600d42c28001c89103820354034450701d0040c03840400f1000f8002e104814645522074444da045a4136402000300903089220b040d1000d00400c0711140004000d240301d04040c0100702c03910074410002c1900c001d00d030b10042d0810f6005011105421003c2d82e040d000408442e0424a410880004080340c00b4052483d03500b60701110605110901145241302d201800655440d0703503c40e201da5640c044100c654080c148150008 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 414899451 1250 414898201 414898213
    0xc060e03040b1e09031f0e24060904110f0109050411070201020601080a38040534090b150301060801030303181a06150f04051c080306130902030f0114070f02 69
    0x800b1420640095244903010f00040c10007112842c0c1d814141c0038183c8490006a041402c040380e10020421500208107580c0b405013440d133941c4840c89039130100b11aa1050100280f1550305e40e200d0b000e400041c1801500a01c03900c1c03480400400103402124049015008180020480071000141105502d4200a4031342c40c40b010810b1213000b1444944039001d880c0d102c000d400041c0a1350f0201c550080c0e10600041a4202d40d058900c0a842440e00c4082880c0d44031403645d00314000143c0c100c00c10b85000b0317500016034103c0d110015050403904402e0540a403008000069002e03003040307003d4100c03030180c0c07410310252040c00c81803040300c0c0d030903580182407002c0541100c0c190960310302c140f40e002c03202810300f4031064107101189501d6081001002e60346580003c0510107810864405503213090800413039032640c42c0c16640c022032030000400d6940110100424044540b5890b04a04c100640140558450040f01101580a07028901c0722401485034040032400c0140f02e0080e400131040c1c0342d805844 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 414900701 1250 414899451 414899473
    0x912080f0a090b0a080f0705070c0e090309030a0f0204150b0a030b210a0c0f0f170115030308060f030309030a060504260a08070806100c060e03040b1e0903 68
    0xd0550040a84001000304511000c40c03650b0345803008283c5030b80d5540f42e80c0301c540340600401c07100d075200816581c2001028080c1ca40024a4005010266002e8042c84c585540c3d0748401d20f403070340c055200300304d80c544122103260060203518091172924a00030b175400d0242c0303801c48032031104a94007442114404d04c010084284203e129900503d65110010000ca01c10301071a03ea50f00042c03080140d00d1503c0c0c01c52006102000b800d891814003c0c14503184004a0034504018615010114072812045000c61110064a501c00f0341c1300c0144034510400300c410154a0741001091454100c4001d402452110580700c1140342c000141c03030318031200600400c000040750b590380002d8640034004a51740f4034040e036840320941c008020081c54980541703100d52075203800c840c000e0100401829560038040c401e03051200c607072503008c144035900f619800c0c0710f8400d03401032034104010400081c4550035400003240c040783d40e2103180001c0c07036144100d001e1a0031561108400708118821001c480c0e070306a112000f200303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 414901951 1250 414900701 414900727
    0x80105130b030a020a0801020c070e060a030b09070305060a0b0405070207030506070c02120d030207020907090302030a1e0506070f0e03070807050d050a0c140901090c0e04050a2406091208 82
    0x801e40c40601038650219881e400f02e800440c55420049259402041d8825140380400407040107004040320f031071040c2051070201b42480054007028210081c4c035000079120030010008800110392200c00c884031441c02c981600c0007401c070305404034407560920012407090f82c4000741308019039801202500c0b15841e000c0003518400070403d41284c00007400e421a80e100701044c0869800c2c0e4050303480140e0307114444d10401180c17000082c101c505020140200344051303100058010340c140c3d0300c0541030401c91801d1000041318101818010001d1050004004103544d20441728801401144c95000724400d00008054440a40e0b01840c0540d6101c2e032401c011502d010251251228011401d0b0b4045d02e01544410407811450780100202d130b480105003040300d0400c4a81a40108807002c01004800c40c4642c00428000342180038510513074036080401c0600174a50701400f0804030000e4090300c101140742d2003410b8081144200ca01103021008002010000d2070b4510944541c0404601e2500316205650 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 414903201 1250 414901951 414901961
    0x105091902090418060e1e0d051b1b0f06070323040b0c16121527050a0203060a0e0a0303020c030d0518010515010f050306120703030c110108010513 65
    0x103030303c1070700c0b03400501120407031080c0501e1860045001044100c04400c02034a44038910381400381445138021200b049000102c0c9540c0d058100340b0300310f6620900c41c400d0b9440100f03901c0600140e809846d43c000040c1c0c900700481c0301e00e01010344801403075101e8402080400d0064003005400301e020f860313003466241f000390019094031480740c2c1e5540c28141c4800070a4002c8c0c0080b006040300c4d6001003094100100c5506110000b130104404102c00501503942d2000c401800c03003141c07180300351a50425071850019042284160050741e2051030300424609100380c1c4c41e102e1903030a900901502003c22807940322801031500c40325203d801098940300342d903000c0b40207500c02560321140b401f080c440b000513038006006050261a40302040d00c040c003400c801031400c40e0006410070f5044c080c0c10000b09821798004080d082c0002240c200181c80b03a4490011400100345070030b01400c0c40c040c3c0e50700401055003102d00c41c024107000303400080923a00d0039401074170140c1e82805810b901c0b403030514202d40c00701c42503046 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 414904451 1250 414903201 414903217
    0x30904150b0408060f0604021c090606030503030a020a03140402010905010c030c06050f0114010e1003021c020304120f030506010c120215090f100b0a0b0f07080d140105091902 77
    0x1035006095964556800c1980141e00114400e81024060000710028404a581c02c685c0403502140382210034064640360000c2c48552003d2181c888980710140015540840700440c1c2003000d41c1d43e0b910700100302d90300952080055101080c60881e079489240460031840e4411681a10b540c5241c0b03007020f0055440d10456801103003000451060800018014060540140c1941c0202d10047d414848032905040d0700c0a2524100070600303440c2d0200da90b464040001d502807605005a544090840000082c041000d0700c400d12800001031208200c4080c0510703060308116134424010b410380030f4086065440a491203070004100f1509840420915011001e850b02d45004070f07409140d50114200600700c0403503030f28aa6070000c0d00062035940d0305100084410240300010002d6802e07100005140c04443e014903246480f021a411048480d840110380070940c0000c50140c40d40003a00c0c0c00405020362810300480c0103400c4000041c1814481c250301d0060703441d8501c425011058564880c0203400400c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 414905701 1250 414904451 414904481
    0xf010503060d0c0602010911010c03022a060313020a05090708270a1a0114150714030f0712082229090111211f120507060e0102030904 59
    0x400000a015843c41c00c00501517500040b80d1141a41031180c091203d802c0c2141c11300c0345a40d030402c0043c7c0c1c08201d01e80c48140201175182640402c168903005801c00d1009241c0100e000020f10280d103c00c609041c4810b40f0841c0c0039400d09840f0010701600c19810b13034508021851840108222941c005010203406070070790305480074884c3c102111498603260340b03010380e10000e00720540c1440070503105401c0d01405120024008680103400403070b00801502408012441e4085004410010100b002280d44046042125101c41840155810960051000302c9850950340064400365004204081c8100c0c20032240d100d45003043c02001c42c1c0700300d50311800c40d42c1c2c03240212a034900742d8203012500040940800d082110340740504100d030840b070b040c040c4010b103150144000d50540f507035008106c801031000c101c43c0d495034441400f91600340550040c1c00e14078000340c02022444000141461030703803501400403204d0780b954907002030b1600a03a54040c1401a04200081109800e043d080349115254000e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 414906951 1250 414905701 414905719
    0x70206070b0703020304061d0d050706060e070f0306080a020a120f0210050702041413140c041e1811060a0e130507170c03180a0213150b090f01050306 66
    0x15507001007560084952802083e4084280300c02d03c9000d100300145404085511840e91f002c03c40aa907440ca80c00000c0300402c41c0000310b20b000c0201940103040103003400c0c4045911030900102c0a80080242070f0b904002902d0620005580b10700010040d4009030044c0c00440041e00307040c4176009200310101c00761060300750b1034001401078552140c0d0301345014143c0c0e521600c60445104000c00da9000c4802d000351a0040400d20a80d104011504a0125485440c034206e44154206190070300020303031040c951091510b00309050300c0862807050201491462400c004200180440312142c140b83e603400f51400d54080c5d40c0c2c81403418241e00600f001e4405007840c41c0307082480c0c0300083c01c0c0b0460a611100c03642c3c07210144948280c01078044200380e11480800c8806161440d001085030100a10068000c0c103207440070315a0090600120200340d401034503e106200480c601e00b8043c000001580300b400d4a600c500140401400042d5404208000d01d03903801c61000c24011a45900702070849580a6141 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 414908201 1250 414906951 414906953
    0x31107020d2604031e0201021005010b090406060807020a02040b0a080619110403030e0d0201110607081005060705070b0a03110711030606040c020d110f0a031e020d0503040807020607 80
    0xa40324441e6024491101a030504580107035800c400c081c41c0c0c15540c03120000780f00600008080c0702241500100310071003441c84040c5400100d240100000d03282c61418505000801d0706503500c0010502d045041c0c5081c850240d40d810102c5540e2021035181c401a001105040010b18041c1c118400582c401026484c0340b64a403426281081c0b801d540082c607840440c40b00a030f01000314002c807000c039a8040555400c051039500d0282000f0b10040d6454812904002e10f1011680030700100303541e50b520310741194003610707240001425803d805d40350070403001a101e40c0000c00d45840012125099071000241c02154070700301d41c940c45c94000b14081d80902d910303480d058400400410103044240d000d510715800d845884c2c1c05150914001410b42c500840c10a0769245030242c00290100b070707450780342ca0304168851041d4003c070f041c8580f1407010358150040412800c1810780c0051901d00c0c000040206c03024070003280744160f0740c8800700b0b070050700494070510010b40440c1c41e060181c5503690020308034500c3d09038a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 414909451 1250 414908201 414908209
    0x1b2301080f06130c030203190b0105070311070e0a0b010e030c130e010609020c160504061433091504030309061b0f081c15090c140a0906020f0105100603110702 70
    0x90300704c1e40c00040d81c04400c03c103080c1603001100c1d40c40b0b103203140c082001c90315030b80c002804c078030070041c0c0901841304400301200c0501d41000440020300020042c0001800d1201841010f000c04040c1540016400c15569030140740128100e00c06600092415020348507204508010301030489108585540e0741600260103512400200340102d01040079202d440c1c100c0080b000000d825400c203071300032441d081c4103000c1c00360f01000206e40d0312000c81e0304a41c4801ca030300c603103426101c2c05803489094078030700403060f0101c0d51100060041004201c401c0007010240c1005640d40b07028900c4090002441f00c40c0811126016511200032843d42078000840c401a9031200300102c3c0a4503000c807040800003500c2c840b541d0903003e244030402000d01080c02600015000d41509180901484031820b58454005030024060180380d5640d90440701e0301d68440d90f48910103411410326224038805402800402c44800030180301c0c2503c1840d00e0b24903d502ca90a00b0b4084004041c040601132072914100140c0d8050780d6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 414910701 1250 414909451 414909461
    0x20613060806030708161a090a06031b0309050d0c140f1c050a020d030c120504050c1810060c0c080a0605060a080f0a06181b2301080f0613 61
    0x480761100002410310105040ca44252688508482d07041315071032801010440503410226050410b003051090349420010314071344201d180195000142c5c040c001580d9406402c40c40071b140304c412101d40840f500060035010b030303261648024805d13042035600c4050340c1c0c001c101c40da02050040007003100c0743d400802104c0c50145500900e54250b44488100c01c80c0c1d510049000c00410b210346012410b140c50306101a42c0ea03042c01c4a03200606480b900041d451f90300c5941603051880d6000e030284142c0c10036080003900c441c1940000e80c00340d0301d20402c0410080d07450004078002c241c1c80c020482c1003403404000b01c07900303500440e0440704004230f65030000d40b00100304240ca10260103007000040e941081020080c8003c1e83d0792040313501e80c001121004010001159002599411040c04a408550b44841c0ea18030001c00c130300109000125107064182c03414a035960004d6448550506094462010a190389034121400c060b00080c8010300296030760706840d0545421550141c10f500344010003002d102c0941b2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 414911951 1250 414910701 414910709
    0x1e02030d0203030412030b06090420071a010f03150f02070602070812010e01180216060c050406020c1e0d020d060c2325050312150906030c0a060c020613 67
    0x190020042c8001d100702c51800107005a000e04003045070a480750045001d50160b40071251065594082f4080341040c0c0031440308070158001e0031a542c401251800740b08031580c4007011401c0351300c900b001003803800054a00c10705a98216940408006445413503001070b00d8010052403070103800780292000298140040c01e0824450740ca51030f1580d1190764400c006003c1680600b1040d000000104130f0401845812900880d11280140e0365041175490070403508110350300102001c1c584410003044075400405003007030b02d0740c41d806d1310481d51048082042c6071680000c540401c0c5803045014510703180c20044541810310280030000c1a00040e25840c007210b004003040008501081a54800c10031890b007001c88480040e201181081ca4190640e40c0f4803040c002d00200c60100d070804d40301481000c0095400e440c0070b01040b4481440c0101c0c0701643c0c2c20360007103003e0241c95010003082c003d140200d40b40202e444082c1c81d0490b090316154045030b03060301c801002d0383c000e13904210460100303029002441c050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 414913201 1250 414911951 414911953
    0x50d030b09100515090a150c05190210030b133b0c01180810020d0b010e0f0f04110408010506011b050606060901090e07030507020c0d02060301031e02030d02 69
    0x400ca15824400102001012000200c00c00c120611039503607081e41403810071811100c1503444001281c08108220075a400a80800c40c1070303050030444a030b0051600183d07511440c252103a4001c94401030648441c40c042c000c2d032260310301104960407031080d40b02482014004090306881040390228004a41905070706444138081e5a2008110344c4194901e8006a24404000756400e40205681612480c061000504201500b501801c0c0401110071000c0a45240804d48408503c0c00b42441c009601800503510101c0c2809408030301903004228181481002a18004010071031208101940c00800092035001d5940c09107402008081c0011380301405254000180d1801c07c1c00c00036000c44c5040012001c00c034203a09801e00000e10100e03240d034010310309451041e220f900440c0141c880686039003040c00b801640e0001c11407030310342c140c000300d004030003903029128024508070a10101d40d100c00d0001e900180108010000602610000c1e20ba81e0340c200c000d14080851030740000d0901a06282c16401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 414914451 1250 414913201 414913211
    0x612050a0501061401080f04021203130501300e1006060509180c04030303050405030d0203041a060604270902030609101113140d0c0602070914090307140703050d03 72
    0xc21100b44995805001301a451400120050300000e03c00c040091042641c5030384580030030700310b40390b000e920034164400d40c0a032611092040e060076089d851901c50640003035910908549a00c0300f103920844244111580011002e081410f480b01400311940550040d04c10384041485600303480c031414000d4080fa5031074a903120b4291040202c0f864503e2201090310480d00144003482080c101210101c139894107011800340d4890030468154000d916003125040c0c0000104020030003d0b1098848140030180001400d480707407400e00001c0d00550050145c110522018105010714904108401c500c1c042d9010954a003581d0202c1c0c107080007170b20a07880903403000b416103003000000d009034207540803034054107410a00039102550601003a13100342c44c0220400f8440c0034054441d5550308050540110318008070590b42d202c02542e030302141c4101c0481c0340c03402c28183c0c90300da14011188c0c02030740c00100450402c1301c1912081e0079161144c0d0841d02a00c18034a000000807014008620000704903240005c13 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 414915701 1250 414914451 414914453
    0x3090a0b010510050403021003150b0703020d0c050624060f09150a0807080403050c0a0c0512030412110607050609030a110c10030b031509030a020f120405040507030612050a 76
    0x1100e900180c00480c07082d42c1c403441000e251076120054800312a011542113290710348048041c1e0042555004198164003282d401040040c1000c0c000c1003c00c1c4a40e0888515004602c4221808090902c000b456908800049840d00c040002c06c01d00da1001c0303440c48103101e03032200c1c00585150700c50780040080d070501050f070401600c1e01030541051980c80b2020341c0c0c601128250000c1844800401803030a01c8002c0001c64141807040003074070550086034007150001a07003801e0030b168030b041350b114176403080400d40d0903020b40102c00700943c6d040380c191080d410364060700c0e07944210701e500d20792140da50044000d0001201181c000c2003594043c4500c503002d190f480035004001003010404001e204104d070b00102481f0540c3d2103100d039012103480d09180005901315068000307810001006100c5096424520a02c946600f0105c0203009a8100341c0845060081141000c0c0c0c480c901e04405502e0304405000410090034190886588078800745000102251661707905102025001030903074899120884040c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 414916951 1250 414915701 414915713
    0x3090303120906060a120303021c0905011b0306030f02060702030c0d0b01050924241305090f010302060406050a03021b0a0b150d03030f09350a0c0210090b03090a 71
    0xf1340244003034424540f01400e2152034025001d000400400300b41c1e0004410700d44110048500400d54201c840c00d0111300321604006028000d074040c40c090080085884810b524060322030303a07044175030050080140ea01c00ccc2d001c000c07442c0c010700c20682c6c050088281c0081151703592074100521500c0707041000300d694140014400001c8000300381c000701c1407003124500c00c0d00c418800c03c0000502c04480c0d1070f40102c121004643e0646081840740d42c0c000c070225000e00c040616040d0326054590a035210051540c0b28912044004c01c00c0c0720294200c042040244a0584240010805400355090251034600c503e0841421010059686039042d0001c0410500b0003800e9408640c00a0351186030240522481c00000e00f800b152020040034035665010307943c0d40c14245c1c2c200d0140e5681149101c00c044090414000b1904040c40d40940b0215441d0618030b1996182e07400c0d1044040507a80345000481d25900b40201940c12103010002d005140000141040e5440d00031440b843d010030161110a0580c600a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 414918201 1250 414916951 414916963
    0x308090a0b06120a0c3201090b0a0e030709290319140102040b1b0d05161b090b01030b010c0b0a0c11060901020a0801080114010b0c030903031209 64
    0x124200360003148810010940c0245910b4002c203040341c08802c1e45244001e102d02d0000c0100008141080310480028409080b1030781c19140d00c03803c90f82c00c1c440d2141d4012296100312840105011510500042c0041c0c182400038280041a0381000c441e503019140c006403805844c0d40c000000345440b100300101e1110300000c0c43d26000c00c1c03140655011907120340081d0312947d0031a41180880e24601d580c07000d000c19500305000e040e40c0700713001315030390b0b070f299052242158804055641025810443c4401d0084001050045481d8648c0e40604203c0d910424040404030303a00c1c00c0d641009008401d11895845060102c014200d103000011629817200024043d00d5040701070318140601600381c2c0021582c0d0140b6070303621540004000a01100c51101918400581d0100d4520380c407402d4100b00352407105500500c1070000c1a01c03103d0444e0707a01d6820909130390404241005d044402001000105003e50203421249d071440c058a0500c0342200c0441c2ca9604409454034042c04004284803a962081c045 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 414919451 1250 414918201 414918211
    0x2409040f05060f0909010f1a01020c0105030108060f1b0d0b01030b0d150903020a0c060503011e05010225090207081905070302061f1701050406051501090e04080d090c030308 76
    0x42031041d440c101c000100c01c6100b03030f05454016001c000008001800070743c440e40401c0604a007c01010139125604910440d41d100c06a002d403080c291081100e40c011801d8904aa040310000d040540d1485c80c4a4a8a04050320b008452030801600c50500050b110140492030035aa0300000c49140b180c00040a442d81c00310b0042c0280780c0841100e010448000c00c1244800c14800045421005450100d1074280390304000390100c080500080380c05a4010000c50494148001100d8080107410819280e21180d100301c0e40940c0c4414080d0041c0005d10390002c100d2031000955041207030b59000c4100580e0301240c822070b40340701e00090031945500c0841001d201d10349589409424015550303400707903440340003030502c44c0c01547d1001070703403560000e28103907402070289138080610204000710300c14007034034060350100d56080c141400504260000c0c405030b04082016500d140da1140b40c0301d41c0c2600c20304041d00a8401680070003010700c0f80f2025000c2c03043d00b107200300616209a495824000c1c865400a01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 414920701 1250 414919451 414919481
    0xc080c15250e0a0803040602060103060e010204060f0e0328030215090604081305040f02030702011b09181104141206070801140f03010e011b0801080d0e240904 70
    0x36508040c010407807040c0011484a041045511001c1d00004903c0300b901d0740490b034a0311000801003292076002c00c029040340d10420091110385411034401c1c0c00c6c2c1c0100d000350800241c401c02d121a0407032240690304015030001d015a080070300c01c031010842c2d41d150480300c2919080d0307208203207023050790402ca8010303c1c100d840301e401030303c1c1424031b4460340b100d41c083c1001d0003100b000306803109c0018180010300002c02c001002000b11011903a03000001c0d4004941d0f890140d460941d45013003001d02945020599800d5946102085040c59040302141d035220303c2516940c0c2c3e0342c02c1c007400c61000180081000d0302428000e0000604207c0030400600200c4204e0b00c0950040c0081c4820175030008100e40c1507a200e8440d40380c001d0071903004104103200240e071041e40740d03081c03882d0050301000c1940580103944680f19007501840759804140d03120182803142c0b00c0d0301c0d44010001980c0c00c0c4035281841c0354030402804140d1903140324940c0d00011440349024491018002000403942c0b40030704c145c0b1075550340f8103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 414921951 1250 414920701 414920731
    0xf210c010302180d0203100203160e06030609010509090a0b04080d15122013090213020a05160318090c02070504090f11060d0204140307050f0904120c080c15 69
    0x3e000e0302001030325480124007440000050000710f6034180042e4401e880032030340c00c40d120314103406800241032000f900703c2c020039403849100d0010708010703080301e10030240600885607a03481c040a0010841008103000004d00404000790005031154868070700550103408495100c100c030744206c0e01101c860b003003400d00301c001120b41000340c0303042e00c0b60301c15a840e0001411941c6044400c1c0c0e003940500642952a804504212049a00ca6960384103180040c000e0310040c043c0c00c0901410b43c224410303c00040081801400140d10130510008150105846813409084582c00c06030303602c08881c50764014484603900e07100c030b8860b42c9034104241ca00408085070103200d44c0000e9180c44510001809001e042e005c000030103100b1907183c00c0d00304c0b5200c0303500c91011503403039030b40d000c00c035882302c100400080c468021030303400203010714005100300ca40f007000821050b4142c030b07140e41d4106044580c0c0420801d0101001442c1c003c103031a18060562844407070090082d401083e03244018030040100034065103072a013 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 414923201 1250 414921951 414921967
    0x80c1204080d0f020d0f03020706060905090111090a03082520030606330c010204030c0803031018060503060f04020306090604210302070602180a060c020303090d020f210c010302 78
    0x5540c44d07801d45d1030300b0280d40002c5500c0d0300b1000781c40307250000f80850342003142c00250303486547d00207440380030805e00800030b012040f24283c0c590b125110540e03a10440810701070010860000041807164408040307280003040002200da00170700d140d0350507903203c0002c5010fa800c1c3c2c5000c4900f0081604214050f00b440c0c0b500c20005907000350800113040e0341038441c5c409d12002d074a481441440c860100500c25403540c0b64003401c94040d500c81c0c00100c2e82c2c0d8103040c000141280000050f0383c0101d00c600b84c1600007a06000507614118442100c0c0d01042d5162180020310f52070a12000e80680315850b0042c0c802e1810740141494000f001d0074101040d400031040001041407480c003960952401c80000c00c1c44140c029003200070313005500020b030030b00d40b0024880c0c00305d10001001e480701c4101a00d9180b045a83c650050302d122018150103505500200b102c1d90301032421a014100d40c510003407040d0251000030021402400b0a4004542e4001c0061000411010108181d462202091038194a1300c40c0c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 414924451 1250 414923201 414923203
    0x30228030305030601050d0e1011030f01050607211206080604030e040515130504120216060315030615061b03050711121507080a0b0306040f080c1204080d0f02 70
    0x185220280402c50040701042c07890303204404644040c80c100d10180110310006038004c0e00c504810340615801031824041e40342801640050b00d2046d0040072b17809080d68a041c2c14040785074403a0004889c0c1c01012810488403503003800100c4035078080c070365400c551400180c08080807192140c000000e20b0384480c04000002c4c0d84903010401e250001c0d0f40124494681c131440d034120000e14490a40d1250f485100e400f00300c111030b0301c81c2e0701c201e0203024180c0f2040c0203104140d845013280c42c06600a98090202444014041c1c2c02c15203500c080040240c0116a4a0301c0d00821141c1d5000d00003001e05944208104031903020041d98400404694104800303a1550341c080c1561282103801020480c2c2c010030b09101356145440200c441c02d204064502c00c3d0341c40f80900f241d0030350840c0c0010104002c0c50114030f04062500c5148907060000d4010316041e16541ca43c091405025070049130782100400029400310000e02c0071500816a8007002a00c0d28145000380e030a0221425003c0700300040c150117820f040c3c2d8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 414925701 1250 414924451 414924529
    0x60b0409200415031e021c05010e04050307030f17071707050414131404121103090a030818120c1309020f01080a020d0c0c0302150c0406050a020106050306040c0302 72
    0x3c5a07040000d0048984103208040540c80030901c211140701155020142180402d19061403180c10b0040100fa80c032441c600608102c1500d0241a40c0d10500c00c00001034007401e00d03452130a19900f030545511082c41d25000140d070f02202c03010300161076450202c50301e090f5011b40c2a0000ca172801d001d4105030600304400f512401700303c41103103e0201c11400302c00c030030415802440406001c05040c01d862510f03003803014010b088410f1201c002044251950500075012003034840a503001801d046803a461920b40c1000742d00703c1c1444140002d004090094180e6407403000f20605503028000d0f01d21410b4084c100142c10f05812280000582800e901c0030050b51203c441800c0101d0034282240759450b0000c1e05c07030007401074661481a00707180242c2007000316048010f00c070500e0310a50803140c52001d2440c5404074110241c4030140355003828001071142078011005082d000f0740503c0001012503450700020b2510405980aa0361a02180c0c403c0c415400c14402c8214546801030040444c11446c6803022660346c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 414926951 1250 414925701 414925739
    0x4030519080c190c020301230a02030103030203030711190c080706030e071e091404060f0b0102060a050714130f050a030803010b0310092a03180206070501060b04092004 74
    0x3c41c06001c0718980c500600d4182400d90700030f0003c201040701000d00000b41c50a1404002c404506440050503400f003038000c0f01c0c1070b6981a400385045031902c080c00c4c3c545c1d0454078010011402640041c000314400c05100440300350181000c1c00c8a180307000e80d81400e00740d950300040d00f01030501c103000000005c0002d070710702250b00110b0303200d0303044800340110a0b0600d0340e5048580d44500345040084041c5281d0300a41c007541c081c44c402c12082043c01c46c172000300c4890404803030168001c00001000d4aa0b2a40301603030202d00c50405a15841480c1c101304442e511541c06000c460074414014008818000c000201400d01544c1c04001c03281517446580e420302051140301001040040041d444940c0308140000820526805000b916443c543c040c82b1290407001f0340039000110401284041d2090003035425400b03080c01400c03000c0d0030980a001690744154410f8481c0d649400002500041120041c8020070400742c0000d070100c05241e0100c00d1001d24194986030410501080c0100030762804944281 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 414928057 1106 414926951 414926977
    0x303020c0108070e040504060b1c05070506030c040e0a11190f0315030809032d0c0301092f15090405090102072307090504030519080c 59
    0x205600f10349160015070700c4803854000781015400350780c016024010104031301c464040422216050411158203e0880b1001361003030245c01d0000b00c01410080311210b240d402c080303e0680040c010ba004070700703509080d00041105500b00d603010707140070b0809403100f580304d0081459442c1050f042028070b030041101050783c480c1c500d1080c440c0250081404d4842400c00703042d52a154600e800a0755a5900752080740d0070300c00b0b541100151102c9103418a01c84988800c0c00c440b10905050300200043c0c000d0b81441409000240b40410060411303843c46078080c1c485034642110000d0025124549400c0042c90440d03900d0000200c006014507401554280420f8903441c618500302d2090540180280420300f12000ba0302c4046001d142188000a046580e0661120828022118140c47c02c40200e440001d10100740c80303a0070152003990120742051580392030710a00041c182c2c0f166040700c3d540 = true := by decide +kernel

theorem cover : BRFrame.Cov 414748201 414928057 := by
  have h0 := BRFrame.cov_init 414748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 414748201 ≤ n) (h2 : n < 414928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
