-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4264
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:03:22.724551+00:00
-- url     : https://prove2.me/submissions/2c460b78-4309-4cb8-8434-1524ae8b4ec1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 766726618 ≤ n < 766906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 766727868 1250 766726618 766726637
    0x8030a020d0c050903101a1203040e06030a08030f040c030516050f010c1a130507061e0e03060a11040b04030501090c0602060f180c040f090b060102070501090504110c0d 74
    0x128481202c04000144040050030300024102da90085071560f04140360748000315080f00003040c0e02c05c43d9070a03030300d600f41d01205c40044880880800700103002210b40e08108854543c2e100300506895000f000b01c0104100070820014a80c03003075540f5419001809103400b01100f5840c1e640f010310780f502c080c84c51207905224000412403132806000f102c41e404006e00e0b200000704210755500341c181040c0c0e15000b410850100001d4000b90500150b1059280c2041c1140c01d0180d031040090507400000181c01c2084e2165044001201d00070341207503c0c440806001040f40d6030320010814014100c2da422880d4a03041000006242c46040001c2c10203103020b8400040e405c0c88a2a1500980185074020015508400c0401c1703e40300c403002e4040d500583c08032403034101800c0301d0012401c16154100056000d46050801e0404040341d902541943d0b10524071451a500e5010040e642c80c9454825a07000070241d4001384202d04144e0080c1d0405208005101d0500c002c21541a040c12500d5400100142d502c84 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 766729118 1250 766727868 766727887
    0x616141c020c1f0608120f0903010203040b090c0d0c060c02040b04021c0f05060a050613050d0b0609240402090105040504060b0702030d03090b0a090f0c03030918180f0f08030a02 78
    0x2d2034489021400c10040101c149460f0200740c076003480f0400c040c8006d40c0800d40d0020820140e04803808624001c000b1951f0380b8040ca0144111601500c40c0e003d24171801903882c5103030403c45409006140c000a81e4000306207010011905218500340481c1c10070303182c142c80003c903103075400a805500008040a20f02c1100a5030081c121940d0000c900340c3e550400041c40143d4031140018000d4407000c1d07803140ea55802d90b09200c0d4000c8520780c89150007200c0d015621084c80482103119029100840300480d65072105c0115000000c00e010714440c2c05000018074001c02d2030194000c0c000394106049c85400d11b50f888000404844940c2e1105444010000300c2c40b045141c14000607044080905040100040c02c1d11007211168000b07141c440c6a075900c0002400340051048280d412a5021032540700711038881c41c0040c15022584503002c01c082c01c001c2a41000c0140317000f820342d1021886910b0f501940280c0318100600c80402c0b0039a6043c024004120120340c2110086124040c680400340e611042135 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 766730368 1250 766729118 766729153
    0x11b0308011401021903050901180305010516020d021b010311120a0b1e1306080f100e0a03021011130803040501080a060501121505130506030616141c020c 68
    0x101e11411500203550b00400d404602d03503142d81172601494000e0726401c003900141c030a0f40c0c1d40780400b00c40c060300c201c001040120542040d84568400515054603424516081e41e484115120550151f040400f0400d810b418000400042410502d404a910f51300c0d08814074195004c0d19810100300c01201c104604c1c00300c14004c02040c450191920001c00d402d2204132540d5002a0321102e114002004c2130940e0420507030803400143c0805d4041d0340c2c0f003240d801d0b48660390f1100002c011280ac1d080003400b509480c00420f003403642e00d425401902601c040004c01c00010144a200182c03400003d108400c5000c00e40c1001c400a00b03440c030300459860741018005012000c5c024003d241c804d007491400c4c002039078000c808003d4183c40c1e41c4041142c001580c80380b02e10507130030f411032500700d046d40660096240254004c64043c04003501520810303110195014280c10aa00328440440c01900c0b007048000714800050030380508a10a000d548086413260009903407001c0d000c031030700d944044c5c41c8070f03205140d1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 766731618 1250 766730368 766730399
    0x80901150f170f060712090b0115080906011401260c040602010e0c061603030f02030a0f2304021314010605180a180e070302180103030809060408090f011b030801 71
    0x401c005040f0202d10740c00c06503a800c0000c01d80d0701040305072182c0b100e41c00016000128201c1d80521166115a11201e03200000e803140410388000034030b4080800c14203040440c90340c0c140ca281001240224180000548000804002044a104003490743c018007580e040380c0240584002042030303a0352468600002c0c02d6500c41d40804c0d5003600245800f841540d500c4085590041c9040c121034401e01250400b90001c140b4100d11050700c0340000304000300e041403507200c91030380880c2e60802c0008481c6002107003011001c1ca51000f5558066402181c094a040712070000711052074040481c4071417044554902030f44080c1d002a0102c0c00116039064071800405860041d852f05550f40d40300180703480b00e100c64442103800442003032a036551199407044010b20004029503000390083c6000040844085000a0309100982c0014090f0010076411030f40410564011908561003500708880002003281054850040506114296130540b1000c2000c0b04110b000358000e8807010481d40c903110203007106004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 766732868 1250 766731618 766731659
    0xc0603022803060e090d0903030f03020c0106060f111f1e11030402041a031203150901080c09090706210b090a15050d0c03061505060d060302041103090d080901150f 72
    0xd62000600b51f4040c002c5000c5a4040c5446084441003180503002440780aa40c10020b508101c00411465005204581030200580e20240003525900c4a291240c0b40480b42000f480c03000f50405a041c586a0800c15480a1140c19a60b214448039a9141190714620120001030380200411055240c50b10495a40045040101b61252030b200300080c0c460103080d00c2519090300c0400860f4000c1c03072030101d420000c0c1010f40021f48650f141d245840d0f5406241000d148140d01c650005400c078800401c1d40c1c4211001c2ea1a404420782d01c508030b158004580b0039041e034000c0d0751103850500580c2c0f107116240c024621310718000355480300c618044031703074610710303003150f405203407a001d2810019121240744011642c00140004403806000441c40108401d42d0003076610950200c0c070740e03118004a60112007224401c4404000c035881d80c042d84042030004481c0327804a50082d2030709401d0240192540303907011180f280005481114011180e401c000542c21000d88451018400d00800098030ba1a100b00813 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 766734118 1250 766732868 766732873
    0xe060f06070b04020f0f0f0d051009080c060c040605041710020f0304060b01020309031f0923010609060302010c06090c05060f091c05070303140d06170610030c0603022803060e09 78
    0x1b24560007148070301c56040c010302d002d5140c865410081c050140510031711030203c2003042c0042d0140d41004070f115042034149043c81d000d1000440c0c54a1128411142115115200c2605161500001c181c01c00c03407121005845001c0c1003215172618405100604240403131000c050303228142410802c0440d55006c0096055510801c003040700ca5400095110450010702050301702d080129400340d01400101100a1401c42d440740c00c8601660000d00103510704000600802c0041e685140c0b460035510640b20190101c0c0303000c01c2c9000428055004480d04a006d015400c001daa501c4010400c0e42c0c3c0501c0c20700c1d41c01e80f4040340e80480c503d00194403041110b00316a0040c42500982c80d100c0d120b4142c0d100c02018401090201404498854261040c100c02d502c0d042101c541c1e114000007103050600b03c07510f400e01607240019004520050828207898118840c80303221070501806800030741c0001c03040d406841c00b0206c0900e00c119030141103008901c0790780e8041080ca1400041000704600039190524a4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 766735368 1250 766734118 766734139
    0x504061b05100e0a0b07111c2312010305030406090e011a0901111f0b0d12030b0409080c070303022b050715022802160e060f06070b04020f 61
    0xe10014030070b000c0c0c0c40b200200240d04043c00c900e60745032005070600101040b250404012180b41c100f10745030b81c1404208144c0307940c14111190306000301034612003180400c401d000305400d1010064503c80a0030030300c00b4501e00e0041c007840c0710f90300d28900340e0089070168030000d8103001041d0b000d031002c00105181c0c0140b07200d0b54100503a0890b000d484000c0f150300200d0104041281ea841100b6903003103841580292001d404042c00158842e18825484500240c10314001406030700309171031680d00c0c440d0410f000b05944418010120050510140c0c1c0701d40c41921003c03180c02041d1090001c261401d110001084124914600a8101a04038091521400c01c45d0b602100075407542591003100a120700d040d41c0d03100018508025842141400c41400341d00c00704800c08030505030080d44048500c040c5410400000c005001c90340c0d224401d00b180c1d03440008201c10840c02100701441600030000074041c20b9000c0c1c0c8003000c11515009030f001560b80401410920040d402c04c48421051154107403802d2881 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 766736618 1250 766735368 766735373
    0x105010f110604020d06061a040503011a0102030315120708010203090f0d0f0503040503070b0f040b0a110714070806040c0e0108030412021311160303180b01050d0602040b04060504061b 81
    0x150b410051000e8003c00341802003000b004002c1e805103001d080e144d9281c2441030f016460030980c80c0c1007402910f00961038405041d0465240000715480003805178021451544c407946c0d8148c0701c420803582140c1104d0030701441884483d0602140015245131400141c03286800e030362003441e16468540c000116080b080c881c0c40d020758042004075001c540f80c2411583c80e01c803460280d203548284280501502000400c0c030007604000140c2c80d004d5801030110115580310689200c7c00c868005d044550722802c200020f90005a03942d030900340754400c940030b91701d00b590b580000d0303820004119000c80e103180010300d0130311086080c204a40e0140c41c0036170041d4107040c2440741c41200f02c024100041c0c41180b00d82c186040011254115058070000c07404c40c90303246c1e40801c28103610400c09001c02c60100e030914100703006440d207507104c030340c41d082d0407807090220f90740f0f80424880c007141d000300e00b0b0b18115020400400c0310614100204010181682d40c50341d01d61030a1401440845204040d51600310800151000b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 766737868 1250 766736618 766736623
    0x1a01090605030c040f061d01020111031306110714061305120d1e0501090606080f01030f15060303021f09120e010e040e030301091b0c030c02270105010f11 68
    0x1551024280a640da031500f00d2141558000c550050580030141c05002c03980300da20034514401c58401c0401d40803c9401710303005900f40d90101044269104082c000610700744400c00f014280303180201c0000422a071808889541c507032000c2e00c19a000c801401345241079200c2000300545c003043c61080504058482e5072040d440d1f084080c2c003e80c41c5a40070510f01940902c6a024841b900c00c81c000281c410006c80f010b01d03002e04024424280582c0c43c203000000c0090281c0800e91180ca0294100d10480c0e0855840b0300019011840c01e8844052242079407000c064144103507400385000c0c2e002011a09031004000351881200c01003d0161802c02c0048000100c44041c2100032021074200300d100d9002c40001262010392080886500a040905040100c84080011410380b6a40030090003945640080b0035600b004c880320400004550160300800b280c40b030307202404020b100604c822107114500c040c9034428a44040e2170f1040001020041056603041125050650402c3c10241c8401d02003405594 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 766739118 1250 766737868 766737887
    0x100e070f06050d150e09010c110109081617070f020a050607050a0209190603230c0112021821060f1e0c072f03060f01050d050c100507020102011a01 65
    0x5540503260403400350300180b13a0b8030000207042c2d90b418104240c9411001c2d64060407240c00362101054405840070100d5506005440302c103030b000460585464041d80c611200c1c40e14051007518100e03400c0714202c18404d9620010100c0038022200c0c520004903600410000481d20307880b49205100400902c400200c001c181400b03d290120b86035403050380d1f000b08180c26400202d5500382400c0c60b050000c410071808181e01e100030800702d00140760314206040010398440e1042c1810340422000c2100c1c10600f130030b94004107201e480b401c0c010100703022000041800b5161080317072040701c900100318148402400b00500755100000b0012814242002400441c070440c40009242c0c9d5411154000b5000b0002ca0044032036543c0d000107050f050794041d1203c500c1f400c120b000303000c2c18203084030318070801c40c940054440e01440400300d4020059103080c041241d040c0070f10408486600aa10b0840c010307540d101e042d581c03224500d49900e40ea03040c03c0d10009084800b241410491541c00c40d00300241d43c3d9007c607102 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 766740368 1250 766739118 766739137
    0x31b0617061201290603070903080c01021c020307020613020603012903040c0509160206060d020f0d03090f0902120f1f032609030a020f01030e100e070f0605 69
    0x15503568407240301158502d5494000602d40f9801c203440c12111481da452064980f03485400780100c04002002002118442030700c50703e000841644003031006c82c1c0360000918031000384034001890518441e50b0403000c0020f83c0d4940d081c8550120410082e55010b00c12136501810307601c029040360145500145407408180038070050314048a403000b035a0300c19003000d00340c1e2100545115407070b4070b003900e4007050000756400341c10f000d81c1e040d01c01318512240c4402c2c4403401902540242c8860364409050049103c04e5180581e481a00101c240950b0744980c0002c0203024029034441c2c00060030400802c2da2252198071841c00ea5104200b0184003c0107504082d40094608153e203c0da603c3c0d030106101c0010440c41c4050780c40e020440700008010051101c0d0b101c65680c00c240002209424081c001113004808115416802c42d90524005107400812014004414100020344a4084000524040546a4010b180ca07500c85a00c141840200600b0005118071458902c1d02401c009000300b15008002d4003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 766741618 1250 766740368 766740407
    0xa0506131106131502190503090f10020601031b0b0d15060e0102060a151d01090f0504120e0103021903020714030304020a09110f03130209150f13060902040b04031b06 73
    0x50b1600034802e11074000203100c0b03200003101b0800d00381049900d0740d1040c00b82900c0780c13182900010650070117140e242c6444d00c0b00c4d0060704113031380307161900181c03030765410440241e2002d40c1030042544805107019003000c0381c0c00000002d9060b800e40700d200c944c8050341c001c0010320454408003c00785c2e900140b03070350740044030000c04680c401040d40c203101103520302e81110603600c51140000100d015908040c030b048421038402400502e2200c502d2000301c1d03500355400b505491201d89040f030854098918a4650103040c5001440c0041d51400b0000f850403119022000076000550407041c00142405201844038180107503156041550008140c80100d10034248250f490710701004c0401406030540c1c8180140241182c2d50703103001401010400b40841e022071040761408007168921179281c2c1612a109005024400354450620401c21140380c48aa014021a114400400d5000b01d900242c00101811b009881c0c64508510300110403200346151104540c10681c020010160310030100b40c1910440440d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 766742868 1250 766741618 766741649
    0x40c050c121e0a080a060e040c0b1c0c020f10110319060b1606050f0103110d05030c0f0d0914010503060d0302011407090f05061c0b030a050613110613 66
    0x202c0041150003480342d80301010041900c0e00c600382c2000f00c0c940b05550200c020080e0700c2e00e94020040c0440c06071405041e945e040041482100302c45802400c03000784103600c116820441d600800160b91003400800011b80200000e0100e0b0001003107003002e075915501e13083c0300280041c00b210405e408000d001440179880c0c5501d5244100b80fa510001c0509000a47c05039103000045140c05c08038101c0600b2101540f4110004600107450a04141070b26400364121031010743e22010003030751071000201550540000c2003400e41c030813020060071460701c0d00d000c00742040c1081c018001c1c1c104841a48140c01c1007941d160000a203aa02104a07507110340115207860a580503030800300c0c01042034050a080e1242650b05001c880c5411039030704000c4507000752080c80c83d00e40b90001c0c89114094009901d6107074900e00c1d152280c0c105e41d41c21480c2800409402c40c0e480f400360340c81d01494140c3c02c1d90002131942941c1015410f02c20a00104e2002540680e07030a854080201e0503030719a80f03030314841c13410300e12950f66 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 766744118 1250 766742868 766742887
    0x1905030c0c030a1109040c0305010207120905030d02060604050c040e0109090614040b070804061103090109020f0f060306060f070b07210b0f09090f010e0c10030b011d0310050405010b040c050c12 85
    0x31f103080a1900000215128159454441d58140080321024041080340714009098540000c40c0306c0381c42030383e5002e000c09884010a2201414000e040422034071402c1c400841d40d0648410388900900c4441c0c0003155180c0d050620104549440d0303107070741000c68540204400708103040302c40f50700724050346410309055031207040510040060b40c50200c803402000090103102041500961a1540203c8031111f01c070444600700100301031542c44140d0014030a000003540b5103810000b60003441c0103510703030320300e0012107540750118034400301c855a01240031000081d00300c55080810403441c600300c003010005455181c0018001501c3c070348107035105010303c0c0c00280b01541c05103c3c540108032440c0c000c1c8039403038100721565280e01c5042031803805420840c41040b543e91090007503450460040e140c40d032803c0074907008003200075070008401d40c25100300c000e1004051854450b1502c40c5008000018580c0213400401080d50801600030081220500036106100408a0498400070315556003658920818 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 766745368 1250 766744118 766744133
    0xa0f170102071509110402040f0b0f04170312090304050a171501080a05152203030e0d1e0e03030904090314070c06091e060804051905030c0c030a110904 67
    0xd000140910f00d80c0120628466880d040030b00407511508141c4101c0c03001409100407402140314940c20214424002c000c80c4000c030000300041110110740d58901502da01c0151000254105032079100c1e80009000d0101c00c01e81c12042d038200800304061840c00385806c00040139001c050080810403c050b039124440c03480e00b00032440c440402030711110101e41c2d4914026440d00500b4909440d0307401582800b400f40c4d02c2c0788181a1107101d11440c5110140004c10803014004200c4d0801c030103041ea90700c009060306504004540d10b02e5144d5030b40ba962045141d000c65100150b0881103414480158402e078800c0d40c001c01a00d2840d2804d071000a00301089050031101d10860020074911400d00103114000d1000c600e9070a01034602c1a1141504140c0c0c0d05ca0201d03030140c10030392507146030b42c1452003404003911550105410a02800c1200c0c00003c14201141c2480550441154158800240d40c5181d06042c8003045840004a01500a4120b2525a000f800c503110312800d21034941d8030300140030401030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 766746618 1250 766745368 766745377
    0x180a0b060409060e0c010f080103020d0b04030207031a100503031804230a050a1b02070905190e070302010806010e0906102006070e060702130e07051504090b0a0f170102 74
    0x18000340103113409030741c1081c0c884012490140c002121009064030031030140c98000d0480341d0242620110303156a8960900c3e025000d4000c50441c06400c00010100703421256051250502400040032828000b4000400c0074040d40700c203009400c00e011880308034100c5007102440500c165004a00c6400008441b120880c0f800c41600ba81341c40c4a060044554084d400a8807071000b0740c00401072100c500c11046000c03101e1009240c0141c0c0322840900031020f041e00016000080c40c3c111054400c0300c10481000c3d107a41000414650340400380800566178072003129504150b003800c10320300c50009100410312030000144045d000e0303075100e0000004940b0802d5014806d0340a069000c0c0c4006528003200d468100c00d0741c244000840d510355006861070074074211080954001c01a110f13012824001c41c01030a80d01100102d140540304000030281c0754040103038a10120014100d030343e541014030100881303220b15159405016400c0d0140b10044c0c03e416868142c1d90700b02d03404a1141d001c109401c0c0607108 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 766747868 1250 766746618 766746623
    0x260601021603061b0c032c0d05240f01120602090d030807140f0d15080a030c0501140613090c050901061101060f080d080924251d0d05030406020f06180a0b060409 71
    0x16906450018081c012515550b00035001c00313100805000209402545c03076056640c201c8010302e400041081d40c108dc00c425148601c924405420a0742c51400900054000c0c20203402248030002000b441c1c0c0da0207070300e9640000c1e007840c03030908240d80004405030b2402101d52822425072387e500b0344520307502202c3d84800145405800c035803005404c2c1c50010701034804010f088940c0d608100101c0e000024005245e44900400390100074000c15502030840a440d100d002903610b9101c0c40004a865101c102e50030b0302074401d43d160941010403000180e070854089901148021450742c0090001e03800120b81c01100703035004d28003c281602d0380702d10a030425449441604280308140308166141512a0600e84512000926100700410070007100402030805000e100014540401c03101040302c1307040b00c0c9070350310380b0182040c41e00f0724065807410b1466225400101c00b40e4000204440c14180c104030050b40500c0e03042c81e000220300461070311960303149031504c000d1004030540c00154007a00e90750b04ca28a1240c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 766749118 1250 766747868 766747879
    0x2030106051b060c03390c070e0c0702060739060305130602130b1218210306040207051b0a06260601021603061b0c032c 53
    0x140e6451000e41240d00c40e8881500702641006051036040000c50541d10503004000c04c40c3c40c0d0b41c0c4c0d80c4500191110f00ca0701d44207024040301e0054610313040d0300070142c150b20b80d600100741e600c7c2500714455180a40d507031b01c085d0015400300204900540d105054409013136054a0b035a8644019203494503c0b9607601e010052042d062614003075040103035046600040c894070600c8440c080c1c0350102102500c80032210100891984040c010000d0290380c0101640380174400c4d2032113210f44074009010389901c003810540c40040c000f0240700c0412040e00c070f040300c2d02ca0150000e010000c541d10103c038500b802400034020a10004c000641c031500c842e01291800c59129040d00c115101000150700e94038901c20f251401005403400204850740180c1e1190300001c401e100e0403103680c540b42c01c40c101e1544010881411801a0741d007019203404045441c4001d10b204a0011030441c0c903c0550903e4403103150380c44030410001091490200e900030310700e180305040704082c8110840606005001c03001c071500c011031304103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 766750368 1250 766749118 766749121
    0x6040e060c030a2a110f1f0c0201050105010807110712030f1e090b1e03040b010303030c031a1c08191805031f090203060a050601030b0a061d130203 65
    0x1412040015885200075810400010030a10300980c4256410350200481c0c0c40c1442d040c078001340c000c40d0f2200340090054104d40030b0341c108400792401c1034001844011520317144020031004d20b1190043d0401e001e905d1000708429854140000d0401c0c101a24000601c8a1074412070102d0105004030005404007514105d02d0380401d10300106480403840c02c9000181c0c2c00944285905c1e80180054507a0070b03180c1d01c1003d81070030f0041ca80d807103911481110313a00c80d4000389840c05c860140000b840c400e40c059110034480e507145041c00707001c0d90030300458502018a096003005081941230035002c16100f0958691007081d500c0d001a241c0042c2058015004180c00f003020020540e071010144101416039a48148601c000c0003044440270303080c001c043d0b25030018248803008c003040748003111505510430070100301290160007090416000344c48614041340c0310400c00a00d0b5806015000365080245e030100c1c0e589290040045c01112421721910031080c00d4000c20895550b0a813a808210700074403800c42d40c9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 766751618 1250 766750368 766750381
    0x40c0c060b010215180c09101712120c0715240e040803070c0606030809090705070b0429250c170a0306080109120810080709020306040e06 61
    0x510244041129001d040c8100a401c0354800305000c28450042c0b0b20400e4140c440f02010064254440c8014006200355200e44030165228007802c0c2c011881d040000600b9410041a003200c48040c461590150f8040062980291200301c02c8561900119496801e581ca8001500d4114800c0c2d0b5009420703180b09040130f40e459421513010500030000202d034081c544d101090001d0480345244500900c01d84020001808030391444001c55000020b480c2c8096410000d542d81812540b0903003050742d007510003140503c00e60401c00c01c0c43d034024200d42842c608001d4955222290b0043c0107000400d914001a60480030200340003003840301403c18401c55085160842c181050084880d100d405650002c45c95651010301605603054a00d8004443c81c90720045184148280e80c0300704850742c209961004001000d45080c0f1690003500c0c400d1050a404c4205030f840100f05410241c50243c010138214020420f040b0700062000480d20b86e02c5002d03132282c1c0ca4400080c0102412000711080d4050070040040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 766752868 1250 766751618 766751627
    0x50711010905043e2d0a03050a050c040312030c120207081c02091305040c03020909160603020906040306110f0c0f0d08070e06031b04090903021002071101120b040c 72
    0x18165680c0010241c00181c411003000b5110320242c04011600400100c120f035051a0f0011170700424021280c1e200d03034011250a0102da005588030070029940e40e007805007200c2540616500301c140310490505280c110348400d02441e9501c000281850b5840000b5000d142c01500c0341c1069245c602d400b19220002d6080c0019142e0141140900380007100443c44040c036042d109480c48240040e101c1d1108002c108031950040c407000d8000c0c1c07040d4014640000050752a10002d620505298002d003034040c150b031690030101620b68200c4000c1c14014420894291200400e0324101c80e0040c00204445242c8480032115101d01f00440148560003e521442c441e0009402e0b6425203000303046a64504003c10200e56801054030807600280d40d144860b880d80c5450006903401050152171308003042401900d2480c5503000d0345c8101034060301d03007803800e047c150148545940b04000c0c0c1c806524040c0641d44001d800810241242d041c032080089850025025601c69030b10004094010800310400440182 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 766754118 1250 766752868 766752911
    0x50f10050307020f160626041b0909030507050105060a1802090103020c1b03070e330409110f0613050411130f090f1401060318020415030c08060705071101090504 71
    0x209105000b07800314440195014043d81900030b428006030344232030b901c482c204042d8880310f0350082d00342c41000c00c1e0b2103141d20521810f64480d40780c42c1e560f140c081c40c101d07081d9a0020f040c51b10641d07150304c04018a0700c2544440c0075410141e4801a42c90818030010f80090003121203072601d07845400564a20300b00742d800303016010031b0118100d070f407070030740d81c0c41440425001124103030072840d940c0e4110704c52840c01c00c0880f00d0101c0303440720680d24040d88a01090860744a070009031820080804402d22a0403e1246c82a03a0b20090360901c3c9807070003001c0c0c60700382a4024480d070360056507941c1800035850b450009841004000c00e0408129581d981d00c0700b00d1803a203c0c06590909071401003014102125403244c40c64842d0890a0000260310f449400e0b80104404100c0e0b50309190300c55010801640d542c801e00d8070456003d203c290303005043d400c0c550b2800d00030342c01c1103c159010100b8092465049410355440b29400310302803031400901e0300101c1c0c140400e54011038200c4d0400141c04102005000c020 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 766755368 1250 766754118 766754129
    0x70f09020d0b031c14041809030e011b0b0601050915030916030b1b040b07290702250906090b0102010c0e0a0b09030a020a06020a0606050f10050307020f16 68
    0x610018651904043d2150043c01000a4000800c0c00a402c1d0300d01401522000030100017a850402c1d54500356802045083e410002c4442ea507a0085003c042d0420090013840000703203480f071f0107481420ba0344180300e940c40c1805070800c0e1b00c550005031319030307c01e1040795050030b00903207451012144000f1100070307500145d410091034025031204407040c00070b520f1900120303508000101070a0b05e5040d6114000982d45c40c0d0a09074201c00c00001c21384050396001820401e1180f04041c80d120126040300f60702e03845442c00c484c0c040310780200307000300c0582c0002c40300340e60003402c0445440d04c035603420707500d0041500e540445c000904240c00000d6000c0c0e1135010449030003082c0c00170b0000c220f44841c00c4965680c0000300c141e01c400d54440500c00f0700456409480100c074042c04840c83c0708259000901d0702419640300c1c03001a803080d5078900c1041710a0103500c00070311080e84c1132041e040220b40000d0420034401940d0b01081404000240442c1c420001160b00301039140c1501d04460140c04420b0b055005070044 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 766756618 1250 766755368 766755371
    0x210f02120a0e120a0f110106140103060f03020906010f0302090319050f070b0d090206040b0c0a0219050d080f0702100906090803090d0f03020a1b051503070e0103020309070f09020d 79
    0x300441d1038404206280c410460031039544c949010080d040d500b482c4100100341c20401c01000640120809100e00c0015040300a00042141c04036000107080d520703107030003008058204407800c20042e1551000076410401c00d080c070171070066040c03804030001e0007103508450b0b2510405595000e262005220640703810b0241f003d07646a41003094015070b50f40d100348900d80d07901030108942440107820f039000072a00c0b4801441da500c2d050355600d4004460708011310b001c1454100021040841c54038400e44041c02005400140000b441d010005006284501010303280d40d000150f070b44441e030050812580916070042c03c1074150008008024801100c0d07018000110781184004200f4400000588540140c010301888051890303a460613444021110110305510918604d10001403c0d000074074031141740c0401e070f101041d140104025a00034401d55100034404200107100c4138a40c05030b0b450301d41c0303082820003680e640c407848502031819031243d0290003018940d00012800c0152074009118086a0f41c50 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 766757868 1250 766756618 766756631
    0x11030405221a040c05130501080603100623180105061606090317131e080c0706030506040609020403050a20131409010e030319020d0f090c08010507210f02120a 70
    0x4140c070305110304a41b0414480003050308000d55803140042e43e170301040c0901540c00d04442143c451090b501e068120254210080380404005034108180300303002501210b1000e826216106803140c40d0206001c0c450040070000350038015000785205030200682c0c81501000380c5a01414001c041c40207500a040c860607500000c01d207040010b0000c600f000d40c10440598031030354048020742000007400422078a003c001e10070710000100912500c00103194a460108007403070451304010454225802074410f513407040c002400030800014443d0752a9910440209800d000ca0320b030501c0d402108440603600100102c1080c40d52121038104202e801180b00c9240c0068489480c1d16007a2881004004071550081c400183c1c0400940c6091241c89034902d801403400040c040b5250a40f8035442c421309042d502d0720407072000c01c14440300748401440074000030003403410407510003008418400d01c0703030b2002c0341708801c4030000307980c154000540250b50102c110f546004641d005c0b51a07100481d0800c8402e1b14005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 766759118 1250 766757868 766757891
    0x90507021b061c0912080426090607020406080601060e0901080304051f12140402011205010e1504060f09050f01080703150e0f07030c1511030405221a04 67
    0x186007460000c0100700340d08140b00d9074000e00b40d490800101e62150ba80725040c613000314855480080c1040550350310b0b502c59203031505001d08121a81c2c070301d00c02c040a00b10010008002c0da4401d454072180211102c99440309140001030203000c06030030902c5039018950000071b00036045603522801880540e511b05040c0c1c0d81d4a1451b071a80201d10600b034121003c55801d903841083c144460103a12024104900190000000002190903464003910a24003010030b0005640e00b005960080080440d8180469030510307101c00380d40440a40310003500a07c110164800e6912500920701600690510007041b9585401c1a0050042070303070081003110a40001080e185804221101500d07046807000d20480d820f0a42c14000b80f000d00e540ca40540107505038003c00751000e10035440290302844220005a0a003040c1049056980b22044184500341d40074000000c1c0102c241e41c1102c0d8210f64040c404083d040e50850600c0b240059070380840d15205183c404c000e41c90000c2a4104005c0e01d00300075044060 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 766760368 1250 766759118 766759153
    0x91c1a0a06091d0d05160c080d080a0209100806040608060906041109220602071e0312090b010512190c06180323010608030a020307120e10080703021309050702 70
    0x800040c0204d401102a00520500600081c40c03809961030703c18000c480d10791a41e0101042d690002132280d04696220307048503501074007003900b00a000790114688403501380000c1410481c90560000e101410f4000f882c0c0d65a940c2c8408020400c3c10143d422902d08010303035945a0100f10750460350f51051107069501400c2075155648035104010355801d6038010303648000c08980d0822400c448254080210600142c3c41000c1d2100341c29108583c0b40c0c42c58064540074150102d01c3e17540c0d1950601c0c0c01080c2c4049500303191210304481c0c0030303101d803001055014421802c002d108072182401068a5075000100f207a05a911400c6400c15034551110150403034100c400305040380b2014201c0c2510b680c2c0d40d002010b04642408104040000002d0116a200d00444c1540c00407085200560800b143e96424017a00303000c41007401856241070355100b4159000941d070701c03400050032003c1001c0c00001071b2469001c0d50407aa1200386c100441550580e442441c0f40107071008455040c018080c80656510a03c1e00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 766761618 1250 766760368 766760411
    0x10305060714160c05060c0c09010b0c0a060203060a080114010e0f0f010308092b05060105090708160311030c0a02100b010509100309020603010b071205091c1a0a0609 73
    0xa9641d5a2070103c41044003442503030300707481c2902c0031611400c0004403580c074030004002d0000103401411148114004005080c0d105a0002c0c0c10b8220401008942c0900441c10303540c0740d544890010703117a0302c2e2030f0046880b80c4150307001060705611f00280b52101c080071280c1c050407541c4540d9410900c1e82c440c03001100d14001a520b10907044881c10041c000207071010003420305010302411680d1172281c03c841250411003194107a400c8001c4004450003405000c1c44214050f05064038001c07440e0411030401020704000a01c50f8580f542e80612040d2707a148a42c01c8910b40c0072090401d203840f4184580e580000e948980d21040c0544a6100502d00145480c00f840e002141e05031500d90508c03200c81c0a1188504420300440109a0343c0d400e10001a910700000d54040d0078642c480b243c071460b441c600a841d102008880d103081c07250511070000c1036925131045100310410120a1901503005251030111007603010380c0e4900c8492004100704112407550b2110b07045600340320050010720301f14540800c00502 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 766762868 1250 766761618 766761647
    0x901090b2809142b08180706230f120c040b0a120e01150b0a020106082d03030f040818040911030c060a0504140a03020d060b090601050c100e1e060103050607 69
    0x8454412030060317004220540c0e1203600760a1003200c85010602450900410760054804034500c410f0181e11400302e02950700610030041f0003185480d41e8400d031903041c1c0c001c50340006004030041c3c00041c08030b9020b100b6600106104101652a099001009880d0b914130400704e0004524103052580000320501414030034600c5410360a400500388071101170789a0000003044199920b03004c0010f001c030401c1268241c5646e089071165150f030210381a135950519960120501c1d58000e01c188228984100d0145401642c8412051b6880c0482d086120403418203060751603020340341c120860306000030004140e404040880a4921002910303040011034000e1840b03880004001348810b200c801d110718215041d003034002b48040c220300e6403680064012850300c032049412035182c02c10744200d0f0405800c9181c11400908243c3d0801ea151003810341d03654000000e54802c940c4681030000d0b0900c0501c0a8440090703280080f101d45540d040100d90b4950003848201c40a211300c10000c0c481714466480c9039140724 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 766764118 1250 766762868 766762933
    0xe1f080d120510030809100315060c1b0602070b13120312060812090904050c0a24030203040f02190b04080307030801080a080712050d0f0f050901090b280914 69
    0x40c1000280511f007504550040c0c185640c41002006626215000780014001643c40341e40680d1342e880c0401d0001c000c0a044001d246043c2c0342070103a01d401060090aa8506842994862030001e0071400100d1490b80128803a01c6122600024190b106400405c04004030b070041c03040aa40d0150b2030307981c4400f90005541440107000c194014a001c0c01c99a800900a00460b0a010029000102411010350002000c0e07030a81c6056004145000401c01060034282021421481e040d100c28084585d0400001d100790850146802091145c80e40f007405418005059922a0b40341c010003541c0ba80700030800c0c0c01040640000040c100d40000340c0d10601d66000c00c11b03e0501e20140e8565211010050006043c4801400b00b03c00e51a100d01c600c03081d1110890020030400031143c043d1080b00c03400303886071616074107091009009c10500c1c100380d0380050720038105075806101c003164041031071613440c41c901d02c941c2056110350a0001c2980c45a9002c190388080d1101d408002c40030402611750703c01d0428260 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 766765368 1250 766764118 766764127
    0x1502011b0e0d02130c030c0f0e030a171c02041404090807060b06040e0907050108010501020a02030a11120f060405160f090506040209030303040b0f0702070e1f080d1205100308 77
    0x50901000d040302c00d51000c1c0803994203254201c80c040580380907001c11400a5543c400c80150140e00a0407002d100c822800c124038140e0108001c80c2d210003900d100688100c0c40c03070b50241e5200700c0c044219400541c038240044540001344980c80080e40c494462030442c07c012640300ca2040c64148141310040340e118849528100456a65801600800c2d2030181d000c0703400c1c00300290f641103000660703104000d0300000e02a001d00380701c00504000f106030001b0381154010f10311030300107840000d1110407a075040780e40c2c8400078802600041d1281e02c071210503c0c2c680241c1cac0041d404c10300009032540c0502d202c0d206032000e0300070883c1d40300002d030320740e00c19402440c8a012027000000c446a010540100c40604050b107001001004070b45142e1060f01c04650f42940703502001015640300c1e80c0035030414128409010040d2134030240048505015044128680c11403180312803140e080302000004181e480192601c5000381040580221320f210b02c00e00d1498100030004482c00c1c04801d90406503540400d019040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 766766618 1250 766765368 766765397
    0xe0c12010b0607020f0a0305060a06090f0e1f11040e011508090304030b0a02040f0e0603010e03390f0d08011401090b0d091b03140c0108012d1502011b 66
    0x1700d40c0c049403281c102170b100b50040b0100d042440824844ea00507034006c6802d030314102948085030003095401c42e038180b80c4000c0c0b01412002290b034109210508240400d8541c80c02d4a020040284009030128180002000110019aa0300340c904030b4070b16130549100680004c105890038001251000000d800800c0b041c40010300c3c0c0f45203039070000c80303118005041c244c4641c000146805181c20071180515035400b0054549000d000c6c1802560b000d001460916041840e402c1c12107801c000311004844511003000482c0a01f18014000314170990f08179826407403d5407180c1d441d003604a00d44800941007500110740307c0d80d6100c440c841c000f0107079207000700b540c9040d10306c02180d00500000025540c42c0d03901b00c0081010300115201071442840d40c0002d261651901e81050365208407001500d4110005084a81e80c11001c8681112030000e6428008503040e0f8011403911004c0c0100c284406031340b0700c00314502c801480019983d20302d0350000c000f00001c441556030303400c4048901800003542c035500c4484 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 766767868 1250 766766618 766766629
    0x80a02130b0a061110060b2b181403040810050a0207140d02100905030a03050417030a0b12010504110f0a2c010b1809040201050d0e0c12010b060702 65
    0x2034544400d030000444402040000702c1c4001e0a41c400700001d038403a004403801e0709040c032a4040700425110208401ca00c1d04528541d1805980c8001c0e14032806100b02035205075031b80b05d4084600100e004104a5041d135000103890071075074250305071040e030b0881e0b0805502101c000304503010364070058000c280303100c144200c580141c072000302034561540e02840b9080c00104011f1100c4d84182c9204058a44905650402454801c191709010046402c0024a04c08500044111240316100d4035000c21a69103074208101b201c0324008111075159800800c20010001c50742c00f081c010b070070031200c0c0c0c0852041c840300315003a03807404e03103001d00200a040700c01c44d860701e0031001c040071690303002d4008085a592812a40300721604003415188038580c2942c5000e8401b00400500c0c09840010101401d14801582999a140c240e03803006006440c100301140c196030158064801d490340201c01808a400c3d141d040e180c0b42d68030460400d0082c1c05014402c00c201d60103004a925040700600300c0350401e2900e408102 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 766769118 1250 766767868 766767889
    0x3030f040813150201060603150f05040c0e1207030302121c05060a150201020306030f120403260304052a01022d012f0301061704020a090e0d1107080a02 67
    0x200b50010701000145010105031080c040034031900006021841c015000d8140c4803490248074004020707510a05c9108400403150003950380954000078601400101600c003006c0040c41558002211103007440700b00b03400a41241901c0c031980c2500c164000003883c40245000d0b40304051b80e40090b0041c0ca40d013480e100d42c84188d200340020240c0c0911948e444920031940310f908030490050750000108041428204a50010004100e004103012494080b00c00b1460040f404002d00700302c500c0130100b400180304024004c07035498540c80266030f0704180ca4500e90720388043c03400200c100040074200036003800310240880e0740a0181c0282400b400b14040044001c81c95110704065422103820320700c601c070402d2041c0e0245030803c807061222199115151140560351101001100d1000c000511103680d200c80380c184d40c10340c02c87d4001510703201d6100280c0518081d420692a485c6054002d501c05000003c1c84000d01d10f00340c660300164081c0302c820b05c0e12592980100b03401580312147d0a0f0060600c060040e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 766770368 1250 766769118 766769137
    0x3110909070509070c0c0812040b0c030403082704050907171203100302031c02071502190b100b1e03091006080303060901060f08040212010e0118110303030f0408 71
    0x444416864500203480100309131340341c0b8002840d04a00100300500c96441e0300241944500a04100c40d44007030402451040d401001c210001c00300d4142007030081042a80e020310b0b4018030058540030210382d9080e405619034401c442400c08218403800e54101032241c0b078018099078010b06012410b14000704041c0d55000c03040c0b016441101100803206074800b0103980100d01c0c95410f85010f40c0303907004042c6450103005d562004107581394802c1510540024103001190300c20410317003440700c03116103080e4200710413856108024200b140b40340040080d8062024800c00403402010412519804092580e0290760062500b407460314040c805042072030b4000d5648282e403001141c403c00c110151903000e0320501d6103c103102d9031010090060038506072005c0c9000d8501450b010301a00c01107907005007400c002502c040c0c000ea0300070611024039030003034002a42c8500d154000784540015009842c580b40c0810070207a4140501e06620362403840c000c070841e03024401100c082c0c4c1003511241c40c3c0711242d500c1420702 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 766771618 1250 766770368 766770373
    0xa0207030e0423010e0109140906071812051c0207050a030b15060406050703020d0e010219030320030901060e0405211201091a0f0a0303051b1c030c020703110909 71
    0x111041c2e003a5244813406008008418407855240079001029101075500482490b42c2c02000c1010318640024010750041b070340d14185040a070f80041400305540c840c2c020f182000141050442409000185034030724100c13030881a4500e40d03a0140490319a00300f8080e49a00030060703c02000400c510011b49600b01d10440645400100c01e03500055141e8000c0c0d1264020030004101003090503010b0098161006080c1000606610501e00003511645125400d250020000f0900c105062099022050021000001d4a0150034510070b61000350001c0340c0c544225800d15801140d45044400210b0107594004000c0c000c9800d0a2441c2090031700b800d0400c0b1458400784040c000018a0443c0907000f804401c2c000035a0240072034003500c0301c54a42079600d02490600340400030545a4001e0341e0304498162424a44075501c001401d192a00614406c588038440d40301d0702141c48900040101342c0c402c041d201080144000c1800740e8644485200150075180d0846400115041c00b200782580140510b06 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 766772868 1250 766771618 766771661
    0x70612112101080c09040c2d0f0f08010c080f090c0310020a081003020f01180e0108061023040b010309050a060b100c38070302120a0207030e04 63
    0x6030441d04248081d024040380491004025200307082c01003d106041c01e42e0490040e02e0302e600c959443e504903104000e0704d000d2001702c2004010a210341542000f416000e50085241e88000000000c1d007540181b5102c0b16207001c00054642051054400c022400c1d200c10019a5400040d6146098014031600f410b00a40701c101120b654240030f124450340d01d150005898605c41c0304001c0070100010840124001c0a03882800542d988500100661b0360918004c2c80004a080120b407030525190f211400446500c00040358480b0302140d83c61140d150078035034140781e590b14940c0750751241c00e40d5180081421411803500701e80c10182c12801666070181008101036046075503403890f18a00490071740f80c1c2e40ea82d105c507080340e00e080c5a204a20381a2032501c00300c40724142c0c40d1810864090340f081101510040741c9500034402410481c0316201c030701003004547d40b03411400030340698403039500701e41c10f28401030002d50224000e2081ea034966402d80c0d10031300701044480a200040008100c2a0480e09840c079 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 766774118 1250 766772868 766772887
    0xa020f0613061806031523041503020103230106080406020f03090d030605040e031c090503040e06032413080c010606050c06010501030605010c111f0806090907061211 73
    0x61030700c0209190341c2d4a10421540f20600300c500101d07900050700705400d0800b03241c108116094031200b0349241c0c4454175202040c4094461034220121700d000c0c2c100d8105010030100c010b03503010640c201da0007a03d0030300c05034140003241641c1074070958905d15290150f0005006203489401c04c2c0f940207101d44801031900960703100221150f00100c5140004e940886041507072513900d406250010030003981c0900826201c0c8001c40e48901403c929520800070740301040c0c20038100e58000070412038020080d265110f803141c2440d103c00d501141c540e40240300da106008180d00d80d540b24828040240b45040b000b40d1510f05c0c02c407061442e035000c1540c810740240280a640e14081c4030300c00040400b500c60719030312207010640c1030030032005a000d64103152a240c0d08002e142d810480c464986680028210300c400c031040300294140d100c00e8904414400000c0340c1e400c000f6000500c0e2401101e04640d103000340e59030141c54964a002d80e0180f40005610810303900500050381d000300440aa481c1d8649060007801c2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 766775368 1250 766774118 766774147
    0xf06020f0309010902190810020904060906080d080108070e220c0803070213050906130303020d0203181501150323090a031209080f030903090a0e07090e0402030a020f06 74
    0x140c403544610f03599084c2441c00c61400c040084035460681c04480511450010081d4440c8080d0070950a100c0d00000c2600340303555994010009455042010400552540081c075074540180340c0752804106501c0000c038491000080e08001c0f00d038010030011140d503413545840c1c402c1c14004503200c1c5030544820f000d0f00103040e401095003d09280d07c02140c544c0101d004004c1140e401445a801f1140303801d0500c180c0d0f0318046030107940706054660340c61660a0501c0c1c02c034000c5c401d95035a541c3d800d10100902511302408524031504c215260100da064080c18400d0041401b000c1c4192010402c9a030f00c4200920702075082412807668480c1007481c1800700010040e940c031411200140b03140c000495a03030415401801ca6122600368217000c000020503942d0314000b521a05090304903910f00840014071164080040350507001c0060a1259031075500d40c500540b24400361030303000101c1d044a0001c41e2525007a0040740c4544c6c4c00034002d0003d0685602480102a040d001960b0072440800c012440070150 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 766776618 1250 766775368 766775371
    0xa17040b06010314160503060102120f041a09012304030f060b1801030b0430020c12120d090215070318062606011107060c0c05011b0f06020f03 63
    0x1600c400800e840e2000004084800244036a1041c000000900901c0d0720020914480341c810780c00c6c015546e4441400503494a503040e0341501c15000d002800120303262840c4058002c40e0115050440e00c481841007030455401460180d43c00906420307102ca8006002d04060085110301c5145945400c0c1c0f692281607000c4a12242980c00740e842c0c4007421641e007028103034a4219070712241043d1a07941190340341c00c902107000d400a0010b1806001e002c64031050703c020145901c0200c0102c40780c184000d90080d40340c10089101134030a40e0031050311804803170007040741e40100ca060310001c0e00e000c61070700707a02005011110080c0e070030406000c40c04558207074207030090205901035110301c51640ca0708080054410107035044035040010702c01e50000c0b00b6414a030b03403019003150209000650f555020040713814041d026a100f115109a202c00105c40c0d070071200703114282e409401811b10b103540b240c0c01034070310340d88041030001c42002030f001e24000304800e042545621446018054581208503408850301c1e0030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 766777868 1250 766776618 766776623
    0x5190e0f0d0b150609030d0c05070f060807080c0a02030912030c030a120f06051e030a08130905010503281a0f0601301a0a03030e091b0901050a1704 65
    0x30300010301c007001040300d11036143c8400032600e040c17501a10901007a211122081000107200b1055a0782c006c000341800402c02400084c52110508c1e546e540000f407117008160b5a000100741d40e00c0108002d110300d01c003240d0b41050b25800031341c6000301c21000d00403000c00421508040d8007052000c0c010108045c030007000e044200f640d800500072015815070302103401030360000140702d1800d41e080140392210303a401c002c1d14001e002c1e83c0006000d1b0002090903c601c6c20b50060402d240000c008000d000c04055000c107413100c21300c081009a80342d401381035031030303030b0803d00142c508103122113500300c0946040118a40e20702c22150046040c035120780c0301009840c02d641164050303509008014141d41d00221100c580c10300380018140e9840441610124038043c0501d0300d80c040e0301c034003401c1080c551880c0414108407000c0c1a00c10b07040d94904004000821401c030f0b40703101d03143c500082a0150040c20f9081c1d8210300d41000f0340e01c4c1414000054030383c1c6e030101400b4000d0001d034240c0d11214170102003a95100d5030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 766779118 1250 766777868 766777883
    0xe0c04031a0105010c20040608030d150b070807050723091f05090a0612150b01180b1c020a020105090d0c080306040203331005190e0f0d 60
    0x24254508035480d5080281c035940d00385140d0004115036a031100f00c5001c515040110429401c4100110f98030f45d090340b04040d030b00306041c40b038005008240000100500032a0910070003801d210002900202c02040c0324041c00e4000030311101021401010007803c01d43e2151003103c42c40c6079110a0034120100c0c4900e08402040404014031081c140480000d9101200181d14444400c0041c1c50b191448428000c40b80a1920100003900d603058075400b080c05800b02c42d15041040c3e01d14600500c0c501c0b4820b6400303c0741c5041c10070041d03195000744c18003104401d90320440810070341080e01003c0075070060a1480300c83c040340d2040c9404001944010003880ca001c1e40040303294903040312002d00e004030b005840e00170820300f080b0300e9021a24500c16079401c04400c540c01760341d079115803018802003d044a0b43d00301d8059184203504d031009007071080001c034400030b030b8960a0b80180300509482d54007640d400c2164195070034501d41d02081c821468028aa88000c0005c0310401034040802d0100c04031910407510315 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 766780368 1250 766779118 766779127
    0x1706010201090b040c1a25150f091e0b0703050901090f030503040b0f060607060506150c10051f030b0601210b04050901090507051c0803040c0302120714060903070e0c 73
    0x11480c2e401da030210303180c00702e06140c41d18020907500100c0d02c0525001304845841303032460808001d034800f80148c1c400303482c5400340014800d014044c0010050b807a1300300c6020f0084d10921a44d4400e41e1403d481c4243c000d800c810182c0d94900080c1d010b0f00006082d01c119558900c00c1e0400510304503c003817035242c000c2c0d46403a164a054030f420701c1c8822000d0100e07907110030080d040283d60399501e030460304e405600c400302064684641c008940300d503d148003600c02d9464040340811102c04001317880b92400ba40c44c0814002a00d407a40e11a069080003040702180611083c0c1c20310102c0e040310303840340e000041854081a050f666130310110301120202c00102030b0949441c0341000e00d29290050941041700a40208032140803030f41c0d003c0e43c580c0c151181c68020900703040c890191498600d4101e55142d00081895542d140c14613045c2c1d06201c080c00124800c01c4810910100c0e114000f59800607900c2c41c4826003026040001041942e0b040320940319814860350f000030608400240300540251503103441039444 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 766781618 1250 766780368 766780379
    0x1181a041a160216030b0a02180a090c08010608042d060510140303030603030d270303060501080c030f070e04020f131d0702070e04021c05070f0b0a1706010201090b040c 74
    0x80100b42042c8485098081d84d00307001060688001940082004e40c0060760345403d0741e8111181c248602c5401e42c05001843d0001e00300030a03811600711358500b5a51540c1c030741c0e02c1d45010307aa610380c25240a0071801c00f02407140c0b071a80f0b120b82c00c070201e2040c0c600100d2120403150344071001e41d401240c0c41c0140214880741004002402d0158001160045010b14118540100865030301e0103005403031007880d03440360030344c1805c8072041e189c8020900e400c011096106c1d243c0d090180180009104da64009420390002900b078a11607800d0702d0081401c109408416224001c0858103d0203429100358000d5082210a000301062002040d001c81c1070b07299000c0452800308003401c81000c54014a118544c0d610404c00050340c0800e00b1010369040c02028611500c460000c80c5148280003100c0345448a21142003042c004000341090484c1d203041c02c0511013580b64086031889000743c0c050200411140e16807541c40898951034540c0c019410700c00016600f2443c0c07205001e0040959081d51940300b1400280074 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 766782868 1250 766781618 766781623
    0xd02060d0614041103040b130804030b010807060c120809070522140c0301060f02100207080c07060e010c2402070803070e0f1c02120303071101181a041a1602 69
    0x840010450f0100310a0448510f0f24941c0c0c40020700080081441c0b1000a821200c0d00c6c07408884160403402d403940340c580f41d08d000030003140c003070041500340c2c0300ba1940080c90390700c0f03240c05142e65a84a064080310000514003a514a4805460300180c0d000d50300010946e80c480c4c1c2d922808400b1100d034012400c101d907001c0303081103c99980707105c0c0801107040c08000c00c0311000e10407641191140d252201c0481070f04a000c904020502c00358003039990001a8807001d00c000c020241421604081c26140f01c25a11842560044401c103c8680816031000070030010400207030800c6030719048601d282c590a03001180f050100da116140844045031702109000405910401095881000340c5040140d404403400159070364000d05c04241541001002003001c646035548118400c01d02003003107e84a00300f00d08040c1c1404900341c41c84049600e0280c4200e417421034400000e0710150040a80c0350501c00c10301c25032a24120041096400719100003480b4652a0b40c0007103d807040140c181c03641c094140000d402070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 766784118 1250 766782868 766782899
    0xd120504240c080c0f04150509030a06051602060601140c0709020c0a201e010c0203010c031d06040b0a0e0304032a0e041104020c0705090c0327030703030b0d02060d06 73
    0x1130300481e0038042c0b49884890304003110155002c09100c0120140403001c100d4051141d400c82e1601030146410100401c82c654000342e003d0700c005900c4a80040480b50120f985803030840c0d69a00249011484080c9415070b0001041d1860941003a550700b242c0b40c0860400740d030f01c08841c00c200359000014400a1003140070301070000c24000701800414141010010b0b40b005242d0802c5804e056a00061050503800303540142c84032917000c0c00a1000c000324840107401040910171a41207000d1001c0f0300e50203190046680380c400c0c2e5000c0c412008907216180b155004001d20701711400144010040880481c43d00c28104440c9034281040c1e9610398095000603084680a40c00381e038100c1c07044410b10001075002d0000c442c5110040d034006817039088a0124a01d840303865403080d0f40101c0e98900b40b00d44103422200a500c651280040708610b050700565400d6006402508454143c00601c890000644250843c0340414001411125103022070b8002944943c000ea620013011075540108100221110301c506 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 766785368 1250 766784118 766784131
    0xa031b14060310180921030e0f030d1a030a0501021c061401180f300309030b0403140f0a11010501080a230303010b0c0c030d120504240c08 61
    0x181503040007440052000a54012004900d1080c880c0c4c82d003180c680d40c071a10324243c02202903c0070f00e840b035419000d010a51610400002d04103942c99911003c00248070b0540302c00f4100540c501440290610014550b01214100121020070f480130141c0c0e003000020311060141000607501c00568800110b10054405030007031071420502d00b003101265404285c22000ca00707080c500881500f2038801c4d844500150009403020440c010301144280c0e119180384004140e0540c04000e04804040c85507491185030300040c00199166820300008040d4694541c0003486410308008140c41e2f5801070034035400070280407032400804a44104541e81c0301503051951000103000304000e50400301c0302c1e6194058080050884441d241c0080402000c600391313490200b40c004207817a01c95844442c02000759200211041ea18402d4200440702850046820f00400c0c0c80e946620402e9042144080c1c00b0348401401035a00c240122209013013486111903c801a103080080000d2220036a54041c4c449803001e402d1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 766786618 1250 766785368 766785379
    0x1230d0c030204090305180f0a092016020f041a0121092a08100c0c060509010203190e0c010e01020a1221020c03030c090a231c1109060a031b14 63
    0x52300c4058807070f0084801641c070001c0c00454500605041c2980d000301440245d10701c00300c00205032880404070807480c0441c61080300ca50704184209009c00081d40c416614a201d07148038841d0041c2c2a60150a504407603a0590380c00d03140e01010102100304440c004d40c0184d6440320200c0880000c0c00126540d4074032036014105603868141000011540e420000381512410780e55040d9100805006d980c80312180d540c000030910540c542080c100f03020f50801c0c0ca582c500c09041001d0000c0400560042841000080700109888901c0100459180101c002c210341980180c2e9400408180803070740300e0350307480d8585d02d52400c000c4e580b00410010003480001c0c2034110784140000100d140010003103d8101d11001074094860341c2c804005500e222817a802a03108200b045503507060445801c20b404a5203c00311801e2441c0c02c00c07145801c0540200000050200840415034022442d201202d583c0001001e01212189a220b5440b0044400040c0c0f2051001c0780050b030400c810703402c600c0c0880900400b940c8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 766787868 1250 766786618 766786639
    0x12303010c2a021e090924192a0f0207050622060201090c05010504120b270102090306060a050d0327170601230d0c03020409030518 58
    0xc000701440642d06450105a0a12100003120b620400081c00c0c10358004050b06030080030081901c40c841e008800480c002c8611400054a11401062610300d03105500905164103007e8048030341c2c07043c40148801d00801c0400038110640c00544078080e0b400d207440051140000c03080311210396504484c0d502800f004a10060b00c42c1d50790340860310800301c81003501e5198491502d1040725081f11108031511144409110b0000380840e4150000d0400a0140101500c00f0740c48100465081c0308900503103421081400d02e4400148900c140154000e00c00301c2c42000c05a50048070980507902099080700a80d00468486840d00d4144001d94001c0b0088500310502894080400c0039620000b0001d010300581000c0e2015080041c2c54104003070074025401542162588000f0310305200715a0922024850100041001d440c011641c070305d100101286040c00c030644008010440440c06422990308a49100000058403540074601ca200d220b515202c4c0c884440000e0050840012280701c4c0c410200085d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 766789118 1250 766787868 766787891
    0xf060e01121106090301021204150c0801230301022214010e0108070516150c0e0102032d040f08060c0702090a09050a02090405011d1b091306020301230301 68
    0x200104400c903880038502da440140b8400164180c01074001e0150035500000701d00203240a40c1c020179202e603202d910307500100d40d07048400300f0031104c0240c1028049000718006109210760b180c0110040f901c850400b44114040c0b01c04242aa004400188400144050601c00c1000600710010180618810603c942e548c1c11000900c1149540135a5040c44a040046890540716400f2120b080144030b1040340c002d070552903c041795144103c21404014508070001d80d0031445440c101d035110300705178015820000c00900540030300c01d031402c6058400c60f881042c98a420010805000140100b0712700380c80c00c03481c0100050a05100500264418004000010040e030381d0303046254120381c00f4070001840750020f140080c5088400c59010f94001a80350803c000c1003815009004c0700c161044401540d24140314501c0c1d034880045020320503505604484c03201c0d60031b042c82d52a40c013032003800f01da499002181e1110300803680207801072100d40300c02c64a610f401e82c0d040034400760114003e400030804c110058 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 766790368 1250 766789118 766789139
    0xc0705070e0108010c05071101050a0513060206040b090c1e030102040e0a020a020c060c070905181903120603111005040f0305160e061305060301020d0e100507050c0619110d0f060e01 80
    0x2351614140310001c10000b510a120b00c0658565042c0003282400c4203403181e0019566403c21541103d01382ca010b400600c20107000306513508904400b030240c907083d42c01c0f00c00d0a00c10a04603613250341c02d90740c20312000071803000c0c006c01240100e5203400010380c3d42c440c410000b41800114140c4a0060b0b200f003004c4000d845000803620111540d40750000303090785032017940240380c000d851809441403042000440280c2d81c1c40c00b076080c50070700c03a0726803020810361110001d040d0b4100f0310014010705032039800a201800e00e2001010741e5252840c00c00d00e4039440b505200c000b68020340003030300c1030345c4680d012400c0070303460311910005809640d5507000c4503d4031000040d1050409a1404885034450012034900d0702d094055500c5c400c0051014010350143c01111030b6124903a4400806c42800d081c0400e001c0360045045818000d1402e020309065602d901c98944021012264078041642d102d48151450107184050070350a60000404641032210003c900192846a000340942800c0d58004110200c5003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 766791618 1250 766790368 766790393
    0x603110a031e080712051c051009050907170d08010803030c0412050708070b180a03050c091012080a0206060a0f05010f2001140108010b0d06050c0705070e0108010c0507 74
    0x1000d102088031030f440c1468076070007086402040d00407400041c0788800e80003405070800c10210030f01081c0c0c0c2001ca0b041c07070f02980d100761082e440124154a06000d000283c3d00020340c000610b101301c85c40c1950300e08a44203031680e01d404004041d081107506d5680f207980134030b80034018100000118190300303045807120240e02c01e91041660303000070306101c281004000d00000000f00002c00540d030510343d0700c0d17400799044c3d400304019001c41c3c00e80b04000d40142c50400004001d80340c10100030002c003100c14007804208000640444045400d20200003500f211004900b140c942c844d540c010b80324031561070301030300d01100903080901c9031076240c9081c442ca110a0110204450003488d00c03aa000d0407510090703c2c41c181c0320044980e040c0344245420581c0030150481c203144ca0759101701120b9a80e84610040c04c031510b4200c0303207900981000c1d00d07201080d01900501d400000b4051850310381412607440d1443c00100b6400840517a440c500100400c61080c482c400401d44281030207403600c3c110350b45241341ca42d00d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 766792868 1250 766791618 766791653
    0xf0d0806010e2e09120507030605041704080d0f020f0c060f28020705150d020a0e09040b04020406080304051f021e01090b24130f0f0603110a03 63
    0x3518042034040c0e50ba4021403042c0c81c040040030072496100c14500a1600c90380842d207201054880c407000490301a506a40e81c170b081c1e00300300981005070450741c40c000a4007000d00140c5520401d1036240c41041c802c040244000c01040b0020104c0001c0300e2030207400d50846078200c07415500442d0000420343d4010988400701d55084400940d40c0d031202030405110701a02c0d03105503ca030103c1d40810b4079003042011004201001e502108c40341c5a8030b10410401003041c59040500840c00c0c00040100c2c000c64000d46990b5503241030078904110520040b0f54181000c0320103403a646da6410034030040d41058450b034409080424003840c034090800340403c0d00110301c0442210f020b0088174001d250f00340300380915406402d54089c1c402c910042d823012035001e0116120140c8500c0c88110100b41e1115106941004c0c5800c4564058129610f940070401d854070076a04007142113444520403124400a48241045540000742c0004e02c5d500350b00b8244004034030228080c2c0213151005090001ca10036407194000c500 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 766794118 1250 766792868 766792877
    0x8150d0b07032c03070c210303150315050f071103070206030603120f0a0806010309030e060a0320040f08062e0806040b01090f06030b010b0f0705030403060e0f0d080601 74
    0x20200602070343c8032814501010070103801050341c08a4000c401402410300540ba015005030302c80c0701354062400212511001591018008000207000b50080c88050404517003001000b683e9440d00174800740220965425160f0341c9041000d4084a586481e1b0480c01a2900002c0e01c0d0030600095a40d105d8504080d20400300880080c010365403c2003054070480b84d07a003101d5156100c010903032038035402075141100440d0300b010008444e07510038130440030701c1905940c444c0c6881d5101014080f0700e038400400107007095100d40100820304000340000740b128600302c89042d580d520b080e08020000c1c2142c3c03c04000c94110400740194114900b0171a8480283e00c400d541c0c000200b0110100d64400a40c801c0c0302501070b074000c00081c07100c1198000e040340e00c2400d090000c140180d4804044451a0100814070300000006001170304d0004003818038034090304c00103441c0401c0c60300c40701d00e56003042d40300710750182d10f948404524260038080d0b012000c900e4001804070a100d004050070811004020a0420 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 766795368 1250 766794118 766794131
    0xc0309020f0d0f1509150506030309010c0303020d062301032a0215040506040204050f040c1503180602071a040c0303050a12020c070512072301020c090708150d0b0703 73
    0x4220680040f0181e001130703084020f554196440000c0c1014100c10748003220300c400c0050207001a0f01480f031162900801552924208800544404d80c0c4280180c040640c01d0003030000284243c031480b805090030340c0500003452500000800000040101c8070b041604080b0304100300da40388024401c042d84061407a041071800604c089141c8811401109070a003a40d200f40000d00401007a440c0c015402650140010b0766201e00c00c2d9400074060320005c1030500300480411a101c000b055441880343c1510b000301c0c040000c0705c0d82d5990001c1e841001d80c2e54650000d030f81000c0110b018007506102c1c200c2005940249480d489813074440585203c09010300c4070004414685510800715000040040d100443d19214864901c503910260381c003a0320b000d240002511207200c030300010444215440348100c1a8003140304075524185404a03c0c1c190f05600c1a912025459034070119201e04c90010750741d48015910300400003840541d2030413034407802480011040d02c086075190010550008040c10049002d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 766796618 1250 766795368 766795373
    0x20f0408063c06061b0d050d060e0103020906010c29090d020d020712060209040612020a0b03220512030f071404051e0a030203012c0102120106231201090c0309020f0d 73
    0x51760b13401c000c1d02c119016598100c0c40490308200940b5141202035000c101d1641c07035000d02d141c2c002e000e01019500c610414005246907100d0142c80c10143c4c401c000d0030315000d8a14802031102c1807500c40299600101100300200c85200f0010040001513610003020b89a009043c040d444080601444450031200c58a040502c0400d8040b20040342000c0e008001c17480c0c2d103d041c61440d10502604900c41c8041071307000503000c00c00b0380640c2d0099004013004143c003032079110014200d902e0080211818002c006050010700094806144a0310071058154900d1403c81c00042c030000c041c0c0d140c8184008180020300158545202c007040039910903030700c5294040540c000843c40c040c5517100942c15801c20807d20060514000c80100c00700600108204140d011003e5900346d001d00781f083c07041c0112071001040000d2003807207464140071100003100010f003106910101154041c40c82c2d400c0d03c1c0503000c010450360741ca0717100d41000f81300540740400c0104c505a0000740241c05800006110300d240c5407500c400d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 766797868 1250 766796618 766796647
    0x1008070c140a060c030b0901030314070512160218042019090c140c0c04110d0c0903021002010c120b0a09020315190b0d020f0408063c0606 61
    0x4010300c10040b941d100340c5a14100c0003030941030040b080082c1c14010500c00f00e05021002c241a20352503280c0c100e03007a054119621054004000580c0d07244540840e820400c2050030050040f0041002882001443c0f030041c0641c070082c000f009007a4503031110400c004504640701d5180243c2841c1914240c6c10940707000a109107d142140f0080040354000014003030400d42d003c030398842400e8a4a98a003081c1050071241c03030007620b0342201990082c0c0366070095468268001c5c03c80744060f80c1079a0801d80c29825910071120200900360106003c55414000e500c3d000c580b010b00308901d0b20080c0466080017200514610b2010500301c0354984940750301406603141050030014007106c4030115200d1170015503845005540858050194040c050001405162066000c046d24001d22003280741c900c036159140029030000080510048080c4004507440e007003130103003038010f00f0b00200004030302c400d955180021190f05030602c0c03840040003038804010084445042e60045040325050307240c8087e44001342 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 766799118 1250 766797868 766797893
    0x306040f1509050609100b010201090510050a110304201215060f040c170c090a03080f0f070f03030b0405100303110a06060618120305120405070504020a0c03030b1008070c 75
    0x340140500c204224140c5d6000602154400c600d26003800003941990059080740d00c04003001c5c2264000415070b414142168102e560440580c0c4000a052159200b2440140e002910202d4511000d148692100003200201201310324040300c40f207403410814036086560b019a48000403400c40082d0000700556191800841c100c40060000d004441046000400c0640e088125500c80408800806d144183d25403d03100f980001510022140707041d45c0758400f90780c102120f0000c455070100800b140b2800640064880d60348580d1030896400d07090f240180c15a0b40d000f41c014041c03460700c82000880b0700544805c000301c82d01030505000f403003403100c0300ca801c100c42c184d03010f0611030901000044c0c40344e2108450b02403e0f03807040c40a003000d44600200241c041000c03c003034000303607081c0302a207881c18424801541061041084406440d91440810241e8015015680214402e59011020b058260080484000b402c9503408000390701070301d003e00b0381400500741400f080514000041000502c41506 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 766800368 1250 766799118 766799123
    0x3040b04030b1018050a140c040f0b071703150411030f07080f060105070204140106020a12170c1c1506030b04050103020a09090f050a080403060c05090d081303020a0308070209060306040f1509 84
    0x34903441c58454023150040d400f0380f11b816100c2403070b17010018407508094281d89280c0d0740102c00207070444611510103c19000506090000e5600c012068060343c3c0390f2085c54070010070558006e4580c43c000c1ca900703848800c010005414070181c0001c1040d010460840c1d56400102401e00d107864000350300210b4020203130003080000d649440c5001003130184c1c0028070b555416200e80011038420303404280c119a65407120280340740104603136000c142411401c40c05410a00361000444064541b00d10400c01502c4501c11081c8c10340c8000c000a1204c1a458050046a60019501070056525607030108030991042e12481410a50340d6440c00704000400c6000003d0503002411104401424246000c0c6076000344011036100d03281a42703074100f050007001906d40c41c8800514804100303e007612191190760020440e4414590070308030110041c0d0340c40d000310025501070381c0c6581d15a881441031010204001d400c030752181d4050b13001c00000602c0181b5245002e40e12035020300041511034a031030090710824500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 766801618 1250 766800368 766800401
    0x3091211150f030f0f06121506010c1b08060a0c0e09060619090e100e0708070908010e2d120d0605040e01050402041d0a03180803040b04030b1018050a 66
    0xe0140c410700502aa90245c0c14a4811070195216201004818410b02e940490650050303499400161902c0d02880c0d8405010304100020f4117460b44c40e006580e900a0b1241801e54035020148403c3c003013000880d5002c0540c14040204200382d44000d42112803450b401403040001600040c01600c491080e500d170312021039440d40480c0617480b80904900102c2c028449a01200300000d603105c004015582c00b00c452500e001001500c40190440311001d0061400042c404040c00000756160244a52081915450003410030082204101c1e0800c070f50441d0903640c0e1100d0740031351042a00300440d110340c0c0c40a010451a0382c1e048401c01d400041e0030030b58010ba601500c1d00090381c48100301904402d11581c030840341040b49462445000b010755010901124103130740710310401000a4025850f02034010700c5007010001e1240d540100a2960f0300c50340100e0549000440c00300100320380203005079000340e030540ca008034190805104c2407011002c3e8440d518400d488a0109049031a140d1048004013904001c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 766802868 1250 766801618 766801621
    0x3070512060103060b0402070f020f1f17010b04030c1502010902090709030605180d0e01090f06020d14190e01110a032105060906040209032803091211150f03 69
    0x164035803034000034801a40d129080803640f00700e5213083d100310380c08a98010081c030800c8860380c00b4018441c0d40684000e0b00280c815000c80c0c41910250340c1b002d03034903071942d83d80700020b0b001c102c20310328003207040c3e10020483c0000e020500006680005041c140c6660700802035040c0d002c108100d02400c0310440294114444806100049a1040ca080c055a0103140203000a4035544a40803601c0c0d201c1501140d185c2102614149452150a00000c3c0d41e40505d800c0c07900ea41c4a6801001c499215403007100564445240c44c0e00080d08010141c80d80d00300a681c0307604044050b289021800e032840321344402c000e41151801166800f03110020142d4540c4c0b0120f641c407240c00d1801a0018118400c7d400742901c1c0380243c8100f2005600131684074881c09000045980c80320000c0c04086e40008240540c5402000d065998480c01c202c12596820f0090701c00d12103207049405d014049805030b4014503015440952520046070030f8145400e00b07800182c59545448000182e42170781070148039010406000d0010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 766804118 1250 766802868 766802899
    0x1090e0a0c030602030f06030a02130f0207020a08060f0c0408070e0c04030818131811030a0b09150f07021c030e0708030d0c0306031509080702210d0f02030f0306030705 74
    0x501035449200c0c0151606011f88031602016a1001004030007940010f00740704004612000d03400c403094000758150098100f1040390700140711002c55802400d0b0030361094040003050700360b00c007425400030200c01c2041d203407a0400940300c0d250503090190703034045085d42000c2910710000004460066130440301403900e403809250906481703031b000d071403d601c103075641070040c401000a0300c03c203000456081c1c0404440c1405640e1680c8400b02e141c11158180928038900d4040b80b41d1740811489590b100c4090186d0130301e8028400031440b405810303008003040c0401004182d580004502c42a00701c50100a24610a42d500480241078580d0040845029000b000600402c00001400c4181d00c0f8039014800703105070400450440d02188009410340c105010440250601c40d070142c160f0f02c0c00b54400c903152080345d8000c140020f004c000407240310340c0c034154031405000f41802010079803501481c22545010320752000958034055842c0a4548210010111b60142c0d41041820020080a800c0001e45041c58 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 766805368 1250 766804118 766804121
    0x20070303150806190b27010f0f06120e0a1704240e0d050c04150e0612030906220801090302061b0706091b0f06030c0201020702060301090e0a0c0306 65
    0x80d00c210040403901e14001c0780061011901c50721610102001c00403266011400e00d0117071088200b1103401148405000103582c0320700080f200498510b5041a880394036140c188902d00409610041c1a44d185002c03c0c000d5540c0200200300355803030380c0000300c0c0d18081000c40c603080c4440014000c042c92641d07403008014100020142c4111080300c0040d0007610001c0000007482d1421603da4800125030301c0081a0790b150850030f15020900820880d03c1ca080c00c0c801050072202c61000c8240740c0601c01c0c1040143c0034403c1302995025506807601c0924181c14044640e481c002c460846209910100307550808500c0c1910f404050122a40074054150361280b4442c020403441c0c100754014024100081d940d42d40801e40d000344003644442d4240340c1503207900c80c0c100408460501b1580c00e00c0c000d00c003e812004141c1114042e0124a501c41007451800340702400701d83c44100c206007964010300490025907a010b0a80781102c00d60440418070700804004581071006030000103100703280e0f024021041c418903 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 766806618 1250 766805368 766805381
    0x70f1b03020f0f03031e10030b01080109120e03060c0f0c010f0203040b01080d0206010306051e0907080c1e0402090d021c0204150b030a0b060415080f060409020d0620070303 76
    0x210003d5590403c00c802140c1c2e141d02c4121070310510b1900d64008103070841400c000407035120300d0210045106981f29a10b0315a9200203030702807242c4c1e079110f211400900588101c00510b040309800c1c110f0401c8000c1d400f01e0303104c0e01c000b02190005003002c11002900c9804808890550703011a00800c0041200080d4200070f41060f02c6c19200000340d0b10002c2001a40001c03518000320454009289582c41e550300c2001810004040d0002061080445042d2445454025000d900a0700103008030500741917081d40760075604582184078001c2448403503611210601001001032040d90f0250340d80c009500403c01d03d02400c4402900801d525183d0b030001d9608000e502038140c4225400d0141d07894914180d000028280101982d00104201043e03a480d181e5204800ca644041e203040e0a240d0b803a001001e01882ca200301c0e002040b840000c000302c1010590003aa44000100e078108101b4140d43c02284400321b240c4401000ca90350740c6002d206c149425002001060806050036954845501d0020b014100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 766807868 1250 766806618 766806643
    0x3100906090c0503070503060f091501030809011101050105010e0d0f080304081c050609130c05120313090203010b040302011107050918011407050d1a060a23070506070f1b0302 77
    0x2c0b0060205240c90042141d0b811580024005c1840b51240c21203a18070030b4020f03040340e4980c4107a0180440700c0c0d03c2c1441c058000c40c01012610f031140d54810000d041c2447c4c140700e02a00307915001c0180060f0780c01c4905c40915410076901900050403520b0702c2296245500c0002e00300e40804000c201c10050450001c140c08134900d40d030001d0041e07002c45603505942c0251170299009002000059210451a040e1280f490040c4440c028850f52607011074114920011608110b4000007100c1e410044080d10050080c141c0d04021461585400144400f074012804007d040106240c08020110b80800021000e4100101480c00e00d080c60100e400341ca000007105074840d542044c526080c0400c840d142c0300d200320f206e0703250145005060501600148004100400322a066008a030416100ca030090003d4035095200c030112141d40c11003250070581042e50404a803001004060000365001c0b40300f035002040c60410120428000e08d06039040b207201d4a0440c0c890030313002c3c0c03158281580096285500f00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 766809118 1250 766807868 766807883
    0x4030506180d0804020109060804052b1b12050c10020a050904050601080615090d140606010207080a03120236040b011706060901021914060703050f070804020310090609 74
    0x84140c002e80d41d4103c00c440203408240e410000700142405000c06035442442001600d1402e40a21903141c0440c188c0c40e07956141510100144c02c1540d00205011710300d02c40034858581c116150b0383c0b801401801a1018002c010002c85c501d100c02c08100f0008a00c182600400d64070b94004400040c035503002201c032144198200004031300130b5401004010b025030000f030860301198400e29500316083d8000d8100340d42144601c00c8540c040f5500c07a03a01c80303403208050041d0000c0c0c213024000a2921100781c02245103500810004130010390015191842c1140d071910168449005000000c842c0c00e80c0558846134000da410760f09456003030a480390001d00411601000361029080044a0242c1c104a000f6080e1422201150640c64004080c2c41003104c140304070b4101c00754a274503650005600b1a0100c4e00301c100d0603140010380c0703030038000540e00010030300c3c04100c036251528003401110005002c040c01d000d02000402c09544090245040c0c2001812040c019000649800c400400122400b41d07520f1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 766810368 1250 766809118 766809133
    0x120f070c0e1e0106021903050d18110604060807030b03010b1818030309030429120103060c080402060301031202150709080c03120301051302090307030804090506012d050403050618 79
    0x10020a00c090f810395456034020070f00c031440b006c0826000c3d07443d9041a8103024040c804001485024040c0112081180d291031003510f0507450000185070f10407410303511580091006005040d0b201021035400152031401060206401c030109006158080056400c40452400d00d54000e000d21081030140c4603120b41c0e803100f4030617003450f0340d201e00081d21010b0031500204020400c178109010301044841242244283c0f1a00500711445c3c194080b00003480050007a40041041c080c1520400d24410340300e0600002c07a2621758001500b511050000401d0103007030451403000588204a0034014907540b081d80c28803400d1041c4042d150b400c492080604a10a810103001c136400e002c01c039041906d00348004942140d080504100042000130340b15104d0650a20841c50310740e03002c01c00035002354026040f16554a05086c03504c001d66000270051810701c51000c018010294a50004200500b030030101e010010151940444440c421580007400714810f103028042c29814038001c01380c81d0071503a0202c0300c1d0f2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 766811618 1250 766810368 766810411
    0x910050903060f040201051e093102211e1005120a050303012601021201210b0c1c02030103060507081303021903031e0b040509030705120f070c0e 64
    0x50f500304660081c0060001e01c0b48091540400103549001d1540b18071144c2010010008681118261700710025404034403502031101d0030120410030b580110015080d80741c07400207024240c045180b04e55a4041884990000b2159903c01440300707000c2448140ca41d0139070400e00010500d00e0f00303a020b0350b0311954220b8031281501800091804450740c1c0000074606680c40c241301c000b501b8881030413030801309580417a4942c91305000c1c40200040800c3ca90b40d90f4065040180d0318504440c031580c198000c440101c0c14101150185e46050303071002d0301e2900c066854054120141b0303c102d09000d801d0740180003100110402c11943c100600c5401e007a680c91800c0d035560110555010405d0340d01030050b030405076112400061250f0040401802030034049141e07011034504429250f4110700107000655103004449280ca028050a9000b09440d00114180481c5072101c0341c84045c161140344066000080c2c0c8004002e4081c1a0740003035410440d00c0603000e0340d41a0140303000c0c104488410958243d0105901c1c2d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 766812868 1250 766811618 766811641
    0x300408100e0c18130c05030d110d0c050312070311180907260717010311090130020f030f0a0605060418080703020a080f1c0926091005090306 62
    0x3004006910f02076515000c1d04540ea5507800c070000e07210604844404a256101000501803524450343c81a51450004080500308199070a0400800c400c460005011440010540c0e104012640161a0381e880b149003d600401106102c112001c20105030581e03209481510a01e10132030549103042c443c2d031148011503a4030321545034820310050761010500d80c1c0b5880c0e480030f584584582040001004a00c0803608109401d81c02203030341d140c40008504540c06c4c41a02c460040807a40182e040e0740d0015520221007c46003280d030212041c2e8400041e05546da07119030f4408502015055400d10342203031850a8032403a0084003030781da20341007001040d503d003000d1003040d02c928040039a880c040d00c050703070702c48000e075012a03419800c40c82010541000300f81e051005100c80b036864103481e41d40340e484d401644000203400c0f044410301850411040c0c0880c043d40502d107400010884220000e00c1302200e944610301948a085404c40074000e00c1d1800c0070f8000d402001c0c80c08003103084800c95943c10603a400e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 766814118 1250 766812868 766812889
    0x405070f0e090c03041e210216080706050d090f0c03020a0b16020103050402030f0f0c010e0a0b030114030307051203070e0405160f050d05040c03020909300408100e0c 73
    0x4040081000005c0c0071801c040c0c64101c0c049103040c400f584014a5440d400414011020425441003c503003401798401e80400508455144a601241149140c00c07603003078541070a0b120b001c080c00f0001400301030b6080d041c0c2c020b001959100d403104140284500300302440103410700080303005161515011444010200541f2aa60500481e8200b42c0031070350b0046014003009002260548a0303045030420341030b4184142020b0b41c01c2c200c014040c01001c0400100032400c2e010b40580034000d004000d12030084c100307080301c0c1910030f840c0c0900e42940c001408030f031070740c0b00d280d0015007a4041e41c0c2e00c801e142010345004501840150b940c00c10703410a01d03401c01080354015640403208800700700703a4499440c012640054505610b003451801c00c3c03607800c420801e5410440b022030340540b00302e1091003186440a420f5030840402d00040407100c1180034004507031102c41031928246600d040d107404449210b4811140030740300804c00c1c0c614010134100300c07501524121605103034501945804032003505003130f041803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 766815368 1250 766814118 766814131
    0x203011a030907062a050a020310141f17060105190b120c0f1810030504030807050309100204060203030603070509190b030a2910030b01030b10050405070f0e09 70
    0x1020b105292410540345140703ca8070b001900d0f4405c01241d64032000820742c1c0d141c1580540042c007080d10342481011f082469249101d80300510302a0001e05012034018810f91181c0b03440140d01c81d60485900d4000e110805511074404400c1e02c040250081c4030220b40035049600030b807038106640c070340892104644a41d60150741070140082c402d1350784031104d0020464109181c80384a503c1c0c02c070b924901502540c848480510107819905202100f403c1c600c40c0d94000c905503140400c030504196500408a0344041c0140341001004030124000d0001444020098088040c1c1156036542d201006500c9400c211601c5119006401000405040c201c900d07506c2291802c01d648032412041d5222002002c01161560f010300c5030903101e9000401b070034900241d41c0200300034000c0d140e103004a11900c0240003450b0300e0310b1500b4800e0030000596a501907a0669030310891109141c3d80c0c03480b169440300074941c8420f07800760802d82484101c0d41c002d188021920800d681c1d07050340c0500c240a002d514001614103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 766816618 1250 766815368 766815373
    0xf11040807080a170d06030c0b0a02060c090a060c03020c09010909030f0309080307031109090a02090a1203050703030504150903090f23060f1905090a2103030e1f0203011a0309 77
    0x41c0c843e544204d8000b4410422010f4000074103035202d40312000e9038034003500030203500d4600081c2184100c2c4c0403c6030f03542c441d1044503003624186469002c250703009007510500e0140801150900200360090041030fa580602074400c10541d87c0d111044800307089800b00940100741004400e94115219000b03d00d0714076040000d1a24541301c55030120000c01e01071180400c01d0100b4445116940d42c2c07207610500a85031440701503214402c0c2e0042004001c032036840100411540c144d0758002035080420f0b0b500494140c1000582a9201d04010f9421280d0164002c0d00c6840d100ea1502010b80290b05041520310040300c50211503200c220309420200e2115104410801e500005c644500d8440010061f000008610900b4040d06402c024035007140c0102940200380e001c51032003414100b01c1840b00040050072a0700400031040d80c4540902851141c0c0642056102d014011031076004200d0301c85415092803000e00ba01b2546011130000350402c5c010061052000c2d26191120012803059030b0042d0a610007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 766817868 1250 766816618 766816643
    0x503060a030209180f160b0705060103020411041521020c07120f080a020706030c05160b0a060b0d051006030c02030d24150201060906140f040f11040807080a 69
    0x1c0042204004044251210b141d1604500040c0c082c031403041c0c1c0103100b000030002041103400c1451b103192140c220081c00071003402800b0203d50000f0b1214112070301982e0001d25448024031804070b42c403d41c0c21000c80c0c1440d00381c0041c2000d9200210310800f40398000ea141601e640002c09905030721502100d10011303030001400f400b4801d0010940b182d8a441200601122402907840031a150400030285d400740c5c01c00d8104011341c54140c051501383d0703241450302500d03005801030100c0c040043e00300054031b020b1101c00054504091640004050803d1401e881d4a0706291114000505000c4079000d41070721140c003000603071030300900400da1444c2103900a581040c1001210388020101440e40500740403580400000341c1039400c0c40c88000e030980c00d04618054503ca01c01a00756020399020700070040c0740c20400c02c1840b802100c43c14aa40d8203c40b07002c1c9150b00000042c015001208518907450710704202c100c1754424510040c070441e880c40d02928003541e40d5a01544d21028240400340030b5001805 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 766819118 1250 766817868 766817873
    0x280902031003061d070e011401030c08162c0f09070206010501080a0902090c1909080d050a02010e012c0703111c12050c16050f0d030c140102190503060a03 68
    0x41004d41000852802403d0001140c1c00d91403400c3c040c0d60080c0c0d0000c1ca418010702407000900040400072800f82024400c0110307440004101e004018001d0072000d15107009691600c2c441c04040e010700c1010102807503050301504421442c10410300761288a20b89664400c0c65a06080c2c0b8a640b10b0702107a00904100c0c0e103008015660040010700420700c0b103594024000050b5904083c00d4000d1480401d26510b89014056450000c00003040010a0109000301004000d00c0000c0b618002e00192a0298540c40e108000368050241009150029420000d51040f090708000e07a44892140140004081205504950b6280d003a203003c0602000305051305001c26040518400500704c40c0301d501c0415403825503d410f0304102d11a132038480080e00002e0700443d10307503080104480301240041100207043c40c290001e00f0502c040514030303000d0718070314039800c0c00e00d80100001d50500380c01c50941548240302c808024003e500070b03210040d8011440c00c070030111900c43d0303042d24843c28000e800c0c141c0840c00c58 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 766820368 1250 766819118 766819121
    0x10f090b04030e060408010908030402100c0b0c0d2c070614030a15050d030c02090a2c0309030618010c09050112050a0f0e1b220e0c28090203100306 65
    0x4143c282e030400010000055800424442c600c00c0e98043d0f054251242850f00c10404802d5100018500f040150b001c602c0c042046a100250070044600c3c11a50b56584c140140014000e000180c18419040051120b85000a19840d1001040c00029030b4421234681c00d00350b80c121080e00484804003414400525003d505034046001c0d038488040031103032113542c1d03000109808401c4104500040340021359100b18104450f81a801c1a1009000c0c460010300c0b11184501081d0065194090a9444813081120400f402221641c2901400b07480041c40c140c1c18091880200150303102c00b540c0307000c12088026104090303c1003511816914520600e0905403104c01a0001410001807583d0b01c0a1303d114404040c800c990081450201034100c049440d00ba00c03440d6401e4a21081c0200c0c103a680151170600c00c40051a400900b1030342c0041c103004510740891804c3ca404014135002a200d841c4450200d403804c80c442240791411296100c656201c004680c01d80c04140e45034109107850030824400200c06 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 766821618 1250 766820368 766820387
    0x609010f0612051b031501080a050702030f070f121808010605130207060b090112060b04021905031503190b0a0917070203011104120309060806010813031e02060108010f090b0403 78
    0x3111311003450101c40c0e0340300003d0350040d1401c0e0305d440000341254200e540c00c0340085900c00200c40081095140c007600107074591003809045803945030300113008800c021146500c0000c0e10340061412101e500044009017106240b04101e0803800c00a800004101005004045c1501c0d00903007045441350a104c0c4040180d00b1050b022203d5544940d05000240c4480306000c0c000c000d0902070b61210911400d16004642030311030705034001c030300411000c8003d4107074100100840b0302e01d261040c0d9a9a84a0501d0036400d42000c2883e0b2500502c0b129130301e0280b04c1c05841e90010b0040c03120188540327035103031042c048402d00c6200804101650841e89488071484024007400c2e030000c3c0c00418124003150069449500c03903003142c03c0031210000038905066000744400302030409800c00b140e1a0804100180840000800d4441040c141c81e1100c4c0803d8840c1d130106000303c40d50b80c54542d05969041000e500c40200340518616036203010711280202c10180140c0c1d52280c0c00c5246481991210f440441d0841344 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 766822868 1250 766821618 766821631
    0x819050f0d21090b10061103120402092d040c290c070f031202010c020d090306110906030708040506090a030522031a010501021b060d090201020f03070b0609010f061205 74
    0x20f440e504034010a961400540c85a08011001d01e112401d00001400000c0c00e0942c2501c907900a020950312034041000c0e0940081d0100d6440100d07036100448900032282c0c2c2d01b800c1c6e11117070701d0a5100c0880f04604416a010b1403240d203082140039251451a00034400c0d9000c0581c00441420000981c49118030091080c0c01d4002c2c186c0358000e80311b80404108003015031048407825500c0400b0364200340d0a1017060002160b910151403425862071008000c080c0724000a8242e0b6598950321a031380760790000720b503003d00300900078580724508000c000c1c0c25444216401e40d443c0c01900005aa80c12002c10510155581600c0d903e051000ea01c0d054000000342d07080002d00101124804004115000300d510a002d88500144005605090009080407070b50302004031080c5403c0c4506003690369000586884558030b91b40040c185da05400102e1800109110807403180c00009101d0b0180070380105c01030312846095542150380d0340e80759000001800c86101c1d0400181490741004d848880301d4101640003107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 766824118 1250 766822868 766822871
    0x909031b0106091a01050d090809150d0f06060804110402040504090809093d1a0c0c03010b0a030b0403170108011401080a0507051c0215030702010b120705010c020103060819050f0d21 80
    0x145800116074903155982003040cbd03040c0c0114025003100d0081c010302e0101d492000003403055502d080b001805030100900028460812000403040076252035041c1c4005200082050156040500717003001664440c2c91064000c1c032690000900420840003003401d14603280da5a4101e1b03490520811151450400d1005a80310b42d07144005001002d11207036a441450110b202ca6039a0324299101e460a002809501c1c00703030341042c6150090ba6500742c04c10381260b0308070720200300c4c0d65203510b001c4804140303180d00d0301c0406002c500046458901503002d12340444943c00f190000e45d0300e0b800e5051751507000c09c40c01055940100703410300c20750a003442a68112010f0308054441c0b80d03607030b5001079610440801ca031440c8482c080104003219509010301c4002503816100b20f54500b400340fa070b1a031a40c07101c1c020b01b410301500b40c0000b021139205e6072005000303003100f2043d02c403414410980340314803003000d000c156040d114042c5a412503107400315015021030203544500d050042072402d0401840e43c644804010706 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 766825368 1250 766824118 766824127
    0x12301051c020c03071a0f060d0303090809030105010312021203100b0c10020c160510121a030a0807032c0d060914150c0f090909031b0106091a01050d0908 68
    0x10f080c20005800407a1281c40c0300c10140d03080000300380590b00001d080120000c0301d042440010f46500110f4400c1540500d801f207280829030070282980d00c40c411000ba015841c210000052040501e240240c1d180c07164255481064410b944003241d010942e080c0c640c80300224003c01210082c070005012280040c410359400e000788010400890700080c20302c0038507170072500c1d801441072001e22150340500b80c21600d5034050b41004000030810010113500b0480141d0300d41c0010220b100000308001a20002011140740030402c6c9041501600100704c11004120301c415151180d18011041c5ca04146030a4501c60b4070044000801039410f091401c00c4e1140c6556280c9640070500034104084003080c0c0c00700030500c00700038034090140090300801ea50030103a424080d9480c0440e080c0100c9610700011951059503840b00c5621a06602c102d03d00c082d220f018403d560080542c064004800321003481c1c00401207504a48505c505a2005450440c0018810051400b810146074017606845020300801400e2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 766826618 1250 766825368 766825387
    0x2010e1b0f030a03050d050705041520070623030c071509060905010504050705060c03040e06130501030c14010302120a1a0909071e030302060106081e010e012301051c02 74
    0x741102c01d41c003500011700003e00380d070841034a801119044207242c1740c120324040c98820aa00240007200c146002c000034402c45a902920708810749400c0c5001c8002c4c0e40c0750311303500c05010b841101e0341061040d920b50130740254003034941c1a0040c0c1e4400d140c0b01d12064601039055030390080c0b1f910074801269003a583d482d86640410070310702c100315040d03109100004460415080c51498070b9804e520461203030004201750302950b00c005c800d0f1401c48031517004040442e01c03880001505603c0c1d4002c07a00a00e0716207400001030100e000050411510200000102c81c08540c0044040c0d01c2041c0e841c01e100700020001c250f00d00301c40d5105401040b880c0c0c1c08a002c901d105000118010f40588070b00056030b00008042c0100c60a42007004064064201c0720b910080c0346950203502c4100500c10355050040c13110019507070001d046030b04044d00111142c0e01d40f9643e1140081042c900d0203028082400f6846000e00f20010002c25031556518016115030303041c0341034894600c42c43d1a14091807402c0030f0f001d0080c1002e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 766827868 1250 766826618 766826623
    0x80102030a0204230f040207020a081204030b0f060d030e04090501090623010807030b0933011e0b09030a0804080c3109032d0f02010e1b0f03 62
    0x92914901c000d030703aa81c5040340b4081c0c04070640b1340c1002c40030410008910b141d510818000c9105000380c60140c0c0ba001c0ca030001481c64034990340100d401d80110810001120103020003441540d108090004264840d6032001c402c17080708603041e6820142d07034020000800c1c0680781010b81c2e00030007000882d200c0703030035a102d50031340d100490111202a01c03000c811b0810f051558860000c81b094551004443d0701d40821144d50702018803020340391900080114403810028400d40f520b2007000765000d901c680d01c03040041070b00320400856101c007071081d03400070402074141440e440c1c10700c03016007201c80c1c120f0a281a54909a1005242ca03a0602c24100720380c002500c1940a80000d0215030040d02455807101c0c24406c0c00ca140c04445c030900c4510f00c52450b00c25070388640700c4594564441001500b06030381e16090310401d44021040030b200d1800321505030ce5004600200c600000300380e07a12224100740080582c01d80344448030001036500710081c12031a01024110b0181c03240c000030a808200c40a0402107030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 766829118 1250 766827868 766827871
    0x150207030f02010e0d122024040f020a030c030507050d021f0e04060303080610030209060703080604060b160201120b0a0b0913050f090d0c0c090509100c261b0a050408010203 76
    0x207001c11400030400c0ea0700401206988290b54400700070b011584030003822030a4402408c5590880040807401140501940407441081c06030302a01001c0010b40701d007801d1011155a120489840c0b0031500701080700e00307201c1d0b050391000354050b01404c00c1c000d1a164080101c940f0300322034020804014088078156580340901c000850281d21141c0044c00c0803014480c0c0c0000444c030003010325004105120b0305407039a608503082c4c0b540500c0c0807141074a40c1000280505600d034005449a24045072090710709032802d000c00e2029200b601c40001da82080300c014815a8400450306030302c0503e2200030002501d20310014580c0c0d880c0240506810380036184054100c42d001c0c4c62601208006004000d16040704128050030001c09090611301410a80d594072035204150140c1c80e041515800461524001041704682c4240003030410701007650141f100501c0c100040f4a240001c040012448601c450b0064005009078007441c4031070b1585c400c00d034400c140c60788140d4540040003810030001076651001c0c03000e035 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 766830368 1250 766829118 766829153
    0x315090b0a140f090703080d1e020c0105070903051e0a0c09150e150103090204090f05031c020408030a0c08071403030714180f030c130204150207030f02010e0d 70
    0x310544009102d49030030a0042200c8001469081400304414000070311030201da501c02c9071141d5a0f484c000041c1d020704990042c43d009c152880c25106507000907030b009040c1c4441d100008114581d6104800c5482c8000380c48050002d800121001d002c68002c3c521a01f000c4459000301e407101585692034500c200b83c00e52115500c555112011100030360300e0380402008244020368449a41009610540004a803000f01070515550b0180c440c1113480d5034000c04111a04400b11b95007284542c1080c035200e030711840c0340c607142900e488943d24600011380300741d40c03c2e035030000029030404080c40c00030b64000001c0e500640300014103000740740003d00240a010300e1084201c000d5501c0c0e09015202518918008200707881c0542e051102c00e022480036048400024011034410b80414820700c0824185490302820315040781050088032200003646c5c000b4400c03214900d40b240d89110700550100c0c1c40d101540070040245910340c5c0110090f41c0f00300c070040281c2c0030042080d90703043c42907524a03044144051b1403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 766831618 1250 766830368 766830371
    0xa180c050a06020604030545040608010207152307030c08070305010518060604320109030f030509041e0f05090d021f02040b0705070306050601180315090b0a 69
    0x901807810154010001045103000030412403c0581c0c01910030f00821481d103401426030383c43d5082120f0940d925600c2c84c02448207001c141003080315400840f000080c9610b00460034540d0000d42e041051080740c0910f500b00403c2d132518085900c500028042c1c0050449074440c85900049118490b08c400c5409911551000222812540c0c009001110020803040c1810b25020041002d5213070b454440495214540086441d03941c1c1c0d400080c0c060290750449007080f0646140500c101c04090395030443c0c060514021454581410011a51981c030703400020301502d000740909000900035005014903a03401000880e624105841c0c0d4170360009250406000640c4580c0071081d009514455a90803440450107012a0b0f4800d0801075541c883c01204940c4880c411045590044010381c140c901a0010040070384d91070302c1e01d09102d55a000280000d44e0383e05c0c5008085101b40d070150041201c840704042026070440e255442e5044000400800300c1003944e1502003003030000d0102c40303515108005a100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 766832868 1250 766831618 766831643
    0xb040608011a03011403010e0715020705090702150a020c030313060f091707030203040906030b0708070e030c011b050703030513050603220c0b03070903151a01080a18 73
    0x400a010080c1070b8041c2a1810707001201c0d1905542d0b8074203d90640300020f1651a80601c0540440d00629590b42902c07122301629001145402036000c90260020aa508030f079030040d1034100304030803900140d9414000d64400d42140192240050314240e20010803c0d006003440b180d444568107541c070840c1c0c0c420740541e140041004000d92031081034408401e074002009003d40d44c0d6500d20455204e0070031241c40b07035004100441098820000c5402800d40e1080510140340e80c0c0c40c1c8041c0168096274480d0100d00560000f4500c144611050a00c2680040c028880c81c030031803005541c03ca506203503050300207014840c4400401c0c0200404030046100e07030303030341942c881c0800704242851420b81c000d640314080410a22026601c41c2d16501c1003034501060041a4600d1444d001401030641ea0281180a0700441008401504050708404a82c0540101d05140d1143c035181c0080310340c82040d881040901c10b5000005511412515034028061a80001d10b803000701d148482e01c80010004a50408500d02e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 766834118 1250 766832868 766832879
    0x1050f0301031b21021c050109080304020f063a0c0809160303120b0409050a0305090a0f120609030504050d083c0c07050405040b070f05030c0a030b06040f0b04 70
    0x1c1c0710710000c040f540210000303616001034441d00403603243d40182c8134500708101908510446c011541840317500c80001c01540ca81e600d000c030f0b800c0e001242d003640700d03207402c5010003550706008088450134242000c075510114503014101c040c0c180c826450b0007030780c819001c101c0444500f520600400c80c803035844010403850040101e40c070b0400a6886492186030072034007000000c0c5c00ca951800110003101c0301144000300b200101d0300601280e20050321a105100108040c1500a8010288040c01f80c034080002512041c0000b640c200d64419907000d0b07134146902201041c2107a01c0a5415407003031400c10326040e40d4400050428120000c1a112a44001154030015000e1410f503140b2881e504141940c4410250803050b400c42084120350186100160200fa0107000384102e030007074000100200705505003801c200903034080840e556030110710301e411103001e03c6008400752032050003215aa140b0f00603507141c1c200c0c041c00d051030301d281d08001c083c0404105041c007401040b01400214060700d44851800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 766835368 1250 766834118 766834163
    0xa091505070c02100212160501090503041e090203060f0906040b0901081e0f06040f030309020402040e0916032021010524030a0602090d020a0f090f0e0a0308040201050f030103 77
    0x44e03040404c0d03601a0880c1c0c1c48508651056480c03a2400d040c0d1080c0000c1642000d034054035490a00428600000502040d00b4400d00c81c00400f01d01c020b549520019290704c001000c034403040e01c20030381c01005550b60140078038200c00480d074054006007020854114080c0480d070300d00401e070042d81140d0040d03d9071106075208217011110510801c0700034070401081c00601c5444172800f4001400e0311031484100c50516020390405d0b129103502400c03c640e140e81d150b200f01000030742515038812030301640401a840c01008402141902d8024082d0f828a403001820107800c81110519030307030080c003440c10b12030121100e01010103094480c04004a51440c2c24842c41c9407c16940740d8105e8400c802c44101c90f041d071000200c20781c003e6840480142c0d034001d03100010707044c407481c1e04c4000c0d400250384c24003043c007180c41d02c035130001c4490803882072101c00140c54000c0c054400c4039841856540c07009000c100440c0c42419a43c6e04980181011890004859908542035200360000c0d6011500032a0103c040d4068 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 766836618 1250 766835368 766835389
    0x6030d0302190c020d140705040f0b101b0507090209010207062109140a050a1205041a07060e0604060c1803051b031009060e1608060a091505070c02 65
    0xe180c21403412808495101a040200384620200403820021404545986a184600300e8000180501c4041c00119803a0740746158002c0c14000c44c10211001d00d00c03c42d034002c81e102c42c03200400092042a885c0c000315480d1202d420f0b8071466a9a84c1c55410204800b0301049000d854101d030050307900d80d400c0c4006440d009041c0e204000304919000110301075050094030003040c0030f1520740072800003c2400c1140004204501c084c0d042e000d4a0300050400c0307000144840e107144600c00c0020300741c8042c102619240660b00ca489401007690303070400c81e1451144001c10300d09208030300001c0c00961034030055180c000c00702c6040b0340380c4e5a1202ea600080707421010000c4c041c1c2e495601003460906541c0d8464a5005001001010581424a550141ea000c0c81202e4400300c0c43d101c00c0004002c54280500034004240380600a80554028948800c082e20801c1050b11940700c000d003104e450380400c0d44001c00c1120820b9804485070803c03401414001d00a4038000e8403a544e40c5200e0740d01900400909449 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 766837868 1250 766836618 766836643
    0x40f0f05090105060316020a120806010801140f220504080301091404031707021c030c090f081507020c1c02090f10060f020709020a1709070b030604020a0e0d0b0603 72
    0x2664401080f4540d5000100c03a4004207002c00360761600c400100c140c3c60a529110010000d012201c2801c44d4154407160180c400c0070240d0352b40301b03186da880c13800c074400319001c2c04c50540200340141c0c2042c5505001c42c0f044070050820242207658403551a2030000c480c01540c089600500001c0100b0140030319000b03400380e10409000301c030101e003070691b0094281c8402142c198040704e82d280000318950700902039250301c0b0140161f550450440080000d0052084c2008680801e48061010031224103030000300d030540d40e01300004d28000880c46480c846401000b0300032001c6100e41c2c08810055111070303101d0142d03420000b660030f0b03040102d03204101014000800600c1400c40b22000c00a00d400340d0101ea100701e038039a040c2905203614560f422402d0540a07000b40c0042c60000031890b114541c40642c1c00800d8881c501007884646070180340c03545495842c401c0700d290140910101d101ba180c40d50042100840300e084c440156401c2c2c80c003003180c051a080c02581c411107000c3c100a00307800c043c40529001c01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 766839118 1250 766837868 766837879
    0x50118030c080105091b090a050c0c0105010b09040e06040512074103070b15120f03040e060a0612020f250605060a24020102090d120215151014040f0f05 67
    0x1b40b6034070110b02e401d0030091800c01681c0c0c444020820040d0888105c07012024484024030140d80c4038401e80c3c6407540996109030043d494892030894039400400e5260285502070003500741003048c8111040c080d006450309884809901002c1c01d030300b0011104c4440340002c0c903085070708401c00d20001222005211114519250010402200001d008418031540801d51603c030490007403140c00812a441520b080903482c1d489440014210f244001015104031801d01209454a50b20001402010b4003248503003008190320114841c7c041d000c5401420170403240500345420302d4030b010303c0c0300d6038164822450382403010010f40c8401403000b40d020303c2c1da101c5815941034452520306801042c81c0394420300350041e000e03d020394510302180300f90115045800002c0c00e00c0708280060a240c081848481c00890140c07045080c040d42c61020281964130170411044545a06415541882030140d100d512103010401e0081030074000d000c00101a201a02d100300351200c0c69803c1c100c3e2980352440582040e813044 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 766840368 1250 766839118 766839163
    0x608190515070509010f2604050c0f03060a180c06030903030f0b06040b0f041a0a080708100302010e03070905010605040f09060311010c0f1a0618090601050118030c08010509 76
    0x3a0b000310032501340000a18103699940000036044900413850b070046929105902d046120341e507080704045008a0244003640e0552403954200014010803407102074050b00040001035018520703900c018204180080c0040000d121565802c01c400c031103800420200b960f421002c414550305115203802c610214404021180700300740081c0441c00741e4802c20301a1a800101701000101c04170542d00100003107020356a09007146042c0040075000325103900002444407001603041441001c04031700481080340c0b54001d00341540c00440d820546081b01c07a030180b0800c180041c480f8200d03c5180e00902075a590ba58460b0f0030300511540c2502e403584000c24041c101b903010b00105284954003544144c090811881e403041c189880d0004151204010748442c0c1362049d034200080c0c0f440310803807007614100e40d10701d200ba01d1032030140380030041034130002401d900410050049c1d5019541d500035001c05680f070788c91105c0c0d5941d5140300401e900d80001c0290b13511201400719030b52042040742048410000c902c43c10 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 766841618 1250 766840368 766840381
    0xc120b010809060c2125020102091509040902030f01050106031a0a0b0a0c080415081305100c11061302010905061e07080c030307020c12011401050609040608190515 72
    0x8602c809000e05183d210001100013240c000c0d9540c5c801c00e207003101c110b01c24502e005d408001010401e26040c50001c098003e803002e1641c0706108030b031056a8018403402081e50501c244bc0340b9074000e036941c1a0402d54403d83e0b1405070703030f08207c40b0700d100c50f1900004c5842d60408000409440b10803854014440e542070350303c03100342d84071007179202540d20307111a00b40c0301e08965108590314214840050244000010f000c100049071082c03940d85110b05891f00344664403041810034a121000c240540641c100091115542105801006284040e8682407900e00740030500d16080c00307019070340e401c0c2a09018458204550304155144000c3c1070403a03c0ca800c00c8070201030003111603407143c0300d403440b44400162303102000141d8040e42c002d11980c42c02c4980700e00d404031011b560340503d540d8070362113236014000180d200c0c130050145c40d40c041046074050003280d1a12003800b4960300171200c0541e0040e2981c43c00710b0403a201300011a2190160b4130310001c001c01e1030528500b460305200d84110502d00f0348040198 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 766842868 1250 766841618 766841623
    0x61510020c1e180903030a0b060703021b0406090f061503090231020c1e012304020607022d010f080106050706090b0a0906060b04060f1209060c120b010809 68
    0x28010340100c20002d140c0000400100010390a00c40e4000d400e184000b440100c0800002552080f011a0f40402c41458a002001000c0c012940000c0041c4e0105c40c0707159584c4a405a10004440c0292020454070384452007402035880740080907a516564140401040c1d04500100c03850345150b00b802c2000041a80100da0350328010b40ca86090044821480112402e001400103524605800115280c4003e00304e05515011028000013400c803031881080c517084030611844250045048050070790080200d0109020703980280240c0e8460410304c80c80c000342e11620300c01c0c00d1180c04a08002422410f104082840e000b52241450411428003142e6080035003101115056611601344162180a1803400901800010782b0003494113a0200a1040f01110364005815052107000140215030300ca252400481c044c86c412071000508111080f19500e00801e452100d0f0003041c000403421070700b0742d251681607413845507405001405c8100440600b0b60075104e00103220000346004040c80c2406401c480c1d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 766844118 1250 766842868 766842889
    0x1091a060a02030d0c03020d2d0e0c0a0e06090a110906070807060e0d110f0d030c02030c0f1e01050f01060f0917070504051015051b061510020c 63
    0xe02032040014030101040c001c000b501c1d440c0749811024403035001c0791100100a07401c1103203025540c030f0801c024070b1200b0001d0100c1c0a208800c564103040308a0100c900b80000e46001c03800348900e4002c506001071252540850600034040f902d80d00c0032035051600c1440000c0800501d800076091900079085100b43d91882140d1000e81c003111000d440c1c420302d090641d01e92084c0500140481d01d041c00c0507078140c0000c80d001217210000d4540c1c284014030f011540da1101030385000403003680c1203c5c1281c00328500130342c04060003119920458ac140301307140d01134601e1724900604d030042c3c5034801d0340f48903801c1d100d001504601401c000000d02c001d0400c0c4980351a0084180549c1080c041104540901107100303d42d0316000746131a0314010501d0703681001e1355485110a00440780103030700780400901c100944a00700340440c0c081408020a038005140201c59079000300d071a0514116522480f002403000811210307009150000360114140044400c000708035107601203860564002c0c51800c400c90340c0380c24400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 766845368 1250 766844118 766844171
    0xc240424061211030c040902330f040e15060a030908090a0611060c0c0a1202071d0709050114072006040b030a05090625020c04061404050109 62
    0x60424019030940d903018011036000070040c101d0341d072240c00c00e1008a00803074518440039416102c0e130365094003d01c0141c07001442c010f500060039040118660b031400c808075201c1c1403094a2039040700110340702d50810b139100d03401c2d4004440012905016144814403c80d411003070482c03540c080c0c40e0035800401d5260041441c1c0006040c0d540224030b003407141c80402c40b4103a00300105503180060300e070034000d03201e100361f4208400c0c0b91090a0004568a12070411070321001c103d03100a1000807801d43d2040c00c4020500800c2045000f00d07140040c2052105526654581c80c50561400516040e00300601c0701009900c0306040081d689074960405800c24121000d00b9044803030155162480e0b650000561521517102d900900005000100c525101014600819204100f81700e01d0311442c80f183e9503a6402e4a041141c6140c3c0c5103c03074940071100d45240345030349031401607038040e4018a000804446142e0b0110b403000090019a99240c034051081a000d03001d01c1e0000c0114442a03010b81901915000c101c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 766846618 1250 766845368 766845413
    0x609070b040303141602120f10091112100207140f0a26390d02120d20031e130807030c0b101404090f030f140c2404 51
    0x13040c5c040700345900401e00781030300a0000000550a95030903070b5110a1401000040e014050010031100000d005103004207800402003c0035400f604100110304e031207054070510501c5900901d003003106107070029202c2140038603c40700340350b8041c040c3c1302c0c24064403550803040340d004130b0701c03000c00503500c1c5080b50304612035121200705d0200d20001083d10361144001206010400d01201050390003582401742c0212104150845c032804802d4039207540e82c00d00700c01e50300035070400310307640700043c8600307002c1c1c07401394004000820300f41e01c03803500070038092845001c66041680000c10051400b4050004c1d46082045049800c00307450000a20f030301340c4110361002041c500c0000343d8038007030500c64a0464035880d0080850700d089d09203500390103c030386203078400c040140c1e0b4003140c004098601442441d10721500103904810014080d0b0b0101d41680d284a082000e03c821000849011501e0001502441c800d0100914011851a000300c00400b80420510f000782105810000015031504c008640381c02c90904 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 766847868 1250 766846618 766846627
    0x40b0d021e0d05070b1803150606070f1e03020c010f09120302030c0601090603060b04090f020d170c010207050c041b050c01060b0a0c020f1c0b0a0f0c020609070b04030314 75
    0x601c0c25500540e028243c0c2c1309521010408050003001090054000c07803900184004440c14140c941030b00700b00840b95065a18002040350801c0f00042681911038080a0011300e555542c0010b2140007100354484400d00f401c01c08101a0100f227a543e024800342001005003072184801441140f15010780d09900d01c0c241c0c0e210080500810a0312811142c100540380c0030340e150f6103940004c040b58401a03822a0422500c07000c1d60520f44682211540c1007107100c14040740a8083c00351500320b01100701c03989820340414030781c0d401c280c101504900740d00348000f48e80c45003981413051800c1804c01b1802c0c8a68070780640c1130023602401c0103603a0400c1c0c050500540b5000c0b110101801442c00c2d5211000580001a00c500380c00e9000440d1400548220307918041c0051403002d000103c02ea00040b00112048070440c0400706552042069000e4400c46011a4841c801404170f401d8950065035032025134031070024032007a04410303c2441c0150810034107950902d49151030041c480385026554814403d030004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 766849118 1250 766847868 766847929
    0x90c152d11101803020607090308250204020a05040906080f070303211a030105071e0e04180606030203060108030f03040209060f090408030a0b0d2a090f0b040b0d02 72
    0x484034541c00e02c601c02c100081c5280401040c010501020b04070b0042c0194400541c2c120300a00080d01500c2c0c210003050b05280c91001d8800f07004402400c1503111401d40220701c80140e85134001031080c080e0b25034a040e1a20310308040403042c2d40d41600701c14126004021484402d100018818040366058901401c0155031562203102e15022401e026100e94103018204451144086100c001d0150950007084a176480001c212071182c2241d0401103c0104810100e58140c071542d0410505140148005884008907501c08003030301c6000411201e5589a42d0200300b945424444070b401806204007031031804980b50180042c91000038402031240c040940498400d0f29142480540d5240c003500c0000c00e401c144c14003a00c00d81040703604404041c144040c0c2001c900304400300e2624150f002d042c48003095880700074400002010000c103044541c1081d400038549071540510842e80303c2c0e2920029007182154144000c0e10441d815180c001c00c0c3c00c50504005885462619002c000510441d003450704812 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 766850368 1250 766849118 766849123
    0x170a05040e040609231b011110061a07080405090a090203060f1009060501080103020d1e1101120203070e040c1407082104051b0103090c152d11 63
    0x7500708002000d5100100400c1003815070048480a0041d08040f21900e480036094644448a00041c1256000001155495802915280901c000c141001030050040308203092030001c2e80d030904039106403031325010840d05100d0820000d070180c0e901c132a0f80ca00103260f201d450b140d204510415000b4035500300040c1c07000300940d0040c4060380c0e008041e5905030426044c0300d560620183c030149000320320200c0010301104140301c0c203801c40d0410384174100b6503881c1d43c00700b144d010242141918410b107441042d291048078002d220b0250313846496240c000070020000107155000d203c2038072000610401c1400300c1c0b10340188254104600468010442801051080310130030717142001a240f06402040c1c41f01003126100140505001d000a0800e0082c50f0003002c8401c1c01c2c8c01ea40203406038000c030800c490200341c4400c0c141d11440040c14041452440c2e80c1c1d84504807080e6600c684402200095011081c0f0b034051003c20b800e001a001c01d000c0490214204250107004e005844140301060101c4604008107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 766851618 1250 766850368 766850377
    0x30207121a0703090c0e090c01030504080d090506191505190b0409021b0303130807030c020a090e0c1f11010b0904080a020d050705070323010608011e09170a05 70
    0x18038501002904242c00041c01425500b54115030141ca10900030501d141090405440b50b140c0d1001000f0783c2c1e035094010740050801502c150785504040007030054121281c02406951403080b40203200700c1c503009885010f000805000210b90034203100e0902e82001828100301c0540703204940784c41c0105844024071526608951001040702004240060041150350151548104001d54409400000d51711542c4134402114044c056412603461200440c0042024142d150700c03900348944a00c290703070001800c800259101c039100342d44680c10021520010f10a0200e200c20968003080c0200015001d144c0c4c9040307001c08002000b1050b402060300002c01d40001d410071201400c40109400d00303084c04581948440c00e850054464291500140c43c440c8045403c10343e000800740000c903003035684020200710302041d4190709801c070500c081d052480030b12510000b0480d40000003403164012242081c480c80c8665884515850880031a0126051010700d005801075102d4903603442042c0081501d09005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 766852868 1250 766851618 766851653
    0x1305060412111203150406050d03050903070b0d020307110a0f0204051909060605030607090e040b100801050a0903030b0f0109181b02010902091b0901081b070303060f1203020712 78
    0x40c1103c0d6011940304600540c0902503031207070403a07420704401c1030106030f500c6440b4480d0021000440f03080440d118902805440c400101500c400c1ca50341c0f111544d0a8001200c100c0d006035000040c4a41c1d607800c11004124036900e18064244400d0301c0c0c1b180c0d070b040c1c4225000640502e40326400a94100c0d07111603000901c5641d04d408014407086810800001c18035409600c1c0a0312602010031805401110118211400b140303040d6203c2e61a0360396604804130240c1032041d2982e421402045e41d031420b010340352054404140004803103006040090070b8440100205024a480e45903407403580e41e2204041e03064a1105c0c0f1b60010020581559038000d03d503003403000e500c9541d0f02c240300d90656819000861100c0c0200c07400540d9031600f0b505044900007030380710750100725020400e107000f6501840740d19030f10000f042503d110304103042c05003c949034018102240043d555410920075100741100107030181012a440f41c600803c95079020790360b040e65008613122201c04030520020410380721496100440e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 766854118 1250 766852868 766852873
    0xa180210050c0d08100f080304180902090a051506090102100e0f0a2906010c020d0501060306050118050c0306060909101805060f01020a0b01090f11070c0806130506041211 75
    0x1450764030002d050f03004c04d6a401d4503018521030700044d04102c0c03039100b00c00d481d6a14007451505c0c1c80c0c0070428907030318846641600103980b2050851b015035169000c06104a14100c0003103207a00e440e1500182950501e510b0900c119006d104a00099a0000d541506a500740c0d4000550010508501c2d18020754030000b1012031081040480c100420150f004038100117154944040842d05a004056000100c403401c1c00504041c0d02c044c09850020002800f250148000084e01610fa440302e009855098100c04100341e2000f0509070419014419550311940580c19503082d41005000200240304114040f885050080089160040d80c07a5082000700a80580b0f200441e10080a460290030211440c51140c5542d04114420b94004110402c1103a4010141c2c01c00e41e0a00304640000d000441034149500e43d0f84000041d6044c852008002030360180c000154424540849540703804402000102e907150704101c0c02d40042c070000340480d00564402a81360328119240d00c11585100041191141e51 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 766855368 1250 766854118 766854133
    0x60d1407030318090b0d06020318070906080c0105120c09130e0709060509040b0f070302042601180b06010804021201052404060305100f06030f050105010504050a180210050c 76
    0x95001510b42c8420050f44040200700381c2c0c0c500d441022281c4018030aa080b5034846500800544c0d1580219405441c44600038034071144a00420701c2e04545804c4807103003a584a206224641042103402c1442c0c10034a4401d10b8421000c0000e01c9642025145002c3c44070042081c51183d544d1200007030450340d00302c2d400c001442141c444195200101d03c2925405c51400401040da4141000d6840c45550090486800da0b12a40702e0311054480050120b0308142d82808081008014a15411000c580089040540310054014282125400400b50580780c88410062002600021541703602081c00d00340038150365510300200341c00c030806800000d019441e110411074414100d0380c004814030040756036144856520428042240c0c0d19000c0034180f40e1041c8031115074a20b540e00300c043c2b42d000c1c41c00701203402656695810500c20000e00100c500365101c0d001409a800d05225840d4000c604a10600c400c00140001482a01100c0c1c00130340218805081440d441e80a90100c1e400c91030350b001240c525 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 766856618 1250 766855368 766855373
    0xb1806180d0f060b0d1208072102030a0f0209011215030606150e010e0319020d020d030f1218020603100e16020609010605010206131b1203031b0503060d140703 70
    0x10069003c44002c0d10744100d4141c1c505045541c600711350342c0b0402080810030921005d503140d8100612000400c200c421940108900a200e6800780190280c00541c5900f48101c01e04241c8000a2a6080075841800010420ba91105115030500480300000550049440a2401346280b0382c0020f0030075400c194000400e401c004014040c0c0030310390703915881e40040c070600440d000c1d0f281c1c01e1100c1c1c1c9540400043d00c40b089204580e841d00703510003030030402d080a10f98003203036400c081d0613001d4001c5500070260322030180c0c001408a401840c491810041a0b41b0040390034400c2000d0040607000c0c2e4004000105e00822103e0740e04080e080c16038404641d40b40008103e08658142038004005001c0c950101b02600014010f0006a42058002d00030300da0300c4401206100000c5c980c15078002e5280802d0503601d218a1603944003070007500b0544280d00b0021b00300501940c600070380201885004000a41e17000d6400310961350481400c0311810001c4646050000c10580d4030301d00c7c1c5009004180d000000c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 766857868 1250 766856618 766856633
    0x1d0a0222112a0c01120b010903052401060807090e0a020c070b0309070e0402031018060f06051c050606060a021203010b0307080f040b0408090d050a0f06060b1806180d 73
    0x14040402c1d228046074000c410615180d060b8a80c005001c6442c2e04620708401685070042c1c44018018905100791a03501d40300d091828040c14599080c0106000d6108840460b4000783d0703001d07115a09000190b81885240200b1080c864490b60341205c0c2810049078504500d90102d801c00003400c000c03030700603d488200c960b0b40d0740d0081e545048903104609000404d004158021ba08c100d8004000c2c101e680500c0a4140140443c40c0c501c9440c020071000e5103000503624404d47d00a070b00e030120005506400e00042c0800700712011480d0804094400c01c80340042c00000381c85074440400e807141c6071119800382c0c003a46001402110b41403008000703c0041380014840e0040c62040f49a56200d1045445d48941c0c615262020344025007c1543c0c2030000340401c25510040001d4100034050079032421143d00e501c4d080450062086072910040c0301c142c0e00348a560f000b400301914424084070b00d000c040241d0b41540300a01529940a2540410000305000540c584005480000350180e900702006180c00007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 766859118 1250 766857868 766857907
    0xa0b1305090106050409080f0f04030b011509050409020618010504050a080c030d1806050304020d0b19050f270109080a0903060e070f0b031305010f1d0a022211 70
    0x7015032030b118000440f0700d00ba0040180042c0c002400c1868a00000d01c14160741e884402c55240c040020040000041c0e0205403103402041c00600440f184411600c004240c03075100e60100344904e0400c07108501582d5000122a104507807480301900e000c8090005031001c0c00785a00a60b40400314400019419401040303400700c511045050381c54036414810152080e20b803001c1800c803114401d00e07090007024007420040d0f41090004000c034041e089a40e6580d02a007408480804e64800848110f01e803262040c040c09800c190303d50410040e6241c0040440700d4100201d42c0b80d411a00200001e00c012082944005a183e8001d01038a075511510f41000e00303414601c1c4400c2f1003e5191219801c017403000400d081080d0340f18085031011140c5090f440c0c07015a0406001d9416000001c0c0245002407030901c160300c1c842105100108003040400000d0030b00d800c5000d0071140ca504084400700061380d9102c1e081103100300700180c50496002c0900c401c0000c00d41d106094682d4840052200750301d219951091 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 766860368 1250 766859118 766859131
    0x3040c0504150314060f0705030a06120c05042d0b0f18190c08011512050f07090503060108030a1b0609050a1502090d1106121504060614030705030a0b1305 68
    0x1414811004c02c4c240799610381c03c0301c2182c80101d0b0500800ca0141c0701d50700441d0060608180811910f80700c1c800340d00520030340801114014860f1344100f00b075080c80e00407111609030205100f403840400407041c04180c0e004484503409940d4610b0704054990300c1c085042c5481801074000c560541c06050f800700b1000042c1c030320303020b038034400d02d05010020f00c54003a034078814070302d981c0d0f5031120b910300b001039680740002000302d000717008420307000d907a98903102d1094902c40c0f10b04000c001628140350348080c14804042c4c0099009400c81801805108800070442c0e41007807080c54081d1015a981c14040300205003503070002d04007410501c0b03070300500c10300044000d000c5000d0405074002d494a44100c6d402c03481610745083c0c10106100c50703500464103044101c62540d401400311413500c2a900403040342098201c5c1c4591030070034008486000f904007481410301501031410808480000b00080401c68003004015a0412000000041100c01aa00410107221024110840400703c1c6401040500002c8490307 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 766861618 1250 766860368 766860383
    0x3020108160504030f082b1a18070c080a020c01021605180414010c08040510050405070b031306140a14010506040b18030d0f0801050306040b0a0203040c05041503 71
    0x10800001101c4076031441c03031025441c0d20745440c0c610307907822500c0c5202d0207007600d90075018001d0309107260640b1902001c003200301400e10001c221022214048481c5904c80b08084241409000d0050700d410700d0204002c0c501c0566103009542d0340d201100d1500005c00010040080424503852950f000a0f03045c0f0341e04000d0702510140440000780001001941c810300f0351204407401e51070114661880c449400c94058200e840800000520703090941e500d4100c60350004504504020a02005220004c1d820f003207608288418241070720755179560b8066005207043c607440080032800540d1001030680d100b0741d028a040c40103002051300c2462010003200d10014990503ca21245000c41c102d0b54141a03601c0204407900f02401c06480440f10b030422001d8400240f44245000401d54080041c1c210314811640c484015203100007004183d203c060344024002c1c0d208a06000004441d8655076610180203040140c030303603449007800740d410922a440306410900d081000711005441c01ca100c000c0e01e019481 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 766862868 1250 766861618 766861621
    0x30a080c0c0a0618350a023105090303010b0a02070312091701050735040c17030408060105120a0c0306020310080318040504020d05030c03040611010516030e07090f020403020108 78
    0x884141c03404c081040598004100018800309010315801c0031201807440d0101d81c13200d05542e000c121080000402c4070404101c0c1d040045a040b0111170b0b2021189882d88c0a000d5414900b01003a80ca00040c050311036a1040443d000e545a407003000704034000c5400c4081e070703945448a0103000c1c0019003d03004019046000b504262080c071014083c0390f006101c1035403030f500e100e261032501000c150071402d50b070800c180e006c8460540d00d0040385541b0703000d14080c45142c6d54117491300c40100f0f1241c10040a000315500148070401240c1070100310907044a0060301c002110000e0346800034100032410034000e106045000001c0b090040e0340c0d0155214800200600240c644c0700c5130308070b599002d0b403050408036400d0101e00040c681440c0e04881e41103440685126444555685c515085030000480184190b0020508000a42c0c5c4041100d4007806010000c2101d401c2c1140045e91107408110f450081c1900c4240f14003000c00104141310042c00c8a0b00c0c00c0200c1c84200780b94078065171003440243d00242c1d0303400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 766864118 1250 766862868 766862879
    0x30a0c0e01110c0f0105091e01180f0e071403071e0e0d0204021303050a11010801060e06031b0d020d1508161a0906120403020615030a080c0c0a0618 65
    0x400c400d180d89000300003042d1000300c4034100803544031200411410843c0038080a4080d886180e424088c0700a981100c4402c421140001403210701f514400c009000e00e1100c0402c030a0254010740741c19a8081d41d0404010307a01d141c0b00b624400c1d01032140c2000e00c40d00104000059500440041840c41c01c00b001d41da88000340c4000319a9040b0b000b0182d5485445019440c0c01850260f004000580c0070241b6101c250790340380c848a0502d14075000c1513031540035400c1071000039a840701e482c0313014007100e00341310041110000104400c1d01000f030181c030100307500500b40319020b0762020503581040310428095564510410080d0f002c1c00715031840180541800e20080748551020038101a20014413100180091805800c007203034004040014103a86800c002d40b9041e901e074080145004040c40340011081e043c1072030002d241100060614510b82031011080c441a5000324120741c04981100900b5219103040d916142020740c0075510690041402d400000d065030803003000d01c0035881509501c003600343d42c0c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 766865368 1250 766864118 766864127
    0x52a160501082e030203010c050d0e0102070c05010804020a0302040617120c1c210501080c030705011e0215071110050705041a0706050f1006020c0901030f0f08030a0c0e01 75
    0x5031044142c812807030990760408240320042d03007035080801c8105003d03070703650782c012a00b1243e0341d010000019400250500c8a82c4140c00340c6145510054003c520b842c42a03110145045114080d680c10842c1020104066503034805111001d07503001802045050350324403c1c69a0310000191210302801254501480c0f03540c8441070703603030801d04000a040c5d00c0d414013004000602c59912143e007441522b041c9401288200c0f83c000d800840e10640014981d41002010392502c1c1c49190014803d0344880001c3c886a40e00125010300c42c0f811000840c043c0c19075000507810070364003500328032801c0d8002c82048030f885d0344840b0b074246d80710061781600c80800342c0c4007000042c2c54003168680040b0b00d0400041102e01c00080103003400c2c0d881c00003118282070941d5514019203400703840b5054284250010300035098100700c041e10080803540024030130483c0740000b08800605c14400070780b5045422258206205540c10340300c085a0b400b80070b0341d03030f0b0b03180845654009158082880c800510a8002d028180d4003d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 766866618 1250 766865368 766865371
    0x6060e0102011b0828060302040b0f180a090803042904170a0e0d060f1a1e0402040b0a09030c06080106080412030b2124010303052a16050108 62
    0xc0d40706080c41840907400c0d0313140400030b401c928444c00c40007407031080c00c0c0350320116406115081a0109070b4525500400c001c1d10742c02d4425910640f4200c0e026000f03a4bc0c1c08010041c00c3c5040d00b03262815954014501703005281e501e10160110100100700001c1210010301d000c224404034031041d0f00c1550045015001800c2102c3c010f180500082c00790411600b480054501804146009800e5889450124120070300142085032095201d0f40041d902c003800d409086a200052004401140191400a41c926003050300d2607400c1503800e4180c450f1038459030115400341007190000c81d910000007100404544081c403054034150301068003c54424411200b43d8104c0d401d5aa801d14640c0321f90f242c1203481e040c40d030394880c1856a00c040641c0c80351142102c16242d06401620007603244d01980415040090702c1c0c541c070348001c540080c80c210005401401c00d05580e01407070704035180d5810b04d04100904020140b504d054441c8000c42c414060fa001071036400e50f44a44541e078000c2c3d503030341c8010344a0307010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 766867868 1250 766866618 766866641
    0x90213060e061201060e0c0310050d03050a09080d0509150705070b0d1104051f0201140702101b0c08130308070c03121404140f041103070207081212060402190306060e010201 76
    0xc4100414002c0300a00c0c0238540082d14111030b0700e180c44e9100000b60010704221011404142d01081c0c910101d50801d1103100105410800381c0303200c1e0b11020300103080e40b0a50308500d00c10074501c1c21449130044130b5003c0c0d40c0030541c0071044808440e241c13200b00b902c5400200042d400b5506040000d941d15100c00d00b62011210080e0140100342c00340c00c070030100c501500c6400300442d9a20788694180c11610703a071140c09440103070060002c0000c200c80010a80380b500403468100009404d140e081c8562210240e41000e070030048843d00c0d40310801409920441e10b07400541940804035020b81030002d1040380a0499103da0700c80c03076400200f2581550824240d4130021110031003440100700c203d246426814048000030000441410380d140050101ca00c07500000c2c0a0034408004c1080c0d981d010071000c0d02501100d0010103213159044042e903511320580080031000461f550120360292681d40686e60440d20800481c0404403401800a008000c5845801c1c00501c1c480744240d290350040c401c01382e4459 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 766869118 1250 766867868 766867889
    0x80a020a0308030924090106120c0312050c06090d0e030c090415021204050309010e0612070f0309150903020601140901030f0f0c09051b0a0f03090213060e06120106 72
    0x51440c1c0310050541c000600c501314a00518000b00a07200341c060204200461600d08296903007040c41d203140c00c41e40c6030740003800128090b83e101c1002c00c03003101c1c0c0003044942c07025a111a0700c4138000116603030f026440940c2c443e44a500c003805403a9001081c0641e0340100380c0c0c1c80e500c4a5407420109030340c4402076803e50790440c00e8880414081541103a0782c40d61502e00385c0025107040c1100503550f019603012641a100e9400c00714600f0f581e984d01482d84000c0b0070b4100c3c0d44a040600400725890707141e50251081e402c0c00344031262078814034002c0d001401e945030415800c1c42c010b01100c0182c0060851340e103003100107000b10300010440341c1c4140c0b00d8446c002c1c00500000718903821503907181d480314540641518500d00400325400060340c2d41c0400342c0940602c0c2004190345c10840b800030240b0b03030303c4806c0f917980400a010700d0000c180c0c4407203240300100c11441e0216040d5a2400450210440c0f641440240ca003001070200746126600d2001d40104029210034154043d6001c0083c03c807002805000c0001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 766870368 1250 766869118 766869139
    0xf0608120f13080f1c200309060a030e0607091a070215030901021209071511010b2220220504111c020703020304060c031b21080709170a060e010510080a02 68
    0x181b014040000003804d00008403403a140f0034000203200b64204001d06000a40c0395460716051507024091650800c1c014148014128202500820080183c0a40c034400c40340c0850880259542c2d02e441c184031200e461400c07980c905080300c07010702075885814564800c0c40c40c2004206a100c00040742c80032103015941c4c1d80300c2c074007005a044501c0c0400190b840115901e6000ca41643c0c0e13219801c408020f4451420350144000ca48040c10035254403059603600d6100d42d0060709140903040c0c044920307a4100004200c00e03e03c48400d03d42c074402007901310603041854422020180c1e000d2000904040300c02425a00c00101c0d1070304400282d00c0344400080c010381040c0000c000345409a203d5060b0140b1a0400142d96115071005c13001c0e0000352041035a8104162500e071605a8104080c111786451501d040c401078a804c10340903090180d1807080802e201c480342444849a00288030442d80d0316071005040c86981c54410145000e0078040e00d407000400c000580005c1d84003800034401d21441d5000d0f1485000307 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 766871618 1250 766870368 766870397
    0x20604090b031509030a1202040509090106060801060512010329090d1b1a071b06150b21130c171c020615010c0f0609060f0608120f13080f1c 62
    0x44600b9084000e01f0a4081c0700200d060fa54002d0104c1c411840c02e000080c01f2460041c000f003d00038180c5c000b4013800010461107074070035903100d0b48505481d08540805512103036118880b40c0900101c0120014103401410300c80c1501d8041944121111103070744404540c3d4800c0400d04c122801d9007402014504080100d81980128170740560713200310a03081c4aa580b0021140c051080215214202e0399a035031a0310b2043d11005410191010313111900c611402e00074007070304030325032003c024003401d003815068000180b2204022900000040d8030200b80840b031540c920f03007101d41100c000303d904400c1c00350718070700c161a4007841404103070000380c1d5000309056154005c403400c80821018100c0d0402c5280d541301004101c01e2400b60740058401c0c2d400042881941c1020740480d41c01d074400030459414140c0810451400140b960f8040410700000e590320990718200030b5040c4100070229941090b20300e4001f503040000300c0c902207411000b50503a0002d01040c0400e0b8511340d92808508041035809140103207 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 766872868 1250 766871618 766871627
    0x120f180a060506030a08040605040f0905042307090e0303180f0a060b0d170c100c0c060b0406050a032105040e07110f011b0e0d030503070503040f020604090b031509030a 74
    0x20010f8002d02903502a000e40c1d00c8001065103da007242d00070600004080141c0076480d03e56000424240c801000107041c50382d030342c04004000c44072190b15880004c1d030244890312306110712402049082c808105013040c00d1700107078603508221500d604032103c0c6107803940c20500110b09000c054030180090000300c4141e41c0c8000c01032407821811070f000004c5011a00001c0c19040d01c542030303010f0022295480707115034910f02d80750a6081564100c0c103400d10720810f0a05400c806001207107079000030081019200c80c40403030001d0849a0140c1d40c402007005001050040310a04011100c02171075070550140ca03500b1054440e84a20b11403822140c94640004203090720418010240e0903030b000a071142500f5581240e420740d4004142d0303140c100144401481426002540d0341502c400c244c030010001ca00d592809400c500000f0610b205012000000a04000cc1c031800d1803040b941c000c080e59140e07502c078007070700005148803035002c0c0c040c1c4030b801c484a2a0a00c0c104050f0320403c48c4000440c5420100c0d6001c03103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 766874118 1250 766872868 766872871
    0x10504021f170f040506090a120e061e0405180c030a0b01020a060c02011a010311030a0507090312090501030605030c090a0b01090801060b0d05161e090803120f180a0605 74
    0x2010410000b071240d0b12600900e00450081c0c41d0303030980300b0701414141001d074100240581204402d034844186240044c000c0c181116400983d8140b03840c6200882c4040765040c400c800204020f01e080950b8160701605004c0a070060390030a4868000030501102416000c0000359910b802c81e90050000030091141c2e038000840950741071040c1d483c0d9a41c03a80e106c2c02175a494054440160351103400103540d2041d828410440c5230320902c3c00b48800024400307030b841c0d075100280101e000c01e511040060a200d000d215078000460f4000c4c008140b261011100038140c02150154500203403c04d540007406250001d1042c015040042100c0516107a00200800a25003130b010603042c0a8004000030b00003c3c20711450005011080515030ba803804082100b0807030701c3c014420f08001d000b0f0f405400080c3c1c3c2c00074203004c4c00700b0484801c25400512240503581050140e00414003444001090310920b403c8035244c5016014400072a86192100646090407d0301801030700385d640d0000c440312020504030340007075 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 766875368 1250 766874118 766874179
    0x1b030b130f0f150f0501090c03020a0816020a08040e0a11071e06060510030203040b070224130804060c02010905091b03180109050a0b0f0112031107050619080901050402 74
    0x10b40d1000512100d80650b0f04600304c00d080203944900401c41c05c1802d01075203c00381091b240841c038008004102402803030f0041c1265803565810200746031914001c00c1141080ca07000078220740c64950301ea014410042080b0b840e10f03e1681460b07140016180d02c00d06481c860380d0300001c00e0607040e00f4002000c06001c4000d8040d0b03115911248002036079211022550702c0c5011940d409aa05c2c03803d410302011204002d0070300c0d011540708581300ba186203594088841316010034084580c0c2c68072004808218106156005403009400027400260242c1161600ca03005100380c03205601e4907501c104109883c04115400440300031090303286000e06082d40001d581c44040403500c2c900c4011820702040c00c55243c2e03001261150300038003040c403d100c140c03076000754010101e80a202042d81426004402030f00030b03030002001e02070200388800351313804144111005444040c00054564416103a0b03a6003081c00e2080003400314800c0e0002ca0700c03007003040c080c0c61b1056030084c00e0094039003001d14903000f2240308010003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 766876618 1250 766875368 766875383
    0x301050a0902092b0c0e1b030c0906030a06030515010b0f070303020d0e280503121305060405030913050609010611070f0f1401051905030604091b030b130f0f 69
    0x41203c1c401031209050800da01c2100544c80c102d041e01e04000d0481c0b4540001501c0780c4000204044003091030000100d40356000040c03512521400d0b4801c0407401103c0003503600c00c40110800030407158550100013240c0c092000c846484007080f0203120134450a015050104d06c0410403041401040380003804038034800d01c6d0061400070903c44400480e4241c3e20054296000392071224a140d0f0749071082400030b00712a601000c4140a80d0310607580e442030000b40484100c0e800c0c00203030507200510710050002d40250a0b60414949481d01c1c603140e6201d00c00180c03080d0241501405201410b114262240401406071a90703071f402d03e8000d0320300c0c03121980350288502c07601c603000c50754104820315440141a00c000f0f0984031401e18032205140b5034408203680c100942403200c420611185548041c04d60b20604046d41e581d101c60000c100030b0650150050511008810f541d441445000d4034a002c40c6e010310000007080c1c076203940c0d944403001c10501c082c1170441050390400103d100c015030508207034842c444 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 766877868 1250 766876618 766876639
    0x909080a03142e0e0108010506040e030f0307181701050f0703022b2c0c0f130e07080703150f060518070e0d0f020102060a0c0507060e0708151b0301050a090209 70
    0x504841204c0240c0080c0c8007a5103680501002d03080a000c2c14040780801006903041501c0d03035400c45c00c81c0c040200302c4401c000c07280700c0e420484540c42c0c0200010701400d0b2080e4141d02a2000014064a415282c0c00202d40d40302001428940c42482a40c0a500080a6407038604c034201c5240c0128140c00c80140c054030365504619074034402c4c205a40860a020141c600070004501d0084900300b41d0440e62060042e61003511981d5a6a2009000c0902032600070703001452808100300e041c076103100c5802001e150300c1400d0010050041c080d030f4460b4082e808090a204080044440206840251080750703041084004001c10a0ba1031103c040d511182900d4900d0840c02c00c50300183c02c2d01c118000503220040521000401c0d940d05100b080d0b884080318000384448038180c48002c0c01d51003914000303401e0039a544004c0303080380c0741400240d008004c5c0e001141c3d400764048020f02405a0242c0c0e04c2110100175031080c840c070404130400e40741228030040440c00c0c014940704146000e54000c069880c2d00504080 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 766879118 1250 766877868 766877879
    0x140909010e030a110706020109151806051e060d08070209150a0308040602061b25020a060e09010f061713020a06080a0b030a050c060c070909080a03142e 67
    0x30f0b1001110310b03a2100c505990940e81c203820114160800300c216418602c2280100b02001505d8001408400c000180e1030010041c07550740842c038290041001e802d110a019440c2c04500512070320109004140240362a410308001d81c4602001d001081900280701d600058600028041c0d8003040140704414040c0315030001038851021a00103c1e00300a000c601885010390400c6a5a88000d000e80414502d810f60300d410300c45801005080c0c100000c1c1e50b400c082540c40780c04902d40c5019800382145810546600f0b01a01c000c02e006415800790f402d2000006400020012074411155591201d1a0518800d212842c24840007052b500d9129040142d910058032411401070051074113031707511803280c1030406644040d00c14100d00d4074800d500003000400440c0b004503840041c404100c4140e99191400e11000b410903845601810701940b8001c0c01400303000d03c21008041d10901c1e69003c0007007154403031900103030401c00c0d101036034801408080d40c4458880e02d900103c0000d182b100480c50550b50741e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 766880368 1250 766879118 766879123
    0x40e2b0c0507060507120c0c142101020417070e06010c020414160e0d021c031e050406090515092b05010b0f0306060d03140904020d0510090204140909010e 68
    0x603444900003840c0001e511090050100c03104808800b14548007034104402c0c8c0300c20402c40624024040400128540c0251956488882d02d001c3c042600a0070302c0c1c1c1c0380403a0303014000d4000d48a01c1d545840c058001000059003c6203040c10307102603002518240e1200d000444d0501402300707003260001da8401c00492140916901d09202d060840074280000007603c1e0020b01c5400d1a801c1c0d0750140c403440d01d060006a032400044c82e07206012041406282c42182012100300d0301b4810f08503c454209605c04c012154024024402e64800791110a607090340c410510104c12417040d03d91004410901001c512850684d407008446d55000004507900f01e40c1c00812841d94602d860100c0319a0340d030351110910390510781030f2440e28242c11809400d040c5412004509650581c1c00c0040801540c031011004d00c005910035203480a00180c000c40d200cbc00300c022080010704d000e440c40c10001a000d200003070000c900e4000c0b40e090b5280302103104c0030303040b141c020b00c0340000d03010301060402e5485030308070110310b02d04 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 766881618 1250 766880368 766880383
    0x305070602033f0f150909030a0c050102120415060e060901150e03030a12051003050c010f1106042301060821040320010809032d1207020c040e2b0c05 66
    0x100306131500141814030b0113030501104180b0381c50041e4140b0741007140700303400441551000091410502d242030814641240203125080e80721401d001d82d20140002d00c42c8200d030740300018203034075410840e854840c1c00d01110240c04862280c1d200301a5001440070080c0710140907031805040c181540c030001078100003030a6412480070000011140c0100705c045030818058290040c500404041d00d090654403260303119081d1900307103418450b90b10740d450016031040359070072200941c503803c0d2042800e05d4a0b01c040501070f44001c21204240c0c499a40780c4c0840103114683c100c03007906000700202d0441c00540100d0010910500b0600c000501000000c58102c0c0d0015921101152000049440c80070024041d0480a01102c0466100380507008007400440c40d041d074115001d0a0004d0030504045075a2818424000f110301c0440c104024820034a800140c1102c0c2c000c01180c00b4842c40f05034021483d40c419112000da0421020b00c401450a0350b90f00c0200741c40781c86503180600c888581612003d2a1118 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 766882868 1250 766881618 766881631
    0xc0906120f09010c0c170c030f19080f0708040224072109030c260313090e0c01020601031e050d0503040c1d24040c08010305070602033f 60
    0xc00d10100182e4540a1141c288112030310301309041541c1258035559001540c40000d55444800000c2000000f90100240d031040c41500507240d942e60380e080c1281104001d00860075001c00c03404400f08040341d07000100b05219071070595600341290740d41d4003045104248000c2030200701d4940480080140802c0d001001e8080c016808101c0702060300050712000d803142460b03001000355403802840041d000000c458100c6258120844004441004071740098041d030417655024800000c1c401c0d446082c50005008031072400004000001c003060003c0d81f94414801c01e2030042c0c0000c401030001903034694020014030403c03403041442d0364540c0d82d07803460044050b5001b8081100841040304001c000c0003170300050450310f8940100042c0a851900c102c0801400080c82d0420202030003c1d081110861902161802041403010100320200501202d40a001c00d4807140a904030118001b80000210b80d003c403480810360f8955094002c204074003010b074010842d0b008041441d503400c070000022800b4050130b0b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 766884118 1250 766882868 766882891
    0x180f030912050606130e0d0f09120b06030105060303040501051605010b0d030504080601061e03023103020102070b030f061e040204030b1f0b030a111b06010612050f0c090612 76
    0x400800b04004000d41051300085941840980004048041f410031000d070030501f428020039801d0324003a82c0155a03608440e5400c090702c0e0583e8188025152018010a800d80c0200040e44900041c192030b4032407801503a01280d4100110f0030100c00c03102403020007034058000040e030408002c00180d8540348425056001074404034044c843c620060004600400003801d2190460240c85000c8000c254070280c08424164081141103000080036410380500d013408141350f00d00346008100201141c2540010303801445000800308200000c1001c690180d11000349a0070ba41d62500100518496080d01910f2022504051440726803180e0024201841c0f240c00c26514901e041a1881d214402c0000381ca110b40c001c8010405c11519a00c0c101c80e08100c02510100d00c0346031000c4c60401c5441202d6040c1c4001a070004000c1c085000810380e68162002690340000e0081018403210035201e043d0784400c0e01c4000d007808647d124003510020448940302820150a010035600c001c0710080d001c448944003032 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 766885368 1250 766884118 766884121
    0x206120903071b0e0c030c0c01150f0806010e0a090206160804090c0c0b0c0f0403020a090c020c0a0312031e02130501020c060c06010b0306181018180f0309120506 71
    0x1040500c241200b4000311000c0c01880d07413074401c552003aa10050000024002d001021840706886a0119006100d44400038425000508240c05c1c4062a8ac403408085100100700490504c0d004100766040b5911800f4148194030b4800881001b00720b1920b0403a171082c002c0242001e4010301c09400a040e9000c0c20ba5070741c4540c07505a0b500300350fa0700c22585404000c0ca6015000001d50300040d0240c2110000400907243c002031050311001e0311860f00702a500280305200000d4484a6030800e54500c10280d0940700c804c0000700c00d220b0000301a0200a0410360780040c03203152207119070700412400c0e40c00088404503040c0340d5068002c03644a0509500d03108a0400107010300d58041200c012000c1080d9140303440d1100d409401c81d165001030050905008002001c10195a61201320180004000c8060112410030046c40080500c4503c03035145075682c0100710080c2c0204500c1800701c082c1900d144422000010f40e960010b00c00d8285040f8207103c0b8405001c12142d8282c0781035000715102d0f000501d004e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 766886618 1250 766885368 766885373
    0xd0806040b0a0e01090b0906010c05030a0c110a030b01150c2103060306020415270603090206090402040806100f060909021c020c03093d0306091a01170f060607020612090307 76
    0xe0300001483e40381403210310ac0d103117800120300100716207480c50289000000380e6402d1600d03c0e00d110300c6607000e60f401120024088180030b0700380362140c103c0d140c64000802810344054191090924924054213000c584521b60460f021800d07540f100059280c50300290094890341e403442241c1054200c02074803142803c481c2d607040d402109407048500716140110781169100c400f03c407191518080c0f00109520790b06402e00b11b4881c90301348c4d1864100180309540306c58503801c4490751035004a82404d400242003d001400f151400e500301d0aa0f5030f550f41c0c00f4013072403c1c14014400380d4071444601002d19040010041d510601e403010302031402400e0003031651103204000b040000020845c901c4041c460f100320148024070042c0d1095120800c021481c88074000001d001d80043c0345607407241c042981800c0c5044850030204d5554801c1100c01d0300c440328121958013040c00589021900f4041c41c019050104025203005130103850705a02c0200800d2411f45c0d003404841d44580300b40d991042a601c041014000c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 766887868 1250 766886618 766886629
    0x1090f03020c03150112061e090c0e0f041e0c090606020705040b030a0201030506130606021606050316080a1d011406030a0f03140702032407020d0806040b0a0e01090b 73
    0x1c00700402c8000b0804481c00c68a20300c01c040040c841c000c1010306d104120820001203400190304c1060b4944105003e81d40003074040054030030400304030740d816000c0d000466118040c103000b9005a1120130400c4580e504d554032880c201c910800c1c070000c8040c21048090014250000c4040030300729a035000f044171854000301900c0d2030100e401061107a0b0900c030003410740c1e0301c00180e03010403140c091a012130507440f070707802003150301c0123000d050b4015a08180c0041540c3d900010320132143e80d064098404866601e520450f00c5d4001078070481034845805265140141c402c00919400c12008070340025001701540c0d81003001c40b5031400002040e5161007407079418904a0304080da20200540281903c054203980b5001030643ea4100141480301c061444107101c80c81d1802c0d501003d5000d003c9404100c000043d12040c10207000b016a0304051040c0054176461002c1015510859280c540c105540c54501c1003001a00f15502e15a4024141190004000340c03413804150080800702e00010b0070412807000d004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 766889118 1250 766887868 766887883
    0xc1504060b033009011e140f0406021203060616080408030c1027060c0302040b03250e0a0b0721050d0606031518091709130905030301230301090f0302 66
    0x18103000f004d04c2000130503600403046006010751420203013070990200d0740641c2c41d59207888070f100741d03c06e010a01510994110000b00700f9658107800310341203401c5003500b403881807204560550b08214240a601a50255420140d40c03040c8500141c44c2466240d038181031a54024226081d0300f03038403901c0716480280080c0b0500d00b6921481c18845e8000c41c0f0386004605605101b40c00a0100c1d035942031020000b03110791706440241007102e0f001942ca04062482080c0400e50206a6178070111003c000368865000d0400c104c2c0310000034044a45061070849011b005400c441d000740c410340141c4500e0742c1c005202200d40410f204094031100d0b200c8410600ea2422070380142c118900b4140b900e2107107a240000c1004030030450fa2051400c80342c55070301c517841c1d2000d41501c0d07800401b5001407900c40458400e415010b000c00002c2581c0540d40d0642a25060084e41e1a91102034002e4208000601c40715254810302c0d01c0b084800c034010ac101001100101e800c5a60100f410740e0314840c001c0240c0c0406a05100380d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 766890368 1250 766889118 766889203
    0x3012a2304090e0613120507151e0b0a170a02040509010509060c0c03190c0606030506071d0a0e090a0f111005090f040b151b0105010b0c1504060b03 65
    0x140f4131460021100070008554000181c0f41c290b0009005800b240318504940607654402c0c0c0142800d016800d811000e40003890207940650a5841132150a440c00d118050700000d00514031440300f49020303d1203c00701d01100c015402c0f80a012080c2c00961150b0003514000c107c5007000152614115000301d081403030181160740c00340020061564402c81c00401d8422054400022500c03140c2081c00a4881d400c0703030900200000d0800d20000284000410603a00c07694454841c0d448022203e644190140b10f80c4000302c1c0d010b87c000d1010301c5501c810305180f0341c0c0442d00c0011540307421000e4039111030b44080030404071413a40400c09001d4950400c0e2600d40704030f400300c3c24401c2c02c000003080084d8042007140d00443c01607546d1490420039aa0b0410703106006400c00350002d81d03034488609440821a5900554099036007030030000540c2c4001c1004640408001102070000a07800107a500407154014106913600780c1c84146000042ea4113101c400d00500000c0c4010304900d00241d81001103c6070311021 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 766891618 1250 766890368 766890373
    0xc1003051b1b330c0705061008120c07121112060613050708041202011b1e080c04060309020f1302070b0906011202041119091403012a2304090e 63
    0x3e052000c406020303400d911256141c83c0302c3e180d882e243c0c48140340c052944090038900c2000b0038040920a05621402566800805d41c1c2d0010184544c2c00800d200d22403e81001c0e50008004000750741d44041c4070701180b803284c8031100044010000007841c50f4980c0069080390340020040c00801c1c50034a02000d640e080d07900301809a464600d4015242e100000d102820181c54200303050304c0c451017940101c50f00b0168805d0b4520480034450300a02190003140c0fa544c1010510110b8150360340180c103100e10441182c3c3d1035034901810070208070b014201c0702204a8000c0140d40015185540f05901401c0450010000507200c00760350400b80c0300e408010b007990100707030000d40043c4840b0304034100e803150080d015540410212507111510070341c0d2198807801190702c82d8100450031581c5d0f106003403000b1035012442e02001c1c46120400c160890352007a00c00d0b82802103410100c040200540080300001c1401c2c02c0800d00d0750112162060803455183c031391244580c00007000d110020301c07403048a40c0e10009000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 766892868 1250 766891618 766891663
    0x2070305220b190210061706010504270618060b0f09040c060c0f0b040506071202120411180a021b071a07051f050412020c1003051b1b 59
    0x140e401ca503100e240f090310840b594204200c040b490080041600e44501d0f4a02000800d5813211020a003005071030401d0114060440000b80a10b01400b8850f041903468020f800300780012070440c02010f000075801c50fa901d4880c1c0e0449451706581c460440454050b41c03011404160f05410040420080130440b0721800e61031003071001150910010b481940c10360b0030074200d029490708209208200b030f0f5000405d01c3c120740003000104000450417502810080e2504d01d400006030712004281c0c0611030500403840000000a00854031001d807941212401034030078100d07034120b00d10b034071481034044588200d280d0b000940c07051001c8100d4080301500a0403009044103c1c10142a800c000952400c004601c04003c9216814441c00340030010090f01c241441c2031029804040c0003015002c1110240c1d1451403041503200002c3c004203079600b580c20014051464803040d100306030010000a03010112200340350b001082100201401004909080c1c0c10440840d443c0c22491803811480582140740c0121856 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 766894118 1250 766892868 766892879
    0x80601140d0f240509180f071a121b0403060507020f0c030f030706022107020109060b040b010c06111603050408070501031103040803060607150e070608091b0301020403060207030522 80
    0x11045082c0d1320b0407640d500d641d48038060045034030310828036401501d00401d5103070544d0003400180d2000301c40441c10101c941103100010007695010f034809944000d010180080d0043c00f50289072940b0714a06002c040c200b9850351074103821544200c0c0c0c4d21002d40d0218504002444081001404a01c0e0890040c542c1454890207680c4901440c01c0091000b41c010410f4011042c00010341c107041c0f0341542041c482803030a50381c005d000c0c29901b0b0007500c00720318121511501d801c00e8006c440c9080c5040e180c4443d1000700741d541030000c00a10046900716601480110542c401c4889601c40c418003966805807138600b0009200d0800010368450303414103140103010700d480b50000090740c1e805074212200c56129a5404042180f0740b04110b030003400342c00c03500014910f081c075a50100851000c41c004450f0310581320f0500381d80d500c0081e106c500141c0d100b082080c1024410382e010b00d0744e00101900260030640d50396280d009a804c040c800701d010440108040544481400c4559040346414214048181c1f809 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 766895368 1250 766894118 766894181
    0x7050a0b091b03030c0309010318050a120809031201060503070c02031b010201150503190c150c060509010e0c0d030c0803010e040b1b0a0c0503160b01080c0108040210080601140d0f 79
    0x247d460358181078440c08134950036145056102851074000054444034961842c1024180a144980c60042040380b00070840459000061301c4683c00da00480e524a40d08003202a505174000130040000c01074040300341d2006032014032410850722440d10441d4480c0c0e82d448006800d40e510b0002118045000d100d007002241c0d400951242c0d940f0700031040d04030039509410170070041140c03600100508052a4035003d000c540c8032500502c1280161002c0145458960049003030300c600514800780381d0f000410084071031403c407802101303641c840c0c2031500c030720a4aa0f6415415410983c0a107016400890400050100c4008003661012401c103110060381100390711403410f8003032400c00c042000b9002ea403d9007000380410840e00c00b41122120004090703a10324042c21404001d00840015002e0000c1114007940601665802903a0080a0000b0f0361100c7c4021940311030000c18240c1000021566510144880e1008000c1c400c81c0800104404001d00444000e441e0203030100301e00c00e4100e0810700800c8008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 766896618 1250 766895368 766895377
    0xb0f0405042001120c021c081b031003060f020c011409060f0a020f28050403030912050114040b1b0f070303050c0903010e06061005041203030207050a0b091b03030c03 73
    0x81c15642c1e102d820020048449016003150425180e10b006070954401e50000b40f1b10321000810009658800c003c1070040310728080a540c68451051040459840000b0700d9015560100300b18290b10507a030780d20f0301c400041da0000820120b01130790004c3c00d11392000007805a5003160b03820340e11440c80c074241102100e54036200100000e403103101c9080401c0007903500c0e804a1f24442401e803589911040c1a015000325003080c05034041c41c1e005070f10070682d02c04e40650700f41d400301c81c2c040d00d0300c040e0300f0304d0b01d803061070420040740040310300c1d540c1c0c1c6000d64001d503268510306002c1c0e80604501450752500d02c0400700c036844007008040101d4414404501c00310840707011106081c3d8580f4000c1001d442d40c0091810902451100f590305508002d0030901c00f450001d00c4c24885c4000301d0309801000c0c01c0e41e80a4030300348114012059040040c491a4000c00e000303030001c0a0041c400e0b0116154070700741e51501031140707030261401e41c42ca0700007088405844500141041d480801100918901901c0004046c0d4030300c01e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 766897868 1250 766896618 766896653
    0x9150301092708220608250f05091c1a0105180402010302071a010b180406060c02062d1801030c0906030c0c0501050403080106110109030207092408010b0f040504 71
    0x240051545101c141014500000340d01c41c0260000c0141c5805000d00a840304031540c5501f030800c07118410072445100c1100034006050344420030b0031540f1501c22129030f031111140f0b6401400b40c4c121030390080f031002400b80700c1600074294806d4812640d9a040c08001c0c06034440c44c850661070f103164541e240346908941d005507090900580ea4000c601e00400901105242030b1107901183d4000a02000080c00030a2144002036060b01070580040c100320071600fa80c0107039000142c4402c1035038010300700780001b0041d54601118483d00001049a0914139480700d1004070482c5a021442c0002c2c03070801026205801000d003814044c0f10748a020003403000321184524020035454208400c0c0041c060000f001e03c00382c0100084c425840c1908024283c0c003c203125020005519000418208206114001119625038042c003030161500030310780050281500242c851400380d1751114441805989248010000c001c00414002e01403810021a0128901d2403406107040004000c0001d1040392440c001a0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 766899118 1250 766897868 766897883
    0x1609090e06180a0c26060c0307030507051b07171506100c06020d02044106040503030724090c03060f02190c02131a0409020303091503010927 62
    0x20107840c001854981c464101400010340c0c140e0102d0010091001509100070220311500d0b0000d40480c055501c01b012514901404c030144041011648640c025907040781d0185002404c00782280703841d202e4540301c51030600d413980c0180c004104c100c0000040e2800c201d150005404d08140c2071210725080070703000304900d108040c1c901140510a00603000c0052054200b10308546030140340c0708241c000c1d84140210740803112071491403018000344501d0050205e0b1a240b080b170550f903c0031084455442001e108543c010824480403d298038100080d00c1d01e10b0145c8801130384804030400c0195240440b03049000c031141040c6a54021803500c21003241241e070f005a00048188500074203100034014180d501407a0445078004e064610341c000391520549008a40d02c10310414101211400c41d1031014040c0384401803401001c80e5440c183e40500c2200780058156880c003a107042c00901c0468218040259005011005101c820350b94031812032903c1811480c0300d04101d0a1043e003107240362070b4070018000c5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 766900368 1250 766899118 766899151
    0xf10051e0c0601150f230a050d0f020a051b210a030c05090a060831050706020303040b131a09010c0e0a08070e1801060b0a020114150f010302070b1609090e06 69
    0x1540b40103031b440021503034401e96600d0b15041240101180d000324407240101d410007280030701c038600e140f013112520702154849030710b8040e12044001040d035055801e84003d0054610700504045840c215650f2484080300031070341c4088a00010302152441880715007004014002045a51103030403414060ba0315a080c400600d41d6842c9110740c0303007110000c10300a80c0303040c1021440480e07103207403030071210b03a00c54800d60300000d40f1207104076500d00040314003800e205056408500c06858022440c0e403140e0064001c0181c100cca000b00f0140480c0a171240100c03030790b403044c0c2d1440280d07100800313040014080f10a40507040c5400100c50740d40d480c80c000c1c00d503611405400319500c143c10581e15107800e54160f00900c1081d5440106c40103d4108514200c0507500b01003813400718047c883c191901c80c40c4d40c02e4001050717010140034403180e100e4008489040c15402c0000c0b41c0820000c0150510907060450300e0b00b10b4001900000341103040c01d503c501001030402c00c1c660302c640d5000c01d00d0b41e80907044191240c0003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 766901618 1250 766900368 766900397
    0xc02120d09170c03070b22021519020709060b042d0909080405090a0509120a051201030b090c0102033a0507080a0513020f10051e0c0601150f 62
    0x480710810980b4000d500000e0000d40000080082c22407039014001900c4242c0c0c885c2e0565030040d100c184500d8444020040ba00b0061800c104d04000201e11101c1090a00c10100c03240003400500c0b140b9140983d020000c00c0008140c0e0b40517a00150091918171800c0518101900b07030b6410140c41900381b070400c1c1800c80c849510015042900400c0b2250b41800405072a041c42001e9901c2400b8450050988070001400b8220303e0044901900c01040104112003c104480109030000d00345a410008100f020903600006c28011901a50184204206505000100d9840c12120800c0c03103040d5001800a0b200741140c0c900d018490036044014040c484101c0c1114007046084803400030a030610b01404c2c42052503012111714861031100701c0c00c000e030391516644202ca03e4040c210083d0302004140c00040b8508082c00342a01e491100e00b041ca0402d01d091a00241c070016076030003401203201c0440c0c0101020000c0041030300400307807040c2c0800411500350380100345c0720036011010140182a03035a00d01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 766902868 1250 766901618 766901633
    0x6180215210a060306050a060b1e0409141501080906010e250305060f030106080c01030f0e0109050a0614130b0601020715090f0509090601051c0f0f060c02120d09 71
    0x9070841541d003005440c03a003a102c0b08000c180c0e40c00144c0e0300c0c501e007000140e031180c440d1148000756180c103000c0a0403c124010030315808251003003010010342c0140000100d416240c0220400c28080e942606081e10740074191030081580c4500c510704004c00c1000b0700c00846c00128500307064680d02c0303200102990300d48949601100c1181c4107028215142d0440c0c60906034141c1c401402501701700d904901d000500001c1600b070302c00d213001d013070b83e9500301b00500000c543c080d07800f02000c3d0041c170801141a0040020075400c4650a000503102da400a080344010080c5501c90710319800340c07c600000e49070404d070300d8090a4aa000c2c40c01004c42e1403c4011810f03a2703000b009018020050301c1002080c116548500a01450052198180100300500d01041500d05050664450881100101116861f050410602c0d0002400d20b0080241011117072002c602010720140701d4074040c20946400321f20610300042201c000b180403504541115181d1500c000940c0201c1c1e04074849034002003105480350402c0758 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 766904118 1250 766902868 766902907
    0x1020f0f0d060b0706090b07140406030209030118110307060c08040501080901020d06080f0d08090c0603060d0c0617090309030615010e04060f05011806050f07060b09070c06180215 79
    0x380c3e4180003240c030508206039030b00504800d600c02d00503a00300b500d811b00140e0381d0300340c20100c00051220901060000d248070358082e2820f03610050011031840c00041e0124071000606805417420102030843c20620f040030440c1c00000e0516251500341401c040c0c0f1035200502641c01464100007030300002c9002810b09406507010084011410410a9076669090355544414910308159014620b54444164003560100b441051440d02038042804013a00304503060b40020645a03008421040710008150800f48580107002d4540782c02e01c1c030741c14285a00303104000041803490a50300030030803400980c0b00429180e4100e802e003c4108441030000c4010380d8280b040929140c1c10519005002130500c0720b0117441070498a0a886004100001c2031510300da01e0510f00688001c100104800c2d415081c0c0c81000f0141a40595400110800c20300c0016001540c00c0c1ea0200c00a5800300883d018864644100c1c4c0b040740244442e0b5410420740c0e80450090007800b44040c440b0b0801048010071804840c0081 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 766905368 1250 766904118 766904129
    0x21002030613180309050d020a15021c021011070f060c210203011806030320030f0a113702030f0105160201140424110f070b0901020f0f0d06 62
    0x2405544070000d40100b030441d070f80806800084000e2800200b50810683e4104000d40160075100781d1824104100070800e064490101140310315802040405405034614120f2000e0364080c110004202c080d8805a540d4001d600020040801540000981c035003044925103074454004a00c5411400e41075400d0443c0c0c02d41c82070000d014100700c0c00d884115034002c50590710501303d40140442217844c0341c000c07900907010041c0410603007052183c594001c1b4035040403814202040713070726001c400034030501150044040761011507040258100404024000511492140c910584481c0622420b154001c00a0214007002d1240c000703c0710250f44060200d50b0000c00d06034000e0007241480880150300003850400c56006511300b0784401d42036480e1000407070240390003120b10305200c46101d120410640044950341c001958446008041c07402d07580203890080b13000c8540300c1d00c61100342840003000000070302606181e4810000c60821460311000d40741200340703103903040c0d0311107940305c0f6514010807003600300303 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 766906474 1106 766905368 766905371
    0x6020a050703090f15111911132c120309062a120603190308071706062508070c051816050a030b270115021002030613 52
    0x4001186074020b050b0741d40341110f900032000c0c048036220121140301504105039064039040c6889c0d4019100b021003400400200503d0b82481403410aa000c030f400f44641030b0390f852800c10008045011a03610340250b0b41d04001d0903c40d5507210495a10184842401504000350501c0c1903030940703181d540ca105030909076100112050448001c1c200c64041c401d08540e15002025a01003a500c00d01a854201540c101103030f0080c03002c180d1030104540a81580b0078041035840b0801260302c5951090f4a4010000307400c4c0610165108001000c2c103c00000308286d01400707802c0e02c00070102d420440d03e100c40d07020031115400200b041150800b4034000700042c2c82901c10b00480003062181c0b05880c1c0040c03205c98501c00203568030301c411403000b641c1c407a40041ea070034001d1176181c181c0903040e01c00600140d1001084001d50740c96421700f01d56036460300800400c542d82c9415003010f0019920b00c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 766726618 766906474 := by
  have h0 := BRFrame.cov_init 766726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 766726618 ≤ n) (h2 : n < 766906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
