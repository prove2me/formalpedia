-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0131
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:01:19.793522+00:00
-- url     : https://prove2.me/submissions/2e103ed1-29ca-4e2d-91b9-219ac474933d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 23381301 ≤ n < 23561157 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 23382551 1250 23381301 23381333
    0x1060906050f07050106080304120b0c04030b06040e0c031c170106021f0f091a0601030920030c03060c0c07060e13020a0203090904110f040504050d140c060a0501060305070203090d 79
    0x2551b0341d200403910f03080500c0100020625147e039081800080d0130f1405501001903c881c081d1103041004200140640c0242036201c0401c0300c00090740c04400c162607041048001b041a4540100595410300004118540002c0c2c689070780c40c9149148002c01c0f181d8051400e009203000b5030310034001ea0800c0e500c1c40c1074030715580700c075117070003150042400362114151002c0341001c80d6131881c030ba00590700080040c4142070b03000c2024030702488880000c2c1c4448901c0520701c0d0010f0700e1a400c5084c2100c6680b03040200010700d44000c2d00f11400341c549003030002000d400000d00810140103d4400258142c4908050f1410f8200109070840f070000c4260b1000c002c0d03010710b08010a60100344070345070940c3d840251503885540210001d00880712190100301c8100b0038800f28502c23543c948014880800d01c0014049444806402e101240c0324010400940c28010016018080d101341810407001c0b00941d080507040300c50a480130300880d1a60038041e038a9004181c10b05403c10000600b40c0e0102e4550924550b000d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 23383801 1250 23382551 23382553
    0x203120606090604080f0304050112050609010b0904060308030112061d0706030c0314091e0a110f010905030d0302071a010602150a0e010204080304080d030e100c02030d05070804020901060906050f0705 88
    0x401d507104034042c2407603d05141203036650004141080596005011006402005940cc0115103465000940d1602041c0a4246028004580c040f110707100c0354802030246400420954503980c1d2442c882c0c00c0d4a01280301100c4060900c1c0240e048001a00418a03902c0d80c0000504145400c08100310002d2080e09554801c00d6150303449811044107101065000d01a000087c0841481071007894031110002c4070003460640c40002c41c4000303d40c440405805000c82106d40348038003101c1400407962800c6a0300000c1d41801103400da20041c54042e401007403118881e4004a11482017550301d502e145100f4483c501c090f8000000c03010b4100c0328090b0b100d500170b149003c0002c2e0010482030290898000360001c0341140c0c80010240400441001001415502e5140c14041e0b42e0610100c1170b20f070040c080c145407030583c0310b03643c6000c0071b402030040e501004d0758101c04100364030381100c0040c4017950581e0140c0c0180101c2d000814200c0c4070f42d1241c425a00c154071261b00d800241c02d0001e809030b00854081c0c502e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 23385051 1250 23383801 23383807
    0xf06060306110909180a080c070e130b100303120e0115060f02070f0311090408070215030403030b010807020303070c0c0806010e06011805030601060c02130603060c0f02031206060906 80
    0x6401c1d407060300380621555888544420089050110302200903180e07048296800d008400600400030320b40b445c0316444015180c031204121413042c6420b941c3d030070081d01c040c603403410880080c01c18200c0243d054013605240441e6260071a043e030700c0c1249800050300152800b2080304200044c0d07004403242c1400e000002865281d050248034426029400060006070000300b011919a4104021006810180400141d8510f180d980001503101100c0311400b6820900004042c0180d2005403540d050700a042d150b50300e48001510103032984211000c6000c03e2a18095003aa544611a0b00740b04400c1d5070011131554036103010540700d00100e0744e402c54402c441400d0104880a00b407001c00d00070000f074554403030340d8144513002400c000c490418440c08102c618008000a0754001800d070b0441d40c1c1030800840710001800030403540c0003401d40b5140c1481c100007002003048500d0744040701c040c12541d40c1001c0058030080c103d81741c1c4a50003014884120b4480495030074076180009041d80359004103da86 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 23386301 1250 23385051 23385053
    0x91a0405151f08061509010b09011115040f020a120f1e080c0307060605010816030c0c14150703020f07120507020a0909110901060f03050603030f0427020310030f060603 74
    0x34812810f80c004580070f07003010090001e91600d85066024808080710309034031941c1010085d00c2d0500402c0a81410851074aa02822440043c41140050401504011507c0c6000d09120300201480c3c10201d014030314020001070b01c2ca892004a0b003410394004040c2c030183c500d6494801c05038001201ca2071408544a0044000404d05d030000d00349010108040c545a0a0381e007031038412101d179648140e0500c4040c88c10010b1642d444420700c403900095050000340200c4401c003c03564058403001c01404c41c10484101e5003045400940e13030317001e40c03035540c0000329587d07403c08202c5c1a40505201c2d45040e032018402140003d1520282d4038281c40341d890314078140000c40e00000d2113098198001d0782515614204003051000c054044490180305949011306035251030001042d9a280e0401d28040541c0c8001049084d9010f00440b0a02440c0c0b800c295241ca4a4102c0c154042800007040c428150034104001007170381c0d16000707484c4907000038464403080398515241c81c0443c540c04074041324145d80c3c80d94044 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 23387551 1250 23386301 23386351
    0xb03010b060d0905011a0102030a08091f1406031902060c012003011508040305030103020925030b09090d08012603040303030515041a060a03020f030901091a040515 72
    0xc020b00c03510702008200d4500d10b04001d402c654680d4012803a54400b0581070b003560360000101d401054244c46c10320701e15070b5000d41e46c50400c2c44d00c1d10701c50142900c403074807411010201d070002c0381d00c00140001811161243c504050b42d911440580c2c0e10058641d8810f80701525020020b41003500301d8400100d95088104a680c4c40d10042014907a61503c010005002c84050b613045803407040441e040018440c00e054070090454001440b0080c0702c1d4206000083c1401010481d40d03050304030b800a160364455003690090003414801400900a80001c800115041800282820100084d80390350032180d00301001d2110302201e1011003508c8046030b03101c01c0e800c41c600304018001940250740c0040c06040034074580d0102405450294480c1e42060355005080030410400444d0f18070841d001030303075090221002c0d0042d000342c144c910a903000100802000c1c0c1c1e41900040301c854402e01240908461080458080a0b81514098007a9103c0641c8440e48c400c01c400d01e6810800d48a0b0107045094100090 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 23388801 1250 23387551 23387557
    0x30c11030c0d020f030f030408090301020c0a060e0d09050a0608060a150305240a060807020a0204060f030b01050603010e060d060e030703030c030b060a171510080621060403030b03010b06 82
    0x1071807a40d03220b4000034480903411310603840b4161034070000d10301e001d000140c4a07816020190000d81f011100050b0440d003030794254100c0d42d041c0405420b039850100c003820410020640c85011201c1805000c0820500340d1080e1502800d4440007024070625a0030075104076401003000b004903810807039513500841e590310901c18080c40c10440fa500400d0500c0d142d810302034180c01c071449221a044100203441075698456040c40f042e07402e07514001656540e1608205d14244801c0c8001c3d40051a095010071154042c2c507408056038003d000c5989030341d0ba17071024080c40303200921900281c06042004144d0514004071840c084c3c0340905808200031041c9403002d8150740c4204011170100f07039604d90401210707802d8082c09060080881d4030030b040010061014140600c071824066500343c85030700207841108409440303508860040c01e00070743d40d07005a1028000d5403041d540e40c0e20a02011000d5205d0010040020701c25032091000f4214546032590207030040d144880301d00d030303040d5214030900985071111009 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 23390051 1250 23388801 23388817
    0x51c170103050304090609020c191b1701060b07020321040e0f07080601050c030a03022d031b0405100e0a090e030a0314090a140109020603041a1501020706030c1103 72
    0x3c1c0d940c440c9041c01050450b000c40e40007440150060111400444000c9801000f00413036000d9a030403c00c151411803008507a4a2004803e0010040c010075040c2103041d00e03207141714409000b0070001c0e4072410219824061354000952640c86441c1800446042c20010000305c11000b0f043c85c00e02d1780702c240b4420009002c841303030410f0454440070010001da015400540219003800c2052800b80f80c124007980b40d2241041a5050540001d9404a0f003507124030380e40003451009003072010302034164075400c2080c1e1099840842c00521442c0300b113030180b01d11b0102d40440e03600605c800a840020042a240d243d0344c000e54682c01488105c000545102c24014807a10b000390b600559554444d109001e4115078804c0c03512210764a8103400c009104900041d440041a0044c4510a00c52461917130310b40500105c0d113000350420004800e0104000b15a030300340c0c10241081c14503844980d61220010710103000414464016404000d080140d2402540014104409807408bd52081c0b0121800d03843c1d070340720a02e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 23391301 1250 23390051 23390053
    0x2041b030507170a1e021201050907050c060a0e0a0f030f020d080408091c080a03060e010e04050c0103050a02040302120d0906020313030813080118020913051c17010305 74
    0x245582900da141c4589540701010341045800410501454898030400502c0d858030240e0b5510b084401400c03160809528031440c12080d9511842089507070b080aa082c4a840d000da00900041001c05004a00751099090068000c3c203a45d03441c1d00040020381144c50400ca294040d00c4001b0001ca100f8900e80012a802a11800341411404000034a0804804031036020444408180400208968102c44811a086465000403c003182d0080100c0d2a4004010000e071800160581042e406401040840b4440703026001c0aa998140c40300c01c40104071401095908007291444117903029502503a08048010801810981c9a42c0803610003141d080040e4980d500c03000d035080b00b03960b01419820141c603203840518181551800780000c000c40c607010040400e00b0200d102c00d42c078011940300000a2034960001d2007405500031500166447c0c5050030b038000c011707403000510000b5000450035081c0390300100810b001d0304441174000703010034041c0015081084401e80c60340d442d8641c08600740a507010300 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 23392551 1250 23391301 23391341
    0x7080d020c010e0c01020c031b0a080d09060201110702031504030504050a090519060503071521090201020c0f0a03020105030402060904090b071b020f0d060b04021b0606060f03061203070204 83
    0x40c0c00540380134521103440f4119400101446081d4501080028115501c82c0310411005a00c0000030f03681580764012103402e03c1500320070355400d9030003071001089a80d40c1c0c00800c0f05d507103030f003504407001d20440c00d0194040d4450000100402458140503070f2143c0649845410300d5118400640900c01301c0c0d02106001c1d4940c4144080b00080d110840701c03c2e40390b88020000311346030401094540b100c611425041d080c1003520310001d5405080b0514148001c100801942c04402646030000c09a100d41a0b00600c100c0d101c40c0074a00b4229214082c07804002c0c00700b04058030795401169141c0c001403003282c100e8400d01c045546500c85d401004000391042c1e079060482e14102300003c0c001c02c02e00d240350351000c1c1d0b11800b100243c0c0390309080d15080c101c01d0300c034140b021150342010400381c0311407040140c000d4030000e41c080704000000302c0c640801c0b01302400c0d42e040b500c4450400c031303160159890304100c1070b038100f0200f080c500e404881415441600001c2d40d081c101075400103802c0320040e804454454880f4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 23393801 1250 23392551 23392571
    0xc0109050105010504090c0e070e0402030f0103050d02150c0703020a020a0617090327040b120309011101060509150a0317040923070305070309050f0d080105060403110607080d020c01 80
    0x82c000d035809031009a8007003020180b01e440c1d242c0100f01074030a610100d010a808500c0d150b10a00c40142003010180c000d6650f030920012a00b2448001d101c240c500d130040302c0d000c0120a20200341603181c0400180c0e001700c075890306400c0300580da0040c2021019446102d030300400689580c4444001444982c64441d40114621240b84d0001030041c0300004a4101b001600003a130003d0390504c000b0400b00c0100406492040e011800901c41d40310040d6125408201e03051522800000910000e0020b1341c8441510b07900140c0d0900b41c4402c0d0142c107030700134100741c00214400743e41c0d40d00020359400242100f04143e501e480c0d4500250207420040601140000c05100142d241d002d96110055070300c0260480c03542601e407440c0980009050442050380320070224000301d21a8011408481e00803045d291000f00030000c450340c0c0d09800c41c2c0340d004502d11a00005441c81c1c02802d44040302d401450481c4403061034020400c4661003d00200e46c070210500c8031286443e254800340030007602c0c480000400d5965 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 23395051 1250 23393801 23393803
    0x21070905060f06070b150a0503011d0c01050414121203010902070201141606050a110406030b03070501021507050307030204091805011506050f0310030f0c15080106081602010905030c010905 83
    0x11800094000c0e0010084c040c0021000b40030181d001751054070788084168201300003a444402648042d62540c00c4c6006103020350b448001041c47c0b908008111406032800e500196241d02940c41042e52900103502c5000c41424503049000901c4011000e0b00c148045031140307030280d50400c0e08034814603130380230400d0021035802000b5280c46010140f015814111030815259803810b100d40020010f5885002080000b6081d4200c886050f00211080791502c1e04c0e40c8c4010f0040030b039408603a10034440d0820000c0c055002203060f501c90003211038000d1041e0380b075540581d1264005840001019801c000008103d956071050161603c40d0329506c020700580360800d41c0c20760302265a02c0c04030b207010b08001c10095421008440c1c00340b242c0220240c0340e5a4240149001c9101b035400134044050000e0a641044921503420054880400c0c4409180c404094100c0b22080d007405000003050444002c20410070414003121490141d9200205038110030303035202421030b005105181826034450884804104c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 23396301 1250 23395051 23395069
    0x3050402040f0c09080f0304151107030210020309090a0c050708070809100e0111061005010f05040504020406080603060a0605010e09060439022b020a0b01080c040b0418022107090506 80
    0x2d040152305260501f56002c0929103851100001e0000f9400502c5000106110501c01542c0062080058541e4201c1c0079449900a003440e41c03040c0d004c0303c009200c4028130301c50b44520001543da25414641a695421056445100e064541510a000171242ca40c0e40c62004030840c0d01070399900c501000d4502c00503022107110300320340d5a240c01520400c0340761100d500040b401c50704240303409071084a00c9001074a80e032040d5008942c11030300010b400f10300150815440b0740a0300050382143c20f1581d0306520b1400f10307035041c050a40014040c1d01000a145002000540c00013001400010041e0400390007408031503c0c104110865450f00f00f0001d25000309030020780207130303001c3d001030545251a00c5e5804007161221444889807051030809041a520030407065905a51007240a0b100c0c1d43c640700034036541c0c4140094a4800c5090058404d40790502d401902c00a460300d0544c4081400d00e40c1c20400c2d203c00d07a40445200030214000d400c070741c0b54200921030041044010000e01070034907409000390301d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 23397551 1250 23396301 23396323
    0xa03051c180f18050403020a02010503060d080301170c090103030203031306020c19050705040b090a0c1103031003171c110d1103060a0807050603011716060203031603180303050402040f0c0908 84
    0xd1310f40401c100100b500400c50080165091801e15900d40d110742c00076440700314240c805400c0fa40048004a07261000318000110203242908607110342e2200420440c4160090100800580050000c1186000603403140c0c0c8101d482240050308051001104c03d00d031041c00d401c0c203070600040352240c00c00d00c0401d0100101401c0152000d11004070f81601242d40b07a50041c11090030540d54081241d031940c07082c200700329840c88200c00c0d0b0340d0340d00701418503d5919103a80019254024041c0080c4461803d10080f03801c40c00c0c80394900302e007441000701d04100400340700040c4050140104124100141c0b02d2146c51204866108c178140c60741400001d00c83c2005c0e85401180c0d20380e00800c020321407a80ca050590b4111040010102042d10818000307905200d01c142c01d204203030303096860203c2c51039004000342d0721810901c0040b41c58184000710071001e039002917078005142406000d004000ca0300c07a420071507104e0300151010440c01c0303100e440d810868202207010000580b4100e0188a40101446510064 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 23398801 1250 23397551 23397599
    0x70b1914010501050a0e0609030109030503010611060f040f030e0a090f0b0405010506030c130f0902030103050f0703020609060d0618060e090d09170c090a020309010b0a03051c180f 79
    0x41d60400002900f244200040302c401c1c4100d14012110541d40e00048401d5040040c1c0280981251031802510742c0d002800340c50080ba895800079480c40300c001900c58401c0c1c0102e941058681c5803900c0e8071a07013880c0d208080d020003a50000000303090315200c0406000380301031580003500c854004601d8080b541070024951103181440010040c51b500d500650341c016402d4100195121900c01c40d0300f480302d0940c2c0c00b45e0304e04600003100003044810f95000e5070403a030250b03007a01c1d000707078078130010030307110082030000a43c0400103001d004001d08040c03019000328440704200248603a05e682d414946205050000d41c10701d0f84820060013600c0c035440000d40c0140c0144000d011b031402c45030015000404d5802803048007003003d51104031000c001c01c6006800800a07100d84001d0030503101800295204031600030352507080020200150426001040889800c003024160780490303514881e04c81d51003009600104150004d042c040c5003011107000005000c020541841d0501d003807801c2482000a607410100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 23400051 1250 23398801 23398841
    0x11d070b130323100504060507080910020a0504080105010902130803030c0d0902180a06081b090a05060a08070920090d020906190303080405060105090405070603050408070b19 77
    0x30203203845040415654498601c5460b507103001ca046040500410b0340d00c1c16132060050a20021205901441c015400380000340801c1d590032009030f03611481968045400d502231102d0801c00c0e00641c0c098a12070003c1d01e07040b454186d5562000c1d09548081c0c002c80c0e1000c1c5d0000302c0c03640103410150f0341801005079101849c210300e000126140e86d0b004030b0b90f4403000396031250582021566006000300c8084c0282407194143c0c2060000000100038900641645100d210034100030900f070010104110030300200380100d0f070740d02c03881b030031015040c05446503402c04c48071340010900140510115000d000e03000000240f00a9031810b00d888210300840c0703007403180360401c00c501140c2c440c00d15013001d00c2c4d015650800350343c5581004c0303503458081d04401180080c441c80c0201c00c055000d490309010b980524125041642c0b00d504002800c4400d54000b80345034000700c002c020301802a001a50b1007400349800c1b90030402c10351115110390070220754141d0043c00100c01e100030b91610780700382c0c840300394a00d00c5044 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 23401301 1250 23400051 23400067
    0x80105011502030a03021c06030602030a06060207082503080a0203130b0a09030602090d08180111010b060405102c030f0a02090c0708040b0d02032403071214011d070b 73
    0x9241d00c1000d078140205031b00020254441e85071404071001c1c0c01da44c0d00c01001080c0d42c905010009400c03da0f1031180d080c0c00c08500088075840090942c00b40e035084000b500c80300c1e0415041c070b03400212020104500203c0d0040c008080f400031000b81c040031905030050355480e00c240071143c0b01200b05400070910840d051003c04074481e4051068001c1d47d92001c1b00596852101c00011421205140003c100400004460f403c3c018545800c06003030b842030321182c0808800b001c1084c261240003041640244c2d0511003042079292884090740524610b040c40245004078682c803114841c5556203140a205400f103c1a2507800c00304010104810601d0144c000c80700c031340d40001c1004e4000381441241c0080803c0140501151b4070841e001001d90303040942e81c0c1c0744075410b8800a1340045801c90950042103503030500d203840000c50388450301e500031b026090301c0b402c081c46188421460760042d40e441d13170089109944060244201c2d640d0400010b1100e0101403041412860304001e9045544811001d00102c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 23402551 1250 23401301 23401303
    0x1507140703050705041a030a03050405040e060c1801090306020d06030201090e09120a02070504060f0e07080f01061b0b130507050d0305090405060111030a08070e0d0201020d030507020124080105011502 88
    0x20913200300300c0d0701103803035400300c99800482c9501c20065545801a004484101a0464010700403184150382c2480b50000b420f50304c2c1d44440c0210350744421081c0c20041c8000766a82010314a17078038541418a400d9444d107a4450404030780044042040142d640e11092041d9a00701040f000141541d11481260b480e00c2803106403106007410b00d440545e00041102c8400307038000d0101c2c4000d00b02c054420041d00d40e8821148440b80d40c944200c160b508a0000030440040c07003a90158881c00b0750501d99001a4603003c41220840042c0c0040c40c002c000030050080000e0b9828800c5015800b041210540c141e042c0c1002e90070f0030410340c0a20b21424602c20300000103500303c400d43c0d80c0300308101c6001840c0d544540c0141e44543c1d030202c0c510341c1408000f89404034250000d91080c02219076541c1c20890006210500c0000c0c1c22004020740540e05c2801c900b503a0500c2900080d03032001e5244004075241c5003424600c2d1280409014440c101d00720b0043c1807104c110240308440c018501e90252086080f1044006 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 23403801 1250 23402551 23402563
    0x4270c021903090810051b030408180d06050412080601031a040b0307080a1a010f18050a110408010608060a0203040f0201051608190e0405040201020309120c150714070305 75
    0x10301c0d0051028864428140542001801000c03100c0544003044030504007030000b000704858140300310070714044084030b0118800c00d0f01d10513680900b44620f04409140b01c503101840424000c0d40c800c2c00e10394250002032a038010940258820f006131041e515010201800859004040c01d0400d85000c8800d2440140750400304c0780b0200c01c0c0c03030005040c003000c00442e04120103034001003580c0c07180310340d4202005800441640001004484864281d80303030310040262007400e20a80102c0d2110107600c02e0114060f0340020340046460400050f042d60900f100d0701281c00941c081405a5951a020404480240b24069011a2135542140303180b81c20b071303500c01410030030b524040e0401030040b070764050841030421240c03843d540099920343c61300744d001b8100280d0404800b042c80040c4101d441c542260503e030103003500803581600510b0504135110180f0110f0b4081e1203a45040340300c0c801c5241d40c0f54451444802408911000d5582e45043c5802c0c01c0131210f4214039109125400311100b0000705a001c190 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 23405051 1250 23403801 23403823
    0x50c030c0a030e010507080603120405010f030209010210090b01050a0605160b040311011b110303040506010b0d11030c0405010e0312030109090809120a051204080606040905030f04270c02 82
    0x440e8840807195000c4000b000440318a40140d840c00c41488441c1d5004201503104007000ca044800a02d0315412203241401280302c0d00d03000c10304800000802d107010750003070401c0c08818412541400c961b030600d01c094442045058500e4900310005100714248000804090b0259091503803034410715050f1651080482a009080c030400701c03000c9400c0500c140d28029021070703958006c0c84116800310385a550210031a14001c041100350180717160464003c010790b031066420a003d0f081036031030040d102444d60300114041c00314943e2611401c5c0c8003201040a0350003581201e03003c07a21070b0b082100240181c104041d00b00d00c66400b00a0100e140882c140c22a4150341c00082c010410300c0343d501c1c09004500501c0c5a05521032103100c4000d210410024800700703042e0103081122030500021110259900c5540104c640d65000440021554100760700441c09040c811030481e8580840c001080d40c00707812a0b00081150003000344044020301b5441c00300000f40b059101c00b00024155220042c2d955050254 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 23406301 1250 23405051 23405071
    0x20106051215040302010605130e1506010c0201030515060a02030c060a02040e010b07020a05130b0f0105041203051b010501080f010b0102060106120e070e070f20060c1b0a0f0201020c04050c03 84
    0x3400c045c03003900001c0080c207001d012078590001c0d070300905014020301a440d0682c0c0c81440711840007650315041e120b02804040e1035412800e012a001140500030040074169100c2d050300d599441a220740c2c0052a000d800341d409181c07903a581e1030916040030b402400004240c4d0042c0400d0100141c25a2a541190f291800103542d8a1540c80800d480400a6100580c0403401500041c41800180c0280a0200342141e000c400044251f00555030f5004074040c0e040041c00300201003001a01410040003044900942001f98542a08030642941d000340c00c012015045201c0051000c83c00b4050000c1a00090010b48110b46c10a18000c103001b4038524808e1156803205860307850003d0510500003c4d10480002841910300003170301a189260010154001071180035800524000c4600c64060149821018181a440b40b49039a00e45812411b2110008103009904492034001041000500f911800340c2003e940c10500000e130400385c5015071940554113140c100148500588122030380510401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 23407551 1250 23406301 23406343
    0x703110f150a060503100f18050c0609010c021003091205070b070309030509130605011205040b0f0408040806100303090b030f0a0f0b0613050f030a03050904051302030d0309030201060512 82
    0x503030000d020b0301442c0d1201c2c0d050f00900c1541c5507800a10740020b20022680c2100780240c8d8440c01103180300113000c0c800500300b81c0080d2034071801c62a180b0020010f019051600000e0007105800060b06040400e21041c00300303a8409505d810041c0c001c4111f080018a0b05240c3d060030087e44800700070501c010025410188d64a2080c000c1500a0b02910304501c005002c49140303480c04401d0100500f0280600ca02142220410300320640240c041e05d07210350760011045d800c544411100c14103c0801820444008000f403202080441040089502c90019100d803001312034075500300540074083e143c020740c403903000400c100700d40701d10101c40300e139040280c495000880100c031856240041c0254031409500c802c000881242d520111280d0b4000e0f204112a10070040564400309540e0303181030540200456401e02518600d845e00c3c0c0d1106500500d03804a084c02e088903940024240301d55181c0c40c0f00420342c1c0b0080301f02415030912402e000b03804140e0308003406404000080f13a03240844003030680280822 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 23408801 1250 23407551 23407561
    0x504050601090e0907060809010c020304030605060406150914040504030e0f040e0d0e04060801020702010207120c030609050609060a0c0c0206070c08010507020f0d0305060616030c02090c0703110f15 87
    0x742c60580010078a5000c1151103040003c64141c0790758091040b01d00080f5904082091860107200b11300d21800c254000350324083c91984c4550140000804255029940312000210600004481c910b400701d19610001040d0809507100245600030620ba030145d45850208000690044116503000c0400c45d07d1502c41043e02d00098007500f81541090900d01824074801e1001d50058002c8156801c202c07020300c4103e480341d41c640d08074095030401900503031080100700285591118062100d0703008103160940e0545030b4403150240e031810101200c1c194824801c02002036030902646412260a00040c40000282c3d140103101560502e0b02900c55000000c1034010000d01c01c140500901601009008a1420410103503c42c5030b48800e1200324080c102c3c0f0014110312a00c10039100e0800144083d040a121280441e415500800d0403002c1c030400c041c0030f401607500c000e4260310400300701005aa03074080a10f8024810000384902105c95401680c03001c4446401240003015890b80040c4030000e035880b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 23410051 1250 23408801 23408807
    0x40203040203011515021c020d050f16030905090609011a1b0a0f0b09061003080a05160b161b0f03020a0b01090c030b03030310090b040b0405090303070f0c0c0504050601 74
    0xc40c244650180c0078141000803a807510717008045403000a40c090315601c4866070800c4000b04181c40000300185c1050381014840e60160300a020040b090910361820402c2e00e40c3c884009400500d8140c012950f642010099450318a800e2a400003080e5501c0f2019450030400b800010350801046190399130118021040360b000f5296594043d00560031201070106c14104203d08105214042c0c3e071014502001612080300040c0481c0103007100280c0c0c1c001546162501045904401d0100d0108a0108031003040d15100c0341848d070042d805201c8801c15410200381c118000c110260301403003803000390810000704030f0105e400c08482640ac0701d1104c0d05040c2c3c902e001c0782450605000217281000c44d00010070a04180e601c54070b0105d18980b42000b04502d1b14040581c2c0c0d001c105d80301502d150340e0f0481070007400010b821105c9905009030012501d058101c0014059075411201d45490fa840841001042070f44020340740070b0034409041c1200d044d081a00c8078034100e5824080d19001d00e07118408034080b070348 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 23411301 1250 23410051 23410061
    0x12110706090809010212040e040b060103060905100f0501030b0a030807020d080307020a030314011215021b0a11061608030405070302130218060301050a17030f0a0206010306050f0606030604020304020301 89
    0x15005504014005140c80c05002c01d8000c03070003150041c49520441c0d101ea99414085a09950031442c401c0e5041c0d54076070b030301800004004c01d8103041589440d40051a08800d000d000e01640d4400c02001d0300c04d003410480044501250b01290403d42060740c906215200c42d907001d0140e03500240003d60b282460300208240140b9200c00601c0020b0020400075090b40c0850340c001c00c684a07580a100c03d094400c038400c0c00366400c0c0180c0340c070005035280b224001141e403551020000001b450260410708030050b11000d8001d90720249001e60418407195042140509440002030411500300e82400e00442d150101100400c2c8010400c0c40008080b4091200400c8070400a5600900341006070820340040d0000c3c0d002083c40480e050500f20208902c0c0c607202c02540d041c0c3c3c002801d101040d6281c00f0302c810441c03540e80300303400d45c9010401907989000c3e100d40083c03004030f50a400619982d40341d80303031900807600c00400c80c40305948808180006980d804c0d0880b40c101104030307030161701d9868600010340181 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 23412551 1250 23411301 23411303
    0x3070909151e0e010504060e010b0a030e06010f050102070e0c1b070305160513060308090103020703032406020d0c120806010e040504060b010f02010b0d121209050c13020a121107 78
    0x300426640c8a2021811400c2c0283c401c01c00c1007880c81d90b80c80040c4010b032100c6000f001541400030f80107107e04c2c1450344c00b034140c441452601080c11035460000d07a0400600380c000b0100500426010b202075601000000018184405104020f01d400902d0920342c0c00380315807441d840d860026114040e0303081000100e0185030404166241482c0e00c0d43c002e95140003500c09c0c6030064088480400c4c0c1001ca0303100705000c0701d0708061211719120009004400039030280c0d0045051650300d0901417440c416006494815407400c40b0040c021b113041641c040d00c4d240d1030700c41c0c2204100400480c2c00006807628030399203000030541040c007015100e440041c1c51420131500311980042c640410041030061a40000703008034400c0c0c86100e03801c4940403049003620041d01003141c00080c4034a16070300041451110340d02031142454101c0d0300800103e03210064a803541d00503603d40c1d212240344001c0f450700d4400000f80410347e980452505120410240c01f000c141c0815000c0d007540d501070308030a010084210341540b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 23413801 1250 23412551 23412569
    0x10b0309160e0a060603020a020a03050906070501020d0f0b030a080d050408090d0303061e0f05090a0e030310030c050f0904150e0f0303091204080304030b06060d0c020d0210020307090915 82
    0x1602c40c020751195080c2107840d6280241811030028503a8060320031591021155400340074008281d490a540da503214254444e0032030b80800c11140413580a20280400f011001d00215041d03401c258040c0c181e540925149200340c00c82c1c00030500041c03144007190301c03030142184085002d0b03407a07052081e03490080c040a00d4101c10499902000c0650541c01174054612040d45001d03258086070240b100104030b80111a1007850514051000c0d02e890b915056000800160214000400c0c81005045400c10b8810818040050b0301c18410000e0b040000c4019250503144a10007851317920004007009400751028041c15411000a81c1d02c2c450b40e0041080507070403000700c4d40140c0561940958a0340101d5928005008043d20003001e000000101c808aa94030b6004605160458848072000c0402030505580103004002c50418905540200c00c21b038040c680146c0240c1440d1480a400d10103c491602c9400340704004202503d90001d06510039201e001c00000b440708141c0c8040124042e4a42040b080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 23415051 1250 23413801 23413843
    0x903120309021f0f0201050c04170111040f1403010902060703110c0604080d170403140d02120c120a1e090302070308030901020307110c0f01082a0a031d06010b0309 72
    0x7014801c0c0d4044660f2103c03a0352100040000180203d0882d2402d0342c01c4446440f04020820110a80c400e80303901440501e000083c0000320007107141c6540c2c0c0242d0004801053b42d000422552803501c40ca0b50110030154001e109240841d0300140300d5210300c0000500380284c011802c040c1140c2049030521015000e0700c4195500e0f20f411405548443d0044103200040252034400314840b200903145018640c1070b07c958501481c240c40216840d0840300c240e003140f60782403003030820490022a60900a1100802040d03403462280400f00701280d0041c00000d41c941024020f508503103401901c0c4403000001000000d40c5034003403a0482c2071003902d51025080482c0801401500c48042d4021401072500e526402c1005840c040c000d0380351070681803401c0d4409240340240403594001c0c06119402800d01c034400310512201c292886551080340701c203907298000810b13044115500751042446680044850546c501c1c001050565108014040c03000a100c012020440700705080201c00da04204010680702d0b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 23416301 1250 23415051 23415079
    0xf0609030809010b0406050d0321061805010510120c090905040c0509060d0503030a0507050708070b040209180a0f080c0a1a0a020c1507020f0d0201020d050903030106090312030902 79
    0x4146842514518031a5113400c0d00000301e4946442504105c034406001c2082e090a5510156009130030046104010f50750101e242c2a91245803194401400d1800902010304c0ca20964030b8007100c1c8140c01090044402d05042016160800c552101004440c0401f00708003910041c210385a440380c5c0d00c0b9040a5050005010411021a0003841654070640f0851019683c04007080022504c00c400542690007c00102d0003544844d0049036020300542041d0340b5010072a9150541c99000580c01e564101000090004601d00703803102c103402c6541d105072000b002909a80e411307201c050b07824000b400260445c642e4810490402c081d030383c400c1c0e011030039a00030b0907403424941a00310050582424081c3d0b0080001c0314581540b00707031640d44903420011700151412040106000402400081c19440b0340e024082107100e0801039018040c2103580003607190b040d604102d409446002d003a0390b90341e0708280010300142d80e002a0080440c1e8100c080c40da81c01d50207007025001803c014401940103030920031080 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 23417551 1250 23416301 23416307
    0xb0102010e0712060b0604050907030b0a0b0c0604061b090b03060f0405100f060201050c090909070b0c07050406210305070312020406090e09070608060d0303061503061a0c0606010c0f060903 83
    0x110b81501444c014006101c0100800016100d103024440d4072400c040f000c07800f5030b44039501620b20484040d0070b1078980c0e51100421611500f19550f107100f0340d80114200403c0240724013a0351220b0010720540c40101c000460064401c1500e8000d0300400301c0d001c4002041e981e9504010140800041d004010600b898200c00b107003100540541e01c920381c3c0350140051f12501c14400c0a100d60b81e13013100e0904200b4108208042c1c01c3d405415040588624000070804552500080081c61002402055110710b40024801078800c654048401c071580c4043c9056110819503000c003c2d1541460303c01d41e903140d03e140070b8940c8501c0d8000012050710200700452219006449007060390b64550f051107040d640d0350002561500b403030103418001001100820b0180c06e10f6040b101d0158840c1c20045421030f01c40c00d00c2d000b40c41002160f100001e07268070341009105410800b003070024424500b45440c090901c079a60703903030350400350610b41008880441d4400b4002e0001500712481e42c080e10510101d00a41001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 23418801 1250 23417551 23417579
    0x403020a02010206010e0f061c061103060f01020c0603013003050a1713020103050c0903030c07050f03150c1602100206010e0a020a09030b151005070b0a110d0b0102010e07 75
    0x101d01520401002103240c00c401b9900c1480b8403c2c00e011002250348a0091010b0b000301054094290105404a031000420034020107001c090b01840d955240c0c54200108200c0c1040248440c0c1550001522080e06407200d43c1142c1c151042c102e03100301c50b00301c03914030014014400d520b05c42805040c002000101a40324008200c01c038665a100d9043c81d680d00205034801c0300c2521000e12049410b0b424900650203070308465070001c1100384103802c200910b000f080c2183d202c007200100d00e400611040c8801d00c0d20b20201541500182c0082c2918501c54600003004440a01000102c46000c100340c60b043ca02c40c404c00300032035805012603000407035001c4007940e00e80003030041c010a280d00c6c3c0f002400c810018400c2e2051079800e550f820180da45103881c0c81064203405008215011840d0901141c04e0b200c00700c03c44081500c0340e803050f9403001c5a0401d041d0141380506032120442c1008048011540200c0540310003c510890004848513198010b03401007803400c1d494131407401a00c00000301c1d03d200c6031f00c03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 23420051 1250 23418801 23418803
    0x30a05040f09020a0f030b0a0504060306060810020304020d03030b060904020403060e060106110a0602030a0204030f0803090c03071401081008010623100906050c010207020405010e240312130e0403020a 88
    0x41c1c0d40301e03940c440800d00164000c1c4060036000502c03c01c2e401c00020702c2600075403507202000d0b26106c0b1061300c03080802e003951500d400548980b41c940f1810802c2000070041e00c05054030305031045003141010360010b0b2031405011000340805131507055140107541c0d11411508081c2c0d00510440d610384e5285018805000e01c01d5600f90a8007418000086850103a03005a80b1401a54043c0082952035540c3c80d00a4201414102d0b080e64240804400203010b02c061420341805018901c0d228500410403501e071095404035140660012101002400240c1c040300c40400e000342446640343e5110b03807042d441400d441d03210703056a44c20100c0020381c0c5070356184002e00e40d0b41c1d22444a40f5900c00c50381440600302c3c03070000480024034010000c0040c4c0e8496400350074250221000980b800400d900058113941c400c1c1c200044404444040c0f210741d0110143c50f01c0744010002d00d11480c000c0c5200003a440302c840606140d0740090004000340b011180c421a10702a01001c42e10844038202707428000d50354079503594 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 23421301 1250 23420051 23420069
    0x40302010c0908100216020a030303091b05090708220615061806080405070b0414010801080606030c0f030f1b030706020319030906020c15090c0a0303080a02160203030a0504 76
    0x40d815001500c598000000c3d10000002002d041480042c0c901c02944903024100c144903e03c400c3c04010303502d000003400194042d680c00302d0200c41300d0501d2101031550340714031840301c11200b00c20815626003901640d40030b0b00a08004c081982e401d03807400f80c1c4c182c0c100766250380e0011400ca01c5040014540c040d1600c900349102c00c604458a4510a40341075900352007061214980c0e14040100754410358580307502c06c0c4200183c1d19110750754800031040350042d4003e0741d0708010300b140d9040656840600a030041114100800d2135007040360100c4c1c0c03102a0f40c0b1145000c4d280d0080c1121403034404100359580d040e041001c480c4d41071008001305000504000080c0e11a000b0f02c480000d0340e40c4000161080b48041c01101103120030305a03400e40c01000e05140c200c5180d40c0a20074149104814403048607100c192044036200b07854030121090802030359102031441041161800e001080c0d011003020b0b4410310400c0010303552480260101100042240b0095251000141c50000298480080c00880f43d03000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 23422551 1250 23421301 23421311
    0xf1c06060203120f180304080607030b0406030b0604090611040905151219030201090c0e1f0b0a050c0a0602071b0e010501050702040c031104120b150d0b04060f0903030504030201 78
    0x40300700c2c1c40f403103a032091654001e0f009010404100007001d507a50030104026080e40000201c03801c090550b00964080040368001c0410094034540501a0002d00071003120200801c82c1180c2d2071507150700010f01560300465540c0b04c07070303000c01c126640454425000c00c04141e89541c3d6545186c80517150885240022600071540342d6007504054401d5240c400c0a10050005000202c0e45c00c0c50642405400758119900e4002c0c2401080c05100c4010140003010f2050b0301d50b1030006021a401a1004280f00d80b14107090300c00c2261031040d10070346920a1880c600306542c0d0f2444100580b4050001201518113840040c15001700511500700085075001d611000070020341c1c6542074144514248112400709104200003030040c40e00c0c0e40300d442c80c03228501300000e40d000d4080e0040c44a42180e04014180440d6550700010f000d900011982c1c86103242c243c90030a0300018010038600001c0c00001465081d185020a0400c04140c0020351402ca0034001003059035094280200a04025242607016500e00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 23423801 1250 23422551 23422559
    0xc0e04020304020a05011202090d140607020d0206010605130305010509010606120608070608090a0f080306030f03040b04030303020f070501023004050a02132403050606010f0c02090c0f1c06 83
    0x103000780d0380306030b40040c1511915480c082c0191441c6d82d0b58068035105d59802c00c00c0b04011b99905000c10304a9001d0380407000340c40b024440e03192402401419003425503100d01881881164000340b04c0341980e115107845510b8803110300050701c1c1000a034000611039406e2a080060f42001503109030225145680c0b10320b4822003513000c1c00103d86880c040c2c481550001e0708248400740c0500a8290000c40c90400c40e400d42c4100d4a4000c50740c400000e08490182001081c05071500e010090080326038140d2014528080c909416017800784118800181499004a5901c003851030703200c192110250420f00a668072445080a05021440e0035482444441e0420100c40c590350300d2100248510f9100000b085801c40503020000c1c1041d100240403804d07a210101080a0009000c01034820141c2000d90840c0c84d06610f0f0181c10214001c001c1410082c0240302180d181d94402100d40d50b80e601515181000e448401c0c81280900c9038a03c80c1c1c0e154400010074281504010440c000c44001c10b850030080f070358817 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 23425051 1250 23423801 23423809
    0x3080c031915030605010810240e04020f03030307020609010b011d1504080d020a0515061309050c03030a02010f0518070905040305040504060605070210030c0504031112010c0504060207080a0201080103080a11100c0e 94
    0x111140e5400c00c110b80c003061142b6640c8003038843d08140010800300702420b14100103460765108454507001a044031003403012403c024042c03400031150900b4520320b03101c1d4800002d00105103100d03c0e58070600116980004409201003240d000d03146000079107856584104010799100000f201c202d03240e1080a030051841c0c100742000c01d01030640144890421010322502c0f10290044200c00c0c0c80354014041004200d940803c0109000c6500b17800110b82403982818050455100410003440d407034802d4210005081d020502e14180c031049000020181c45e541000c072400c0c026504035a801500d0000086542c80e0008040d11880780300315004a0a440521000c8040c0c0310300e0082c0501282c4107110078070001d50ba4100c0c0d0314403104054640301d01c540b281c045240c00e45200d016104046180002d0034881c05a051204a015201c400028145510716a000a107030300814400600b01031400300f04185050700c10290800700301280781c1215a1546c140c2020380c000d002c01070b0070ba800715548411501040c14 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 23426301 1250 23425051 23425091
    0x80f0705012606030c030106180513020f011d0406030311010c0306060e2202030408090a0e07022d07080f0d08010302060a030b0a0308070b010303080c031915030605010810 75
    0xc04140401c28001a80c202101454003d0802a8180602c00386049141c8092048400501402c910a00300d80241100c100032142c004e04042c1c10707080000394590150b00d0781101d4402d1042c080c40c0c4291282c06010000010440701d800c801e6005040120000606a01030050500391041c14020005590104015821038505200d00c1001c0351005658100518145000d2540a0020000490030039403088858040ba44100c90071500001c001c0b840701003604145540c0e102030880320580c20180e0419007006544c0d10f1560020b10149101404242c86494000006619541f1a0400c582c0e015890b0704c1e1254403620103030b10b1100c140c480d50141450451084461904884d005400586407403021076084029205210041e50003075801c40c40040094045c0c8002d03c03186024152100360f550651400424401e030103403551000e91014001c1c440c070f5001240701950410082800020041401d11008160141c950b20203002076160070000a003d0802246900700b212a01d40d041000d40c2e049031110030700e65 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 23427551 1250 23426301 23426327
    0x31407020706050d0f060b0c1c210b1305090d0c110402030705090a06020d081e06040b0f06070503040503010b030f03041701150303030b0a0603110f1b0601080f070501 73
    0x20384003a008002c62030140c0c0003490310700060000440c18030108180c00041d20041d900070784041000150521201c801880004001145c0480d804c0200d00c0d00c0d280200050001407908000c85008821410001d8a591014441d00340103070400c051000701002c55001080c0c11500014640100410450f0940c07040e4259203a4030307841444603040c000900148002900300800a9051001c208080c20711986c807081c185008100b180d008002180c0903400c0288400d8001d0b00e20070000079540c072201c00700720140400070b9006800352000199410b00c40005480303211000ca0140d0032400004105041c424080002c2045d03032030540003440020030441c181030307071400c0503620550070f508140300c180a180056000c4030020040e00d000444d05e1092030800c402c07202c01ca68421404a0340d81c01c08042c0a06009880320001d240c2c5050411010f0205080790101d8401e00015070b82c08540054801200305000703003070b40d00400031103086848968669021950302c00d546910003040b4403903444002640c0d8172800d50080c1c19 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 23428801 1250 23427551 23427553
    0x90b130b1609180621050114060d06090501092a0503070e04080a14030c0705010e010608070b0a021501030b01060909020702060a0c050f010c120c02010207050c0d02012106050103140702 81
    0x2034503103100c014840212901c00c20180d0741390400000c62205080080c40201c0d10b120902c3e010070100c0c6012401c440405600010301071840e4108041c65440414203612079400a0b40410300c00f001e841c0c91030040007104030051050001085c0f25000f94401d9005244030541e101c0c1154043e501c07039040541d01c503841e100705242030a8440000b0000781050700138004031031480c04c1440344014030410a04094004035801089060081101001d1000900440e21400b00781c400801030141413a000588882503800780c00c070074500004844100503c00c105104005e8080c003203001d40c558403031410b601564030078420900042e110b201c2c04036614841e0320844d00c076140d004105604c1c20081e084c041c0c8000e0030015060b5818054107030511820082030082907804240c6a90750003031b60000c0c50a281c1200e07014100d8034216032061129a000807800a9484030b82003044a801d00ca01803103200413184060044510741084800c1c0c510a804054150416000e03602c00341c2741401100500c0e101e09001c60703012602c0b4801 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 23430051 1250 23428801 23428817
    0x60804110103020c0a06050406020d051e06011808010510151803020910090207030e01031b1d060403050a06020408010614090a110c01020a0216050406060f08060103090b130b16 77
    0x481c0d0300980c0148050326458080d82d1039280303242c54110480341c0403203058980c10740000d648100707030f030651182d0344c1c0c01a00500341d40c0710301080c9031100010032801020f89045c4001c102354075140748284007285006140102c003e000728940380e40030045006442c07043c22144240404c00039101ea00507000e680c2c0f500112103511984920310f408103d80480041c0048401c01203640000c03c600f1414001030021b14060f44510405025420004089039400c0b80350b48a000420001c1c004410b85c406090b0040c406030ba0b81e01950044903200007222480307203510003071851140130180c90030422941c02420803290008000c000040da159110201b03041100300307040c2e00621001c00125903580c1d03580b000c0700c01c1d0080c0018a0405804c810414220b0b40029040310169020402d481c5410003580e40e00e00241c0825101482103a1a14a000c3e09200d40000d0311307410b01802c0350000d0400d92080d808102001c0c0c01110102260800e1075140340345418110301038070300040402c00105040ba03083e0a0100340714481e0b0742d0b9a4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 23431301 1250 23430051 23430083
    0x1020f0d0903050d050a0902030601060504060c030c050114040b010609050f10030203270a0b0603030c0a02010c03020c030d0905040515130207060b0603070e030d170414010f050108030c07060804 85
    0x100622402100b01c0a1100600084c600d00c403040c400c240c441c112080c1d001668044500405261200581c4240104001080140041d540c02600c1030411580b41c10180d442080358580b150151201c008003042c40c403041020842801543c0c425a0f040343c0054036140041500c4109115107005004546a0010f44514100315094800e50085034441c0040c0c5850b0510080050a4051080e040030391440c0c030b5001002030070500100c5a04160030101c110000d5203001003031070825455420f4090003a040c0012310fa0440c0c241402440050041000202a10a0300d201d40c03001400110303c070700580340110b1805001456844481244014030040240040781c40c191910f084800b075841224104c0e143c0703445010741d61441e11600c01030360045003503403120302d65424075a092502d8148441d4081d0101700c51000074a5110000e074882ea5081030708032090a44403c0c40782480c9015020008040b45101c5c035200c00019175010200180030006414803e455032555074500441c2c03001000e64016100d52000c0c04a40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 23432551 1250 23431301 23431327
    0x606070210051b030a0909050f15060f0a050703090611070306110d0e030c060c03040f06020d180309050108161205060a0503030304060c0314040308040209090304080106030c050a0801020f 82
    0x410514402d103405403a1240100010700e000c025807503020803950000c91620403050700401c5160180410282c100302619012940341000d5101030300101001010303003010205601c0b006e08441800c1101044144d4403008050010001d40c400755054000559524000c14414030608051800c0c0ca2008001e040290031922503400600185400c0b130496041000101072805d000d000c0c000e06921004061600c03a00c802d514642008001090010000e4007081007100041900e80f03031504480c1c1260300180c455500800c9030004096082181056461a03425907040583c0900f02209641083e81c42d50003039140c18039083c10004206000c140443c0603c1c151403e030340d9044c0c1c00f850780b099008100244080d42c1c2c03000300b400c40c1d0083e1415100c3ca41c4a0f11a41c00b50307509402146e41c2c02002100700f0f80246403d40300103003036483c01b0300001e1082c410388021a000305000c00598000d854103000030440d6550768540f690810381c15120352802000b100c4e8002803040c2061080c0c441100c01c0383c012a00d88201a0901 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 23433801 1250 23432551 23432569
    0x603021809091905010203090709050601050403120905120a02040c1e0c0507030b0f0906090705010f0e01030b03060a0f0f0501080c0d2d03020c09010f05010c06021204030c03090e06060702 82
    0x800b500f4402c0108240d0801d25802c880c42110780110001640c80c02c040212a007004242c0d00a40ea0700da05050901c11541d070f001084404a030b40102c81c40c2c101f1100030400701c88200311540700f9a40100614a4103000c00340c0030a4030380c02d040c405c5800700203043c4003690944412080e10a11560000e46241c40c1d200680100c15410307425100d1810303200c3c0345840e030f60f0340e00580c042681c0d800c80c20b400110812480c648100720094200900344000c208180c40c10000920a5010100b081c04104501080359420f0f4025040340100d5980201035132014582064414000c150014004043d141403c2c500c008503002c501c5181e040e590b5201c05084030014032414401c162615000c00c0700c140b214401700641d0b00d00711410f05a40741a00781e4040500010506009192070040021503120300220320040005021003010902103d90030300f0258402c2103030f0708158000380502090064060b031440c081004250b0301044071029207100e611402c10482c2c5400c01100d810008490f01d0360003603810450f13080035240002d10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 23435051 1250 23433801 23433811
    0x230a0201020d0c030501031202061303052803020904180506060907050c01020301080601050906040c20030403020d0b0402011404140d020604090c09050111010b01020307110a0e010e0109060603021809 87
    0x50301d01016109a0b404450b009908000002e580b080144208030041d41c0c0000303420003500c010152070501016403030000710b88000040a1003c00a15081140d01c80125480320000c0702c00100404603c035030740507010354485c3ca180c1c6d104614021124042c502c245404503076a03500310300200683e503103003030500c00324035800707801c0c0b9003070040610102e5082502400150b010749a580050141945043c082c404000747c040e042c144603600700803030541181c2d44a010000c03c141071b0366400c20203802c45c0074601d082d403040b50030180d002200301c00350700180010458584d001d14800c1e0b0ba88007081e000300d004400340d400740307005402425032010011231682c0303013aa08031340c501c0d0b00040c00c0524280e0307512420310071100990803075000324082060401841da000080c448004203008000e001e95218040001d40317a101c2c0d040000c1085c2103051480006881c0e418501010300700722591580e903940c4682c6855051002449400c0800c3e0410b0400b203040380c4207009903110348603280b80c1e44901020301010403160b8980104 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 23436301 1250 23435051 23435053
    0xf0d03200f0f03010f0303080705030402011b031407110a080d05032418041703060f0114040b0a050d0f020708030a02070204090506150307080c03061b0909070e010f230a02 75
    0x410302c0c596504400440c003d01020f2266404249145006030600c2e40041240c001c1c0002881004050f0f41c22810105002c41030fa03045030b8094069217403d540541c02040c078101c414030041000010020b6182108090080445a15038066035070701c41640c0e1607000c40c0f0720304005031042c004222580307080e90105c1b65403c80c02e81c080c07200c0601c0c1c4011502d000e08562810510351244010b1000b404518440140401314210340303d807a500d416000305041168680d0040c0c1001007015107070100c0708821081e1340252481207222a5a100d40b8900146290004040308840c54645468021008007910032501d5043d84a004682903560b00301c145070081d00044400d0303800c55162112100014405d00816220f1000303c6c41c041c550750b40720000e061030020356420a00780307640301c4103202e001c0b40da000440740d5022807030ba050300c000e0198000350004103000c0c038501150409142400e2050050304120000343d1f0b07078402e9031804490a103800003207500c02ca8032418900014814031051203440170445c010300c91110180 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 23437551 1250 23436301 23436307
    0xa020403060c030603020f0d0803060f0402070803130506010e0103050c060901020f0708061f0803040b16051b0108160c0206090102010e030417010b010903150f06080d020f0d03200f 79
    0x703101d24041d0b51020602c000000d03690b01c4140114038084c0040100c541080d11741c907a6070400c0c2d07564030b4404e00c005080588100519085148543d80d1501281d4549500c4252703542c503410b140032200c04100308020200d4980c0241000030821f8100c095155040b250000300500548103804c00b80403003039024903203240c114051045043c0100c0c60030000700300145000d000610703180c900000c0d01240050710041b101000e4050300c00c2040055000000d0300c055a440f0b01c44655600c1001042820f8420028030040050041070b89180ca1041c08155002100100707888a003042c3d41d50000d15221041001c001c440810f04901d21400542441c2c009400c0c0c82806000015054000b141c40d5861a049540291107901da141c1c0c2b5038650000178064124002000e081580b0b125045565843d440000300c9001d04115070b4880d0941c0300f5007050340001008102c03900a5910201000c040291145402c04203042e0500c40d1280c0e00b805a4400e00c44c850110b1134100000050180c500b014a10700da2102000800d0401c081c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 23438801 1250 23437551 23437553
    0x7050102030a0203160c0e15090601050702030714010c020907050405010305060109150c0501020f040e0109061409070806060904021603030b03120a142802010c0801030b1807091a0312030702150a020403 88
    0x7c031144034042c419072501c04d285d504800c0100018441c0042049040000c00d11205e801618009050700589035401108445a0366140048580d062001c4004e58060051002c1c00392660304500144141d40c400c0c1d900b48466034403080107450305203481c03081e1018200301801001c5018802c1010b0421a44608005071070030b01920303003141f02030700550007010103080783d400100440c01592044d1030041a000007901840312076100010300503800100b0758400d1160540015000780d4a035021070701c1d030f140010411500c64240303448400341c4180030081100070134609005111245000500c42625401c040d1079540380040d00142180c1c00900708942030040d80041c41401500041c00c095040683d414032820f0442d000c00513402800d403442d0f5807100f800c2c0012940180f000c1020103100790350000c2c07500c6060002c0d60034031090500c1d1450075031100c00505e25082000041c102403034080800000f00f24200c4081e46d1380040c81d110140b2003592900050703404841103094001504081e2580641000f1006080c84d5903 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 23440051 1250 23438801 23438819
    0x6090411010c050d112a0d17040605030114030c0319060b04090f0b0a02030603030d020708091503191a010c0203070305060406020304060501140a06030b030304030618020307050102030a0203160c 85
    0x1e20341c08183c5010201c5d0707810a08020040c5120b00c15001089030072000ca580c04190702e42c1002d134501800c50700c0055005d1010a003500803100c006019040e99031a43e864009285800c28012500c841d11429182d0090740340015103c080300000401030002c031183d81072400111303230240c2c1d4220380c4c0310b896803000d0070706554501c944581702d4010548125004c8480c5403840d001c1c08024411150b0a10510501034683c80000948a2005551200590742d00a90918100901480040c16806210300d245070b451140b020000e5400384041099030010b0364000304604094400c000444400b0b00c1446100080c10340c400d40e100c0d001390380040c09079100342e80c4a0300d40c107007000b030110f9080d50826000824030042154a2180714010b0a100704803241101100d000644200c0d40d510451041603111020301442d50340034800c40e8002c1d81c3c0608104407401d030300d41e9111036859152105034882d0280e403074005140d5001104072400b80d46158003030b6160221513010360107404410081980c2d603880009021a4041c2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 23441301 1250 23440051 23440063
    0xc050a020601360207060c0801060903020d0f081306030b01020111070209060406031401050402010e0109080a030f1101060807090b0a0303140c010b0402070308090105090c0a030b1305010207080a1706090411010c05 93
    0x911060f02598850702420800240c83e5605204400c100005c07004220b071359402890700060765030481d101a552404d5042020660483c000090641d0500023400c003200000751020108403034241d21300b480045091401a030894031180140c41c00411b0802c070340401450021003081e4001001440020195103e88031982c1030120700c465180f050f9540c50601055682040414a101c03009103031540c100f50510000d251500031411004042c45542c03908045414000c0d21900c4007100030304000c101e055621245140e80f8402c510400c3c10343e601e0115030b42a1030510a0320b04058a81580b40c0e0000205038081c1c1200990085281420035586c401d036604540e540c0d400107100041c001da45132074013170803c01401421a0340180c01d84940e6030140c0000401500e46000c80350407283c2088800c4415501c80c50303550200d40880d0030082113548000707242020400141c000c5c240003106c503520b508035140c0b14040281500b4040e10055030128001e000113000580e40c0030407034094030043c03400164404482e500d10b0700e010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 23442551 1250 23441301 23441399
    0x7060203070c08030f040306020a030b030d09030b01140306060607030309050303070c0203060f1b07020a0509070801030c0f031e1a0a020913050c0a08090a081801030c050a020601 78
    0x103000000c1d40c00600031001d81000140200d400074500c1d03c0710300c111150070382c400c0e440024405600407032300c2041d66000390700c11510448040c05a403030404011000401c60146800203c815000040c008a050248480401e007141e0028008045079102d44042068076080000c0c22401c040e200e50082c00059400e001442c00390b0000d44a224080145104050a114000703280c1c0b40070020320b00030440c1c10b000c420280c0100f000b101002c259500340c05c1c0040340300904560829030b003200c0301800784000540e2124403241201d000b2031207003445949a40d5018400b07110b910001e000441c5c00440400f040407103413500c69000b07114003007008040e000b014021003120801c8414242650780841c0c400128206140000d002e080031341020402407501ca113000005005101503a010000a90b00181900d8020800b504059030022502a114491811200d00c3c018100f4840b40c000381c1000c0503480894080e6059905520042d0003a011683c00c0146404044030784008800045400032407508158910f40c0c0c0d200010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 23443801 1250 23442551 23442553
    0xf07230d0914010207050c040b040e06040503070c0f03080405040c0509040513050105090c0117040203010b09041101090509070c0303110f0a050705060105010903020612040614130b0906090304050d020d05070602 92
    0x24070300c641490010240702070300c0d10030b2a074010002040054008030b4080c40c2d4110454000805806000100b402030143c800d082c0d010f80b2a040600060000000180c10108d1144548009454581001501003907035440010640302e401d1105006902e0103410154201c805031610034140208a000502a1074007600d00c01c8004148804c03030011300200317019403544026000002c01c80e05521500003407070303010140034104005414801040c02c650f02074002c1d402a2400130030310b018906150070304428107546a43c0c0180800c0003a600015642003040c901403080b01d094070b5212103c440d5440030f84c040c100111a222034032100704a08160a5048800f4000022480d81e0700c0340c8500d02d51030709038900034040c1c12840c1449603070b00b420070050303a030481150044810701021301083d856525149000d05180070707031881d01080b00c104011079841206d1885c00360500a0318180e048d51280c4040a8541c0c0090f00d03054059001080184003070300341420307005455031001d021a98100402e8032080c0c00c00c07580e0b805c08001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 23445051 1250 23443801 23443811
    0x90618060f0606050d0b0d06050403050301080105060d03050d02070c210303050619030206130902120613090201020c040905030405060403030315150203031506090316080f060f07230d 80
    0x5000c1a8425803046403512202000250704003070b000f5109000e61001d50685988589000b1140d0301c1d03400091000c542e02100a110744e051900d809440f90b0400d01400b04a5841e0a000070060310700044502ca60f00c1c1c16459481c40e041401560350065440100c1c1503540000a030000a5030346040b403581e00e103100543c0380400303094006140040944602074440c0d4414560400020b0200500718803002c00c0360390499406030380340440e907003c18031183d0941c400c1001510204044900080020302140320304011601001404081c1d0584030071100003c4019005900c40d0f00d0061440c01c0581c01307100c01038001c408581c2030a81c1c480c000b50403a8059041180041e4803900c01514412400c0040009020141445524601c1c0040000c4d92804000e049a11a2401500c40d6800d9294202126402840903043e2240e0824516820b100640c1c00d21610002d40300326500d440310220003103903650241c107100e17511045648614500701c400d034606500c1d0b04d00340c1c4c1d6194000b0000140d01401490210030b031000c0850 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 23446301 1250 23445051 23445053
    0xf060b03060405030a020717060106050309100507030b0108090d17070c210201110f03041203090204090f121b020f03160602010c0e010c11040c1407030804060b06040609120204090618 80
    0x10a000d580d908c0051140c1c0d41c103e203203001c08008504103054850030b190860b140d5496600075440d00c400f06510010140c40c24052181403649a044802c100b82c003a00c481e02d0a458080445960b070455090138000180c0d20840e452100c45070b50207194000300107180c0300c0f00a1322a40c66241400c000035084a5100b039003010540c25082c2c084c00f44410b140d07801010a03080441c601c200d90a144070041c002401701640d03140c0380c40303c14001d610031604550050420031202e042031806501314086018160f034803004481c40310641510379a04040c98040d60f091403414200c0550030311a4403508500800e900d8022030040c41d00c0b0710118140a00108002d81c00070072140c2416801601e24906c08450345d041050503075000c0e010844034152a0300b00b10341a1000603400360f800300200c2d2120004035510520940010300c2100385948160094051070191104100601d0740b041005854800d0340308640205a944404015042e17440401d881d2441c000340c800300d20710000f51713034240450300889241005200c0b02d1071018 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 23447551 1250 23446301 23446303
    0x30b0915010203030c03070201090b16020f0f030f1c0905101107080301050d03090506030126010902030604080708130b07030e030106060e0f060c37030801030f060b03060405030a02 79
    0x64002105154100100c40c05200003500c030301c40208200c1e01d03070000001081070386200754002d0a003240c00503c01001030415112403500004800e1459005220300111a055910046442900c042c0b0140080d03280c43c079003210100e2550803150f1011402149a1501c00c1a210580140780381188140e01818074856000440e03000c8070003510700141e600360184405800941890300b107a0541340200e13a040e08086091800725402c038402e40020f5003100d0b0202c00000d0500601c02c9a8554514100d403a646007130940d8801c508035190600301a40c150b000324042404110f10f04000c0c007a01d0300500400e4035208466070110440a0745030b004010786100021004245135208110042c41c1c0400c500034444685802c20003003a000e900d6100c58400c080c51b11542645948034001c071031003200c0f0750043d10303500c4100205400c00070380d41180d224000d03a404039042c1e82180c2c01400013543d02d81d158490a55a909640b20b03224508220441116110b03500e58149987c2d56040040034401c91113800195130b00c404601c0d0003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 23448801 1250 23447551 23447569
    0x3020306010e04020a0e0c16050c030c09090601030b100f0b0d110310060e18010909120c0c0b090111060f0601110a080706020901030615080609150105030a09030302040801020406030b 80
    0x40400b46285018000140e80300c0403003408a4010f003c40030029220340c0ca1480481c8910b01594601490071411417040200105101c00100c074224141c502c040941800d10002d080112a18121a0040e400510000c3c441c0000c07160071540c5080701003281034450240109110b21900140d01c55040400c40200c4200741d80035180c4145481003010b400d505000080000c401585e0040b0824002c206450400395160807030360b1241c0c06640f11841c1215651044110005c12040300140da499000c242842030080c0103003d00c1c009903902911842680d40b070090708211503080040c1050400800101d800c10a101c03c120040c01252007062642d40c0b0f0800400150400e004030042c01a00d81000b01c512010850a005540c491071b0080000742c1d99001500049000300b140345c102c0b4890614490030718444c2070344040e8991040d08190781c0c00b01140c990141c0f490780c01d0031511040b07001680030000544140d01303a4104030170300742c4070303080141c213003500d40e0305060980e0800e42041000965642e048941031030705a4003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 23450051 1250 23448801 23448809
    0x705010e01050702011409040213090b03030c0607080903131d090d0507110d020d0507060f0e0f010f110616180602030909091204060c0201170907060f17090102040302030601 76
    0x425604140d0040c0064214082c6240190601150381d0040740c2d28451802210130340000100115956407100025084036031441c021355401500d0403001c038032103040003c01c58501d005000c000f880c4968419070101c0c0c94220041809110f8007061001806085c54040710402500100c49802c000301304810080c103c0100c010003034070455001c80201c403901500a401c40d01c00b1500f01d10042c40200d001c0340494813a285440c030094100c941003a0328000d0000c00704040c4260785a1382d50300780282e1400242214001d15042080341d0025009091209960103000d40305000c0340035080041444526024403400c000003160700e681490344a0404d1148070360303c0010b1305100d00c1d003001d019514030704081e402540c0307000e04d0705040c0c014128600825110002008120400c2c60a003800c156160b807100700090088641d804100e000c1000d600d08400c4110749559454800c0400800070000d461a02900715000481114080e0030701c0244101585980d41e8010f07100e10031f003460400940d54a1942c8141890401d05902c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 23451301 1250 23450051 23450057
    0x60c0c02010503071107050307080d02061b0a050a020c030105160207060309051002070f050304080c131a01121d03070b1e070f1416140703050a02280603020309070501 73
    0x84800503a00002902d030001407901e03040c1c010ba040920ba80f8074120180d040580d05105481002034100000508410046981d5007170f40c411342c0303490300e51a14203101214030905040c0b051040410141c414005801310b404030b44105c2da07460b004600820308481d015503200314156640003851308032917010007118000b4209450b0801c2940c0c1c450b10b07007a85035824480030a42e140d400203004030a05c0440a03820300400c1e008030689644541d0b40c180c0f907a5800300540c0181c0500850450703c0d03031a040c42d1217040850342d14038003509139041901c40112100205400c001110554481d408222143e540a006c41a01103002c011585c804260038801e210550044c480400c0038214190750303022030341c04106150030199500300f0149240c113580c02501c152100c500c4c0100b5990340880c3d001d4154403a440003403481805004206230000200c042c050300e905041c04007a200380e0085800c1401401d00c0314410555039005888240806040c00a5444580071540041d00094010080c00f00c110004e1103250000c0070300342 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 23452551 1250 23451301 23451317
    0x9050610080d080105040b0619020304090f0212040201080615040b0c010b06131205071a0d0b060301080a02010c020604050607140c0f130c110303070207031b050603010b07050c031207060c 82
    0x40b000401d2980305010301801981c40f1400042e4980360b000548046100c1d090030611090f91481c0000d503682c01601c20b0250080c1003641000041c4200e00c212410b1000095401929980700c0c1c0040d1041c90014184c950412114000201005e402c43c0192004e00301810300d056446131043c5c030325130a43d944000000c0c0700d40420000d103024045a04206002c5502c244000018a110307400c0182c10840240c7c0021f408107801400500503401107401090512b80c110b004006204a0f0010300c0120b010900036103c0703c0e800b01c000480558021f055820016100030000f51500d501c9001162268120402c210f801502041a010901c0c41c14801303a0320080c1c05480108000207150001000720b4458602490f01c2d0ba51040c0d0310f15842d01c40c40d2038001d0f80c0d02c45c03001c5a640342841d140c000d644624510003516200300049811130400406030440003190030040c4a281035034240303440d22541e5131208104480502c00c4503c160010788042c07018803021076800d0380c1c05403100741c01d00740320b0250b41c41609040d003000018 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 23453801 1250 23452551 23452573
    0xf070e27010504020c0d0c08070501060609080607020a080a030b04020906070302061902120a0c03020c06040c081b09010605090a030b010303090302040b0301020316050c010b1504140a080703060504060f0905061008 93
    0x844249420151a144140f94412300340a100c500c01c0303110285c41c0d5400c201e00803440e141c02650170301c121490310040316115075822401700c1c0c5420b51200d008204010400c04000700d5407203500309290b10500280010314200c4103400284455111500850150300000d041005402444460356250211010107510f001c0c0c5614604911040080036030f04007a40d150704c40719180d88260306468070703a910b503000c032215400c1078280258104028801d02c4030a1141040d91000082c82005040303501700c014092141690801c5025201504001c0e425500500c542800102040703d4441e10ba0095019481d2440380a0460040c0000c4c5c4000c0085540039078010014040b41c5400c40100790034040151602e151558120f50100303000d0844000d4031a4404400c00852611400300c90051084880c1015000f02014141c81840440301a52103240c1c031340d40281d1020000b04007645c100d940e1203845400000380ba00c0011004134202c9034800d0f4261200d511800030810800d080304042809028103200074045820742c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 23455051 1250 23453801 23453803
    0x6010503070315020a0306050d20060405010813020402070510020405030709050702150414070603020d0c0908030d050c27010f020111040b0c0705030607020a06060e0408030f070e27010504020c 84
    0x3280c10f2041c401c5500048400b0418400d5005102a0100404442c03c084542c100180318640d46280d445403000c0441450b186494800121800c03500b06850700909a0340b50005d003100340308600c1d401c1e60041e408211200c0010010700042032400d40040c0c005807243d060205151170100035070000d1404501d41414881c601d0380000d00700d40c4502807000b41071500e507140e04d40080e88080f003035814020345c8159a0041a0640c15070003030002ca802110003042814940320040314040349078814074845400400480c003910103642c00003035100100c00320040c030b40008480d0700800180c2c02c1e49101072542c4e034000100150341e4400d210082250452009102a440071818038a40348214400c252240d030000a01d10005201030040a000f04001801d5502600d04088041d40b031396001c44040311014640980410070040702113010b806640c21004a500f5652151240510300801070032520600907400080d45080d6030f04102c41619650807078400700a0021452440302d10f19042e00030138429401402050b0f54044 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 23456301 1250 23455051 23455073
    0x60a110c04020a0905040c0e03030307050714060103030c0807050307050a08070318050f0d05160e040203070608070c060209120601090608011103040f020906060f040b070c0603140115050c0109050609060105030703 93
    0xb001c4500081f0140000c1c425100c1d41089001c0b41e40500011040098132a0800080c003107581c01641e0b0b140c2001b00c609011603e443c400d0100901054800300402c010800d40c01c06011034901c60002c8900d007248a0301c565140980302e92080320021400030310202016403010420840c0303465410403401c020b0601c0e00041400b0304ca1000680684030f080c0101051100800c4440e10f502c00d0070750500c080390380f1880301c0110424101e500341d000344106d010000b161407050b0000c9100d801c1a41c0c5c0c5041d07554103540c54201039441000130035481340c3c80c000020a03c107001d01040c1d0082030410800500c040c649641d09003940c4002009800b1540140300b080301141e0003800960340950304071603e01403581c51600107001800745060384004100085400300d441c90740312000340700361400f0f4200710b403519907a54421000d503160030511400c4c4840310001003040540c002a0454a0748150512074140721b44059540d003101e95180040e174013130344840248141650284501400b502050b0054140a400c6843d143c0d2441 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 23457551 1250 23456301 23456309
    0xc07170f150a060b030109050103060b01090e0601030f02040e070807090501091d0405010212040309030203010605040b0d0f0618030203040f0e0601020a03110106150c030e01030b0f040b040b060a110c04020a09 91
    0x66401400914803085030f60001c009014900503050b1603584541501000302802d0104071011460a002c100d8958003030810041180c4110200d03c8456844500440140c0040109804c4079a002d02c000b0442c0c2d071769911410b00c07601e01382d6030312022454100401010416141c1c0003a05010400d803051201100c02c003100814410100300081e603646440c501940248181d000c0e1040c2c0d227844109200c10194403804081c03c40e03000320000e200d200c0d1210104802c0350f240e550a5944803814130128800110409690400d940c018103002401600e16103180701565461901280140c000040c00c1c04203000003d840340240182c61282c0400749070100c0082c0d640c401c1e1740e1010b0140501c191089a9002007504010054198086040118002041d000e003945001090860105c3d075203080e040c0155129120305a4549001480b00c8446091007060000400240c14415040b585815034001c283e26514010400c5510780c0d81c80c07010f200b220001079810980001900c074030980c0100058030029078882c219074196 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 23458801 1250 23457551 23457583
    0xa050604030209130501051f06020c0901051e0a060c150c05070b1b120a05070e1f0309061103090601080613060c050d0c08070e0102030403080a05070305070501020c07170f 75
    0x103441329015158001c184490040003503081c1b60800804600d0b8000d180e2094013480800c0d0b000584400c0140c0e00c603003c1c252029003251410004012a1518064607940340d080f002030003501000c604085011084941c200d03030040740c040782400e001c104101140e40c94007502510200f100e6406440700620341e100301040540040c4010010494400c102e401c141c08404100000c9030f03480310710311811400703003604640000388186090006160300307005014244548000400c0c0f9a01d06113100003140315a94409180d40406075603c003d4800180700c0e125000f610017071110255120728003c0c014602d003880c141c00030b0b43c27135802c004140300008540a0311414560b6003c200810314140c4000e040704d40380101940c50b81c0c09800c2c201c180d170340d2a070408034090084185945007031076081004011382ea0703440745110003800048208000c0104d10712802c06003c3c258428500b4603d00407190311113909a810800750380031140c021600420044a8210103111442c211002909c4100c1009001c1619941c84074040055 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 23460051 1250 23458801 23458819
    0x70e04020a0b0a0315080a0c090c020304050307240c03080a050c0c031c060b090108010b0c071211010e010309050c014409010203011503020705070f03050313050a0506040302 76
    0x215581c006114000e04481c0030400d8469001e80c0000780078284200010500c0e01e40c404001c65604030100c0d034641d115030000c0102c10b084e49400c4000d00100b00304100742e001c5010a100121f0180ea09010b00c1c4004d100e8a24140300b5282800c0c00b04445a00785004081400404107803000041d81045580d85d00c400316010018103540c40300e40c05802480740200d81d21140c000010500c000056444030701d040d140803850100302e000c4d01d55042c82e01d540700e030041550104102100400030185400002c14092401100762854960340302051300d81950305c54012202113807511100c06e040e591129610000e41001d10702481844c4964640c40d4540d15039580280c1040f9440420708003c4950042e22074150f48405a00903644540c8890210340000034115150f49003a00000700c3c1a9007814000d980c103a400d024082c030003103403180d0303820360080d845003000300c6641c000e462000950188c0070484400850142024607620307114886003214444880c0c00192141c025104103100301d0701c1d40010789044e079906445100c2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 23461301 1250 23460051 23460053
    0x910090512070b0420030309040203130503070c03030f0503190b030114090f010501090c0512041401020307050901260a0c030905010608011d01020c06040b0c130e0601020d03020309070e04 82
    0x30510455641c00014080002420b074100508008594400c0e03018604446100c60800313421034905826082d03451741640140701c0c034031203490603900441d0444031000f003103c0c3d039603144d0b6280d0381941c00160b030036161002d142c0c50800074035070131400d0503191410510f0030350310b1803818150b100b00841c4410301c00302c14166540001412510254400b10a280c019018000c052500d0100390340e03121464080590154200300002074a07441500400820850580324141026000643d1607404000203009940c82034080003841c0e050a028030065010340d81a5403165034605440780098007040f00c0c2c2801700d41c0420541d05910004600c0c10501780c000c00d214001040130040d07000114054000650081e0081d4600800014a8101548a07c1c80001500e8102c0c1c0d5010201b446075081380035100100409030012000500002c0c1c000200030317404000007466038102043d1103a001103020a903008424254406018001151780422042904040c24a019891890610b401c0b0384c4482031442181d400d0003942000c98 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 23462551 1250 23461301 23461303
    0x3080a0504080909010306060f0b04030c05190b0a021b030a050a060b0102030408010608010902040506012606010311030702010b0102060108030f0f0904111206090114030319030b211509100905 84
    0xf5080e0000a113500749950312070030028000d240e140319545401a00840c0095000b184100f6101140e4100490f80744541c5490f09220f4000f002003901e603040d00c245000825506156405898110f420750700820200321480c100300b4450380c001c0001480390744241c1d044c000140d00090740d000110f5000c00e0105441c044000141d15600981c1c01102d03e0303500308000480d0300300c4154481029a4001c0b1014000ea885190055403c880316450862150040c0950b031b25181c4001c41003241c2100043c50002030710341025500c0d20b0b4540003550502c1c0103035110703100300340b8543c3c0c100103c0d80940700c488003440ca850480080006188909562140c0d0b40380049686041c036599948405001008082141c0e034031201c0049030007000108481042c03203001a02c00214001020081e03113900c414000d0000d61410303503407401691590b03048264600405403160628074994441c40c413010041e040c2940e900c0c0780c0c0c484180c5900d0504a04102900d107050900042111003040010000e510810400c000140c118032402c000e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 23463801 1250 23462551 23462557
    0x102011104030f0b01090b010c032604060b011202090d0b0402030309040e0607110307030801090f0b040c030b011d0d1b0819050f0a110103110405040903020a05060f0403080a050408 79
    0xc40203640000c10300006000c0640c0c40e20a00a105840d1110640e03221381c1030000321440542d940e80096141c80031007000034007503140701a20384511000711920304210781c4003840928044404848447d294011540c2c1541c00c115490f84802444c00c065003410f101d040801c0c00f410581401800c45c048000c085415074400380111401550050014040c0c0c0704440080b50b81e076030007a070382140007558050f04000d0208001c401c0e1004c10307a0560b125280f0b81d103085800800341064200f503650303440d40c45010f0502d80c1c1c1d0714070500b00003a0050700c01040f5950b40c440050804480c0030b000d4240c81c401c100e400e0301c0c030742d03207209941c010203500075200c040030307032215504684210039a0807000300c61286501e0030420410700c000d0703201910310801c1103a01c80640000d00603242c060a0340000c0c00012125405504c66001b43c02000041125401c0035041643e01d00004050340e90001040d40942c011074280020f01c802801200d170b01240d0020401c483d030070140d800030a080743c0102002c803515510b401080400c5180422 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 23465051 1250 23463801 23463821
    0x302060d091509050303011a0307050a050a02100905060907050d080306040c11010e0c0901060203070c090b01020c0a0b0a110d0e1009030b040309061d0303030a0b010918090203010b0405010b0711010201 88
    0x10070007864820713241095403540203018100502e4110030046000202c42000c4030304c41d01141e0b0f14a03082c446820070540b00ba4000301e4146041d40904456055122124808d01c005240124000c0030241400c4103020b0400581d81c000354060410b55026401042d040d80840c0c0e0400c2050b45c0c0010300e1441e40750101c40c034428159840c0306550920002070240c40b000201c408003110101c840c0c2c14140d90340d00c0d003a41e59114450008129000c00b0508020340c0d1100d50116010400600642d07013034400c0e200015001c40510b07006203000c0c840110b17013000e05070351101c0222036001d455401071520f00c2c000040035103484209010584120780281a4500b0760340f01d420300388000c503440883d080c2a4102498060040c0b0b11501614000402c160344400070b011000013400003004018010394a5074448950500140410440d494103001c2e1140c00003404104500305001c4102c6c8944000440c128a4030403d800d4484202440e0703c968200f00c014410010461700301c1b640f055018200c01e04100c281d40060707003d002e031040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 23466301 1250 23465051 23465093
    0x60c020d05240106140304050a031409060c060109051302010206040602030a0906020c0c0108060a14010c060204081501080c01050307140c100501080d021501080312090705090a02070506100302060d09 87
    0x60502100b4841480c1c46068520a0300e901c480c03006a0810f81200740000c85000c1d209a1100703845030003280c014207108203103401d001286850711103440042440c45d07208421055445d4042001008034601901c107080d00041c042c01000c8020b801600000d50f2498080d0024288a900001084001c0310b01e51040c1c9101d03501440641d2211148010aa1111281c04402e4045081d102c0014403e2074a03400001c20b4610031503a0241c00ca000d8801100d42c102881400c8803400c0d800c00002c10b0414040003040d120104000600095605100c6d661742401603000e5810305114042c01070151141c1c01c0f1030320191032501c813044a51500710241c1000e07d054101c035400d07504c8030701e000c00200352284003040034000503906800b294605103e0358408108c0d001d01344102030740b0707030420b10810100703a1003481c4060b008015a001c40369503075142c0c40000e03a03e00054034940c4105900142d1101001000d001240d403260301c003000c42d140549960042100385c40740300500b8994580e00c0040c01c0030405407401c0300446d002981 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 23467551 1250 23466301 23466343
    0x303280b10030c02011a030304090b040b0604030b01030510150e060310110306011407080403060b01020f070806060a060206070c060e0f01020f2107050901081302031606030c0306060c020d05 83
    0x1107006002400701200e140010750800c908103107104c41c00c5140718004035024004520385440c5c924600010038440f035440f45d1240d15600c56403455501c910103400a940200032003901c55156152081c5480a07691075590181d04111500c1c05100b0888006002c84e0300050641a0542d01d400000f0b090414405540840ca481e06100c18100c0038644003030b520420080c2c80710003441e0382006a04805000e5590005d040180c00c20052002a040f5040b20304082010300454520811106c03041e8105480354026441a900000800006103030481c0030300014885400548032904004400500e0710903003480280c041901d4100c030111401040002d400d560800700d0003152035240041c81c04100354490300c28200d00d4005002d1041081d4212801d26000d903407151600c2c1d00d801000303c0191803142d0014040107003030104611903c0580c6051085062002c1244e4040c11564107060015084502489644040500e00324040c09450b4000210714038a0b5012900b600071030042d841c22a1406002c0007100180109075 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 23468801 1250 23467551 23467579
    0x10e07110a050607020607050403020618010504030803090a03030b0105030403081803040f06050c01110301050d06090503040b03190c030b060403061e18030206010905070c0204090606050303180406080303280b 91
    0x2142244c01501c0c1542034401c55200c5182c110380c54003d40c000a548800c04100740034001e00c1080c481c051408042c1400c41c101075a9884054060f0001c851051007600102a49810103505129414070302109080050640c1403985000b007200d00d0081402062000b4114030141c544410410b4500802d921900e00310701549a440c01442900032481605da103600302134941d503a603240401580d0503560302a0507035054954030b4840c031018101000042c0c0d000d000c10000402d20b00c2c428802144100035210b0209102c485240d6200200c0c0c540c2c10080040602c2c1c4000300d00780341c0d03408045504403600f002c0041100820b10901c4e42c6030210b4104034801984c03901c92030710070311085a030f11030030818000c0d0241d669503a030342c5030028181c1380111220310002d00c01c02000801460258441c80026010308400203d49841d035022928550040c191810b0445030344030340d842945410f0144c070001e040d90002450442c240920303d207071aa058804c81204103102c0b0300404006004a41c411031280c3c000234602d0281c8060 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 23470051 1250 23468801 23468803
    0x10b0706090c0f06111b0114070b0a060314010e060105012703050a0c06020715030e10050a05061002120a030902190306020d050705070c030204200301030b07031d06010e07110a05 78
    0x207a44512400b1030b400501c8464103410200e00d841c0e90381b121800e0031a44100f000b00440b0000c038082102d504d280021310010003c100c840216506c14040c1c03da000a0307240c2182403208010101e00484034075a03040c44001201c0002c0801c42504568080c01e00160380c1c0400500030a40790b201980305648090710400000a10400144400e401806103030362064180d2265812071302c803c01e500801e0701e880f08500fa00014a8803a610401050303600380709a41240d20764088241c20303103c0036039045044907240c2d414001c103880c201700700202514031800146a0070a01d0548a016405040380d04000d160303451081c03d0664498031521000303c0740341145030712919100d01d001c034025000380a000039010700d0000013803506130103101144d04603900003a10102c41407441d070030000503000641c450f806400014490011072030001c005503000e540315800e11405031030b1a550060403245980f2112107048442000740310140740205a883c1503541070141c81b4856a0303000c6060726002000390100800d441094254424010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 23471301 1250 23470051 23470079
    0xe0d0807020405060102030c060f0c1209010f0b0301020a090e06030102070b090a050d030c05031807050303040b070209060a061209021c08071202030a021203130f030206040605010509010e010b0706090c 88
    0x1c801c03241049562918401260f99020303002980300568464004075004c800e2240515501152841d00207280991003ca403c1c024036081e610910039030b44900c1c0e02901c09091f8044e0319604a01503008504058040b00000c04030340451080e00d000c0402507000c503415031401e4044a200d69002442c9107858140b80c92000d650340c02e81c4005030390601481150141161003801131482240c15651000d0a40c2c070742449100740cac040340c01e107030301d070b4600c907201000650b80c5051014000034820014100c3c1c951038107005010329194000c100c00c3c49866004024000d59412400c15950314901000010704581c441c808502120b100c240414125565030036800d0400c040d06004040051040004005446e2882410390352030003914020300158200343c03100d43c84054000c0245a1080f02c0d03007200c00000081da140c10b4100b0760301d800e05a0060300580100818440c050117030600625080ea40c4020641c540075810b444c803207060083d07064040c00060306005000c40e07a00040e00088d0000001d4602070307334899034181016 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 23472551 1250 23471301 23471303
    0x21209030a031a0f09060f0a1404050114010c1205090301090609021e010807031503020a08030c1608030702060f1c050105040605011d10050c0601090f110a021c0e0d0807 74
    0x342402800c44200f40310150705a11060301402d0840d840b202d6100300281404010007180e003105000030007203000e980380340c030650040c43c1c030000c2c041c150341c801c00500080d50700c140c01017041c12000ca51501e07039507640488044c02e110f4000703400b680140c080c0031085420344525180c1550542c281204001400000d61080b02500d108840f0b01030444810800c1c2c00044d0380202d502ca011a0801c0c000900850007500841500200c20001505494032540080d903013036110381182559038408980f150721440c04100340b940303604500301001003252401341d05070b07a0b030321410600900605000c139000100a403400251122201d2080c040d060021000808070006c003030901c14584034604002002601d54084c2003001400c01c0011445191040044240450500050a07842c10040c040020607084d4009011041c060044d1000100d0145041401e01066426404203540005400c0000e02851030b00011180c005c1003001052000d864aa400c040d904604804500c45c1c01001e800c580b40d04103d0710000805c405 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 23473801 1250 23472551 23472557
    0xd0b151309030903020f030705030a060207060501050306010f0521010905010e0d0513090e0a12020609010510050306040b07020715020303010f0603060e040305030a090818090109021e0d021209030a 86
    0xe0000085020541c0c9401e03201401240c0102c4050025040000d03014003d0300d006001c0b141040e03a20004245000ba40400c155603d940c0851144c0070013103c0c1c02442d00424046000f480309504120b0ba03550b001186100c0c542c4240012145981c05c241050000d2090010000c020880300c911800c1650180a0711640c030001c074002d460070ba0380001d010f04261307180c40c00e4018844100342d0804044c800280140c0030f010300d880c0708845030000016505a04e20814640d01c1d800342445041c18021182510b20280801a4041041109100688000807010b0740550000c40c002c10070b0b12100026405c00d840c0340c02075000307032032009016031420390008002c0d8101e0303884881c51181d00d40c0d80c2c40c04504444540c041e03440d070b909004011070040380c8607101864028184010000b031011581e40d5014442c0d0000740d4010b41c41c60602a04442458100c86c6140100702c104000e51512080c40742080d070994090009800c010008101900c0000203681925660b01d00d0b02c104001d582004901513a403600004244000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 23475051 1250 23473801 23473819
    0x12020d0201060905070e040905010608010203040804081203150105090414010b04030507050402040503031e0f03010e0a0b01020105040803060103090311030a1707030b0f13020c0d050405030d02150708060d0b15 91
    0x10404620486104803046e42d50106159400c0007000064050540103549a40d01c489000c03232400001e100950080d07204102182ea500c1c60018414140780400401d81d07801642071040200482d10f00a00803400f243c2440d0060340c9503074420003e8010000c100591900e51075402c000718030341e801c0b2001401601d000d401144c5800c0e5403a42008143d120300d01032a60035070004e00c5032102e12403020020a40d00d8945040c59820030520400c6d0380c0c1c580e0000d030b2164184c401c95030709201021b14a4851280e5490302031000f401980b9003511041351500c0007904050425030f40c0d80000051511580c08148854205000d60399900c0742c51400030044040c0e02010b002c0d90f2800c0340480c0c4c1c0140039100d0b1004029026218000900e440c10401100341886401c00a009400300f100e141c00c1c1400740098101d241443c0c8510b40c81e42e06150505d0b140c0b580d1116100250742c0102d045042204008030b04542c000c1e4145080e00c41b40d6910700205000818a42004000c50501e405100c09031035417000c010342280b0242e602c484 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 23476301 1250 23475051 23475059
    0x60d11270f12070b07030e090703051311120109050609160608041709030d030c26010e13050601031101080a0212070804020402040b070809040e0c030303010603020705010912020d020106 81
    0x6110100a49003036010490510303108042c00d150841c51441c000036000e440009940300c0c101d40c00e6500119044002551010a190092900010300c580007242441c003003046203440010100c165094240c041c12140460108840369511050000010f905e000c0080c449540d062034040d036140f4007078602d841c450140c1181c1d01030b4a01c2040005007110955500c144d0f80d0b85850700c2d005e0014a242150942d04102044091460b4400704020882c9200a40c1d002407460352a4000415421060100180d1188040000c1c2241d080c60510301b4151392800f01750114a132184c48152030407444a1000800301d0003080d0000007404000c3d103448040b08420388035408941c1d103a8014104a01c13704a4885049001201050229200746c8020794440e00c041c00c0140380607100d50403442d0b1070704503801c1210070043c005001d48075030400340a00081c50180c40000c000c0740c1440400240c503030005001e045c0406a000c00c441003031080940000f0440c03604051106414861003074025160000600110050360034410001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 23477551 1250 23476301 23476357
    0x30605040c0203091e0114030106020d020c032d070306090804060201050105030a120e010c021530040b1504020703050a0e0a0501090506090d050105070c1505010509010e0402060d11 79
    0x50201c0f10040440c118074901c083d801c1403176000d102c040e504110040c240e283c2c810701c0c1d40c001580600100d40040000d0010b140c00245040c1e04440d40034040d8001c1d48560700d2080d41c5080c03400d00c0101406d103440c903a030029025903280105552000d07101c107040903050341c24803004400074826520b1030390080c441c1c1e03038a8800b407503510f1451020042844180e44226440540308000c4080f6112052600c07400012145e000510b021040c9003002c00014000200186401c001a80d41141080400b03c0321060884450b150011110020000742130340d40d200d00000c0e58084000c0d0511a40640100119210340f0142001000340c0c021100a40c089403250309a04540d1408a0301007085800c144d65207c41681044113104103a0050422546c200700701043c1c260002d0001e00640d84160429a0b400300030f0340b010700705244481000300c0d101404526040c018170060720703a01080c5041d07a4610f1600b082035144d92003c900c07248100c03441003c2c2c0c1444c0c199a204909400001028540080e43d2110010795804da062 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 23478801 1250 23477551 23477557
    0x501150f03060b030a0b0607050f030d0e0708030409111b03130b09030d050a05250308100810050c070b1504050108010b0913020406030b040f05010f0e0c130e010c030605040c0203 78
    0x1015480510003d28481e155811406c1c00010180c101400e203561603a82520700001d00320141003a40000c078040380400c0c824031501d41321125900c010700c4c001d8a0103407010707128403da014003180310382c80751011807407810300d00c1c05c642080d480b02404181302c0b24246030749912500303c03610b840d180c0c07040c480c0000f43d401c00356010380d150600e0090142208200d8180166441d0b4004030340348050000a100f4403c1824a1240c448090b44081c030004849100710320b0010310402005028681c10f11035820f050204900004006800d0000301030002100d807110342c14003440d030003811801400505c01804102c000141c0c150415141c20b81614180180e0362500740160903117a01071603146c0c01071490000904500070b14110690b4440c000b400004405840740c07111802c2c01811501682c410b0700006d6050304200092207204100c00e0500420070500c107044420b1a1a0220702181b18890081282101d41042080c0d1001c10000c3c0d503c00200105000c01502601406441c401d65103c0d0345001200c03500c1500200c22 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 23480051 1250 23478801 23478809
    0x10303120516080601020c0402070516090c09031103071a0a030e0309060708090d02040e1c080709030f062a09080a03020304060c0501140403050304140d140d0f0501150f0306 76
    0xa00b10718507030040080340c01000091105045114901d0310b80c00d0358580c0e100030401d05024601038800d522040b20103015207012548041d000510f88144c0c500b0301e65210301c0c41c0040c3c07540203507280e0f480212800082d1401c580e0b44c10007800d9a581181d40100b2641080c010310030980180c5040c0121319030028402c0c4c8a001c0c09030a26089002008101c000410410080600c103400800b1500001d0341c98012804a5030516400704655205100c00790700d0301c019012402c0f8800756890030301110b01e0300c040018143c0701c00344402000f00841c1c1c41c0003000c00110790428503e48203580202814000302001107104140070701c0715003000c25841a80131500510100d001c40341560103400940c900707454080100d54882012909491035562012158a602e54079504d250045000755902071300c80c10903041132081c8003600c440726078550340f1801800f484a5085001489144052550343d92150400402c4070301800801d440314005a10700800030a00c40030b44048035211024941e12502c3c500e503450383c250100c8096001e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 23481301 1250 23480051 23480071
    0x809060705040b0d0608070608091203010503070302040c050909040506010609050604140d020a0801020f04060e04020a0f051b07080303010e090303010602060c090a0909141b0d02101107030b0103031205 88
    0x203200fa0007059008083d40c80b54110001176860352540c039035050203415040307000081c80000a02104803010070415000c8490303188040d16551501c03001070365400c994030000b802180c0b5001c040c400e090250040e68481000503080091740c1c07a0600e0002e4a8000c2401381202180040b040484c940c1820f000382d500381d640c0d0112102c1500c850204100b1550346100c03080340e21040300704002c90942c80030b00280c000920b013544501d440e1800c0ca24003515403081905103074000e42c810b02c5440d5149030700a158030921049420666a10703030359421040d0746c62100c034038958440d200b02d00b400204040008000c60403036182c40a100e00c035884a5503019203901c820310924006074010400700d84406640d4004102100c1c000708000d8100b96250040c02c2500d8a03a642511004c0321402103191a0009000807800315800c00e000b980c8000c000c40020700c040c0910700019025124881c41d500425000d82e0743e803400d60034400b0071030b10740c2130f540c0c500030b16090000d0104400040341d003944800b1450003401001d001c5c20380d00b8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 23482551 1250 23481301 23481307
    0xc0201020a0f02060f0c150a02090603070309030302040503030406090806060301151809140c0102010c08060d080705030f03011511060c0324060d060503010b03030a0e060a0302091e010809060705 85
    0x9125007414241220b01a070b0b10040400c8441000e01d0014001d0110a071140c0142c5031907006016103000081c5d00400265015004114406241d50303960216580700003503003400a80d844071401e00724028040c642200b070300351000003004942290010801350407100b4403400c03240366944070420f044c00c0e03400c1c1c801000d108c603541314001d20a50040022807949104244030004500255845880f8881960740380660706800c592a07004095034203028490400c0e03100c2c20800031605080c0d012079044440300d5005005010003007a10006c001c4184101c620a86400b05c850341c5031758407081c2c603130441d6241407034950200d450307441900d83e08038003c100203120740c0500741e1180c10b560b00c00c0d201513002400c0304001c0f41d145c1c000c0400c1d80c480e96076000180184c00103d00001800c00d00344000e041c07c469841401a10a0303009004100724a0b60103043d140b00e9420a84040c1c0d103c10400c0e0003a0040d01030880380a622009100010005404400c0f0170495104244d0341c2400b15107600c13a034643c83d000d040d85d102c000030f0020 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 23483801 1250 23482551 23482553
    0x41e030b0105150c030301170c030111090f060403060203040305040f090e0c04180209150406080309150c100515041a010804080a09050d0609110102060702031213020d1101030c0c0201020a 82
    0x40c00340c03452a000383d204810318280c5a8803103141541c2c13098004400c0003001800f02c400710242009118a80001500200510641004104214003078144000d214460750b900840b0075455040a884c02075a01001c02e6440b401c0602e4094155003140c003d80311010920f10000a8500c40b602400925000c214043c0c00b180034801d06110280c0b17500440700c0212040d03007520b400140c03524900280704030307810b076012409151b0200400c03040c1d0301954080e01d40c80c0c1c03040c01024815038072005042442075401c000d0a175991030f480c00c0242084064441ca400c114540700400c440c0b140d055150190040c4200d40811035022451401303c0d00c01084000e1900060140002600043c10800103084440081c2041d1071030035500c500054001601d04011603095848810380710401c1004280101c04080900241100d441d110400940d68092041001c00c030101e5040400c2c484981030782c1c10a019500907022120780296400d110345040001070620340080c1c40c0101c41c1000720b2041241c0080c29038140d0240c4003914203 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 23485051 1250 23483801 23483809
    0x705030601090e0a0603050c0f0a0b0a031e090501060e090c010309140a0302030705070e010515030406020f0406021e0303071205060f0907080703050603060402060f0c1e03041e030b0105 81
    0x104441d040c4440700700c02184450307564150303501c02c01d1540d0000c11010f05614101d42000980c0c1d208a00a0f0505030340e40e682c5a50314148003040e00c803508007a649940c0042012030150451104500882650111400c0c0649141d04a9580c03070b80201e00905c05256a1000e240b10400115020b090b96003003044d40908544c401e40061448500403202403205035100c0c0421401c0c141444812070140c0d1000410004001013800b407200103000c0440c01d00084d42c50480071460000300b00d444480c41c510000000f4040044541c156450f800a8a08150b00d4035141d240195440071007030146501c01460940c0780c03c04080020803640f08101c00d030b8404110190121305a00a41009070460350320007099000c0c4505600c0e15451240b1400e21031ba0350303031400c2c100030002070100c070300c0500b030140680c01c0f18042002584a41c000c4a1a40c00c0c1c6000c9103507a0900752920758241300145455080a48103503098a20304503001015000b5640c40800804038a0310302c0c40e03900002121444010802e2002c030340100900c0c50 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 23486301 1250 23485051 23485057
    0x12091c050307081609030212070513140601050708040923090c061606061e0e090303010303020a11031903090f0905090c09130b0406060306110c10050705040803120f090a0b0705 77
    0xc0c0504245d0300c01600c81d400210450341140e52031546900240707040180d481d05465030751071200420010005420000e0162840210040c0640c5c1840b200003500000c10030407508a4009040f008010481008904d500740040b040b418201110400a000413500004002ca07580e01c2003030006000c10314204c0c3c01c03030030400700d940058019104195240c1000400e41c05802c4000c00c104044d44114041a09060100c0092100a03061002c0c0368810301c010b000003031700012483e0045800291000303510401c1c0c0d0000c1d03d04020811903000d4070f200003503040304140e04110180309440800f107001c942142c03514500002c03035004036450b0201c0e521105641c040c50416003480745c1c12080c1c01102415005071034030340e44594101954111070359603942d43c0810501044c0c3c440c60400f0070147c40b05600c0e00c60402002030b52407108498041816543d0004102e00a000b0400c45004004000543c0e444520110648401c00001c81e84c0ca80400c4080001070641040401c580000541c03080d0200250f894144007169190 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 23487551 1250 23486301 23486341
    0x80f0604060b04080a02011b050607180306020705010b0f0102010917030a15031110140702090603011b020618030408060c031902180f270a0212091c05030708 69
    0x25a032110082003030b01e1484002d00c0a00f4403480148200e1505200041c02107041200d210908158810540005503001c0744441d040020b41c5030a503450300301581d4040d1055110343c00100824030000d10302c010408103400c0131440f248100c80c40c8201085803001a03090790f02c0004003c003150101d14a480c200c243c514003958102100c0c0000041c0f07518280360101406149070000c1e00c00b801100840819894409054040004240b41030380082541c409442e216016070a070003441071002800150594509500100698194681c448100150401e010f9190f52041e5800e00c07010400c0e46d44403460f030900108403000c84043d00018005a9200000110642c2000d000c04003012000b4901418940c4140058000d000c0380464616801c0b1030641004140e81c1403900d0710340220401c201200c0000c400c400f81c48694960350381c21140c50350314110308000a100b00000764a584880300c0a200d0050000210300041d5618a048952411101c000c00d9446000489414000850a000140c01e1801000c1c1d052011 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 23488801 1250 23487551 23487559
    0x180e09030a051b0604030801030c06050f030109020c010f0507090e01050405011a0a020705060406031a1e010c0303140c07020310050c070f0201020a020307031b1e0b090a090c02070302130c080f06 85
    0x79070110f1100e00f460030990301030b000182042d00500600082c040540c008144604101c0d1805200d0720726420a8041403007114070441e8041600740c0800000e41207010300c07403100c44040045107000d59014094980310700960400c0c0710f0020021825080a21440d0706070b416800104034060301f40089880580d01510308641140a0803000007000d07100d90340600b000d0441c50310081550400000c2400d41400e94403503044c071510301512000552420807038900c80b06a000e19100d5001207241c01c040d00a004e40750300500080b2006030402102070030745c00c00340c440103108400340c440e00c0d0700061400055440030fa84030340801c4800c01c0508000340c503a00720100d0107841030040d10610a000c1d00000d007841400e40c01580c290340311440c42d01900c9005040580649030107880c0c01418110a2429040030301e0300d000c4e20605510000c2c00b82c045690300b526000003040241c9081c4150000410002d441e1050761100f24040c0c5100e41c46400c20429500590031011069907503001d075070342c0c0e40081042e1050301514850304 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 23490051 1250 23488801 23488837
    0xa02010c090b0306090c041d0411030109030f030e010b0d05070504110a140a030b1201060e010803131703090604090e0607030504080d0506120109030314010503070b0a0c0c0e07180e09030a05 83
    0x603140b03a00c000c48c00380300701014107042e00e02810a96002c20401d0f02e11752181e4940099440004d17000719901c04401180d24001070401c1102084d540100310344400781390f214002d03107002410048002000c3e0169141a18103128059080c145001c0394001c0705104000701e00756004094204941b54050548d41010f40703000b0580e00702c01c84c0460090f80d0354900d600e109075119413051180c0440c03003140c603004045100085103018441c403030300310070401140201d82244000c1d5220780f45e00c500070410f03600049001806130b6500c0d0b42d502c0400c00140040b610190b1140503410004a00f0340c003e02c42d0030b100b00e4000c000c40f032402c40301c0d200010051134005c00c082e0703210400484106981c4000d00c1030202040c408d40300010360610720300812581c040140d104600c20344c440c1200303103c00d017000c00640d0341041050510001301e02052074001d1554003d50042807c4e56016030800070140e520001c039440010b401c0040e43c10583d200c0c005002d880108035210407440d07008001010040784a07070014071503c03c10b01e00d4041 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 23491301 1250 23490051 23490059
    0x6150b0a051c050c090f010207060212030402040605090106050c0601050301021303020103050a0f0204090920210c090c090420031308070203010e0c01080c070308012c0c0a02010c090b0306090c04 85
    0x1101c0007581d040080d0200420b08254506141d00c1b64000c41c0b009000820881d4a0807000035503400400b601000c0f051008000b0401319121038128074003820300106120601c0d0384600d0000d00c660401c0c81040228480d0b0000043c03581410303c222010b07190702000e207a529a095800642c040c003005005104d00da0345d9010404942d80d020310242020f80481040440c1d150010704002484080e004858910110b840044400030341c0c2e04000741c0d400851004800d0414040e0001c1c1601700000e444402d50480040b03010040303225448130042c12089421901000703401000e100b00280c1179204600150841000c03c08110079000d146556403245100c0d2207c0f0703180000303680c04642990003030b0f1402d000a511448690701d15607001500158882d507102103460a1141a8134001e214500600c280300805d420300590071101c00604442c840c1c024007112500c142d900700300d0603115040d4400300341040103528040c0f0b4050803c2c07150b81e0140031240700a11031401c1d510781c10304100c040e00c005082d0f44135032030040100103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 23492551 1250 23491301 23491357
    0x13080304140a030906030c03060506030f07050403080c011401080c0d17161202070b07120e010e0907020f070f0305120a1b080706050f0412120e1203010306150b0a05 72
    0x140b62500c04c0c0d0320409001d00d8a0800745c140c80748401d003907080c1400d1010a00c40e45c2c82c0d803020390707504c9000c20040c0c10341600d9030b81e070665491081e42c1018100031000100c1415400c0c0c1508a0390400c0920380140030345070303600c450090700c0f44040d071030781d075440000c01900300301041011410714802d1b001c0c08a01c07861721a80c00403e250104025000305d502c4504840d070b07080042c2c3c051101c80010300161031840d00d032101c2da1307580c000038207040700c03c600c01d03ca4046403050b07240e4452000416054405001c0551078104108043e65032040c1400c40d10440c8625200480c0d02901402080d00701c07507002005281034079010307691070740c160080010703442041100401c45450300407135001c0c400e405015291f0182d442d0011305004098410003031840012503044000d100018480303a040006400c040d1501c64030705946490044090f00c0c1e400c8402c182486140b054054103034498000314102c81c440c003410012649899502245403070240b10b101004042070060300c03041401400100f01040408c04908002e0703944440740 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 23493801 1250 23492551 23492563
    0x30708040c0b270102060417031906030501020702040614061b150124020703020904080904090b09070905160c02010507030314070f0e030f0303011701060503031612081308030414 78
    0x80f035081d842a8240c110301440040e01040c9220302880580110302d042e403620455585030042a00c2180c40000000d40c43c01ca21074940b03845034800781800d11845135203061a42c041e400441d0140d10451400100050102009155607250003000d00840d0500700054110b5680d00c0c03140c0041f0b54513004910360018000b00c20004035000c0d10240d00d0003007860842070451023030004030812130429035114480620142c0d4490004030740c41076000340120317074460309040410b02826542c04000c1562480005000c40050042032131410354821440c2001195940d0b01039201655086003280d0201d42c000c0c0b00480075500c90801070207031500a04010500341d01c0d42e05068002681190088002104d0104400e030081d0310651144150100710018242c0c1485030603125241d11061181c00d0800c40b10348820140540290804001820010b00340c98440065882008401500007002ca404160501c1c1c54082039000d514154002e02d102d01c1c2040e1400e003d5034600c14107a00c060029101d1640801c801d0a800310100f1103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 23495051 1250 23493801 23493817
    0x703060f0203041205040f170a060603110f01030612080c03070b01030302010c120c08150301090b0f06091b040603181e0521090409080c03130f1505030708040c0b 71
    0x30050740c0b440c003802c054034071151001104040100402c0b040043c80c2c811142c0345d080d0703030382845016075000f1038081c100d260400c1828014409810510b0000502000703501000e081c3c0000d80307440c0204185900110b0490b00d4a0190204a40241c03102e4000718a99101404c001d0902c401103a180c94416152220001403da00c00c80060b0344501e088015243d0004030901d0500340b0420a02c8000a5054060044c44006040768803040000b00e06020300c0c0c2d000d411025103281c01690042c02c07414141700c3c8100030231007110014052414500401c0d8034442d8030100c0340c0004070f4500c02c0340c1464240801280684142041020003008442503070000c2455072001c01440c8040403144d0300314a0492400d5420141e403040060840c100550800b04250a100c3c00c541301c2e00b0003107400145000c03692400103103e00500d614024944004604510401c914a6620040d41d56815070500c2c0c1e0b50392121007805161010000700c8c0018401e0001c95001806442d10580252080400744181e0b9224a450f41940d080100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 23496301 1250 23495051 23495081
    0x50102030a06090b03061302010e04020703120605060f0a030c0e0604090506010e030607020703020d020a0e010e0103050f0102070f02011211030c070311060106080117030c06011403010506030706080a020903070306 93
    0x81c860311200c00c0c891803004120365581400150540e6001035104d1900070080440c9520a41080b400c41e0b1181180345203649009100b1900c0708210304005120310710314020299000d00d8044013082c64030f41107040e145104014507095162801803070044001e407003600d03061340038880000010076840e0340d100082c00c00b078031401e040084c5a1404034001007450800c03074100e0b03000e40c0100c018484025070120b92481034a4066652041d1203076a480030800e525241d60003101d41151100010805811040046040303070b0181080b0b514252081405908034811507400900e820b1a2000d02c8005500810071802c0780d0701c0940c2c000403500800460303180180e008455038080308c032000900104154019101e5038a001621004000030760500101601070074042c000c2201d414004404c4c0c48400c070007041111489403104041c0c0e031903540e50701c50b140394800d0342c01a4103101e0350030072000980b1030400054150841300e0340c0c1d684a041d40c840707059003002075000a4295801d030045450200102d00e0500800f104840848 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 23497551 1250 23496301 23496307
    0x50307081303022106150303190c0b040f14060106050d051f080d140903030a030207150c0504030201030e061b0901090503010908030406060501090308030a0209010c1a04030207090e030d0506030703020d050102 91
    0xc00e5485c100b8000a089600c2c8110340c0080c1052610000195008038819000f81003841c200084107507480c0050030b00c0208112041c0342003108009000d140610068802c41c3d0848004c00324440711500c0b400c09004007400940c040c001c012001030160411500207415200125100b03461002d4007040d81aa80c11251a0f40d224400b08903080340d0128074a495003101c1144a824600c031000046e48a10514814008064000c07400109020920342005115004130004108020b20306c44007505e260071031301c0b080c0c0c080f900d400e040a403200d80109a480c4907651480c0000050341d280c00c002429500f1281c0c40d03604012106a0204042e2024803840c8140d50080514a881e03103401c1c90501705a80c01d81e08605c2c10440e080c1700410000741a50f007640d4100d001200050386410306800100c030801d0b04594042d103250a80302840d0809105607040c140100d019909a55040d0346683d103004c140da100c0c940d8410154020801300e8400340e059032055411113402800d40d503589031780e030300060000c5050900582e441d035400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 23498801 1250 23497551 23497609
    0x6050307050607030c080f0405030307050106051009080a02010809031b0106051314010603020705031c050403080702010e071701110f190215040b0403020c1504050a05060705030708130302 82
    0x80003140001c0004a07011441c00c016554024610407003071100030890b00e80400d004420301002c3d02a51b02500016044a441e44610306009010b4110343c17003654020f0703a80700c21044105100d44191010703540f42c03400800d0170040d01c0c0d00450f0355410091900c0e6090109002c0300380d44000b04211001d4440c410030000c54900d040c201048078641307581082a410a141c132003000380a0f1500c0c00038904403901d5050050f2520003c3c01c086082d84112100310742d90456885000400ba0300d01e5210a000d20b0082d69600c03086d5a4818080e4200c501403400d08072035a1004400304180315440d03c41d07040f09240c1c840007041d4205031040440203900100c2e008552043c0210b6140704180e2002c08030303410100b0900c0101a20514444900402e030b5000e0405401485440000347c1814020000110100005085a401030b1300400102c065608a405685d1041d00c0d900320000391b0389414001e0303c28554126010714648040c40d540c0b00d900d41e00406401107844241c600000c00341c0d4400d0340d48c29005021a40300c0008480e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 23500051 1250 23498801 23498803
    0x2010c02060d1e0603050706110a02091006080f010b040504090302070f0807030b090309010f0c020f03150603150f0a020304140313061e020705060310050a09020a090501081614070b0901060503 84
    0x141546031038070207213469001c102081c40010f28008465440c1040308c1000554503d07036042c0741c1c50500c0a5007060404003032141d140078000d000b6003102c0352540c40c403065032905010b107000d082003071141100031082408140507c5c906a4003120b43c46100e401180c140d9562020170607010703a5943e0045c50203070001a4204240054604c01c603038018101c03c080d520309a61900080c211040c0a4440410046008003410841d10b4001d001001404010112000000d80355a4405080350840b5014000d02074280740d14041c2c0c1080070170f180039a141111540e060b0b41c03648030400003500020b005441c5000c003a46452306588040c4010000405000c0d6180380b918108100a8940101500103c50901400303144420065010440e00c00b43d500403190299a511810b44441030305502d40c200c0d0354090108940042c001074258014400000940c13600c0300d10030f07542c5c001926444d404458201840ca0b01d807100700200c602c10303003034508240d0062810074145001511201550308080360f240c0c00d01c1e07648030000d002500c0c3c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 23501301 1250 23500051 23500091
    0x1803020603130b090109120903030c240510090c0e03030304020603130b04030509040c08070c0605100816050307140105030a0c12090b0f0c0a050d05060310110406080703060312050702010c02060d 85
    0x7c1c1820020b0b2881e01d16071f00106048000340c8040d20190341d440c103c1c2c10710a0581902c0d060360400910a00c0b160a1242c2111519074440c400c20884911309008039406900801d180c121a41c0014049e5003181d80d90f03006c1c803000f0341c40100707110081341051412100240b180101c085c080c41c040d50f01c260b20740c009401400100c510000c000c00501004100300044107501c0301e80c4c1d11000d13038010380204035030f1200b40c3c581b298a0b0745900003100502417003d40f000141c1e011000e560813141c3c00c604546070507030340c4c41c1031700405000340d80c089000990800c0000d81c0244a90003006210a461070803000000340242c921045880101d4100d411480d45810f00030702d2250142c645401491100090341750104144025201d4455046142c20060301c3c1c100281c13495506100840d0301500500301030142c04068081546e40d42c0c0940101008109030300003107074600380300c2d10400e01581e91140c20000350b503800550070754090700b201c3ca0072810001400d2983e001a168140038000d0090050f8002c14503038448485c1c048590 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 23502551 1250 23501301 23501333
    0x8070b0f0103230c040606020c011205010f060f0c15020712080c030a0902010c050d0206071206050303070206030a0b120309040c02010e0303041b0312020309101803020603130b090109 80
    0x403160303000600100343c20314100542c2ca10203d49407242e14115980680c101101542220740c0030b07161500026900d600803410309102c0809a94035568581c90384072400881b1740c20300604941010040d4140720f01400f40c1800c0260507007500307015038200703460341d1423080e245411200a05032940124004e0104000c4100c920f00c03003e090309150a00f458580402c0315a400010314210625440302a070000796402000b0140d40682c10134151040d150525074080d543c0c8106443c01c40c0015410704401803084c161788100c405542d0024065460b106540d001c01034241c1024200c5418155900009441584c4404d00c810003001910042d41d01c03402c00d901044116286c0c0d030581010741e41401584240172801008480e800355000a0030b021401c20806a400f00c00a103030402040104243c419104050b00000a011007150880b00d0000e41c203a10801107681440011441d0f8030840030100a0006141460245602c90250400720500c04440d0725403104c80d18007500c400b001a503450204400f44210022120a59 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 23503801 1250 23502551 23502571
    0x3030b0d0222060503030f0c1c02030d0c030209060307020106080607090f0e0903040503160305070f0501051e250c1215110927060a0b0d09060209090408070b 69
    0x141000c1d8000c101002c500340000d4410301d2607035240c5580c40c0350590100b40038000181c1202c0e00c2d8082c4e45a81195a40310125080c281c3c4206002c80d8098884450b108441c20710383d0303010b142004088032000e400344c0001103041c018160244992116503e614001d9441135040c3d5001080840c90006281c5c14a000034000004000418130284552020780304034804443d6103c5e288142540c40c0c11102e0700b50f00403074101c135626024a8101408003d400121041603e0007041522203031070f0350b401c030901c1d0004280b040e9408a8414042d4042c80e00340d91465801c0302d980d40603e1442e000e004c8003040030b02c102e02c1c0c1880f000c20720000b040707809100240d070301e00001d840541e546005850454441040b2140040320803a50503842c1d581c540c0850034002c0030798082910140562200a084002000660182c0e4a842249511100c0011103600e015400f480480300340e04905440c01c2e20b41c1a41302c000d4a1a40d406460760f03502001944029194962005c1c8107a0044000544a02e400d20300b24100b00e40281140c805 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 23505051 1250 23503801 23503819
    0x1207020601260102091008160516020d03020f030a02030409050c0c07150201091a1e0606030109110c070f08070807050906010309031e05031603050f0c0304030c05030d020703030b 78
    0x100c00820300c000401d601480518503144542c01c1c03250192040244954011000d8020340f46541d4200042c80d02405000f1425840711080500844440c010180f280317404400d0b01e0580400360819411604119000c1d1040c0d07908030f4241c1e0344007465035005000540c010ba01c00182084008275520407981c00441d620350180c6042c104000159442e509030156803a050340303010b54600c60384d000350300c04441c00c3e0703108101d040134108251041e01f8101d41290407508030b40d6400100306d4142907030441188194401015142143d08003e076040081018840c5030326815020000d20034040410012140204941e910b1b0407000745c00c001c0b42c0c0341003070304a0340074900c650b10205080c4556a100c00907180e0226007884e00080764038a81c10f00300c0e48034502030310001850b00e201c95040381c0307281d105000310311450440038801e050140c10b000403012a202214001070b1001d00001242c5c5411040c2c0003160001c0c028a0200c05038410794803210b05503402400d207106940c1d8001000740400d070f014040c03001c3d201000c4841103e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 23506301 1250 23505051 23505059
    0xe0612120702190e01030309050901081f1a03100903030b090403050a03020901050403020402130608060114030c0a020f060a0615030c020d030e120711090a0c02280f081207020601 78
    0x50300074001c0082c0f09000d144426895003600b150311800a24803181ca40182d075a403418080c00300c00150044c58055a181ca001181c0c044000543e00c451010172805c0c00c01c04030b85810f00200030481c1a440f006044004141620641c1d0b08221100c1c0c4903445600001e04030b80e103890080c044030741c010f00c864090b529002c2004080307900700302555000105c504000da61210b001004a807280720716040250300c00d2001c18403101d24a241c83c1c00c1c1003a00c00a848122f003548415005440310010780c00001409070b01000045e070b6034220000949021420780c011119480300c01911a806d184049841e00d402d555145070400c07004c03100490f9080040440e080402550300310483c000d481e03050b8401010249502e825541c1054081000302c00c20b080320952001d600c80035949418409a0070b803880c1640f042c902c82012905d01e82c65485001c0074441c40e82c00074001c4a9a0391010121a4080502d440801081c0f194460201c1c1d909900c0724201031040318010b9542100d209a44401400a0b16030000c5501800041c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 23507551 1250 23506301 23506333
    0x501090b03060a020703030605060408010507030501080c0a0303050c0102040e09060a0b1f0e0a05031c0207081203010e100b070804030302161511011b09031202010c090e090102130e0612 81
    0xf41c0000500c48050b80d540c2441c1400d9000e0f002035402aa040310002400092046040d88500d0140c0c01681d820705c01ba907030b1100182d56a154410708141e008500d540200300203401000204070180d511030001d41006c0d40c50082d143c00010072601c600c0c43e9003040c020010303010391502c2100100d0b00d04607450f20002d211600000e00a40b50f0003044814810921003098003540e49515580090034014100d540000905044005592040340410090701c1100d0003c90904000300e0001690004030b420f1a045a107040200741030058003070038491240701c9000e40415200d4040f0018030b08680202c40300e035960785c95480c000b840c241e4840c10f600300540ca4a003003408001e07101e01d00c4c01c40e00822807a029445402c01c100341070040540d510120703041e00d00b40b040c0412540e00070419000701c0b0700030411000e0510482509178265000300c003074080010a203440900180b14600b00b80c60300301c5550400103080c070500c0100152801241e800521102208030f007004840c3c40c0801000d502031380c094015200d0706c040f5403614 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 23508801 1250 23507551 23507563
    0x80331050402090d0b070504050315040210030b010519020c0a0506030f040b0a020d020d0506010f1e081306050403030b0913020a03080a051204080705120316030f060504020403030504090501090b03 86
    0x114400c41d0000350141d00f03036840131000c02c0616006030751112641000f01d0090f02c0c641c05481800d02900070303002c080303500f00c0e1119071507440f80350080c1005002c0d21203050224020210800c0c698144581801801d40410035044200e00c200020b40060165101c0701003003201c030140c50391215200b00b030108100024442c1d0701c0708483c1c0042e0b00c1024013119840b0091020064081c045107681c030184082042d8404800f69042a4014102a00d4110b110300790071104940d0708101081720001600c400500c003010034820440b09a1052000880c80c0c581c070407070b41c0d580049d240103580070390009881b5501c02c000c900d00881069002000601100b403610141c0d808144ea100d440c2c40050600306000c0341502245000d8422909038016914070542285098500801560400386080e10148180ca48000124071001e0440e800340d03441107941c0c0381c202512070040b406843c0e01d640300f021840d11050005400e80b103c0c00070380041c41c42603d80c5601c0354204410401100d01c142d003d07603602ca007003c00d01c03500b80c1c48c00310380 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 23510051 1250 23508801 23508809
    0xf0b060c031204060f0f0506040501090507051b150c030a050907080d05030402040b09010f090f0203011d060112020c0109060b0312090d08120703091b03050706050d060906080331 78
    0x203050b4580d101d00f03004004101100c01d1881c154240844d042c0d41d00d8007680583c0c483d0004960800c03c0b644c90300c1000c0100da10449200300416010402401c0d41c41034541445510064041180d0280885c3c05c03441902c1701095464040800011003804201c080d80c0c050903a11501030710080c4074280c54200c210756543c50203e192024400c0c0007000c10159100c0d074001c920500c1c0c0241c44000c05503901d5140742400d904520a101580d403a210b0308002c885042c5c0212412034040140394810300c3c5403042c4d004800300d405840319051000308068403244001c940080c10550b0000c0000145480207820b121007611500c82259210360045071413502e40c80544001d40d66900c0c002c1e901030aa03002e8601d000511072250229030054101c032070b010080e407143d041d003220340311a200f105003090258100000c04202c0c1e0450200030210340113400c085c030080c1c3c444c5004e0060142c50301c0002c143c86070b840098000715282500012650340000544100200e41041c1f05000e4070800c1042c0480b8803810036540c0f1a803002402 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 23511301 1250 23510051 23510077
    0x90c0c05120a030902041401060818030d0507020a0203070305061e040b0705130305010609023402010e030304050904081b060f010311010c081606050106090506120406110408010f0b060c03 82
    0x1401c114502c1c8203a1004c1901507010300108010540b03051a1140e0300800d108502c00929054005541e1180180c16243ca05a0140045d070600750b01e5100c64000d030500034928001c511828080201503541000202e00560040f0090441402e041030105ca9907018036a1a03509101100207200010b80c500d03902c05d81c4000d06143c1191100c0004600c680c0a02c00e07980060541d43c200a0702185203211580200b03901040d03c00d00701c25401c1801080e07404107140c4004d1000c0f5000c1104a003001d5401000400110500102900e207000c2e01c400021b2081030083c0c030140c50031500807601100604c0c100404c01012186240142200d18059012901c81c1105000c02020100e04500e42155030340640c11245c5001e03444508607440300d00c00303500a9100701d4202016504d2074100310001882e2400746040005541014120518080501c800034003451805041100d100303680d601c158a900c0740c0c00d80903201404440303001040491800c0c07118015550303681c120501c00c480c00c200c2c0d030310705600000482c0c0308100c00b10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 23512551 1250 23511301 23511307
    0x509091308070b01050109120305090f04061509140406051c02031218030c010513061803020301020c030a020601091413140607020c01080109020717070f020613090c0c0512 75
    0x14200301124440005040c104080b07070040401c80000382d150f050350001c1c7e03a4403512075a1801c10340882405501d001d80815000c00031004a400e01c4166100c404030003800100b0000da0302d880158605000b00c80e03000c005000660107000c0a904208605a40c90003128280030f0345082a0008150443c004911984010f41680c00001c40d1028404600407650182d94580c8504203020a0b140000c0200c040318824010414114500d600803001d0b02c00c3c41e041125410781160900b5070a803040d601003550300ca80c0c0d00201c0000401a034090004040107080a13001d56150806420003924200c0c0607000036a85a0810240821700001d00d42c0e100c0c0c0c003c071000020307235040c0114202400f20400305c821000c1d85000360010450115000a1030310f2840c0800c0c0e894408036070340d500110040780143d0b10020721400b81e07001c5541c2e01c4c3d402100608420750280c2c09464801c025039001968a07407102840748105410071404221000316482514060b03290fa09040c1e40603150303507541c00c0c0c85003021066a80001408 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 23513801 1250 23512551 23512561
    0xa1418010812161209050f01080412050702040204030506010b0714010207050d0f030e0106030b010501020f0708102007031701140108040b09010e070e04140706140306010c0b0f0601031803050909 85
    0x60b99841400582094008640488002c4c005000c031425006003409210040241c00941d481000342e17070300c1590402c010481c18240301c601100c40c0d0340500781c1642d20a409100c080042002402054000c00300c6030003040d907a40d4240307000010490341441142c1c450b4410b03c4104040745003c10b00b81e1162013540743c507201c0d2000c0c01800390010700180b40f0021241d8078106000c810450b007141c1c0e00c0d058034801d80841700075110f043c01c000d9541169000b0b080e11070304038810319854103205030000070800c0440528403e42440141c00141c45820802040d0002500202e00007204c19041c452140540440302002c54684030000019041c000040c100800401030b2130700280042c1400c1d070001607044045030503201420342d01d1b4003020f041001136170155880c00b80c55200c4048058006901e004617201d9032900c1d00c403605955610110780d00000e04040c1449090000440041e424042d51445503007048808845400d01200041c11544003001189403181002043c1002ca50441c068501401003121403a4240e628 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 23515051 1250 23513801 23513827
    0xc0f031609080a141b0f090c0408060c0307090902070f031d0a09020d0b010c121d040e0109030906030501050d020409050106050306130b1302180603010b0a1418010812 73
    0x1040e03000304410301540c060807040140c0f240351862491800801c850900c45c00385540c41201c06980d410079401060f0008090701030420302080c9901c1054005850704003565214141d0030001c0032500c0801c03071580002003060f195000781d0504054105468114204040f65548041c814407940c1c010782801303c40301c0c541b00b8160021180700c2404074050414000c250b81e44402d07a010b0340000f070105441c181040010001795104e0b444003204d880d00500811007105025100762404540d01800342c022010716000c90740b981d21540516103110103907000006542402d0300f0000c01c2c40105400950801d41007030010480d90799115602d94026404890000311046140343c02401885194009505805084208880e2521849042d4482c50140140855569462103680c1d060000350381c000b54000003480100401c41442003c0d03d500c01409000000e1103644000028030007881588050007507050244800c101b400e0160030320b01810540305141000b94109615152925034510a0015458011503200c903003504d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 23516301 1250 23515051 23515067
    0xd02060f0f091c03020a03050f04020117090703020a0e0108010c021203151309060603020a080c0603040f060e0f10060b0705070504020901090905090c010908030304030806100c0212010b090c0f0316 86
    0x11981c448500380e40e0b0000f0040e000c0d40040e00c01e840807a1030207000890040040d0b00483c8110340c1650b8032501c80700c00341400303080070601804c00c41c210701c140c00d004801038071072503801c6010748140c0d82c4035000c542c0341c108000d0035180100141d4046400103411102c040049205132504207503540e5019090803100404078414460400070480c10a04004a003014844240d114034203482c002e90714107185c87d40702c049150307541c0d010101c0660060002c00005012500c0e00444020051060038007103003034403604034551b2908181030728102d03507608506a4030315044404d10444004180e10550311f4103003286034a4003915001c0c54880c03d401030390001200d00b4242e100e102a400a09010f510811a070b080c000d0040f036450003050301450101e28290381c003003013401e0004140c0e40f1559250780d030071600d540c94605010303199502e08504014000c03d880e403100180d0b551842003444034002000050000348030010032140c8200030381020302c51101080b00903c101e0111040329800b004d42419401c607010910000c8900e04 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 23517551 1250 23516301 23516323
    0xb040e060708070c0c17010c08090a030e0d08070b07031a06030a0c0302090a03150c0504050618040209040c08100605091305070c080a03021c05100306050c070519050d02060f0f09 78
    0x6408024003241e0304801800590101b41d0788402040301c10703c400341c1560301c000c00b075800504a038400502e04000a10500a803044502c0c007038003190322003070240d55065030764100800440780c45002c00204075446038144240c00f02c0040003c107032040e030070000d0301144a074071000e480781221946400c03411003224000c0c1c04841c0804030241010144035581d040003280d80e809048a0300c046401d14100030807a610403002c2d41c0641da001041140b33042054042d092000b0000388110b504190240007100340307541d651141003417072240d0752500d50306454180c24084003548241c0100b42808030a021580c46a00c40c015481410b2070480000560360315139a000751105006400018522000051f40c18900342d40f58001d0702034004000d900c14690340b07421070010190303442241d40c2c030318112543c80c003007010a201e03070010340c3c1180441040a1402d041e507110329040140050207501e0902400c0043d10402108028810240407030784050041410a4400b0440e80d28000d4050040d070381c00503000c6100f0000134002981d82c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 23518801 1250 23517551 23517563
    0xc030806030c030703050a0b100515160204110414030106060e010804050c0306040807060c03060b0a0507081c0c0f0c020f0d030203090306010f060e0f030604061509050f06040b040e060708070c 84
    0x102e070b500e00d411b507660306000c0781c102c0d40403c0366804140300011080444c010388100402a04450140c2804038100d90000640308507006910815070f005030321184079581c102c00d607242010f581c89013809403498070003d00c4400f190090789065404c00082da401540d2000c649001d2812000c55111410100d190603903007a9880d9250003071070184810851110300410456101b003100b40013101ca000030540480703059110b1009806001c1000740c0b0000c0c130900c010f1440c648643c0c2d15904040d154080000345a041c90003109100369170315111410140c02074802c84000c146450206d1005083c5c1c0e0202c0d0a88078a00a440d01590402045008040c028410b4400060020301142c89941c1d60b0702c1c0060740c003030ba00e20486012a41600107100c0130b0602d0030701000110340280c02444152595138a0400629801c2005880341e4510000801d440e0700c02e005150285480c80170004042c01c08104000c00c0f00c203482c1d80e0360320a0785030015003403503c40042070349940315619003006101a07950910560390121914001000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 23520051 1250 23518801 23518813
    0x51008060d08040e070f0c12030c020312011203080c0f0403150209090a0c030605060705070b031b0c06010608070305131212060e011401050c1b010c0606090506011e0c030806030c03 79
    0x140c14a001204d6205078050b40d070b1250b9140100500b540c80c1d2056100141c05404402c2c0c000780d40c030f130081c1c010180481007032041380d191000038081e000711428203810182c00c0b19100d02e0014241980501441d4101016a800526050142008078030078803a0b444014000310140130303070300114259075050301d2100c04003822048451600d01898001071055612540201e450500041a82d0512100fa10100ea0f4860b000700030860405045000f1500001d181d030708840c80e0110090f11206920300a4186500c521006180b19418518040c161960040109040501d0710f82000844010050380c0d050941c0c00200030480c0c3e5603007400072540740d6000c001c10f014070b60924100054020700d98100904880468040010061040004450b20b125281c03c8510720740c4074180c13000000880c104007501342d8405041092015801ea13440b0300039130350103500a07850039a4072410030401c0d50300a1032040c4a058440c00c0c2d0407510036460006040598886405000c2160b60800161140c40400041640704001812114 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 23521301 1250 23520051 23520059
    0x9060711030105090f0a0206030907031b0609050105030c04030b070315080c0102150903070b09070302130605100f0f05130902070f141b0d0303020714070801060b04051008060d0804 79
    0x41208210400d007030281d0700e01800200709040215452842120b800043c006151603038003000300d80e0700b01602c8994030f0f008002c40080021483c0d200c0401c1404550041c080140c5005800761036030165500250502030100104050288500c084800b030703c3d4411401d24094490180403170007482001c0505050340380d180701c042210200040d080361540c42c00d030b0131100d035001403140010780c526060b503611065034030501c14900020700c144803185c0c0c00528441203446443d07480d000036144600590700388507507a6444e04107020a081c944c80342c01c802519402e2848850200390030080814014a414070104500400c0044419186c20030b0040289400507007503486041a0504d102e2208641d50126130b401d1813415103150003800819036448214040d0392090130340c0744100900000c4150810110201139007040001e0015141100205860045200800001d03040034030050858005030403401c0c18103c00d100820041d940c0350300d001c10803005480c1048890b128400469680640e142e002072101c040030130046 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 23522551 1250 23521301 23521313
    0x5010b090c040f080102070816050f030a050d05060613030813080a0507050307121104050415020c0703020109270906150e060a05060301030b06010e130c050301080106090204050109090b010302090607 87
    0x10395819028081d41c0359071302c0441900700c0c0b0480d040100740341c4084c88203078900041c24440a46090181c0290b0300300400c041301300341c00d40c2d01c18884600465008194130a0680d010311074245d0103001519003d203020348031503051200d44240e20004000314000203d114010142d0a1000c0040c03025004507690900e442c941991510034600440c0d019100780c7c280005c0307501c868410a455a40c110007000c0a940840081c0005002c0042c000c1d41c1c0c1c0071480d25041c8400017144000c0c122030b11104040c0031040d00794400107203042d000d40d0041c1c02c0c11070074a00750a071503503403c448149c4000300524009081d242030300d0010050b18414003c0e90340f498600318001880d101900029225400031102d507030720191600c0400045010a010280c4003ca1801c001840355010b00c542c1181d000e4002e100e45001101c2c200d024040d40c1110184100041000c0010030199809006401c05820b08480a42c20703c0c0c1444c00003440c038046803044000e511f840b08202100740e4041c2d4100c1d03844000140c00140d4a80c4503003028 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 23523801 1250 23522551 23522557
    0x3070303020304141c030207030504240206010603052211030604030203030712020a050d0b0406180207020906040e061909051b010e040501060f0c050309041a09010f05090105010c05010b090c 83
    0x81d6202600b1880e00c40307030304ca40450100300d400c80c90f030018410503080729403c40003500040011814414101310120343d8204441910002d40510009164169900c4500a0074200c043c6d0007001450304207004e00c0000b006040c8100e1202512160000d030600391824041c1e688520f4001454150142d2402c3c481410380c0400254401c00c9681c0702d01c8907802c040760f10741049201e0074000c0b0b000504140508842c01c42a0340151401c44001003000c180317a501c42c0d40c088680003249403980b1520380c1c0001c074034086082501c40154400c03801c9404119084685104680301c0d44024030a0040c4440c02072000c2c01e408190f800a01c07043d030060111511031396004e60703d400004401d0500ca0114034010785801c100d150074042c02e0b050361802e9841c0020484d02c03000c150b841d1038142108039250f00040c0100f0500743c90b5842031284840c98181c541344014001030511900c1c18060b0042039140c01501c0c0d09105a440c0e1400c1c9a0444034281792410b1040c81a0820f13900400910b001e4a074000040b0040c81640412200a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 23525051 1250 23523801 23523803
    0xa03230f07050a050a0f031e0c02010c030501080a030e011407031701051207060e030102121003112704080910080a060602010e0c060901051201030c031a0f13050f03070303020304 78
    0x10034066901c0d018030070784180c001c0b4030700c03800021010400226118031031500e00707040f1040350502186072030041810204610450759202101a9030f013130800a116424011001da91016041c01c00c0554186108075403641c0840601609005c040198500306034420140d900b258010a2086611540c0d1840c3c0101802180c105084c0100302e690000304103468042c507141c80c3c104549008048071480c100c0242c1d5454040382840d079055609000642c0300540d080101c600c0791242201000405007549043d441c5400030315000c9020310f003000300100c18102ca110003c0e0004480460806507907071149451056480b5024510740c00038801d545613040c02e038100d000c4a004085280b0140b0455407200c0b0220701722000041030202950055151199504010f001030441304410715140d8a0091011b40c801c011a1003030784115a2507145400c20014000b504144081d900c2000e00c0d01021401c085806851990003e450740c502c054507904082c04000082000a17a161000c0050341e8a030846800c0240081d001118 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 23526301 1250 23525051 23525071
    0x9010b0405070305060120120a030608060a0b0a0308030a0b06040b0d0509060603210708030108030d0b01090b0a110708010614030c0d0201020d2304180c030501050105030c0a0323 78
    0xc00b08040500900949100e800180c0d141103404a02003080072003601c3c1c00700504064055a08210500110f07000146020181a20081900303450304140607e002c0303000302030607182d900d00301c1503440300d03a12282c0b202c003103e410404c16501ca4035071800860042400d000c9007640181c000800041248456010382081180760704100403558400200580740c045c110303001d55160b04942082e17070410100c10031043c0c405032109171050030b04549913602a05d6900c00e805c1584594404030f00f11001c1200c6024203440702100b803800300341051825414080901922000d401480601a14240042030030000324006000140c020b12540d640c600461a0381a0f0650866000703004003103c1d500c141c10b01b259503140181e81030b0700402d01280e52100c11180441c040108d1940b2078004900c204045007100080c0c0042d155401c84156180d07904421802154495001c03072046c94208801048180c3e004410f49900c080b2688400b0341d58240b510741140140300b030500c842c4111481c1841e01114060f280e002c0c62240c0716540f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 23527551 1250 23526301 23526311
    0x40801020417060f0f010b0d1503050a02120a0803010614090d061a04090503030f060105040e0c0d14060d080903010609020409020405030d02030f0d0b040e060403020a050705040603021e011709010b04 87
    0x2203a01803001c004450b16105c60302c03003400421031880d800e0011712040401d12030004492164426207101100c8990068989078840c8107244d0940c41c2112802c40c0400c5940000d041d5443c181d03031121442d001c140706030b0041c440d50311508110003011500f29900c400c8000c1c20100d80030240d00e0001e0007451031281c0850310280024401d062810a486210320142e0004010f50440e6240d20512040000040174541003000178000011541c41803115a0300640001d0304e09a12040343c0c030310440c100c80c0581e0b0410b04004405050144c07503141d40c0d04050f595504480c201c3d07981c903044004240548501d6000c411154800100050b2400392640640183d410450985030381078403070081265240107043e120101503000f000601416801544000120b000241c00480ca442d00d414130320b4200201280c0540140e044814044108441440103101804044504115030760858011a00b060002032050715245100c51040e0100ea01401c1a00d051300d00c103c012110324545500064040c04140b030070540528200 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 23528801 1250 23527551 23527561
    0x1709030f061008070f050d0f0203060a0606031104050f010c0819020a020f0103020403020a090509070302060c0102090108060901270e0a150e0307030c11130507050403020a0b03010305070303050d0204080102041706 93
    0x200380c5408446118030605d40060400080105004081008a07a502618014240145c405000d01449032a0800c4000b843c20714240024055981524007451140710070402480155a2044000403010081c40c045001030103d2800a03010711404250980040ba1002070143c411fa0005420001c24401d0703982401181103140150240d000b607000080d80180002d0741071117803044a0744482c2d1320101c6c0e00116420240e50f900860080d5021425180407a5000640425196085022981c0104041d612400503604d800f5030300340d4165102d0442401411a40c060350b206801d5074103c04240301d4044103482c0c140000e460041e11218809420340c5485044c000d480e0242c0f6408404d482043d42c042d210010b0841d080ea0340c50b103214a6010b0703540e500440300621141342d5a224442d2074443d002c10707180c150f601d42c01c50040000e40655039204605c0710404000502c00500b01140c8041100e40c0f50a00580b02c07111000150302a004e02c0d04184071035840402e0004600903984040a0030840c6081601d80030340361 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 23530051 1250 23528801 23528803
    0xc03060408030106050703020a2019030203060a0902010504050a060503010503060c030c030103080d0e060c0c1002070807020f0d080c100b0102011b0f0c080c0d020d0807020a1709030f061008 83
    0x42240c02a111440500040001c1405000100f121512900c15a501c0401664549100003000d8800007104019201a01030904252050070042d440a0885840c164039650002c0d0b50b07004002d00c01520b05032525103070b00c21640118291005054001c09110341b158403010004d002d50004d1080d180300e4454003010420412007001101d000d1032024407101c0c6580c0c21a1540029a80503440c0500550fa662043c0760b1590781c24450300d4021010302c400140e0305e03150840221300d06079040c0c000d4490948100040ba0003c4d4524040710146941500d01201c0c2418020001c4c541c9080d0110150051000250b904191b100c04501d02c21039100e6180300300310344888440124200c40030014154850071200e220100c84030300815880035205000d1801003122085a50b50f46641c2d00050020141907000c90205409241c05028400913442c00349000be056141030480255a01c10603a0060442c0e9001e00e40364019400101c2215425480601180d040c6402203840390b42d2610200c0b0200b40c00340c0d525402052181c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 23531301 1250 23530051 23530063
    0x15010810031109060109081e010c050a12050903120702010203071b111203090604030c03050c01020a20030c0d03120507080c0a03050604090c0b0a18030b0703020c150a0e0c03 76
    0x1401c410940000040780043c0403011201615083c14448a0b1100003851001041035103078138407040200a8041202601031070035607668440b085e003803120602000e04071640c070019200301c107041d040010840d5210042001d056104d920f6400c000e004140d0100223681d40c0540086015040710b54031016003c40202ca1100c0c2d8054842004202c81418032050384c1e030b880c00c0483d4407222100e000030b8a14110b4171400040c59070340030340c3c802c5414905000003002030101c10312206244d6074081c0082c3c1508000e640d0f03503118900d10541d801c1c100c150b00c0900303600f03030781c404200d200c000384405000301c5c03141921400c6c0904400e103010494102c16007003000146a143c81485114044d02c820130840d4140034080c503081c2d000d0310000740015006540c5a8105020850454800000f0401c0c1d00d0110341d5050700c0c04004114400501c0062416030103007004200040440080b03d82c807140501e801612126841d4266040c60011000c80700d5016209042c03101541a580c042c1c076490310b11000f107403416107102c414561240 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 23532551 1250 23531301 23531303
    0x61f0501050702060a02100e0a1703060a150302190314090a020906010c111305010303020f070302060d02030910110d0b120a060b01050f0304060f0608030702090105060a05040506031501081003 84
    0x101c0a02207003005041c030401824001d02c1c1401542c405165154024045460703403007a1003040d500c01140d4800741f04c01001035004003000040d84500d5450301e200810003800b11031040f48940d10400c5403100480d482503041e2141c1c900308614503140d080035001c0003000741c0324800b600d08032142803601107403403903030009511a02c440c0d0240c021150382d61241c0055465242460003a500301242c442052181d5507261354018240c004030310006060350443c1002840c00c09000101504d642c005041400940e4820055440c0740e0004400507903a6a00c201c121810840d2005090307074224240702800d4892010600503011180c0c3c0b141d030800020220404205000700b42410720307402500591030202c0400c505400c540301042d418108245040203801200e0001c1d070045500341c4420742c0e03482e004a12030030540106002448850010760400c480744c0c00051150130107108140c490b800001c0c00c01103040c0034a054a0007040d0050040e6100d01d02a80180ba0308000c40c0001c900180548000420104000c4c50f010150b03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 23533801 1250 23532551 23532557
    0x9090c0c150b030a0b09010e0601080d020309060304111e0306060d030909050c04120b06030d05090102030316030e030406020a110a0e040f1106030106200601181d0609061f0501 77
    0x1c1101080000509072448440c3d05030145441c80d402080b0500c074000d0040a00f040000390b0355005002e141c0c18513006030800310041c1c1101c000e04c0c3c0d066070b0020649501041c120f403810780e6030f1100c0c80d002d03100303111405003c0c0d08400c8101003449600d01544005d04130344d106a094811540c1c542c000c01402c1541c0380e1004002c58030440003480228090381c49140d00825241e04203250540b80d2607203e500801c1071600719400c43c11704042100c1414140301500c940c01e01428024206048000042e440b404014401000410b004140b5003500e44a50050782c0f03200c4c204000d595546880b0b160007521460f40d101c00781c500495162481d003c03130070107001000031140c00d8451443d15031503558030701800b455004400c3e154240c081181c49459a18880114001c0155845c1e000304948503013080e143d402d42102c4164402d40000c00104805603035a49c80c2e130301ca1045801d00040102c2201055171880c0401d100005032803042c9030070000888000204140241c2466601c5558100090138081022040b805500c0c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 23535051 1250 23533801 23533823
    0x306090e071406071703190506060d05040303110301080307050f0a1707080d0f060503010e0c060901030c050f040602030406181202011d1203180105070c0506090a090203010609090c0c 80
    0x90640c1c02044034140002c0244814a044441c1c0c0310f4002689900403680d44000e0000140b204071205010b09590b261b1440809000d42d1030704030b00244060040d5100b0103912616040000c0826201e640100f440358420074640d5201d503100d50000d581d9420050041ba8540704406040c075403200c2c000385180c41d1a82c0221169136030b040080f10503429130000401290501c0092000c2c5e005103046001c0c00003c001031490010303080d460030007010300f920300481141e40c040d04203003c00341c0c058444004030780900c00d082c01c1c041032000420702d00b12801d01c035812040641020218003c00c400d0760205c0100708590040e0f441400c602e03005d5000d00308400092040d00400c062182136038005501490340008400242e01686013140308400201c1c0303441703c0b1428000443d403c000780c0701c129515080c034159007841c030a2030500e040095940e101c0b406a2554054144550008100482c60b40e84043c1da18026240101086d0f49a503950301001e0a04801c030b01560081605045050208078070440c1012642c0d6085007034904 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 23536301 1250 23535051 23535059
    0x6030c05060703020304080d021506090601082413050106030b0102060f0109180203010c02070e0a1104030f23010507020c0d05030306010f031805070513020a0f0302030702010204050a03120306090e07 87
    0x710703540301460440a501003440006148441405000788203515500070784070407480440d159400d808028403181c411b000e281d01b4004542d9000e02d08a40c03080d2800001c2248110004400e040190081c01d0164041c213080610340307650142d03070041d504079461902d09000b0b182c044401039840b040c08490b00440948010010480102d05420003000f00c1d6161818010072030261300482c0c04d41c0d01c0d001440e000340c4d22845c4108800c0100b000040da02050b00c2100304500c0003c01e101c51020b116901c4090078211038010900140b06100c110f5029040c41946180f180405100b900350180c0003c0383c1040c050b004142c0246036034204403c80e92101ca50080140d8a15030f6900015120080d40e0883c45c0205a5038845200d00f41405490301c5072903500420060030b000d450441000002c0c0c0840d130a980304030380103201400a641d04a06d003000351004a060150322582d511400720b0090107258420355203e081d9002c00418401d4601c217040303d0200c59903050003204c0c0c40e98140700a550310200d0082040d407200c28200 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 23537551 1250 23536301 23536309
    0x3090a0f1109010308030405060109020a05040b0903070f080a0308090114010e10030204050a0f1503120507140601031110080708060d06060e07050a170403050d090213091b05010306030c05 82
    0x6001a01c00d8281501d054042004a880440700342c100700c4620340004184010300c28104040c0d801808544029407800791001001460f501640c450480d80c01000300d5181030030755003800800301900f09450014019696003003601c1c0e859203880c5013503002c610b503000403546641d4113004111410302c0c3c001c1a401c450f40703450110540020f0040040456000480b004001a0f5890003960302070300c0c41540c0070841b04000c1903280100c40780d1048014000c040c40c1400c00010b2060100324451740c90600300140c03200d50604001c0041c134502481d080c100d015080c004030400c0b117062001c07403c000d401d480c030401d0303184d0084007a00c40030001d550b500045491140020024a0084000b084151080300041500f907500c0c0c00c09140f44c0070940380380003c52000b260701d03a8025800f0a607a15544000b520580d81414582c40c0500244100e200022105072543c0c240015501c0d900f110002d29100502e0420649071142401d800011107000c81c1b20484c02c800500003059031003401858252900a20030310541ca103000c00300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 23538801 1250 23537551 23537573
    0x801030b0901020702090403020601050a12050d0809070b160b010909050705090604020f0711181006050a0c02060c0717010204050604090e070f1d0a0606080a0b06090a090605040b03010203090a 84
    0x7141642d02004100016103503030004038041c034072a0b0010a104e5040c9001c100034050180c0001c00381e6080f0b014400b0100300009001c070840341990900c084d803078131034890716401c12070316400c18130181c20001040290300b003e4001400e2028043c51510b8600d980b00c3c80c3e24010b50314100005425644003c8051190f86801c144490700182c00900051a2420200d15040d0a07006440240d40d0039090301c94403207060030000003d0302e030040b440302114640e252540004c29000780030f004400401002040f502d0145000325400360100350001c084a4547c0c03c0211181c3d50364880380604541070f600708580101c0d240050007581c090b07490080110b82440c2c10140001d000341001e44101480b0700c284000010030085045000c800340c04070718510032812a110348036815220b00a4020100c2510341007081151503806908650402c18031a00402c03030810510014500d800703001000755010717004a0000a4414060380a0030403100300340d40070b103c00c81049003010700702e00084071001200e410244482000480c08690 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 23540051 1250 23538801 23538811
    0x105010507050c09060a09060902070c05030d090905040c0911090a05040c0f030b06090a030804140906010c02100306030c0b0a140a05092211070209100305120a0905030a03210c0801030b 81
    0x406c40b54590368084101a1074540c1d129025959002860320144145c554030702014100a0b80200144001d030300c0c005105c400c2604c5803c0e0074030303503035400325040140c0d0803503100080c4040c070428883c2c0345085003c0e406c02c0d03100186a520840d8103100016040c1041c2c010901d48103400c2e26400c000380e645e840c1c150301034089000c54a034000810017040d0a1517445007407020255020700c26054039282480d8002a0001100452170322035000d440403c4840d0781c0c0520100e04c03071513054a0b510606400241c09030080d1070aa00003d0512030f68207004a0860700c014040c001203000344c0e58400c6020500c651036802d610071150440006203080006180f0750038424510014034072464851540c11a00c0610789003100e20b410076280c112031001a910342903181c000c0070b5680010100000044241c03840d520150341c0c0c1102000860181000f03c1c02c00d21050080030290018040641510805400c82ca0000d000c29500d1414003800600075500812f020646e21860103070511646071070104c4d0742180c8520f03a02e007100400d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 23541301 1250 23540051 23540059
    0xb0d0b010c050a060504020102060a090f110d020405070f0212040f090b0604080102040f0512010507080103060f060806040b040204060617060d060e012301060507050a080a03090206040602030c060105010507050c0906 94
    0x385100042c410420040c2c2280980300c00106420503200080c1498006040003150504003a09000031890b0040492821584100f4542469031580c005c103904d14140b58001c1d40c02454001004030080e0010030030354401c0f06603801c0d1500b000154200c04028090750081d01c0c035105500b07034140001c07041c0e40d020310301e1004010403641c18160340308182ca00f03990244e040001490300b224800c01690070300c0c810031070381c021303000000384514500b00e400201a14130500c0090906600c500c1b81d13040305200c46e03000b40003a048401c10340c0c4d114035040c2000900e600d402c1d501280070782d00d08078001618511803c42d00052240c1d600d1104403176154007080111140724070300180c9240e81e44103c2c510342c0f8902441001e441c001c04080c0701038a0404051200d18411050340b080313081c408200040400150080761094400340c1c45031600f0b031600c200c0c0d1021001003003500d5000307402c44000a004031302d00d40c000010b01416a24031007100c00d581c1e203480c011134050145110091030307680703c1101004e10703161000b00154807101c007034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 23542551 1250 23541301 23541317
    0x5100509070306180605090a0504030e0a030f140c0d0f05070e07110c040501050d320f060105010f08040807050c0405070f030b030102040608010314030d0c1d0a0b0d0b01 74
    0x240000d803a0400c140c0d140c0010940d1110308104200c00c07510146a864034104040001600e0840410310a500040c8480c6450b5074810005040602404401c0c40e646c070301400d020b0380a52689082d0036100b03003806040c0ca110071603802000068100140641d001c1c400500055203040980e6030729040c500c080202100c450240e00008030b1781c8613400e04c24900c128015540e652452030523801c55414001c1c0640020f0045043c240140182d80312000c006800c87d80c04101111003001e60016180c1140510190340d017900050303142c0340f80c05e00000515007500102c042c256500340e6a030340b0040d19481c84600b100d50100e40354800242c00301c0e2101020306070369405030042d0350305181e13403400241c22940225508400b02e800c00c1d0b00016040d40c50300c00d03500840019002145000e003400c502070000481480000d01501c00d200419640d50018410340e00200b90550f4244800c1c84503003000703000d1000d0080e1041c4401d0006100c80028a803601c550030481d0718a0045515000c070500b80b0034068070524000605100c109 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 23543801 1250 23542551 23542559
    0x3020d26030708040213151a04080a030810121e060212010308040602010c0206010b072409060603020f1e04020c0c0901080109030f020703150b01030915090209010602031c0510 77
    0x1080190b102c0c207000d5031400c0061800e0b04c1001643c80f50701c605000380c54905507604000c42010801e8205590501440030018941c46000300c84034402c0e0341014032140604100881015013140c1c116021b016800c0705070311425211041c2206102d048080941321501207a20001c1c140300501174810b03068000c0801610305048801c50007c040030a901c12502c0c2800054100a03044e428428003071421524800fa006d1545042c0750103c0354001c514000c0c00c1c00088099800441c4413407060030000340c00c051024490340c0c1d03907820004000c103a2440182c0c001c000701440e0380f10034a0040c803860404000f868090310b201c2748240c00d03c002500200029a078a00c500b942c003e95a40d103104082e402415400c002160201251400405858400060304250f620811040c000514000c1d9203401e036845050001a02c1c501220048020300703000310001d4001e0400362040700c80d0300e00d290889941c1178001d817103180785a42c0e605000c80c1d485c0f01c1c8689134290b9a00440303a81418441a4210540019121050031106626 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 23545051 1250 23543801 23543873
    0x41211060723070e0609100312020703030e01050c060711070909050c040606090506190210020301120309060212070204020c01090203030c0303150a030f03050a12020d020a140403020d 80
    0x20889041e1000d07450004810042d000c00c82d840b4412901c140003070704042c0d24100c81615400300140c1043e214845610000b116054802048401190030a070210703400e41c200340c0c003e91141940c2c0415000624820201c00903540244200c3d024440d031100240410303512038a0854284001c00010a401c0c05014000a01040c490040c011460301642c0540207810582c030800044030320aa1011090041040081140d50703510820b68100070004815104840c205510480c200729070500c0700c840c40c40c4080004201481140f207151034180c1b00c0d4403900d4440b629aa01640e44840402d0049482082045048010b003801e40242a51280d4200007043c2502103500081c1185c00403902040d031940301008105240501004404003c9003d807005000079046031940410414102c401600b070040c005202a580c030b100c0c5455070f2200e800740c0c2c0f0443d1200074034207582001c3c0d448840f0041c0000c4000c0c1242d55102d41400031a81102c0e4003c05044000c20715076a0109101507400c2540c40704c44403070b8040005165 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 23546301 1250 23545051 23545057
    0x10b040612110309010b04060f03020901050603040c080a0f230303070f0e0918071203020c01110a0b01060504090c090b040509061c0b061203070201020a02090612071404110f04121106 80
    0x50304c0300045240b544d040144000c440c00390f031114480b5852001d0401c056141c009041d815500705480c815529511420b00d001101515440039001c1c0c86a910643c2c10300000854000d0301c40d200b2000402c005030f08a0580c005808607071400241c6400800c00f00d51202c1c00364003444842c8141742004104040300800090910341d0454032200c15403800c60031540940710034030141e806040050041942d20b202c42d20001d5444403980c0200c2d050201d01b01c1c403281d81b10010030202401e9607100c40c0c0b13062550f071100702c000c0207900302d031080320a224280341414200074041c3e00203c0a640c26a424181001d02c0e200401181d43c5010b07054a820041c0c1400300051a41e00910750a00c2a0140b40d4580290a00341c051041c070101c1215070f40899001480302d440143e0740458440c2c242034045960f2003080d100c0c0c80001d03241e00720b102d4805070340c0d1040640004940a00d05100201b81c0c2040300e0400909008140c070500e68420301c882015030540c01c22007071004111061091300e116018581043c10348090704041100f0b58 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 23547551 1250 23546301 23546311
    0x18070812040807060c030203090906040e030a020c0907020703030e130e030d0207020a090b0f090702011d1501061704080a0504051302071101030209030717030c1606020d0503010b0406121103 83
    0x12500080502154000300700c0c120044c9801e103405503030303960380781c03170087d100d01514403960f1007591a9804100a5502c60f04025607102109041d03a175540e140b031001942c0d40da5400b4a45003c3c010680c0000c030178074000700341041101c0d09511a80b01000c0c4040030011510b0f4200d1411a085a549280900c0701104001514440e5801c04005940d02d00f94010800c03a0305e016442003c41e142000ea04600a4039510603045080708140c607804100e03202e140741079026088000140c0e0100c1c004841d0341c008910000703800808200d404622210b2a6212441250305000303501044013170b40514404500007034202d100034014100c0c68549242440c4e00c1e000021f11407d400c04841005580204142c2c00b400507215115084800c242021441e05140e080032035120340c038601c566601b1010810248a4184e4140b0440700c0500c907000c15102040c0b54518003c900030b60600602006118100a07401c80c540143e00301c9042e550301041041c105441c0003400c0310894081e0790200c0602c0c1c0c641c4403507800a52081d025600403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 23548801 1250 23547551 23547583
    0x6020304090f110405010c02030f120702041103040302033403050307030b0103050702190c0306020d0203070206130201020705040506010516030509100e060307180b04030501050103150e06180708 85
    0x1a841c2111503425a142c1490801d080303803800c80103c1e00e00032090b0032181103402c2800c08188443c21400064104901c0d4a40319605008181008400c501350700c000b440214800c803010881201d0b5103250048070b01007110000e004d680704026190203001d01405100092450030b400b00b0010841103090411408400c0c002c5010480110038410b80700d40602484824403800e1a00300810b107000e040080d5540031024100640c0000030a0383e000b4445e021160001550300604195600e1111400280095000710b6a42d8018050b100c007040340704076115890401e051b0141d000304140b609050810008050207451141440313001c2040a503080c0c0d800c1c419002417806502c6040c2c031408020280180c070b0b44004240d03003c102060081c00001d54800061300d0f04446d50786480b008000c02d2509080018038107030046208841b000c00e000042100c15001281640d1058801c0e110594802d0820015910349070341310b0320b0b03682140c0000780d840d0303030400c041e10100801d26040321401d03a035641c00c15003480b41c07207207400300e030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 23550051 1250 23548801 23548807
    0x40b0409020a0906020a02030705090705090303030c0a03060807030b06040c05071506030302070602070605041a160501050a06050603060d0201030f02130609030b0601020601031212060e0708150a0609140d0c060203 93
    0x100703420890fa60010710b05070015041e568000e0f800251030b2030482c0030301480350b0014001b04907900d110705d0079584c401034054100c0740c3d07a0800740110b207825000900c50340c0c000f0307092a40100380903c010400c03c08a0764028500032a80d1500310402015121900034101004410f100076400314000303600390144c03020321031000241c6504500b002400d001d400d400480940d40149020400c591341700c07044500b210820145c40b481b81c090003845070308a108000c150a42e8100841001007440419070115004441102d008c004003a507620600045010482da80c42c0e01c910840d441070f0243d4000d400c00c1e0303a0481c0c001001881c0040704241a50707003401603081200000e100e140709000700400c80754a1030704620240014040c03580341d552a0040f0301c845440c000f0802c45420030001c3c0060f0b0036000758014041c040e140e03004a28144000900f10b00c41103e03004912010b0741c183e005241480c0c0201e2007580c100790b40b07440c0030070300380111503a58010702e01c841034000e8030b40c50318140450381991f09074000d0030341d96014542e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 23551301 1250 23550051 23550067
    0x804110f040212040b150117040c03021206010e070c020a170a02090a0902010e0f09040f030c02090f06030d110601060c0c0509011401080c04150f170a0b0a08010b0603061203040b040902 81
    0x1030001d20003030084015110a1b81040c82580e001000070404081041d21185a43c1d114900540f0740a9076620003504103440580c40d401240001c10034506031a4001401003031507941204c1250020400071029412640a010078080c0d0700e112080840030001c15003c4a00b4440c0326070101e5040300e02140c1180300a960391505204541c0d01c61500c4a00f20400c842c94000306010200007004084050002040d0a50102c18503003050b000b41c10401400350020041800d0345090f034450807802804490980c840d00812480c9502203000e0300d00d54890170080c3c00140016802c20070290b0344ea104030803069800d00744040d000156a5655038000340a00512004240340648180000d0040074014011401e00131341408140140c120b98007401c4019145403038020b01550f420081a1107985440840da002c42010300204991090b16800c40c01c0160025034003075850580d102c100c0c5088402642185901c002e003080410000d2428048404001110605417464259646503800c5c00d54410b0380140982600801d07281 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 23552551 1250 23551301 23551313
    0x30509010314191805010e030304061107170c01021b01020c01060b0301030b0601031d010c090608090307080f07110d0f0c090b0916020123010e15010804110f04021204 73
    0x5200c190350034032000142c10a40e0201d00d030f201040341c003030580c1d5a41c0c903140014100d0054003100d0b0b4a07040350003000341404041050741c0780d91080f0f07800d41d5090306182c1900341504c681c10459036420341100710680c0c02a0401c0c2c00d03d285900c03441c0d96480359902400400226203481e1103070800214074100040c3c1c0c408074210550b095984540c03003488040801e200400206810b00140341e4005002d00e400a6910b040b9596800310466611903400d0340e603c1c0103103806440d60495480f100752411034840c40400e0303450702ca4140d640d100740b410007080c02e40c080c00017804141c01c600c00b80960500ca0054000001501004034960305107548040c0c45548900101000b4000b03505030030005402c0400c0140300318000d17400456000c00000e0601001c0d0851440000001e40c401e600c003d0800d042c500032444808850301c80346612a200307004266446814802043e807043d905000b80c3d09903030041e1941d010b50381d0340e40c80341c05003031040700509a00485c5000d0043e03180c0d91180300400c0300d2403061105140a0406007005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 23553801 1250 23552551 23552561
    0x1050a0507080103030212090607060e0a03120e0c0f0303040801110409180c060e0103060f080c090603160611010212010e18060403050313020a15050c0d02060705040902030703180305090103 83
    0x1c401440400c50040c00400d50101e8010b42903d2000c9040e60f6030383e500c00205909114a04000c0d100a19040450b8401c2c0310204000103054002d50303460428248e48520801110742c0a203003035440b80c3c4814140107050400412040b085400203064a080036a503507841401e44104032054501148002001d111410203403060141c3d141c0c1100b82580300c0f45290b0745081040d00a0300401007130110490780780005a1090b0402e4002c1c0141100500380b40365500d03482d82ea20740024030b060384501000c0e00024524240000c9034000c0390070382c0c904400002e2400d0300540c0c1400d0003900c3d0820f070395001c100d8040d900d60340156a5000b881940185945d924205800d4007024040d94510042a0808030602010a5000c5c080c0c94120408484000180311244000b401c882c00a501c540305400003211003440c199000409040d0a4800d00103440301041c0d1003208a840765001c49240010a00502040c0400d04c50ba5020703551081c141d003000374620201c17203040c40075030306e4010042740081c10000300d04140f540d060042c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 23555051 1250 23553801 23553811
    0x20f0c01240501020607080604020c0a030302090a06180e04020d0f0c060908030c0601051e090108010c080105060a05030a09031b0b01050406090e071203030b0913050105060609030a0201180b0c01050a05 88
    0x7084a040e052000003900d41c40054444801c200b810004034820b59502d504885c00000400c08944940083d482c02070083e40210060500c0b071104c944002800c2402007a00d003210b14519060725400600340181e980c510031014009a030441d208084600c001030003034215a803e14062414202c4d094503081000303000f14056042060b1a8100b88461201c0700d1002841e81c2c15941c0481d00310081110300240b41c001c0306240b1070b1060340b089040c000002c0c0658194007c6010480595503240d040e0b0320340e0f0900c41c5500c01c0c803007000c000600400c0000c0c0141880c1e442048041c0c841e00c1d0100c01c2e010b4040131054001a0000705a408003499030041140d490944070307480003082e0341841800106a0000016110b40880c49070704510485201d80b18101480b0381c1c412814010000c05450302401e06200810456401040c21142c07586080085403640c58920245d800d141c10050013051000400d41c011a0408840c1b25100c601c10381409011881e41508000f07003100005034800024203241c4080300b41d091ba01c001e04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 23556301 1250 23555051 23555111
    0xe0c030603120a0219140703111002030403030f030b0612070305060301050603010b1507140d05030a0e1f0905100509010f1a01050405010c0812011d090d1d04020f0c01 73
    0x9443e07a190b004070b8103003084803000d141d4454402507400e108001c8203c005d413000050040c41c90120402000180c0a1400706060321074151107203100f0b00a9990303102e41d02010300803600307100366420b00511a810ac0c04c00b900020342024100760203035080d44044007041e2503203c0442c2e15202041040c1c00c00b481007661201c8210000d0210f074408002098007071080d1494071001c49000a00c0c00d0511020301800110580da0f03004582c251020b030700000b405a00183d860000941c08c1c1500302c0d00e0342c1d0b80001c070460310b043c031178440c1d405035006c0c203200070300800045c0710840d4a8014641c226940701c00c40d1003440e01c181c042400104110110400d141e0480305240c50050240181228a0200b40da2000556041d0383c801c0c24070700a0000d80c7c1c00c0840050250074480d00810f440e050001c20003030f403c0b200c1e002042d5401041c040c0d05407658a403464030b50060700390000005a07120f24600c06100012203612079a10080c000501d84040406515090383c018005103165070b460b08503070000042d6031a200d04040b91403003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 23557551 1250 23556301 23556307
    0x106020d03060b03061005070503070c0302090a061505090d05060108011a06030f0609070c050f0a0c06110c010e0402090604030606051009080303190b120105010312030e030706150e0c03060312 84
    0x4a180c0d41800701905e158001c0b0224141c0c0e55500b030003502207541054102081701d845044a24000f480410103000c128000c4d62540003240dd1031aa038040c0906460f4181e421481c10a800b150484042c0c015000c800e91204401990348023103241403064034040c0480030000b2881d00342a15041c20035804018100380195010010040e41c281c04da02d00076001281147c01051640364150b044580354500040508180034a80b0b80075540741c4000f400d841017520034000e0059169417080140d88005803410080c059800c6821044095845070b0003036400480024030060a0410340c00c0880c03815040f0781c0086406580c0c0e054140084c0c0b42103041013000e01d000f440c00150031070070141a0744d200d00010b8610143c6501d00101418484400d4005440070000070b4803000403418116134850107000d0a00c02035809040c8001190200e902c00d0281402c021840c00056141c0300b85565407030000e12072403085c1d120f00d503800840414140c12a4010501521803121000d4a030304000c000c06041c40155644029022020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 23558801 1250 23557551 23557559
    0x3021006050a18050c0f04060c0515090c130e011104050301060b070f170717030f01060305090307260c0d0f0503060a0b030402010c05030d060303110609060c0d021603080106020d0306 80
    0x1c401c0c600f044082c400c0100d4951590b44e040310b858016100d8504000e8801310300410705c1680b14a11780c000ca03004004880c6054010310142910300d4068072111250340014540c211181003040750903003041c0b400800010000741d0211280d08464403880e26032140c0c540042c0c104580d24007400b40802030041f003594949400c881e40d41d007031001144138400402c50b4072049100050344025400360303000c15801000750642400007280000d225402122a16500c041d6007002250640c42441344510881d620741c001d501e0480c0e2600c03003922484008001100d40b581d12103074401d0ba100010040c21904109500030075900c01c030800c01420039903401d00e510f002c0100c01d000300210703544c0d03200c03030003003155a02c4000b9640ca854074001214810364a0307a0250462100040700c81015003154441c000300c83c082c1ea240e4800044181d01242c403030600380c41201a603409100403c1d401584a1b0003042c101c50202d0005180070111403a500750000b40c0700083c1c01040301d00c4010402980c0500101c0c01079074881c501044841c2c10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 23560051 1250 23558801 23558819
    0x1021e06180703020301110406080a06030c1e090e160e190b030c030105010b03090c031504020108074103040c030803060105090a080601060219030e01030b0f040903021006050a 77
    0x801045003644803100c40000480c144107000c8036001c3c5401800902240484581d01046036002c4e209603000141250006501290b0034404c03141034951007000420f00c0c51030200903030440c1c42e244c41c0b01030010106034000908982184601d440c04d5036000c1c0901203d9520741030b00c8484413100e030f220f4003284250200300002c007001c9500a20b01c1c05900b0b1070000e00c0c0a00c3c04046441c001d40b00c0c60407a0598600400450b5003804100035511a2101c1c4044800c041c1141e03050588450186010f600b802410702c02040040d0b001e0440e01d0fa01002516050505200d240c070a20314118800301c0f48040200d50069240d5030b4404020ba403518408082038840c614201130340d952841410500c80900080d00110203e100e40c0e200c2d0b4201c4021f110028030f550005600c0d030714850b0b1129020f02c215005489005610981c1d00c80c1c03010134522868060711400403c99940c00150050702501c2003450740326003500b10300c0d5000e075524880d003240c141c080e90007400d0040c04808080202e0b41139400951142812810400000e030f0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 23561157 1106 23560051 23560063
    0xc080a0e01060605070602030406020906160c050901060e011101150b04080c0a05060d09030201140a05040201170c1e04080d050705010501050901122012070501021e 72
    0x84540d02908032103440c4155004204180701c82c00100f40c00740d010315030090050202518202031b24001800c643d1080d0700d5000c42c1440340344140c0601030228604400f4080a80303508a99504180c00600000c50800b940c60400501c0303000700e03143e03080071740143c0c0c20361001c0e620301454141c503501051160780103809064402e1007200d8500d070040c41c140010404a070009015580340000042c6481e014002c6041d080d4150740d00da40c0a071051000e007288107485a0142d038030000341c60805100040200384429140c0d03180c3c030540014403403003014102c01c0350701d10100064030200031900884015031500a992010384103014800701c1c01d00385900301c002800d000d84500020491031780c81e0020443c0ca26400c0c020801380d100c0709201c40303000419a00000e403910410350030350340c29a042540010300741403001e02110380a8100035420005560108a00610010183d00003c49a80d40d518919075840c = true := by decide +kernel

theorem cover : BRFrame.Cov 23381301 23561157 := by
  have h0 := BRFrame.cov_init 23381301
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23381301 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 23381301 ≤ n) (h2 : n < 23561157) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
