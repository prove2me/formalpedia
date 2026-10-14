-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1318
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:20:42.784951+00:00
-- url     : https://prove2.me/submissions/13eb7283-5de9-48f0-8b01-86de70639aba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 236870503 ≤ n < 237050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 236871753 1250 236870503 236870509
    0x18090c0301090e10020a09090f0209151b160312050f0a0509040209060c0106090f23060406050a0b0c060f2502010213060512010b04180f1401030501050411030c 70
    0xca040d40c0000c200065075840001c2c0c0c0301d15060380b50000d1032203a8400222145010b4011401b0f1040710003400081c4891400030030814142d00a0060450b0044070200d417034183c09071201c5c0a090905c02c0c2d40c0c040c0200c0041e41101c0f610300b01d04031202c014040400354050083c0304000c8414031200c02141092817038a100805040301d00d10034600848200800400c1c04803060781e5940490f44044c0b4001c0c401c1e5101c01c044075503103000f002d06104540c02986044844048000240904075025a202590710a020314030540260000c2e070042c03405901664420001c00c880c0c2e00d031000e050150404034211610f0b040003401c26803074030320060130488040820804000c031444081400c0fa4040b07140b0442520710090050342603000e0f0250b4001c0001044100801051240c0c0c004050405079001040c1c07010035981c2d600940842d842240118001004100055070f000190740d0003068054241c0032000414842d04522001608030a810461b00341e5159024002842002c1006030624041240540344a001003000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 236873003 1250 236871753 236871757
    0x90f0b06040314150c09030f0d0207030213090203060c451203030a0b0f150301061407020409030507030201050f0c0316030609050406091a070e310218090c 68
    0x83c03911207000703c2020711580a005445080c0c650b0541003140f8100704541c0c000b2034005005043c0288100b84605001e240c3c0040c65804411143e000340013043c0c215024090419540c50040da202d83d268540e800040e113040151078495960540c1d101d8a900e480a20384c0c1c0d0510039802c141000c0000131030a68210881c401d11155801d03280320200c2031701510600451050708100040040c540008020410040d286800140c891314045941c40064003a482c108071562015950030620b041c400c0c0014440c2038020707102c40d4444030a882401381840c400da0b0006040e510112070850024802007101c00400da02400b0b007c1d04148480400030b110300c0c0006c02c0b0712407808018460080d0359100307842044402c1c0030f0b070b00c1040036000d60842449540b42500b4180c0c00340000b00d02c01c403410030314400b800f05001681801540201c4135a5604e8030130030a4001008079008030808020760175446d248443c01091086200c072950701a0031200540c44020214a909036412115005401075002404100b421101041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 236874253 1250 236873003 236873009
    0x1407050d030c020c091008160b0306010e0a03060c050a03060504092a0909080703231c0605060711090106030c021518030a110c040b0612090322090f0b0604 68
    0x907000030b4107010141e049152004c500300c62038210030518148441ca030600805602600c00b8402120452045954800d05040c042d104495806034148041070b86584601252005180c0050801038456202c0e03c45e40101d902620510340400d50002d110b91019426000c3e0b00000e000441c1c04002400142e211030b0a1b1603601348250344004204040510b128031a06c40040280400c3c260410003550603180c125050741c06220300703030041203080041c07810741003500b0b6462008980d0300c60204e09002c1c800300d00c00b84603048514080c80990320341d01d0102d91601d0780409401061b00643d000000c44c001502480f4440030103030070400c00c15040c0701c441c000607070300080c5803d03600c4202c0c0244401d503561500b614110060104606c4003500000809803072140c1c1c050220080c40c1a84010740f00c84252080401040b6030504241582041090009102000200c1e140c10f511980a00689180a00515403140c41101810445d002c00b00341d4a402e2000310001e00c04c11030303035841003a42040704041080004143d80100e02c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 236875503 1250 236874253 236874257
    0x90203060a090c1508040b0c130303110114160f02340902041502071e030f0c0509010603150503010504170c010b061606151503020c03040503030a0f1407050d 69
    0x10b101034040002a020361001440f201d05130070800090810020903c40301580c09072811103209021402c0e00003030200b20303840c1452031a0030320401440c55074151103040c002400001155620b01d11800f007000c0000c2ea052080407a144401d05441c00c070b0034083d1000f070000114208642c421744880a00503940d42607045d80094844055a0944d8620340c801d10103000c98124024041c00410005080009403d00000351741d000d03000e59030103603190b50003040854200d0540081412030668100b01040451a59449650084035680002d80d103d20100c0d0b00c40c5000e0740303c40e0000e50780301e40360300f03031042c003401610f002d004101c000b4001030030a0740714a80103194041c4080071003840042c6100a401d42584200c04502000e8080c0f030321040c2d4415100842d1850500c150ba4140c10800008103100140c0349440c01e54a580024246200021404800079007200c40fa0700b02e584070411000c1543d0350300300090005191a40d40740c1380c203841d0a110007000320b04200d00306915440103001c0040050004603100400d42c1c424 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 236876753 1250 236875503 236875511
    0x70806010c020402160308061e2202120c030601020d0e0901170a0614040b0a140a0506040e030d0603050c060c03090103020f04031b14030a02061605031b010507030c03090203060a 78
    0x41c00050005d100f503042820b0031058401c141c10815400101c0c01c1e22a02c01140d19030030a2031401da003590301c212004001f0768820600c0c13403c0051000300f11904590707200f10a6005003007040311480f04c4001c01c0266600180d80001000f041713050740e8104002007a0741600c2c40d103001010600d00210302510303810700515010b103041600e9178041101c2000115082608030300d0500c241d80002002050200041d201a20402e52001c0028184c1c3d800340203001009d44054095a482d41d110300e10781008150260845920640382d4440320942d080800160a598204041c0000c84030b00c2c0d4034102d49030200e4000c03058040d9030180411076107110003000340e400708c82080c00c0150313032040350704600b504a2190703800c02002d120101820328101745040c0721310f10643e01003c04276080d091a400800d65584550880258009002c0280315080003940300c2a8403003d224208a0b42420811b44000384418030511650030f40360354401c00c011f0417662602583c01e01120314182000075828030340103c0d8990700300078a000001c60b11 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 236878003 1250 236876753 236876777
    0x10e010e0a0b18060a0c140304050d031e060e090c1012020a0905040c120b01091a090a080114090d0804080304140a02060d06030c0b04150f02160f05130507080601 71
    0x1802020090742a1805483c45858800c026100a00345540c0346c100044081c07203a2002c0d100043c0880340619080b030010040c169022000b1405000d8403007118807815103562010a0511590042c500641080d5100c0440344c54a2414075151011a007107461044992421b9422403540140d085104e10003603050159a4882196080e1030707402084d8001ea400c02c0c42c1044104a041d40411401d01c609000002401194040301c0111012400d43c01945420314544040b02000b07200f0038028004440041c040c1c103195680c035081d0300d0850b02c054204205940b002030030001d071100c0c14403510b040405241030000050401c0c2d12a058140401000141320703556080c81c032a112082000304c062684e5008002565070b1000980440c040c01180c4411206c855058901284143c588000d82d4140c480c507040040d0b48041d042c1d802c80d012000c0d83c0c10b03001540542ea5045410301c0400321110007403c2207040301080c19281c11700307220119810340c1810214134500000d01188e141c2c0702a010ba0008401d10b00010481c0b8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 236879253 1250 236878003 236878021
    0xf090b130c0f0e01050405160e04021c0606051201170a02130b15040f0819020114040306051311040e0a110609030a12140a02070501051303050a03030905010e010e0a0b 73
    0x201d03034000c4004400c2003080050ba10003400041c80c1a6002a1410b10841c0c4a60723031a500010340301010040400d00e456513050003401d00d03902a11011b800405403038040c01a01c00799004451003608460f0028000007007040c0f907041032059090041061a0712840d501c1d9482c0d10054942c021010002d1040e50162a600071680300c40d085030303002c0000181501d4070040245c0c20b00c00c0366481440b907010558581c1500107190100481c12241c2d072403901a5100600126600460701079a01b54060920b200702448044081001da00c2098440e292070004103148454505000c5140c50250514070701c160304010f032000c0b00170000b00e0030220044d80441080c1c40c0005000c0020304901503055100d030035108410149081c4100300c40400344c0054592100000410504104c841c01e1117040007200c09a4000031003080203500c120300914500202c0030481e100151259103060422491686c1940000d4840303048400703101003803007071485040680c0020480341c00c640d46600e455440108000d03010300303580f80000314664 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 236880503 1250 236879253 236879273
    0x9410709051003140d0e01090501080c0c03040e0a0b0f040504030c020d0303020f07052103012d0504020f0a020706031a0d0213090c030c06082502070503070602030403060f090b13 78
    0x1540100d541d002c10130b00c0d46080303640303140b40821000000c81c508403030902075000e419004160341040c2c0d161700c2c09a0348c149200180703900201c206180f501c1304102c0081d2000e02802c081d8090000118082544065401080034100200810030312861a180034000025005407855150507410344d008182164030381401d40080c01028100c07940003030000f85803004c125000c1070000020071b004841d0040710b00410307410302090100b4024040003131021103850801941201030030403000a00d4003c8501245c1f1400070900f070b600112200c802d1800c012450f1000203030117002002c054011454104092540c1d58080781042010518041c081d0000c2c1c071003074083d921854031100707a0410106041c40726041520f00f0f0340c02030020344421b50b5414001c80c404070340c0354810701101d4003812500c040d0684080e54a020500412454a005025441012800a200d45080c00410020b24036070300916141c41c41c60070000142c2d240403808005c65481e080c043d40000d41c45544098008900c283c0310410030f0303200e01c0e010102d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 236881753 1250 236880503 236880509
    0x31e180503031906090b0d0803041e0c090b0f0a050607020d020a0b0c2e0c020a060e01061406120c1c05010f05150705120d094107090510 60
    0x3800004100f0034001e190403000748200780b00010812403540d607281c18204a4820f20001a402450395400d0008150440040c54215002d460082d0314803000180c4076a14840342c1608403000c0c110f114042040946a20502000701c0381580c00c121000710200c00120525210b0089c02c3c41441c002ca500130643d107843d410040c100707501501c6036014a88407282c41e040c6800c00841803041c0c0c41650f5840802c01500200510304030341c1d4a20019488550781881001392400c000c20b071086210750134902c00410000c1c00356905002d0f5900000618a04200c000f00d41c480c039009030a8000d900800c940402d2081e2214640c0d4440300358040c1940301c1003144914551441d0b1504414800e03810200041707200c0383c001d55a0000c580045420030350100c11410030551a0050242c09440d940055001d03440303001280c001020200c0c011103001940040315600c01c0d8130b00381303e2412740c48242c050941c001a8889580300c1142c08207848504480940381420404d1703a0f0300024020b860b141c0d42c0318804265101080040d85000d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 236883003 1250 236881753 236881763
    0xc020c04060f0f06140910031116060501080f0a0809010216060f0f1d09040809030a0606080f03040305030d090c030804120201030f110406050325020d02010507031e18 73
    0x15681d8602d03100503404498010880180c1c80800c00081081c041d66110040e83c0412111509000c804e2080004000104a4001c18181c40360700380300041c200c0c0ea00801424141409145642c403481c2001d20446070160401e1149522014090340c03840b034005103c80c222640a2030704d07540c0300842d0004030300308020140300040b4100451404212260880d0000e03003008180d0b030b145000d00c0200c4904558448200c8030b4082c07409401d40f0071141500f00307603810070791150080700e8041c074141c1c40001003443d2406481c0709480719580c0c0d00003440401d40030300c00036071413000c4400198145415601c1c1c2d80c2d101e10070304e580318103899502c0343c400080101804441c00119003041920ba1520750b61654050008005a022400240790a10303d441501c102c1c401d0101c2360014000b41401c01e8189042a189580040d00361a8040120a444c21800290103101e0080403881c0d4054080e8240c40f050280c2074400280074102410b0074000b805034070311128828015100c0f500b010103e144610a02e80c007004070841e0002401d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 236884253 1250 236883003 236883011
    0x906180a030311060c09010e010813080412020f03010e0d0c1502071a1605040501030c05070b0c041802070506040312090506180f06100b030c0f0a08160c0203060a0c020c04 75
    0x40c980c120100f100c005900344240d41d41a52002c2d800c0d043c510405101c180800c41205120741346520071084283e00282c2240030000c109840d49401085400642c064004c041c00c00c0072030402c50610107510500c162007540207000d0390700617103000303922141040c1c580300c20001030341e502c03c0a00c1504510070b900d40441d020115910000b90a2088800341304000e403412aa680c840400d116445880b0451694a1b007a56940e051038100001103024000e114004000c00000f44400004982d800c00050300404800301040d039214036048542e88000ca1b0b60b16642605841406010045003001c03c20940c000d03850302d840344440c00402e154500500c0d001c2000780840c4602000c206800502e590080345d5590704408031001c20204600d003903600d00040381e402d046440740400400140541c600559004040c980c1898100704800711004001c0d005220f1010000d0056010b116840c3e40c03840201580702d01c1440c014400b2000754011aa8482015041e6004140d584440b550301c0303482405480e8000000810070300c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 236885503 1250 236884253 236884259
    0x1a130b070b060a06050304030c1203020d11030901110c070e06011101051024020c0d02010e0904050105040209160c020906060d0606080a0509070e0a0207020d0629040209060906180a 79
    0x2000031200b224014010361080384041802400f40c001c0d41d10581c0d050740e9011030f125050b5162120302174401544400c0c0354080c8404021410103004a0000c5101d6401c015100e24016404030b0944610f03000c0d510000004004040c14001c001c9102020390b1495a0281c519444002c0101d82e00c01e030385000c0030301c00d5280c0740a002c40590540c41000840c2d04100118906895042c941c4a500352091071580141c7e01141101d69030713003000340171840d50500504041da0307031920960101c1c148071011a02116180d5603901044210710f010196950400c0e240300d8040c510313a07032030000500001035542000e88519aa440003170500d903601400c0380d10b220f40390a030500485d07685032005005620182c400300e21032401c110002d00a204002000780449a49003000c0d52262520419a0000d50011400366006a040446c480204000c2d0040c0325005030490300600964890f401c090301d0030051041418803860041001c0c2380103039540025910720f4002190307815520320300b02e2600c2600800b400c015540000c0050800 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 236886753 1250 236885503 236885513
    0x90b07081b1b060a050a18090507020616030212040305030a0b03070810142e0f0b0d15081f090f080702030d080c0f0705010e06101a041a130b07 63
    0x3400c100c0e42c0580d401403202a008100109801082100d100142051060038405403042001030011851074060800403501e52480205840003200c1110140e40480d0501440c0291000328401c00d582c10320701142402c0028103001c0101c000900042d04200011001c0b0b803190f40e055000405800300201107944e51a901c501a0707842e0307400d21100350b81c07007890840450741d0841c614031001d101746449140e41c43c0c1400102042c0b142144650f591880c50740e900300700418011450303a10030b0080c0072aa040a030b21007905c401c5140903220f003846100344100c27500e0b0040051200001d0000012a411071013460880c1c10181124000e10413458060070a8421035505403d00c40460001d00419000f50b0986040720401401602c1c110f009076450482034070708011810b01e1444445c06800702912441c008a8841d44118031245043c80994000941130b510610401081d41d14121000c440c0c66810445400d01c0d160094003040281d07032050000c0501000902c40c1c2c0320340d5100c031050000c0d00b8922021a04d41040b4144 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 236888003 1250 236886753 236886763
    0x1020f070311100315090216060207060b0a0603091104050c071a070e0307060c0605150d050f0105011703030a0c030b0907110d0c05060718150c05070603060303090b07081b 75
    0x50900500711850b003400c1d000d10a00a54050300140841045c0c00c500d0110701c04000d41c00325040b20881d460002e60380c00010443e0005014540c00364102103a10800741d820002480c626a101000380342c5019600c4000442c0c0c41011101440201d85c0003035543e82d01c20100c0f14601c981c81009010714008107c14120040b000540d0340900d101e540c0d5075103044544028150f0702c02d41800f03821701040c50100701c0000107110703070456a44002501c05405850300207038081103102c0120742c000c9819400801c42e00104601c00d201c0c0d94014040c03070840d030b10800c403132145d001c2c1c0f28032001d0002c00d07145440324002d0b180c2d075000f604410301c10038010786038800e2442d00d854001c00c42d00c1003000445050207266001c0100d5031240a542c410703590000b001d001d454460300000d6a4048101000100e00700c0341e001c0000c3c510720058100c00c0c0c1070760240c507002030a4010307141490420381141c104c04181440d200e0306001081c2c0c0149980150303030951161076a03481c2c0a08100b001c0c0c0c090b0f03e0080c08001031034908480c05441c0802e03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 236889253 1250 236888003 236888033
    0x519090501060203090604210c03030c02030f06070f0c02030312010608090106060c03090b13080d02010b010201060e01030c0302060705160909330207031e030504050601060203040b0403030e01020f0703 88
    0xa810059a41c07192400c9840c1e100d00319400780e04c080184410301044002d0742003603140c0c00e10301c0110b00d0400565511f14540d4130080e8010f40104400c4000901036080600c45c5407070907100407005d0192460007000c040c100c00512403e403002c0003e240c1c440811502c08000b01d072945d511740e8030721030300c95a5102001090b44038102c8041c0c1480d42018400609070f400fa00b480542d151b4151102d12a06040051203482d40d0082c0b00c0c06103040070118000201c4440902c12030084020382d60022490840b90000a0300f034500580c0070711a800c14040042010407010300740d03501030703075411941580e440d4030320304040749001c210901c0f01130b44421004000890003034550210f00d000384245289250440c860000340c0149818a84041b0140060340b140c0d02c100180c0d40c010f08400b8801d00344000400840e03002014108880550800801d40c0c41c000e01c024098100090f900510317252004615190a0079050000c5011300e00c0b00034140955000c8006090303000703018143c400708501007222980d59403420040745110f00c0c42 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 236890503 1250 236889253 236889269
    0x4030609030215010e010b160605041506080a08090d03050c12040609090209030a080a1710050f060a1b170a18060912020907090b0d0f06171e03040519 66
    0x440b4005034100c6910449040305c415002c00c580300ea182c00c0d082c212a501403040c201050b004040b8142c0000c00910899000b1801000c20700302048003500000229001c54120350001d901101e00d20000807039000844810950954500002c45202d141c262101d000d083d1140c40b40d03000f5410700320b4244101001400803200c0f03030f50304c058090b681e4a002000700c0c843d01c54920b405400024140020075010001001000e8151524220342c07600d0180e1120400e0f8241d4080c140d00100610030061840c0c600004500c401048840030302d026805000070f004078a02c6807407800301d4812000d40c0c40500000403071700300c140c1c256000346030b956004d00c1100a00d1005011140078140c021400f02040d11441006010251082001c0b0703160300c214941c00300022440018448400c00101c9000416801c40000c06021400c21449002c00daa070070500c640d0056401540158140d854000140c00c2070841c000380d580483c1d00c0d0b900354549100c1c6541c04c0742c2c1c15486a0b4001030707000900c85030741d0a03400590021081c101c0d0b11031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 236891753 1250 236890503 236890513
    0x50f1302070c03051f0204060c020d05100f020415080105010903060e0102090607030f120615270807060914130c12021305090c0c0a14070510030605040f15140312040306090302 77
    0x708041406c9000b10b020718400100010382102c018100f1000e89004a8060011102c41b620080d810303105071010190070482598011404210b88084a1a6010400e0a03410031007015030410b800207000d0046440050521500c40d889001c0176031081d4102c800c0880043c090036603078442d82c14041d00c031401111402c00000e000380801c8000c02a68495942aa06225102114030400032011a91714481e03c480320341e00e90724525070620413080c50042c00d00400c170000142c80040c0c50a480a841c490007a840a034521a000c1c208111a668912000000c504820400641c8140280080710341c080e03c40390044150384001010700d0b2040c14a074a40d021620100d9505106588010724000c8900a5100d031011941c455043d400c00580600c90900c0054090700c00ca549199036030000600300c1099041003000700b90b07619418495400d00d401a2103c4201d0680140604101c060510382e14600f1480389021013141141c11f51110b0341e09000900c20764100300c0940e52233503201d0030000010050200218054820 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 236893003 1250 236891753 236891803
    0xc04030b06031501090e07080703030908070b03060102060c071b091d011e0203060d0c090606030b06070201020c04020c16090b01020705091501080403050d09031107050a050f1302070c0305 82
    0x200040b03c07078001001c1048025542d10b04880f141c094801140e054541c0c1c0642c540204400c081004510001c50103952286c1c9554940740e2220b09001c6140c0012017052020010460280d030002400ca400064814134a5620300c11800d005078508c46100c100d41350101d00e0f10f400940c56000e90403c01f0a200b40c41402249010030030081400c962040c950070281c600e031101e00ca0250089a0301075640302c80b000d07141030fa5040240e0361351885005d0541101c68029503c4000f401200e83c14400c40082d000c003510710301c0c035004964002030758941d904040707203200d00c0c1c0002e101c1507032240078004035001c10b4072200000c1c100c0361202c4007603019007624186a80144619400010315150209c885409058941c8072458118091001101d00250043c000d6003844020030903c41e02c15111700c02c1f1000740e40680c0c0c503014101c1c1a983c0d0107041c19201c2e80f0080c0714034000c450510083e80c644640300700ca15012207814180d030440004510107406241c1010340000b41401000040c000b000c18991089042062410744d8580 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 236894253 1250 236893003 236893009
    0xa020d03061706060918030a020604033c0905030a030518040b0a090c091d07080603030f0f160212060115030603110f010201141003050601090921170c04030b06 70
    0x42c42d81c1c4440c50ba42c001030100300541000e41002c0d810182d005504440054507820041c5542e004561142c01a03011004000605910400034010b008060b0b10204040408980c503c40c91820a100091623140c2c0c42c203120b01d00c2ccd02401004004040c0581550020449403c2c042c04a8004140312800115003e00034500c80c5800d1003800203d41c0002e040c503112500301a150001000c0001d038110610581c1c0b440480c00c14101615104540e0301358065541070300e401c2800400d01c201c09403070f840c00b95006000c80f840c0a46402c00340c1d040300f070390400310a466400c00d80c21003507850480400a03400c808109013003a000d08001c00c1087c16910038408907003e11024442c21408c036145071001410100b84480d4006152500d1005580141300520020804080d180160380741071a00395540036400c0c8480b030b01001002020b0000a00400b8800020001d484507078461510144000034000d814024242d01c100722240243c104030782d003060510106881d85001d201141a40d4440d00046d50000d002c000040e40610b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 236895503 1250 236894253 236894279
    0x30d0e1503010b040303120204030f0b190e030a032412031706010212070203101407020f0a05070e0601020f070306021c09030e15070803040c0905060a0e130c0b0a020d0306 75
    0x1501e60743ea1a803070145151011210b541300d02e2800110903800b0407000000c1074041490483e02801904000c445003040c840381c81da220003c1d1201c0781c2c020705140380307a4050340700070095a04500540c20b001c80c4003030000b041050b0412251840010040c1304000120380c1c2c0241040703001c0024807a8441d42c2c050343d481c2c4104d400c40e450860303680340103134025030880c4450201030025210840c80642201e0002e040030000c4c00586106014103004e0101240410000700d6042140030b140361541c4000e041030b06400d032141c50329074407140600507107010000041041a4400c20003503080039000410703100c00c50b85030316109000e0b40c4025000b164048000e04007042c072031302c18801e1890003549605e0710801c07240c401c001c2c03104c524501818400c10440c240b0540d0041010b0100951096103c0c0c400c4886140c14800c1e901c0448401618083c00344881d00001e000d488080e4071100d4002d82100301e41359181009161005140d4280d8100b00800304001c5174049540f900050448214000ba4800303200c0a80c40d100040c07080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 236896753 1250 236895503 236895509
    0xd060e0a021305010c26091c12030b06031f0314010c02011d0d03050a02090a090e12120408090f041a01080601050a050904050406020c030310030c05030604151802030d0e150301 77
    0x40707034241141b4001c010596030740c103500c4500715084900780b24140001170350004000c900d4214450301e955681042000d01080c4900354007042c102000480c4080020815a0100410003898802c14580d029801100b401c030303013130085510004a68000049602c0280605000c0c0c14a4000d5824003190030482400c0c6500c04160000e01401419031003410b8500301d0117400c0161060500540c01c2010100644441750500c024062000000c11000c42e1200c05616040725060750a266003001e100c501f41015200b03800c5904250800885901c2c1d4492600195106040d40d007aa50711514140307045852048804c545e025484090b202d564066075a4001991244501824000062010400c14140d440e0070b900c0160480e0003444c005041040c08201203142d41c0c025a5621040034a00004004004003900381e107000e45800e0b0082c140390300b07242d81c0741090b02e41c00a00b44042d40e51203002c4140742804048005840a400070b0031a0b107100c450f0f120180c0407100250342c40c1c0c0035041d41000401019a404212812 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 236898003 1250 236896753 236896763
    0x224070c030512031302010f03090512130b03070e010809151806090c092e081e01150501080a0e06071124070c0305070602040b030618100306020d060e0a021305010c 72
    0x203075003171550044580f0f07c20000c4000c1856940d00b550380100340e040205138100400303040c07229510480f0848040d5400d03504d500a2180c41e030200200f00c000384c1d00c1803104130721074000e00303048070a900d03687e00460601d07406c840c0c000007160814080214140c44251107400340c005002c203a036440d0700d803540c900c4d03103920303400518503048004400410585121452071465010481042c10921858001c4404080e0b895610000465002056081c42582409698290004030030020070a036051030f001c0d5180c0ba442c0344180d90501003080c0009403404a5600300c00b007210320700070944210340b4200d68040d18040351426882030302c1c442c2d00c05038041c4102e14075654890740d0300880610440e40d1000380440b541c000401048042103407d000e142c0000c1c1c000e00140c07000c0c00c1c91014045d16413030950180001c2c1104415a484400421000d015510403440038941c1900d03080340002d0380e10307152501e20b0f4029058961180c107582c00350204011150080c0e5003d8440786100183c107443c1c460760b0380c0044501d007120700e10240c8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 236899253 1250 236898003 236898031
    0x50108040f021002030724050610170601090b0a1d040e1506060c0f010e0d1e0305091f09060e01060303050a0302030a1506081f0b04030224070c03051203 67
    0x1001d40351100d2203c1d181071162048074035080b00c660b94424180d00104406450f01c0c01140320f50030107041c0b8013490394400c030151101054a40c1d07610f002043d1070214484400700c02d02034808900540d00c10055078001d050764210141d911a140c82c4000c1a40303212500c00d010007104403000c00082c0c07400d800398060054410004081d240c80c5550300201c503000292900c0da020710200400e081c0c2c0034040c440480780140c8600001040081c2e42045410180c0303035a100342c10044117442101803034985030484401c0f0200c6160000f4182c3d5980101d0b49025030048201c0c04004030085040341301c4440d07410040040d8494007060080d041b1192074070307003038890a0000070f000c10014070540001c5d500ca94040c607407000e1a0140841c8204124000900d01c005036041400004c0032101048070351440400610015130080450404841c07170000d18400718051804000d200c2c0c0c401d8a031005c415004180f80400218080401c42d40d25911860130000580192100329014022419098000712000041c2d030b20031411040320007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 236900503 1250 236899253 236899283
    0x20c03040b0c011401080d02070803090105030a0c0903060e0c1905060f0a210c02150105030601140a0e0a06051206150904081309050717010b0406030213120501020d050105010804 78
    0x441c880e00003410750300d040c1d9600e040c800c445940d0340c454036000700801406450304445038200282450400d80001409920400401c0090399000d821a50701213900352000600505014040f204412194005060542414040e811210011449403c03c9804488904005103143e1140c200c0082c54800d2030f5110809205680f0f020246800405404c541441c2c03010060314401088607840b640d240c4100c1d400d0b6590410119256010030054492210441c0440d21640c9440c000aa807007905014824000408080c1c0301e09a40f2815500e101030101803140310007500d0859904401001541728a62180100c1003c60500708030110711070b40554408001528681030100c103105c0955000f034402c80701031004114009445041d8148071010b05503509001c9054141340000801042000001e0100608a040100b0040d030115044500300d0b80c4508015896828881004010b00c2c1c0980c408042622803500500402806600400c9807214284c1f0401c46070340c80b80011540000704440040503160550450 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 236901753 1250 236900503 236900519
    0x1080703030f0207090903120c030203060d080a2c010f051e13030209040b060906040c0c0f0206040320010306090b1c051002180a050603090303040b0403180b0d050901020c0304 77
    0x44640c42d8080c01116001c0e5070f00c41100d800c42e000c4110940000c0c0791544440b140c00d41902031011424081d14007507084d81070a6000404603521550f0040900e000001c6180d4540d028034084140008490107020b80748a0200c40b00c40001c003068508d9002800600014014030f0040e000e80f01300031400101c0c5030700c1100c1e604218006601c10b003d0003410032080e55001005035201d41801d0f05c00c5100b001c00710b5040c1010000d0160745400508050311490512100042071940301440e00f0701c850b002000204581c180d0700201d00141724030380018184203982c4100801c0b5041001314006100c10a0340c08009440c1c0d00d038102c00441c3c2c0c60b2085564058503800c0000300300000c0c420040c01903070045066071910030221901d1805c1381c3c48a07450541c54010302c605900c20346440c0080d007004010664201d0301d94506066482d882c3e00c4000c0c4018884448000410207040c45010f00082411155020b158400c3e26024210401d4004903505400c66080c43c0000e000c00354180295400031951b10005d500341400e101c04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 236903003 1250 236901753 236901767
    0x6050906040503070b1b040b12160e06030408071b1701090c0b0c070f0f06020c040606090608100e01030308040605090705030d14090a06030c020706090e0a0c020a050a0303230108070303 81
    0x540701d03c0c2000c410028103c0e00c44400420041200318221603540c80c0315040f454410744000c080030541c00c1e803030001072b6140e0303003025100e24010411030b0300581e030342c2d0f491612500b90700510002400866000c0e4226001c0d0b40c8003030a001c107661101c0100480f800e901e0b441c4c2403ea4a03c10381c010b000c106a40d80030001482400d0213019440c01c0d800646d80c4654681803038512030081c0382c0c000702c08501c4000040000e1a014050341c0d07088001610b0a1183d5401c09601611140d103d03c103502c10064030400040c281d2a066440d034001d05803504000c10207594a080090080ca400c1e91b06603100d5250602143c50403400082d24001c0312405409840c000c0b0500006a07001200707080d80c0702c3d00480401110074160380d030088107006061030340c400103000740c21120000c1c0b07415166040741052100500044c06000c18031701c545544a92440b0001ca401c2c181c141d4202c0c00c00201072001000e900c945030002080541582009a41440c00c10400350341c1b42a500341044c028000f80b0031000f4580008000748042481020 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 236904253 1250 236903003 236903011
    0x3010f0b0f0910050d0e060610020604080405120a0506010b0a080a02030f04020103050a0e1c140c07050d030e0d03030605090603150c1e0705010606090e160c0501110409060306050906040503070b 85
    0xe10a0404041010800c195081c0c1c846c00041c85e082081000514541034180c0700404a1500c000c082e603280030380d1100c074544942d0140600c101d2041c031121002100400c800382c1d091781d000c0160b910301c1d40d6a0710b00c82d50b00d4120001c600080344e800350015007940014420743e8483c0c015008490324a4899400540013010060881d244480c0c8603614020410740c200003195507031064038040ca40012500c3d00042c8064041955580708039400c1041d6229100c0019510083e02c00480c0c0000f521511850182c0e03a50200380e01051f00140198000411305400d0790060b401c4403015030346a801c50396248e0805440740000020074003900c1480c0b0119120800b164089d03c5115142000e424000454020089a541284400312100d80d1503100c2801866400000ca0000b0000e900a481d11070422410100e080d8540030802c0040200c0300c417800050103000d400c0903070100c3d0051a107030f5030340d80c64600c110060961400140c40e070f2404c280205000d20000201c00707205a811402a600b051400d43e5080101300c0060 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 236905503 1250 236904253 236904257
    0x90906040e03070309140d050601030311011e050405100b0a0614040f2709020105221a0c0105010803030403050715090209072007150f020307050a0803010f0b0f0910 72
    0x1c202840348041004221580c002d03280c0b200540d00d032256202c0360b00c810780c1820b801a00303040d0740480018800100d003410f480e8182405000b18008105050041180e480030701c000c82000c03a0403480300c0b801a03011602481c02003060f20071002c000541c980a507004103001e96000090002c0400841d8450500b100e4924201c2e9040c6140c01e6480c016214030849a40020301c02132540140402040810800c402516160b80014445998a900041c0a50051451403030803500541e07502c2e42c194204420200142c00740201c84c015031340038141d0959294101c205021880c0d07180c40f001052054002068030b01c01c541c19900e1601e00405036642480801d6901c2c07031100d60b16218007181e40143e82d00c500441c80303074089580b6a40340581c0801c411902111180d2458a00c2d0881301d81449036010840703041d100108107042410030452000c50403441c0d032041440240403400307248090b50070000078400070b50480da001c40e400c40780316459102090343c511610354514400c06040141d034015052418030650300c11294 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 236906753 1250 236905503 236905511
    0x30609061315050106181202010c06020a030e06040b0a1103010807090905030f0f03240d0b070e030f01150e010609060309020f1c0303180201050909060607141c0c050309090604 77
    0x515005050781d0f030a0700f03d00c010170555440c002071000009803800041429130203a0700600029000a8854841014040c01e00c82e0009050400940290030154054101c10308036465032410741407004c0003600503180003550741c1c144071120b440c546403002a64140e03801940606440303498907e8223070092141c0c150450326030000b40007004800713482d0406401150054042c81e9501d18010a001d000103801426030360390001c030012500501e07100d6080038003015a010b445103001d030f2107001c415118800000c0101c0c2e414030560301e6012902606401104400701c042ca9042003058a50324600d038031303007000d00415002911030241006082c0c46a000000c19a001030801105903603040c01041c0c504a140804d002090960300c03001e0304255040c403402c42d002422103150008101194002840740c415440c1c0c180c407941848021407915500d80f130032101d440b40d20000d0b4000c920400200b541c0c680d2041d07891004803c4014210ba844640a25500c68015078818065494000c144040184003000078040c19009581d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 236908003 1250 236906753 236906783
    0x12150d050c6304031803031d040204090f09021801050d170d050c07030e190905041728140307081008030a0302120612150c09060a0c110306090613 64
    0x140844000040c0900712034035a0381c50103050107441390900703414050280d40080310402c0840d038892301c031110040105140f040b00403845d03800240079002e00e81111181c00d240152160000c0c06541c4100c020754826075482c101034411911900c1c4980c001d01c0b801c1c0d0484101e0100c0400129641e17074420000301c0c0c0380f00382d07800c2c5803240440c0780495104440b40d02003c4000030b4044189a041604240b00300003c64528061249040000c0c1d0781c0080d6108002032030b0f031100f000c1420401d2a01a007100c030590045c2d03503031312030b024004030032000d185e49042c0c46907090280f0007100d01540324051010046900c101e0040c41c607142c91608881c04103005103281c2d9901081c410104030340070140002c00c00c246480d0340153725180382c2c4c14490245d02e40500054416115074450500000000c142d460001c3d507903444034116541d5040050466104072040d4a078003d01c00136007900d44940000740c43c08010300410904020700d038480b00f4140c5c1c07030b0400d07540383d00281e20650009000320004140110a40c0c81240c1100745200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 236909253 1250 236908003 236908159
    0x70e01051201061e03020405092b020304090c090e010f05010816271d060a09020703050409050412080f0907051e120f0f0a0812150d050c 60
    0x364030340d00c0001c104d180c2041040d45414000e50741c2055280014001d0540b0a08101301140e80195040443c90462440140c00f40d00910079180103058040c001c0c041c01c0b0152030b00400329042e6010b84100000c00200121307804920683c1141a180c0c10303191400d00d915200140c030400250034803410104a8581a40c2c1d0710642c80e40e0009840325254520003d05500740381c02c03801c2042e1038824010711040c1d10010000d150340c50304913035411600a1040140e84a825040c200d410340b02d50b40110707500908100600040280e0021400340316030459841005a846006022140500a5840085540c44490103002da8500a02622003404110105030340750020040400c50307010a4440f6130342160085141c000096005100c4240040d1a071405400d0140e03280c0d58800302070040c80c048041900f56003002640d842c04489200c0c1c25148000c1c03c442e500c0e49070785400c0c1c2c2c1d01d4a1694899000b0314601e5031103001c0d8030341c0d100980890b0030b01514800c0b03400f02512880d0715034109458950f003904002004d00c40c600d5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 236910503 1250 236909253 236909279
    0x506040603050d0c12030c0801050d050c030313080607090506095104080709050a0b0d08180603100302132a11150c2206021e070e0105120106 62
    0x11181c0d842c4d03d0146182400d000c05500c01e029151401d150422004450b40c0da8003042c4d280c1501c8045521141c5070100e414200c4c540744a00d44401d800d03100c0043e6900c80340211017481c0c41150920011154142e403400c4048504030003d2182680041080c40030208514007900207181400342c0b11141420104140c0d442c11010301d01c58404681d024400d1155600940f51500c4502001812440b20307140c940b51000f20707039460f091842082c01c02d40d941c6002c5083c0d0700a9800c0748024044c0200308050b842803e0511000382c0e84aa1001074a60241d04002d00c194207003002500e00c01c0344280200782080c1d18640a0083c0c03058030f40c41c81d0280326952219502d0703da00408503074032402d840c0543c12611040c00440544108504c1c07055109da54001307080074410056010100303601544000c06591552403100f4035201000403501000340d0f00f40c1c05100130501560008071080214641c001c19000710a500c1c0245441c0e6150b801100740401c4400010301590422040045040e00010700014005585011b100c080c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 236911753 1250 236910503 236910523
    0xe0d0618020301240b0405030d0c03020f060709090c020604020609011409090c0717070b01120f05120a02010b120a02090403170702010204090b060c06070f0507140c0a060918050604060305 82
    0x441c0030442080d40010071140d400d8045e02c0610f55251500f41410006a80c1c2c640c0340114a01300402c585c0c1c105d081510074461608000790703050072101306042409001d0079088040c06001011494154040c40031440000c03000d000f1034014094a280140040045030f0125241c94071b550412410880e120041c4c5440c0b14807445010071264442d190002c0e442d0150003001d04410f0316840c4e0303000b4400038000ca044c42160504644480d0b041c0355441d100740c640040c84482a01c4060003e0040018400d0003261500003041c482d009135000300301c071100410400410660b0f444c0b0801881d8840c589800040c1041050190000d0081c1071101600c0a05007010311102c90454136400180d4010030308200781c4001e40180203c0c00c030100d4801d8100030f194141c00b036503003400400d0302d0704100300e405554194600400c10ac034805600328141340d40807031300c0c1020a40c0c3e940c59180c4240c00341da402e0700005403892103100c10405407001e840501e40e02e5036070203030444044d02010340410343c000e954010000001d1070030040c032021 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 236913003 1250 236911753 236911781
    0xe0306040606030302010e070e01050f2b02010809340f150206010609080a021e0414060f1215060a050a06030b04050a110f0304060e070b190e0d0618020301 68
    0x4583c103501c0c0003420355244000040003940456424486403000d059290306540007a2604d030f10740308003800000d03959140d81c4c040c6000c00940c2c60024010300041409104400d0007038841294030b858416860742c3c2c9218240b035200c014a0040d008003c6040d103180340011400380f504041c100c180c5c503501c0302ea81803990b5601002842a4a1480119560b01441b01c903004080724145040e040780382200d014aca81e400f80ca0000d100709800b013400c900e0007040f00f20540c0365403c02381040110b0061004010360030326042e180240300d140140c904a8582c136200c881c0da040c00d0541c4000c0d04498410b121080d54116015045951007524480041000d44130b01c20580020501ea99000c642c0c0003101051200310741c07020f85828945401c0c04c1001030003d110f032085649100040101994035a92400e201c8010302600c0e01d60f11090165007000986050340c0e0001e40f14100c89010748070b4104081080c1924418281007045401c66408942c0d803010555035849442c0080400c04080d01c0e5440c90b1b40000d003190401601000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 236914253 1250 236913003 236913011
    0x91306200f1e0f07060506030703140a020a0503011803210903080a0b0a0303050a0c080f0c0c03060705090d082a0105010f0905101a070c06050909060418120e03060406 73
    0x1401401c1c4420501c049112101da5160603201406401c813446000406040540c85078041807564800304000002550800130b680004482d00990301c0d122407081d00281d01c60b50750008041854a4180310320359013000d00408000c0c0c2c0d04800d030f0302601c844540c142090360309001004d1000709540c0701e00a482070307244250b480841c0d03858550101011240c0c1d0742d801a001e81e890b107005000082e080012a5502c10312820940d1244080380303400d0b071040c419202492591800400c000c400c6800c0010610710968003101030396110f80d80c500f4101d81c4c41c0902d40301c0759800b8400f41c444ca000b25089000500c1c00910200941192200c1e003000030400c0c01c071102c00c03c00702e1781d990340041141d0322807c0000c01c00390001010602c40c0e400c2500c0724039001c01c41c60180c91089580c428280300c1c13400c6420304450080da40507007940d84c0143c1d40c2c030300504150014503500c0c0c0a200d428000960b1803a00b8440e031070340350840580411809042c1d8030390803d002c03244421801030140d01d00e01315540d40c3d42000000c0c41540f01d618041 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 236915503 1250 236914253 236914267
    0x807060f06120c0b0f07021503010305190b0a020307050f03130201020d140315010203090a09020403110909030703200712120e030d030b060f030a0504020f091306200f 73
    0x12040714400d900c00108a03803031188490014040d00340c050200c520b410122600c600403001c1e401c850b0f110711a4000c0d4411210021490304601810107036040300d0103141039071104168000e000c0c0d0100301d00500106052206c100041801d4020341c003030340c1c00006a10701207007040840710b440600d9500a491702d468010484400701c04540e41000490513141044c40c007034030320f158076400c020110700000e800100d8411607146c0360201a40b08105956059400030460800c10b5900c3c0400300003035000d4041601e101e00d4030080369010b03050601e112805144001c0041d07141000340d450407240701d401418242c000b840d03070307182400310007504005c1c44018028040c01c544000440e481c04640c4412420311010074466940b01209950340d01085078030454055080100d0200c00200001d1414883c040864600c05004070610280401a9001511461003030700d00003464800c1008100580108550042400804210300800541c0a4000785070660708106407001000300d41c8003049507a00300d04040140c0b81c1d0081844 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 236916753 1250 236915503 236915531
    0x91d0402030c22090219180c05041508040c17011d07030308060120070b1b06010510050d020f07060b28050103050405100c02010e0f0c09040b040f080706 67
    0x40000c484110380340f01c9550b0031031945250b4921004a41d030b0140b0350f03401031030040d516070440749a07800c05038103440b28103103032680d007901d95aa001d90400301a0629241d0fa075002c50740260110390a9948004280c148000e249000b1240b50000520881d1a0800000c00058080082141c2c1c00000b14003800450304081c0c0d081441c44001c1444400c000355400108c04102107500705801d16013118082c40c02185031800c0307290024540000c0b801e100b242e803260460000300c0c0d0080e880504900c410034841d0103060304041c03580694401c07003030059982c004110703e080705c4400c1c080c40007010002010117000d030400c03034406a04c1c041d9400408e404c0e11103c0d112907203120503203040d0259044001c00c1180c032554500c0c154000742c880c09024002d070f5062554a6011a003405001c12001c880303418800000e01c011186114002c0c0a45500e043c00745031352080c4d2a000082013404504000c1880c0b007d01030002903070f40c80d21500d84500700900259400c90300f01010f400401c2c03400b001001254050440850142603083c20 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 236918003 1250 236916753 236916763
    0xf0501051603020f040605160506040302150a0e071e03050609060f010b0f04030f0204020c1b01110706021b0604080303150901120302060a0917041e0f0303050a03020a091d040203 78
    0x1800c002c1500c10080c240c840c212610070354065410764981551114007610015183d0020640041c03d01e104560400080642c0014880496440030300400000c2d1034040740784056031403004108509400880b070030f000000c0c110f0928511044c3c210042941d10ba6241c481c18200700080d030710200290007010400c0000040040c085005009002041c2c0c903040c55424a030b001f40c001c03408000c001c510003001c3d030300c19507039503805131090b01c5001401d44000a042c0c2841c501c0300310301c030a20640482c040e41640c01d446a00841c40b1811960710343c010b0042c21800040c00c552502008090341c0e1300c92000d20010404c0c1908002039413041104554004410400c0d030100103002c01305901228203c085034000c1800240e01003100e540002445002003802042458a540030440b5620f1201071040049070008041c0e00c0c1d1201c2035151a01c205c0d2444c18680c0350740416840c06c01ea4000500458400c020300c403481842039000b001540203d00d0003031281d907100c030840904020201020f0001ca2200700500c01940f0341800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 236919253 1250 236918003 236918041
    0x30904060803070503030c070c091107210c0209060604030804060909180c050d050106030639020a080a032a03050f060f040e0a0203010e030403030206070e0109031401090f050105 78
    0x46040900f6661502d03602c0c84010107035000c440c40480d400d0b04000c0c0d807500390000740ca000c031018013855100e04510380f0035401c6a042600e02041518505c5a09100c40480b2101d5158550740d221170070075aa024840603510182a03942c1104040100101244480e4050302c094203039540c410301a90b250500075020340d40420347c540300c080410604000080c1c2d10100f130504440c402d0702d1144c00700313140341401801800c15910141006080211410441003c018800308010498200803803c40c00c00b001080c1400b803507031f403600c0903034414500d82000c0b444141c00b0301910700c0645000300f121034141c0540348010660580c02000b042e0048814115245c05000d40ba900c503504140c40800c40c500400002c440c10b102003451400f4035580c0e0714001044d642485040c14079030f0040c00a201c510515020320343d03607a0151009400500070301d0089100d03e4855000d000e0000e0050359408450fa06607243c2100401c17480404c14904d40d0b0340d403c8103000030805002045054054400020640390061501c01c842c0d01d030700 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 236920503 1250 236919253 236919269
    0xa05100507050307030f0b0414010504060801020c060606090a0317090411030f07030b03070e040c030c05100f0e1f02010603111c06051e040c032009040210051b03090406 74
    0x40d0400058591090075258007048924010500c030f10103d8481004003482902560400d0074140710319841042200c02c0c40c100c690a5408000b0241e441605900703c0c002c076016603032142c02c190003045240c078013040500f001d40d000030a801985696607580e61080f403c4280c1c101400d4001240c00030079880c0070b201c0c08004002d0348824a01e51320384034511003185080180101d09250381c2e600c0e0003005072030410812014080c2d01c1914070b5941001e0910142d10a454401120308258440000c1454141500305a5200001e0b0312040041c0c1030344141903c00694035113401e078209059402511084a250031062054203a5800000d070441c1036042605a129407003440a0155845480b42c5100602c00d100400750150028400076031529000171040d102d50719401a12804c00c100400e01c020f000302c00b44180c0031244a9004461076492640e42000c0c2003d04c1456a50f000c05180000340241c2449900d58000d8242c034a0114902815014600c03010403084201d90901d03800400c281c0420700b01417003003c0241083c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 236921753 1250 236920503 236920511
    0xa03020d0801121202071d0916120f08130314060a1506050d020c0319020606030a1a07140a0905041d030708130f06080901050708061e010c0501020c0a0510 68
    0x2182d640d00300400441030013001411002d0001a42038800d0062102500d050180d20024a222103922001500b050320001d502d8080c4902111303082031110000d2084407040c40f0660400d0007651030746c0850180201c42134a541000f0403d404001080440c4d1601561060308000820881004164030f4400000d00e504401c40c5400c0c482070060185206aa04940c000e02c1c10076a0380b41000f80703032000b1340600c50720046c0a21001c280d5006da101c04c0b0400b08640314071603007146e0300f030354500b4105559401c0c24180500715484264008404049503025660b220507030b8104108102d8803040407a200e40c0c004440303640056003d41040c005441d05004440d0520680c0f05c0b0012400b1180240395220301c10301c003000f480c526000070030724021100f85640340014001295040865070355900c0141044c44119050003855181200145000b8001c5403142d0040102030702e500505c1d040001c1102c400042025841d06110740080303c14000f450034001050b05031415401f03041e09548a1501c5072a200aa02545003201d0070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 236923003 1250 236921753 236921759
    0x213091802011d030106030b180f010c08070c110a141002010506130b12030309011b0305040312050705040f0f03030f0f080610050d0e010c0909060612020d0608030a020a03020d0801 79
    0x400983e01803240d018211205442003c1c40000c1d0041002c0d0348018224a5100700300061070400c038000504151006040e2040c3c0407001707040900305e44481410401040b81c01c5c02250300360303100301008081030707100c0c1800340302c3c4603003102c00281040c5240c2d11806c0070006d11034491590707007084001000c0c5100c2a000900c19402c2010000e290801c15054a00c4082e60300c08204c00306075502c44800c15503807102d8082c4c070758904182000314040c4c60400c0c0e000303c00f82034181c07e640c1c2440c403030300c5040d200e5a05079468502c040d0000c41c8400107060007901c50300c1046000e02020401c41c501c0c1044500401c2201c90381390000d865454050000400d407030003001840102040410ba03160030102455010390f08031000c91240306440c800755507a0003404281d8600d24544148614801c6c01588030b107030980d50f07940300c0c40d006a694074459025a4040d0060500040030700003160000d1850750040d0040e0205604c0218409454610046c5075030841440000180d007c0941201455014803c0c0403000d0080c2c07511408543c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 236924253 1250 236923003 236923007
    0x18020307120209240a030b061c030e04050406110c0f07051503010e0915042f010507060b040b060705060a23040201050d09050715120e060c0a020c0301021309180201 72
    0x180101300028074900e2680149456200540c0c0c040c1d2690700808080c00692a400d243c4829030046a03858044c81340396121802c2c1c094100b610080665040d591450780e80c10700010b04c80070b0100940700f25480d58865502c080c00e0042c440280150b21940f5004013180c200c001c21700b902e403c44a500c180d00a030501e01e0400e0307103030000d001160b05440100d89a09560303202e0000c61440c08034045401e05000801c9024082045803c005014080007a07044402c540ca60352220141c1c40d400c050f035002c0c0801c4041000c0800945d07150001c25580000400000e80c80c1101004501c06620224041745c0c00e4200e0010845422000d11808180c4010b81d194200b080441c0c1181c0d090262010744003905200c0080354001c0d030000c03d074001032441d80d440700c1034070103159031090440f0b03403501d06007040c80104031140340d4802c845009100c0c00c0300121014008150942301c00c007c0940c10b40c00154001d045004d070440c0d80c016070314240014007840940c00c283e80740c079620b070144800458980c4072004a00700148109000941e03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 236925503 1250 236924253 236924269
    0x1617030f0c0309060409020c010b1e010c020102010b06070b040c08031e1c0f1a040b06030112080424030b0111070510030e06041401050f011a07080409180203071202 72
    0x161804040036914041c10440c5880d500030700154035488a00064045a4800e003600500320740580071000307000c01d40e078030400c000b6100f243c40384800031240120040d0340a903108003c2511aa40180000510180300501044141e480b03000d05130b45003024141030000b001240c4803200000c00403200074504102d80e6600790b01d03401c1c1d9199062640d04801248041e0b2214011501c0b024a42c9a140e08200c11500f4105080107088500081105050030540d50a49801c0c5030083d98102e060080c0300c94070b50b80c01c1c800c00d000b0050f140c40b0161060030f024800842c0f8042201140340c00c0200d0741250080080b060600103040d6031201c400c5604200e0340e40e5084030300c17050000c0c0780010745000300c50703074401040400e4088000f080d80a1420380d4520070300003488103004904030142004100000240281e07079034032203419205c0702c00303209241d1a0108202c0521408500c0d5001c0e2110f00c1c42446c0041c50a99541607010540f60584110800c1400c181042021894104001801806088000c002c80b007255000076501c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 236926753 1250 236925503 236925517
    0x15010f0c0f031d030d030b04060b0928120311011803020a030f030b061b16030507090515060304030807090e0121050a0204050702070315050c0307050c0106080708161703 74
    0xc801d00e03044500b0076085060001d03d44140c0a412100b104d601040c004000d84010800940185e00e480804603880c02c01c00211944008060805102c00c15001400c44610344900ea02040706003c0201c0418034502c909140410640a030303039078128070499002c2c0d8900715417400e010310752241d142c403510000280d0003188140c0ca082c1c15051400d042242101d00b030340513050760003440f0743c403420014400e0420040d40c0d14144038001060110740e0a0182641c2205100c0c10600003e007241e40078030b00402160707103da0820741c5d0003500c0088210700d40640b14081509504152002c60111b1b84200c00c01c00034030780c0447c3e10340003030400404140c140e501d00752180041e5541c91940720810596011104280030003000b0405025901030400c003c203107490702c002504d8024601040f101504a0480111a07094a02600380518103410541d841c1d43c95800e4160744540c00f4101d08a80c0c0e540302c40000881410a000350b01c010725098014042c1c2142450040441c5c2400d50001c9600180c0c81001d101980000410313103045e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 236928003 1250 236926753 236926757
    0x1060f0e120706050703080c09010207050603130c1d090d0f030902120708150115051603110601060905040c0302031005010806030a0804091506020c100503060604090515010f0c0f03 79
    0x4000103404200742222408040c181c0d44a1510001041a4010020310005000c3da0343c0c050f43d5140c59408054a03c80c464031640141c1c8240c038280070b6460036400a640202240d200072004071010382c1d8440b400c03046a40032030b541c00070240d601d20403041400d146590200e1418050b0800d9060800042e08002c10031030180e0070141c3d150801002c6445601015110b40d00c144103c070300f4981d0b01c600c455030f141206800c1000103560b000000a220040042a9080c1010381e140c59090814620b070740c640354030b5104800c1d4100000c050015002690a010140c0600718607618028110b0810081c8010740c2c00200012080510400400651111140186080d180240380202541d00c1c0e000000e482c01d0400a8082c00b50040054002001c01071030307010283c0c659031130540c0d009448c5c0d01c1c0350503600c49440c46c0050b900111810300c940f402900c200000d40d4000c134005c4ca01d40c203007510f4001d42070407600d0489030003c40d2000301c115002c084d80c21140c0401c80710010f20b084646101241da5100c1503010b54640101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 236929253 1250 236928003 236928017
    0xa022505222406080423031e07060b010206010b030c181201090c05060711040b180906010305060a0e0d0305040c1e0f150f0305070201062c0702030c071211030d1106010e01060f 77
    0x17443c42441240c02001d0208d41000e2400302085400110b5400041c08841451400d641440207500214031103049071000750001c0e0441c1d880400d9581c07207030f11070075901240303c500c507912004c140e441c4007060304084001d400004480c5035610389600302820b160403c2e8401c039030622442c000103025041c0000200d4003a14080340030031180d40440c0d2541220b12a043d140d5200000b00282403c001a0150481c2d0042040b0703802611a071078145c04a0f001551020055003000003842111402604060b8001e0300c07540c1e40d448620ba40701402ca148003d484004003010b4041e44040102d050146d0a100181241e1942200d00002a1034050150b5240741040c400741621540001c01041c002e50001d4001c2c403000c40e9180e500342c080103050a440c440d441c40da8942c01c40840200300044e01c0001a10b20500084c4000d2240b035080c242c0100c908000104229642c419010410219480c203004200220801c0d4945151400d180c0b0101400c1a00c140c225070221504240104216940440b01204403006810011 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 236930503 1250 236929253 236929313
    0x7060b030312010312120902060306040e0a0b010603141012020d11300d09170703052b080702071a07050d050a0225052224060804 57
    0xa03055000d540d66401c00b5054034400002404000b84207141c1e084400d40c1c455005404030b1509001700e84549002a400c80d5042c40003a0445c2495400303600c902d43d4600446e142c034081552981020482604407100081c1c5a08501414001d164485030300f1200b01202c2c2c3d502036050501140d055040c8000107031041625858134018003a952365001c90041015224640f0b00c1a80d40410010100a6421040a0000301c4460303500401c040f0744c0184030240e0359114400a490900c00c2d4100c0342c48a0040c003083d01070040008005042004201d10f84d150015055100c03002c2c00b105454941d541d00341502c10f00c603100d010420640e502148080660701d06260150200e601b0401e10b00c00c5014408004149204e90600303484041e4200b4042c2111940075402c40f241c0d0384010284000e045044040360f03e402d44514414000da01e82200119414200c42c1000c08001198030a01b8081d5100b014030b0141144401d20820f9486c84035198200203841a802d1203030090410b942c4d60607400407006111600c60003428a80 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 236931753 1250 236930503 236930509
    0x50909040308100b0f180607020d2a140108010605070507060503070302070b0702060414010908070b06121203010816060c02190906030b06040b100203340317180307060b 74
    0x40f501814003c0c0c2419102c10b400412440d9562040511600083d002c03003508056251182c1142d0820381d0203411010b8181c0c0e20394920124400707401c00c10140001d5401085403944207541c072000202980c00d444c2c00319080c070800260074401c0c1078105c4800c10004003d400d010460001d00d2808131030303141ca041c503544d56030040120024090b410004210034a203605002c10300341d0014006020702c0c05454811207c5501041660803100146001040004248030f0480420350504283d0b9200d00060808040c014403000e290341020500d01340042c850130044014082e02c4410403c1044022034000500102d03420200090440580d0100007031107094094031010764005880c0390b000c010b2520007020700801e0380b6072801980041c800c03940540503600c0d2007201c00340f903d4105c13614419007126401543ca0b1440c0405210903c1c203150f400302c4242c50071071a181016411084000c0400c60183d1340315408500b0200900008040240c90600e680001c42402104104003104682e01107901c0100010820145008 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 236933003 1250 236931753 236931781
    0xc03070c03021501080d0305010801020a020a03030906061a07110405071e0c140f0f030702060304030c0501090b0c091002010b0303193e03030709031e021002010c0f050909040308 78
    0xb43d800c1200190000501914001390b401040540d41d2000e204503030702c8110303440c200e0055003a60310040c1c0c040740e40d980101b8082e61250070035600960303011400907103ca51075400603950140e010301c01d490008141081c816440007041c0c0e0168225410703c01403c0090004000c00e00c0c4243c80d036204030280390100d05140c0101990410300d9405071560409070300441d1015140c040320a18020180202c0380300890685000c812a10b56540c010122800d40c1c8458804842d0711019100465240d940c800d03501c8003142d823820030305205015003040240c2d90f18600c401e00000c9041e1000c84820341e030521980401c04e40d008000e4032004030b800881802101300955081762100104060b11050304400f10202c43e0040b402c0c1446500000030062400c440902110440e90b217120480f25100021102901400000c451440f40d155054050624031818402600010140d00c03054160b140940e540710140c9003072a4010007800084103ca041a40c184603c042c0070420402005100034100f00c02d580c00104ca0000d07a43c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 236934253 1250 236933003 236933023
    0x307050906090904050d090f0305030a08270607120b0102100b0d0609050f06010b0301060c020d0213140f10082d030a1107050a06120911060f040302040c0201050c03070c0302 76
    0x20140f01400e103800c1841d101c18070b242d489800610480700100e1040b8050707001b20100c82d030240045213080d00000c0111a8288050a41554184020b0345004190701c0400c2610280080c00302900d01070820f008050065600100a040c003942005c8402441c0d80e008900c1d00700c1c0d100b40ca03d0101c0d81d41d40140000e0000d1180340d000420051400c1e185030305001002503510960301850080744e0242e40c9801080700207010034820400022111402e000050a2900050b05d14620203044180c85042a0441c4e00940c0c0340d50840c0001020010100a250940d0403151904240b1001010201c079060004032500c4842c01c1c01c4112140f052450408010016080c03c40b003281d19140549450700c6812000401080000d6201000d42c45840404505440d040300d04000b15501da4130f500409146104803140030b400c1c2c204042c1e952058035142c01c1c080351505030050541c03201c240f0007603550f00e04600c104400c071111041000d0171a17140c401080101c14050040320b030400d031039081c00c07100102c25180892030310034480 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 236935503 1250 236934253 236934259
    0x70f150e19080a11040504021005160b0703091506050a0506210c0705060105030c010e120c060409060608090729091302031503120d0e071e030203060a0908030705090609 74
    0x2030700002e00c0c11400304422401e18031076511800950515001c02040d150181c502a6003c041d00801c5103c00b4002d02c001c28041c0c2140050307001c40240c031348071009040021500030b030100f0307201c1124001300320002458072071541104100304019400c00001ca15403403505d0003000c0c080d400c002212480024401e0b10030503100c40d09030325268289807070301d500200c0c1d40211500303c0f41351003804000700d0b851501040100e01074006039101c21002e0741448c03c02c01d2613000710401003594001c3c131380110700380c1e250700c40100040c0c0203402c40402c900e440c0c80e40c01880c05800915402183d00007500034442008101120a0010803840381072008400c8110001502c1c49031880c10380d4000303040381504060311145e0b0041c2d0b03ca8020600c0d0218412000f009250700c581100000b0081c5040030403110414226540c81149032903030840842d0f05c2c054845070390907143c0801d105074490759650f4400070000c520b41001016403107076240100740000525603495a19901001e0058801d0110115801c5140d4a90506864080e0030003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 236936753 1250 236935503 236935549
    0x1003021905090111010c140d020702040c05031006021f11040b040f03060501050f01020606211203160513050108040602070b1807050105072f030703050f070f150e 71
    0x3000903000c0d51141c84024081424182c10310101c3c3d8061003480410501d54403408880000b1141c0109180d200e40c504a00955080c4650303c056203481c031904064030200e495a0381c5d20700741070151012400c8142d10080856110145080d4008540c608402032407640c00e04c0030650781d111038118500b5020702d0b00204102c1c4000308002404005003181c1c2d00840f4000c6604200990300c5d0001d22101e550141d0100e07002d0b9201c40082011800c14094103c00410096290b40040348800c10702400c2a05415910700c0011010081c003040a42560046283c0035080c100985410001c40303006c0005141c9204440c14081090001814231542e80c0458802d036600044441030782c981603c422150313501c0c201d42022144100b210200d101d5000c1d40459504540094003d10380788000750122484000304100024800704c4180d001200392420070550000c2c5200300040c040020403110030a282840355408206c55442e004002c0040050f07014038041140814900059107000c650042040301182c06a903d0120741c1c8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 236938003 1250 236936753 236936797
    0x11e0513050c060702010c14010605010e0114090111100207030201020304060c0309020102060103060e0313080307050601081f021803031b2806200414040f050606040e041a0a1e0c0905100302 83
    0x12b6010b00309560f000d0f00c864080d0110400115a40c0580d00d817143d400e8441000304892642c0614944d60500c0340100071211090181641c02c42642c01ca00c4c5d0131400760b9000b000384020480ea50043c41c24800e4189000c02c443c140c2034000070750b6400c061102070f01450750761040f00d060040510454481405a807100e100341a034a56100e43d41c0e45c03102c5c01c1511203006030400444c0e08040464440c240348141c11541c900d0010468030407000f5404050b410b000300e181c81000140e9520188060054403045000305500051702c40c4140e800d110100301000065695070b00e041003042e42000601000c10b42050000804070305040c007002c4020071035418052521f6012030700144605040200982c428402d0320180020082c150191040d10821740c0c459a1040041c0814000080b440e0003e03988940200c06c6c0c0c1c6c250b1503000394203442000c015141125000d44452805959040590a06012150003141000f0941701c1040c020914134850150302d00c2034200580c9415958802c4d0161600030a901c0d50081c00c3c454 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 236939253 1250 236938003 236938043
    0x50d0b0a03210e09070e010e09010f030b160507030507031b15060506040312080c0d050906010f0e070905152a010b10091202040e011e0513050c060702010c 68
    0x14240c036004aa100e24040b2510950388901c0c00240d002c0d8001d88118195180d60300e0603107001000b200a54100414105002d1880d598800440c0c02004000750681c9001d08600f40504040c2c4010b01301c00c1440b001d02a12205264000100c0300d1a980500d0700d55111401c40c80c04941c0040101d000d0440d10801037288070500129029040c0042c010074010021180d80e48184034590080f0700c005441d82c0c1840300c81c8000580038a03200c80d48981d10100103072400e0300e00c401600850310141d4010750151f11010040c0174046141c003c0802034008800c2030a4545800c0744d009250321030500903d4005e13080d01031140010403981c401d5800081c410a000e64600046402000345400583d6440f0b1640d82444950a8a814903403403602c08100300da920390203240c0c1030503040b454912032800d04a8000d0750340c0e41340f1039801c0310a1081c40c06041425020075500900c0580000035140054460241c03031005181c01c0340000d5000030701d005244400e450850311080d450005075191010342002070419091207010000e103038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 236940503 1250 236939253 236939273
    0x3006060301050a0b0102030304121b050703120c02090612071a0904140123150403080a1403011203030905010f05090a150203070504091a100504090e0f03070201050d0b0a03 75
    0x50040c0c00800156072291000d505643c2c114003400d0268008201081c042403505500c1c810001c440d05207144a5184c00d41d0b5204440029002600c00760017015081c020454001030705070201a0f03501e4100210b04036a0005460208060401849a000000c086c400c407281404060000c01464519500f407038250034080c01c540e400242d48510582c0b03441491031040750f05d48201816540300c1084048529039003035440f00c2da000b00c00c00d0150711080d2580a20071801500000344042c511581b2500e4a0340903050300600440e1b5200c0a0200b440003e10040c030061030aa070a8619080d0185008603004100b400d0541c01400d42902c55582d040c00c1408100d402d0308001410380040e4803401035800d07100c10228000c0200e010948110001403010001041142e003540c016400c0c6404c810810310003003032400006940760209480520100b1070104042000369401e100d8000ca14641c0740161007440e0320042c10584034421020003c0c1031002c0450000541e84090348918000034000e006098031a441c3e04103501c02d2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 236941753 1250 236940503 236940511
    0x9080a0306051504140d0f0506070908010b1212070c120803011503021206090603100c110c030c0d1e0b0405010504021c03020d0e01050d06090506150313023006 70
    0x902281001d0119190f014401c45084a0a11000103244a81031082201c1090107040039034000c10328040c400b02050083c440076006444a444140e02c2c1890b00c0840c60030368a940038514881c8044100014040102045e070402400070003a4031a070b9900c0070318000440e00e505400001c014a440c43c1c0ea44100051100190f05a503410400a455030b821003004a003a48034641f030954600311000c0109047d0300300540625082100101611000e01c0e1070600402120100e42d0003000181c580013a42c00c1041050203480182a4180c0145c8107041030240070031018400c1c40d83c01041c0081244e199117000315814080b070a903503400402100c03d42820705055020349001d035001d0f841340c045403031b540c8500c076088008200044d90603006001c105980090603144410720602d1541803200030000c6501d0a2082d11130175020302001c0c2c0e0000340034105101400b5520b1800060b600100a0400a020070f01d15442c90800c605030341111150100c55500040030f9261901200309000c040044200144e4480b01088082c86 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 236943003 1250 236941753 236941759
    0x30c070c050a18020702010309061a040b0105040b0711010207030c0f0306140405100f020c070303080f090d02032b0609020a0e030303150402030402040b19090e01140106030c0309080a030605 83
    0x1000c0e01c44040002288880c8220308580000c0c1e0900d4600f11225001380041900504000541640b241c4490050343c0101e000b4034003032180111b0002c0c5500d0b00b482080304104007031a001f1f040c141400c107031076818450894090b00c14001000c002801d42c1c42042044040c59004401070f483c290340e52808c050f6948180421142c803401c20f42e0840c0111150880703d8819500480200340044130f203692040102400c403402e440c140d40030400f10100c0320080040000a62095844100524001030080043d0388068590450fa030029800020701c20b50010a48205442c0d03031301c00d030541d16103401c3c81041002030400c2e840610380c00c0c030350300080340c00c0706901070150f418158503800d41040344841056180d02c001c668200300f480f0a81c024000c1810325502940d44248050000100e003803401000070465400d1507504d0101c130384e5105d410700143c8140d00071150154030302d00c0207008241ca0102c1c085110941405040200f40c3c0d10000d00301507600c01c0d00040c1c44650401407056540c3e000d4075000380030f800203004482c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 236944253 1250 236943003 236943023
    0xd080106030920010306032306060d0206091c050d05030603100b03030a18240210020702030a0209070513091b0804020609040e0f03040603050f090c03070302120111030c07 75
    0x20300314003034025885015400102e00c844050710100354403d10056028850405035150404000620a030100c0220030340d060518038801c019441d410b0345032240091026009200c401c440e80b0040c0c503800141d403c12003044401d94440d284803400103001ca40550710140081c42580090b000d9030b40c000c001175016410170740c01c1d14505500ea0320920180c0304006421901940f040140012881c4144010000000d80240f18225280d4412443d100754900c51042d242441500044802c41034040021500700303030326143d05500b0001c00e80c0000e5141c60030307410003a018251000c005200709226004440001c15460080e44606849049102c0102020950b82801403c00c0c1d60b1080e11a000796100352280e030740103150b2464a003100c1d003808040e004c2d540c2482064440c0003409500e401003840034001400d0301c2e96002a4518114951420200015240e00842d400503502c01c1501d48010841100350394065401c06d950020840d0800c0c0105040800483d010340c0200501c80d44510304002012000e010f5200340c8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 236945503 1250 236944253 236944259
    0x1302011103070309031101020a051609151802030402120105070815010c0503030a02090a0e0112020f060901050703180f030b0f15010f03090609020409030e0301060e091207230d0801 79
    0x9a03680310310741000d008250008400c0000440400d51b0010500c018030545001e02d409699543c07808442d0b000340840300361001c1041c0310f80b1803603215110b0403201c0d0313528031008a403908104142c0c0941c0340440d24201500000041c06640320304561603c0510060020492454681c2005200130380560f09105034102c1c000c0c600c0102d42c45005030815154002000d0b51940c0c603001000802980003440940d04a0341e2284002a040340340101d1600070000c01d095030405010503c100528141c2e0454020b108003000c0c02002c0151b41d03c0000e54145680c141442c1d4002d51880c02160210003680c1e002804208003500044104010404424011205468480800d480300f1001140180340d0100781070000e03600820540f10988250089103813640038160010f90817069070046400e40c0d80040041d00810409010b490140c1401d1007540d0041640e5000d640c06030620030001a241c020134224000c22031401308a083c03e01020710041c0e031140881046121405180f6036010392540a4500703e0340c0031400f440000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 236946753 1250 236945503 236945537
    0x3070c0e090f030a0e090405120f0309010e1b060a140a020706020c040204150513030c09051602060601140912030d0b0a080610090c170405071e030b0c03041505130201 73
    0x1513040c00b2859264400308640000500c5003411008200b5102445503805100b1015005c0c001081120f0080f403040d5502c0c60315401003400d4440c034440d0361100754001d05010850700000000c00e90300c5602103c069640d40c400080848501c6822081d012402c2030020b002c4004603000034440084071815026200001d00c00c2e000c1000704c1c060362041d6505811801505110684180010110320301d03150490310245850b915001c3d03e01400381c0000406995613001d201009014141c1084030515a200609962a003c0c0c00200342000e007100c185120040855020540e9450781080c00203004810708581d11a50400702620140c4584006c036409012000c07400704030002d011810520800550340340d0325510f85003072a814000d09402924400b0408000031503003a000c510460b050049000d1402007560900300b14001201100304440070030084a03160041000411218034554844201c80c803940d22581c807828070074840414003020404940c07900c800c0004c1040c00701e40042041c1d0003070313031042094000b813408 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 236948003 1250 236946753 236946757
    0x605010c080a03090305160501061a0310060518060f09090f010b0909040303020702100207090c0e0f130902030607110705090c030a1d101d06060d0f02010203070c0e090f03 75
    0x207040c2000c00c01441c4440c0340250008807078544280340007841d10540380840c4c52103605488007100c50365116803041103590340c0d400c4004c0704111076000301851400c2248003080e0301900d500c07070001404000b1030602c811070124000800b403100c000c0d0009540d11103041d0501203990000300590b11513034041c0003140c02065114070890580d2a0800c0d1586011001401c020102100800c22810181c003041078100580360760402c0c540b055125001841d10a0801000c0741c113036804603903850204030a145200c54960740e03035210520009416a00c200325051444a81d002421081c80065058419082400b0100341e220b0265982c10074001c0603914072603115400c02c00d10401c180c039100341781c0b11f05101089a0281660240b11801c0500b40a8584601503240c01ea0a01c0301003d07114400030f648034210420041d03140d82c01c0c905680a94064a110318002d0700103124055291006450005e4408224045900800c1110f00048c0c2003165900d200d9034601d10411072000444504103223005411a0000710900001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 236949253 1250 236948003 236948027
    0x3120e0c0108040b06041104030f050c0613060c050709020a20030a0c02040e0c04050c0901030506090c0a080a0209131d0c01080c0d020d05040803010305071410080a02090a0803090301060501 83
    0x5281031190f155920386808242d0084c013140d9000355920600c0440e46048401400118825003074540700c1c1981d4108a410308124800c0103000348410044403007034010414051080c0e8105050041c0401010705100d442c011003500b00c0e030b0395980300041e040d61003504510781c24074507440020702c039a45401158086031a401100700314030115010340c0700500145015000744000e20b80a8040b00d08001d204000202503d03000d4a0032040ea090010b83d01100d940d00d800742e2039018406032807215250428046031926132044601080400c10400d000c115000c3d03468045800399200200f003d03d20001001d0301c83c00926104003241080004001c10008a101c080386984964405031100503060303480324400211907010450742d41c5216420028020010900e120391800342e405507045a880758110304d40760340352842c0c03900b04807000c400d0204158101d558002030180c4408030b92401c7c41035920303901d90500181c0202c21560344c1c0b011204070041400c08001014200b403841c101d00a00204c1c0d9250015224560095 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 236950503 1250 236949253 236949257
    0x4060b1311090f010309050d121508070608060a03121814030a0201030c0203071e0501060b030108061f0503060a0905011808190c0c140103050a0506030c090601020304090903120e0c01 80
    0x20020038020303d8109080784140a040c100800e00d03280940c0e819040c03600d0074104030003185840200702e02c00b68942c03041c001056a40806c0b42c51039400c207e0b50903030710101c5224641c200980c120010f00640c440c0d1809000031640080d004c040039035001c1d40038294501d407040500b205261307030400140303074680c41c2d80084280300d028000d0030b403250301038004401600d580303040c142c19840b00700501d0001488410100400b40362081580011a00d540340241c2900d850b6805140b00810610050080e400e020500381d4102e460580701089500d51004502c441148039801617506000d00020881e030203010340c100400d12032041c0002c000540c1e500c0030f8001d03040e0714060040c0030b803081402615200c6496004c8903c0050450520040027203c41d945d40c01c411510b9041007540d9240940c1c01d4995507014040d503900030000300380174481450701c2070100381d0b6104141e0a0503c115840404140240d00a000b00c0d0040e21080b0010701440e0a981000303441d1105039001d04c483c03145400070080800030b001c035070612007590503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 236951753 1250 236950503 236950507
    0x41509030b06010c14030a020106180608060f04021908030d05071e0c06140403020f100501050616031403130c0806061008070302160308070314010806070507140604060b1311 76
    0x100340111500441008101c1d58000740a80c0600c2c40c0d1170410250254010650020440c03030b0410020300b0390211040c5404480c941000ea050060b9040803400c9130b4807071501003c682556455000207030390178044504806101c262000003290400001c00100a01400600148803d441d1100c0444010313a405075242e00e42040d031881891070510582d50106c100e4014038011034441c610000c200c1085e0000d07501200568420314203480c00800c04c0c04254004e4600c11010030040d894000801d51a20421031400c0d40c5204942c1c2e120105400740e104800e64005801e001a103030b140c1500d5080c000c2040810540b008000c074840058000c50000303403c2d03c1018040c2002c140008003e90607200c000d0b0152400060540034440101e8240e84018446452406550703030b1040e5080c40d0a01404880841c4a43c0c8415486d0301c1c010b100b6080009101a0000014508580d030703a811070030300b03038521121220540f015006a9040c4004d100c540e07001002c90100894407a80c20100014041c0d04542c0354092404c1d030b407402 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 236953003 1250 236951753 236951761
    0x501020d1805030f06040c142202210117010b060901200d08011706040c0303111f02030402120d0207120c050907030e010e03070b0a0c050c06040602041509030b 70
    0xc24030030600341a2090701400c05840e00d400019041100300d45521000d948408200810310a1818200e801012000402d50f0f40407003190100e0540038039a20042030004130304141c11a80e2400d81c2c12217820005610f500c2009400800f2440d0b40304100b841040c95082e80000040b004400c1032040800c0040024031540c540740400c001524085001091209a40c001040c4125a06004d203c6440401c2e04c0d6a00c824043d810100d4512aa1480161420349276100504000000b600300030003070156909801c01032041043d1020395450080701340030022072110a0008810100c4480c0c01440c050f41c403c9401c0d00030980000109540d4803060002480183d00c8414100428010440b001c03920031700400505524a45403c0070600c00841903500b4400a55101c000c420004000e01c50240800c0080c1c0283d8a000c01c00c3e2609601c0320300140601140f80d03034445080e400ac03400b840889a00e02100f10683e41c051801e42042c00080d000b901c54418402d2008100411080c440d0104030103481c0d2188110170b460711 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 236954253 1250 236953003 236953007
    0x3070b09090a020c07090207032303040f060e012a05031909050a0605090a03080c1c0b030102070c0803040303080601030b09040b0702122b090b1617010902031f0501020d 74
    0x1000d80b2001c4115030812103640102824068000503001184025940303d040389401800c0e80c54407214004000907225414101d034001c4811280c2064000f8012040c1e10043d041c030000800c00608121701941c0b0302000710000104030340b020070303030800380680d0100c80c4011020161814402180d42ca90314195441c030510160301182c0c0070700440c0f8003034030840d200c00e03000c0c3c0d1b03403101118410385d0b1100f059070200c8034690406a20203003040d48000014a11410a8201e40702c1405195201603040c007100c2d01e9860309019910254140c030382282e08503c5268041c0c3e40c2d40303600f0f41c69600ca40016000144080009050395010b4060030002040250180c2c649541d59100ea4461300005059502180140031107811903404100107441400710391010304c403a40241d402c1d20f610f032403001041c08030680e0822090740041001d040c0350381c6e0300283c80c81c13141302120b940c2e5000b00c81d11030440104013400305101001245070140e0354040c5114048106001075002e58001070589110307094444d09005a0181411414840c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 236955503 1250 236954253 236954269
    0x1e27160210060306060513361a0f070306050f10180e01061209051b030a080301060e1002160b1806040803031b0a0905190b1204050c03070b09 62
    0x50203105031055480001ca60000361030140d070058426985509051055140c000b800404101c000d5004011a040c1c04c50310b0600111816594000043c2442001680c00500e0301c80303251059101c00d200e100e11a0b4410050201c0c1001d5501c040358016200000d0580350003413185400b80c400c02004400071704a00d500700715a07002441400b50401c0300a001d40340c280c10307031260548042c081ca602000700070b604010008094080c43c19a003201c5030304168010011501c0800e0005541460140c40c1c1070002c0b6010200385444402400203082c50800400083e4981d40b012402d86e084000b2183c4070a07461800d601240d0340c1e100b000079412080d003a100104403010b001e800034110074150107a03070711455600741d001500729049a0320600b01600000100310b000c41c2032680030b4106940340c2c00444c4c1481411100249007510034080e079401907100c0070590180504072101140148101007120360740d880c0c1040c8140000c8000d4804544611030130080300524900030500741c05451170407488600b04135011040088030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 236956753 1250 236955503 236955541
    0x917100911060a0914040b0d0209040614070c0302070b040602060f090c04090c0801050a021201090c03020d06031a0703050115080402061306021f09030909050405010b1e27 75
    0x8100c4101c0c032003107140c0300c40016208000e22030311008280c9241808682e0003031510700720203201c2ca283c2030385146540c0d0b0708444070b002d01e07405031602a1103554a00c0c0900c0140840d50303106d81d0f036004400400610907401564184814403a60a5811841d61141d1445041c0118001c0c3d001503004480002e002004040031950700585901c02c40c0c920b808090049011940586815901006114014404d10340240503840d00841c2110046103045c6128080c006200010b020f0110426100d0300e5001200744241c05403114110315a40c100901c6a0740d00c2d1207180d00541590f0003444010180002c0c0d03c1d58080e09c2034904a0f0110100f880754200380b002c1c00c039648140140201e07030102e0f050004032030700002e07170102c1405480360340c00409a81240c1c40c001001c6600480020380c4440c288900c020010341d01100324002c0310389c0001e0200ba191030761716103540034180c1001c4042c0c100e9490940840119803051046100900a4403d440301e80d81e8210201058040c1c400c0112001c0440c2c00821060000070a01081d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 236958003 1250 236956753 236956763
    0x301030b0a020705010621050c100225090f060e0604050402090a0e1203010f210203030d050c070609060b01031118100903050102030c04030c05120a110d050a1209171009 74
    0x90305445081c800881d204100d0a841f0341d64200006004214080001013000355040f03c2d20280c408030940e0095481c0d01d0302c1d1b06a4544030b100e6801103142e18074070300712101508002c04140305840003038810300c3c010f004034030a0410081c0d05502007881414140b0031a4080d5402500310b0aa40d692450900c01400d9405060426403140c441032060710300205000c0e6004e0200741d0300165849251615401c4003030352748020146501d51048a180040c3e600100b10341e00d01c0d00103240462941d5540c0000b11242c055184080d18590400c850b00c410040982e0010501e45003d803010000240003120001082c06440040c900c2110718004101462414100c102c0c041002854428200c0d41c40b41c2e1814203a030829583c103032580c0c4010a060003001803940010001c2c1006072800060362440450f100d90b82c1a402c407001d00140004203184030240c0769050384000c020307007000c102e60100c402440c009038a07039520110040016000d010104441590801143c54165440014500481c0e44030b00c11000b00305408003126 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 236959253 1250 236958003 236958011
    0x302090f0913020d0b01030201020705060c150a0e1506190308030a0911120601080601091a01080703060f08030306040f0b01020d0e2b03030509061b1803010203010b031008030301030b0a02070501 85
    0x40140c0d138405201da019441401290032551452001a10700300c12504244e10805050105152a0800103110402d04c546503490580f20348601d6000c0004000d11405511140100a000c43e003090302c2c0564180980130580d51b16540c000c185c2c0c207140c00e4000780e01005100d0321041002c1128103845801c04094280103c0e2558000741c118400034a00300e240100040441e000140100308041c020f200383d6004280c91901800700705100880d0080d5046100741481c1405201000705403030134403d134000406400010640c81d11192540c2d892540c80d041102ca0f24420f80c1856001703a0004524083c1560400c0103800900313280c1c007a481d0607143c00317440340c20003604074030464040b4010b40341502040700317a08e02242040d002c3c081d50303040c010140c80004165844691061083c00210403d42d00070f5103100d99070f441c1041e140e98400070714000c1c105511180c00c0d0b06600100001c10032054640045002e0420b04151044d0940d41d50308241d01d0b07000c2444003410b03010b82440055004d0049400814425105600000d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 236960503 1250 236959253 236959291
    0xc08070f0203121e0907181a010305040309030503030a0b04050901091101051b010615081302011d060708040e0601121803050304020607140d02011401080705220c020109120302090f09 80
    0x800e909000b20b80e1450070307500081b000c000341141080c1e482104950300d10305001c1e51810905070301c598138210300a00d04159807000010241440340000c403000e141d111b41602d5481c20800c09080c0030f480c0c0358103010300c1145000c0209100c5032051145a000540c424a080824960031f03005541a401011007134070030158466040c0c210040c284242805098103150016803800c0c841801000c0d010001c2c00b51190030901c185200c0940e1f000000f042c0d402895102559400345000d01240440c084d003600103001110204001c0b4480c1d04410b022846110b00f03903a910403898030301005c2000c3e0760030301c2c210710f480f00402c030784003004070b441a001140d100f40064650740c60b186450361900c6110101d14072000041e00244002020f0b1607082c040c007030b01e403c206020140903504100817103440d00c42511440b4452901029101f8107070300c1010741a446180c1030781040003021510880a03003c0e140780075003200c0c0180c1e041e01c545003d0740240b095901c8442e000e000803c001401c00140010088042c0042030f43c0b8507044140 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 236961753 1250 236960503 236960551
    0x8160f0609060f050f01050405091501030b041101050403030806090403030207080d051005104803030c080108031b0c03010c030e060108070308180a0b0703030c08070f020312 76
    0x40202248203880c00200014941480380c00c840400c1180c14140e070070003080c805680c24444820f819504100c4000410f42c51b00080149081000c02c840f801c035540000001052298212000d8422400307110f60a40110010f0011903091050f400002e0120f0100ca01042640c104100c40aa01510170300300145040d003540c5036080d4517000364503003280458440381001201044020484000c28065926800380598408094080044405c8403090300c5001c07401d00803554800c1c2882c02c55a8140d904443c1c00d0030000200341284800007030140d011038100b81109250170f01c83d44415048940c480091802d08070407080300c0c98040300030700040c140b51298861100e110364003803250809035049910300050900c100741200e410020164007890b02c940007040100041081c4030308482d41d603040111032003803084c02c0b0350000700349081c1c40e08540a44000860340c8420560585e0024040041e241c860b0000740d42c481300c0485402200401150050700140403416a0420b020805504041c0703c5a4503860403090201c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 236963003 1250 236961753 236961773
    0x1303030908281d0d02010e0f0405043e2205090a11030105060f090a180609050c090114060c0709020a0237080306010c0f080a030e0c09040816 62
    0x20b0451052007445550030125005110303030003440200c260034001c0560340b0300004e81c100791004010b41030111341003d90505640d0300d018000d140000a004000d50304240c200b1a00003851840750201444c0d8520030340c690246855411484001a0003c0c1d0b50241581c3c0184140c07880300f030a0090f4401e4450303010b03010b041c0c220b01a90340704032520f60040803080002d092045454200f2a40316010364508801e000aa03128100d5034500301e1001c0e101c0121940b01e5100300303c001c010050341e042c0303424080f800d80410020640c01c50000d05d406101228210340141c404c0050b192000e201c5c00c000380c120b840800300f0606041000e17224042590040e152002d5440c048842030368448169800107800000ca1040b070b2150142e00210819000d074440b007204400e01c0342481711381da039a5201410754030010001400581c420384c0c00400c1140d00c508180055442858101110f0704501d0025022904142e00c1703a003868000950340c0c2d40301d01c0c0208520201d440b01e8a90301e0055210100c00102045100103803400b081000e10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 236964253 1250 236963003 236963047
    0x607020d05100c02240c1b0607031e020307080f0a0b09100312020706020304050d0816030903050d17040609060902030d0206070e0405040f0201030c031e050604050a051303030908 78
    0x2804030f0400101c2030004e0904114100380b1005441d03510038955a01840600d00d90303c80b2164282030b60300c0b0300c0131403881c0d0a4407401946ca5068401c4074100121107505400882540ca0340c03d811400401d484c032030381c0d0243d001c01c40c4c0d020005206080001c00045050720980d0f040381c142007000410707440781004614401c00c100c80c410b940c0d40c1411810020040e145c0b450a26510301407003c0d00c0803a060040003520ba10651080d140704101c0d0461110501c15000f0850300c10800e000804c0c4403000303951401900080445c807060315140a0040640c2541b40580d01c05061a03203031a09200da140d0f00c56440c40e0090100500a5400070768030340083c8011307101000385140400894005150700e141401000384000c3d00003401034015400c01084c4000030703021102d00c00d0101d0382420045149443c0510490092070740c40310160008501003031040040d00315611050207108107071030602c903d0360349545030f005840d000c1c1c45c400c2002e2850303190030380461b200c0e6002d904441d1080c00801d1900d0b071502411451403040305 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 236965503 1250 236964253 236964283
    0xa080304170f010204050d11040f020d0e0d09050f0118030501050420010c02010824060f040501032403020607140d030f05070c0305030106031a04020c07050306100305030304020607020d05 82
    0x1103104618601c1041001d03040310400c2c009600d00303400c00010400c48214840000c1c40d0000500b260311140d90380d07070860301d07046500400c1151903d28102465018041692400443d07000d206080300398184a45041006c0d18005001504001d980c0c0004481802902c020407142e0140e407200807000801c00e01406004030b003c2d03031042c1e0340582e91502400b00701180300007050611031013120400050342c0150316654002803480c0103e200d180c0c501d4502500b45502080550f02c00c0001500c41e2035000c5220107002aa00d0a9804224400d1080410000120303034401e500e900005a0310100014500440201030b801d104200c020307078155841000d41e01c1c20254004520200303890b41c21206c001950b512505500040d43d14180700126980c0d00c01600c14803043c049c820400d070301c41c01180b17101d5000c1d000c1c2e001c40c000301030004c40d0382c2d80d0341d914000d48801c0d15018451084c01090041500c000c0080710300f1040c4c0790005c002e98a11744031a420415281e01001c8120307002041400107401050062100b06400b013081 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 236966753 1250 236965503 236965529
    0x1202010207031205010e012312031e0408210d0606030b15190e1809010501080c2b02010c020d050f0d050a0c12020a02091602390a080304 60
    0xc0c0c58041c1221518a984031102464000100582c0c040d035007800341150030800e21a2001c0c510050707002e56210002a1240d04410b04082700805200008014499085c22910002104182c60603515043c4207601c15000702c0e034005c00800c1c803e410a00889003419070300c0c090f0246041040c0c84c02c141a600150f1244001c60b548001100142c00c0000c0070342000003640145a1400c5000707803540c41040843d240c03100800140c0300c1c099046171200484011143d0182d00f41c034066262400c2d100c1d000e00310034002e0030760328018034103110b0550518000d40b2540000c039081201c6e03208601000d10142c194444416070420910055030400342e11070b0100f00f001d50380a403001d0030b80600031040b42454010100e420404000301084100d8036203501102c081c59165000c0c544601542040404070f00d00091140042d61244002c024011a8580c540b02c0840010441d000d4984414121880d00001c05065051100c4120000b1006101807104c03102410501002010103080c141c072800f2562071500701d5005000c0c00015 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 236968003 1250 236966753 236966767
    0x30a0e01030b090a0b040f0f1a01110304030303051e0411090c1c0504021203120709050a1512060816031a090d0f03020c0d0905091e0c07030c12020102 66
    0x1001401a0940000303007001c1c0305440000c400314054041c01000000b409540b0324070740300195501e811a90409000041c1844006e8152041c2c10090a01d407101403403440c0402c144115550041c01907842c1c41c1c0c1d00700b020710b0420f49191003c0d806804010001c2940444050f80b0581c5840b1424080c0d0141c0e0068504148030861007091000b043c0010300b0f009640c1405001c9072400d100e101c0024040e41021010100e682e443d2480807841c1d03004500c8808603103020115070389801009034503059100780c1280e0340e175105040d5100248115007909000e464052a200221204168024000b28185110032940003810950381c0220900704000003d65030071104d1300074005c2080c0b0032484003d01500d034001c00705180f1170030072000c11565800c15442c0f41342072000c0c10002c10482c0d40680d054569044c004c0301662528036001c900285101494005d0910800824020031244124501c0521044910038001030f0745803100f11001c401604016011404c12210643d64800a01c100c909026007081c65000541c541003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 236969253 1250 236968003 236968007
    0x41e12050c160e160201090803010306050f0106030504050a320d030f0501050f0411161a070c020117060a1a03071b0803010504020d0e01020c070603050603010209030c0f0102030c0d02030a 82
    0x40038145881c111441c54040c000f140c078012070140c0002e0410200c40901c24004810303405010030300c5015140308008000002809400d400142c4200b88007808121140e0704c55405033b003100c60903940a00154030451812000401100ea0000c0b45a900c241d42c410510a0300001c00f000d01240c030801090340c100400c854074568150060962015085105000729070410011901203083c01c10207500c1039880b1043d02c1833250b4840b003102c002804994800c2c4003d4200c0c00c0103501c030310b01c0300d08505442108000046070140700e042080d8109030b0580d9009401c12401c4452010148080e140301d5000f07a100ca0009102d90002082c1d01e10415200f03915510792801000281070f20000b0090081424420051003001451040490341510402c0fa00140c0318000c0420104c018146030440d140340c0d43c400140744495440c001402402c6402031340d4180003680e504c1d01071500b030b4007a401105801d030b0b20040c10002d0307518200888264014040c0704681c20508800d00c840d1030049042414800740c0c0002031500110380d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 236970503 1250 236969253 236969263
    0x70c150903032f0d0222030507030201020606090408070b060105041809050c19030305030c070c18060f0807090e01111b0c04060b0405040b18070905040b1008041e12050c 74
    0x50b0103c580c2d0f0307240ba414000ca65841848641d030789440d030000c0c480b4440e500030b074544501008100444a1050f8880c6440e640da4582ca00050340940328040000c0c08610f440079407644941c0c0d00448003804d00d29a90346010b50f500d0060300341418001c0038400814400782800080091240100303000c03c403212030342807090410301600d90041c05070550403e801075034640384002008032540f52500300ea41e9554281d000a5901481100818981d0000300000720302c00304803820310001070000410001b170395507945140746d2444103100d5202540c005110070000c050350f030b40c4030400e402c161a00100d0340410400710000d05a00016032000506031100d105894180c042140400501c0155001c1103035070b00708a0f080125026501c5000d100d03649551031b440c05a15451540400585440241441820b014801a11b48011809028010782c03404482480d00c5c80c01c016000745e4150715445802580d1980d85076030062000518802c40c50750300b145500d0002908074030421100e403a860740c50540f90240480914108 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 236971753 1250 236970503 236970551
    0x30603170a080f1803030c0406030b0405012103020a0f0807030f030209010203041205150901050712020f0403020d0f15060e0f1b031f080601030302010612030206070c15090303 77
    0x3210040c04000c011035007000700d26802504010703500510307a89900140c0260f0000410f40503490001105119541941070064015203e964800b80065030380f0b10b0030321084680902c40c00ca40c2c00c01a0078000203650010b12001115400303071040d03512403111500d40d00400c2e030200c00126109100007465030149a8000c0015085411501e0207514114003400000e40e2030085000701c5241071000b400070010400100950b0400c182121040f251030301e8240708140c001c12085a904010402e60720950b001003500384225004a0142a40f00d4180760440d001d00010261030042140c00745410741101c0081031005401d462a402c0c01c60300801d642c1d00f0080c1a80034407202800b00101140d6801c2440020000d0840e085078181c1050580380e01c0755950780c0550400307100241c219400c18890000842c2c2c011002c958141030724044c1c0c00a0003015542d100030460400c0c581009801600003034046030303260b0320501c100d4039907034001c04a074200349460440403000c8921b0624100c021903510394420304441c8240d1500240 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 236973003 1250 236971753 236971793
    0x312040e010f0b0d0203270705041505010527030a0602090a140f0f0f0402070521030702030d0f02070c14010e030d0e04050901060e0c0d150b0403020f010306030210030603 75
    0x645440c01041503801013201c040c14441d0080b0004002c509103542488134000e1030228900040c6101c0140c1340c17074010f1800703200c0c0a079050922505804090444100c00c640040c3c0d201441d01802e0445401d013200001d000c2038404541c95a003e0b0959020010446003034001c41d030059032400d0550420418840c0340c1e0007126001140751048400383d841140484605400b035403080c881c0f150701d0ac005010b01840100380d9034000d202007014030a1000c001401d03c00c080b181c56205140c02c908080205183c04221040001030b8070070030180104e05030b00d40211034420b030306603009424003c02d03030769204c03030030724a41c2000c041840100036258003582d00c49413400301c3e031105501804c0e4100c0801002061031001450b414016621080455200d1600b517000d8401451317440e61100300c3c2d00700a112012a684076000c0a60fa50b03013404401e1300f031445030081003021600c03211442880c0c9031075513082c07001200b603c00481d41856601eaa00001680f65401513614061140c0d50000340d030780c10f504c0e018805000c00301c14002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 236974253 1250 236973003 236973029
    0xb13051e010e31030302071b0b070302241b13030303050718140d03090e0c030405120a080105092e08010e01111b030d0c02032a0703080c07050312040e01 67
    0x21a0308074040400f60f002e60940350143e41e400a070306000503800602c078120b081c070032851403000602c81c030309102901441f88698251031007100d581002c00c2c1c480d814032442e440d150f1000300102d90103010118062080e5001910020b0910322081e00035181c0d4100c507401940420b40b69810018000d50000340303541803c0d01d400c0648031036410302002c510310000d0f0315401d6004200300b01c50082810300070f00b4500000d0409501c002c520780703480c000300c0c004c81d041503134120349502c18210b04503e08800c04060742c04c0100c0ba940d40c09181ea05c1c050070090580e00c0908021074101d0b441c100082440200064900d404548003402d003500d5152107181d508484c40341e201221070f81d2410403408207a202030303170490350707034410302c458414144800ccd004113402c0d0722a684034068642e1502d14a182070a401001800b8811206c1c84c44941412144044240d800c040b5001c41e40c2c103801080d8113000048000014000084c00c01c070440329039075140c4011a181c24241511580c040e203011604000030400c0000a07405000c2c80c4010403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 236975503 1250 236974253 236974321
    0x30303070f030f110409140c0304120807270513060b030a090201050c06070207090b09010506120a15080c0307060f05070807020f0d080306030d030b13051e010e 70
    0x8150300e1008140c40300b0561100c81c4000c40885680000310290001d03506160f8460b500c0c036158000302106d8803103150302100000000d051401140a40740302d250400701c0305244840c2c000c411107103501c00030b003003000340002c009200400341480c1c0100b0031060002800c40c40342d01d0804080040140741498509c0901e41028401c1c403001b040d02003034a400100c26640820703418844c5c80142ca2500510a5582c803c0c4960010401100e5002521404403840c0441c1048000e02d00d40520034580801d00803680c2002040102d101c0d01c0200c00c544e02e82c031006c002000181400740781c43d15004400c4507401604190700c5190380624928041c402880200307120300b0000c80070840d452001d095401441009005120003090800c1551502d05641c0c041c000010326803032610a640c81c101100d0b81094484034000d210f8000300006c041e0007481403031940100180421910741e01c040d4180d000d00030040c6504000404444a280004401042c1c54003903d2020401011480e04080030030000e1408004240c02400b05c00d402 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 236976753 1250 236975503 236975507
    0x140609060f01140f0a0810060314040f0309080102030106050406110303040308061014040e0a0b0d0503092e020c030f011b2a111804170304240606090503030307 70
    0x510120762003800e0402e0300b0301c1d00d0752103030589000f807560022460000055152143e64010005c5109507140e41104404541b521011011a000d021155103803c9006d03001c20041464491050313511032082c542052941d455a40d8503003640c1080e4030100201c2c6006c036090021b2600403030b810301580c482c03074001c504515240e00c3c001d204580240c080c500640c070701d4440e003941500c141c4a40c0b9100380c400d41119526507031003807640c55800e4215803100c0c8980c44c1c0441c0f0b0301d403490b090a0031010103410400650030295030030104400a24060300040c0c5d003082c02e4010505602d5164a00b035040a4036802800000ca060300516003490488080d005041e4541070303410041c07008012131000d10300d41c1d615140c8941d4901c1c01903010000c207034030901c0c050220400a003030704114418456050003035040c3d40c41c403c801d45036000124081000d8400070441c0031103803030000941e00c40c07002555010740038038034074025003000002c403403800e091410b0200c14089c1c641c00b09101c100d8000d8480c00040c40140d00851941c03600c9080 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 236978003 1250 236976753 236976769
    0xb040b04090b070905060702100c03022b0e10090504051801090c05010305060612040305030606070f050d03150807030219050a030606050f060901170912041205060a020c03040e06180a14060906 84
    0x8003104ac09403841c0f0300d02c2454820400c0c0410329103820403503900908000b032000e004441003242d51001410302c0c03160003494103201050650380c041c10b40712404040d08000410018010043c04500840c0707504290401450007405503110007405443c140c06801d0801000605a800050405010f4882003041034a0002c000910f294002c0e054500b041e01d90f12040006003032031107055805402c9041e49010038080c0140407620489442d45505c0030080040c41460501120010740320389076003900a030000700094145810140041080c4641020040c2d442d500001c03441205500203032085039030703220107214038100f9001d60389024500720f842604006084c0c0000701070413038400d101c010281c454000300b64a19002c000d103a02d0749003e024660388a5441c1c0c91095659144410142c4003446800e02186036500c65100f1901c21004403400345103054100000c040d1066005000c040e00f051001410242a407175044603140600c80c440d40104040e00420070b1030009410280100c0c1c81a00c0820038001c00740e0741d80750 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 236979253 1250 236978003 236978029
    0x1b0a1209030c0b040602030f06040501080c060c010219090609050a0e0406150b160614010f05150c01050711060a1127100305270a03030b040b04090b070905060702 71
    0x20000c640103803186001ca5691002e02001064401c4200030b010420200d50040d61180c003010300d8003c0b16644901c20081660800e02c2050f50326048021800b14509101c8010103201041d034001500d080004903a1600f040e6203052114005501c0c00010710405a11180c408020301040b0f8150b407000707003041d018810b000070190004085503621000c00c0b14505c92100504010038030800e805441d000e0750401350400b8000c04000716605d91800215401c1400c4061001c1d0507a202d21000103282d0342414203201031216004a181c449410512268801c10400d00807180309001c0340d5112000c05001101907407420402800b2598407c0c180403401c1108286c900c00d440c8441501c1c000b40c469011034690040c1c00380d0719405140d8015102140c0b0b0343c8116007540080e070049a001c4010f007001c9401c000c0030510140c2c90212800c00750001400580481d21a401030118400020000a8005010380028003101c280c85411030764201a102084411908205000002c2c1001e582443c90100036500140b02e11088203 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 236980503 1250 236979253 236979287
    0xb0703090c060305180a120908060405030406081e01120c1d0604020a0c1a1f0e070c020a050d060c020c040204080a08070c180912032a020c030111031b0a 67
    0x100010144070f0006210a0041c501c05c098070141212803d04907904a0210300365000720300243d000180706000003580381d105a4121024500307103030034514115401c1d540605000b0398801d2425002403600002d20400c0c4c001c00c1d400c5600000340600c0d16001b011008568040f610304482c2e41001c2c1e201413415007000e80c0c0405c007140c0050382c81c0340703c800c16500d03480d2609014090210116042000c030082140350b601413000300401c128071707150195072400c1c0c0d50705602407925812803410110346000d01505206603980c1c03005044208007500c5030085024072040313400a40e1301a45030182c80c00e0842d01401030f81c8000e50156000e41c649400c001e0a243e0301c80c100d620080006074001000400e108d1034a12560117880c20149008511007403901203400340402510036a0260f600303484900c505030182c420030600c502c1e003030380a0440302240c1e0313450a0040e240f00c1491003507022b00e15034401c0f541c0d8284900442d40000b22500d603141d04000d003640c0720a86541e40c03441541c50040095401c0346400c0321790b0f454400840 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 236981753 1250 236980503 236980511
    0xb040c0305090a0b0612010c0507020f1012050c040e0c03101401021e0f0109150b04020a080103080318100c0207050612010b0307020f10050703050604060f171f06030b0703090c0603 79
    0xd000130406c0c00440030310004080d442c040242c00c0d00356110006040050080f24071021620686c42000800b264a18401000c502c0c1041c030615100c1590f000a6031211585a0b183d041c245d940d40110103044044856007907440c00002044000c04600b0080c502400300c1075150001c0d0540400081d6843e09a060b40601c1c4446034048800d40d03240c1044003404001d51000244558001c03403410320841024640d15950190a1410112881c1001d1086d928804815a991070040e46540c032182071540c0003810310f90245008070b41f0095040c0b403c100b020a000f00d4035000160100d01090020300b8010705800592041c903003040941c5941c190244803605440440c3e005540d2034a4070760003a85082c0c41c0760005600c40c011940900d10500066018034400d10013500d080c85290b0355401040112410390107520241130342044180001c210b0100da4a010700c1511040f180904c00580803141031201901e0300c1001c07261580c03418130400001c0402a5001031980c10203106050050340c591003440140c0c0181400c05540e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 236983003 1250 236981753 236981761
    0x60309060204080706170106080f130501020717040f0e010312050a110718050601050c1506060403060e101112360114010602070509010902030403051c0b040c0305090a0b 74
    0x50355045500401c95041101c41c825681c51016001000d00180c081100c90110300000b01e03103000f140344921a07040c1c000e4100690b95080349490360302501d83c03029075440d036003405110001807500e607802541c40c101c5e58085488500d4503d40724030b44d51080d00b0110502e042c6100400000701c0303d5000c0443c801580c2003054442c5180d900869081451014103920f0f480380703001c00074450b802e807280007502c540488000d011950f80c40300152041d100d00c0030643d4695120311042500c821000c3c0b4900c2d003003680240140d150035900d484031004e4a4000c2c0b6915050341202070321204505540c407038110f4498030080041d050620b9034800c041c7e00d2030014180d035038040d80803101040c100c0d1100fa1141c001103007510050001b15060a0140c020319581086100c1d26a21030004140a0300001d42d01c2d0440c0c1004000c0e5195a09000408001e0f40014100701c0600c18207011403009a60340c2424012110b04e8200c3c0000c44140d08020001503815001d9450309040ca00f0061200c54840440e41000083d0050034041c4a51a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 236984253 1250 236983003 236983013
    0x6060405040206120c030a1803080601080c130306022d070b15130902210d1107052e1d1e0301020d3810030608061005180405030301060309 61
    0xb04d01e11100f1055103c0000700011000ca40d03000e0b42c0503400d40201000440c0c092405ca044601201c44040c002c11030800000d016984507aa007070368445070100456081c00395600110081007144e8000300c070101d40114010314600c0c000018a46810182200e6650440c0c14001c0c2c140d40d0300c00c080c0c2c040e2100049071300085c1d46e042a05012000540046c00303140b01030400f4082c42c0020300704a58100d2042c0e0f90203250207151308030b2504010300c00041c28068280e210030401c0a40d4802040448000b050044100004003aa5184503c0288012038404210500c0c010030064a102d07411003048000c1c400700303035500f00041c18441061058030030140d4405c0c908003c90f100407038401e01186515541980001500c600740907080c0c20070411501d401d10004002c02c40d01d1481103450841800f68100c021059107484403d180c081c00452190305142000520503486140d51820702d8001c4401c9554691124410003103407c1ca944000302e0441e248440c000d85003410f9440d60b489220610078501010f44910703c441c1404 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 236985503 1250 236984253 236984257
    0x92a091a1011030f07030804060e0628060b04060302130609060f05030718090b040b09060904030c0218010801020301240801050103020a140c0a03031b081b04080d080103170a0206060405040206 84
    0x50138414890300d03185d5a190042c404a402c40f0101d9946041400d42c405d2410002480c0b03002d450380084007010b201845803500c0c039026041400c00c0c6190b40312800058000aa2401003001e00410368016907140f007080031201014400d17074460010000301e0300d0b0030000a80e21030030f10000d0591501c1c01c15030700d0712189401c80303200d001605410000038040c00000f61003262507200c01e040c48003d903030a002103880d020412400b80411501c0e2a04140303013400241c00a03100d82401551340d0320060540403880464185440c00030000d0b000b9501a03980040144480c006441e40d6103d83c0c800e51000b29040e0211080003041401d0610506050640101d0b0340780c001030141510590000400e03641036143e40f5014030280e61400304210580200b4079001d00209602c160030024045c01d100740d143c1c02c02588078075403a0021040500070414a840080c0004071b40c0c01400e2100b100505020356420b03d2035411401c04010004140d0080100c01008005981441d50042070740c0d90b0000c421100020a59905c0c00801d82034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 236986753 1250 236985503 236985517
    0x9060e07270b1306060f170606070c0e040807061104030218070207120605060405060f060a0507150e0105090c2715030111041a03100504092a091a101103 67
    0xc3c0e41e01000320a003107142d1119040f00c3d03642d5107a030040c50340c4d4841a510407151090424120f034481000801500b003400040c8812445000003982860744e98003140d024840c01c5e0340407200b0020010319a424081c4c10b01a035000d4111850314545880d14507400903400e078640060149280358070100041805009001650050900340c0303100307210f01070a142c400020101120001e12803032078071000c1000c034100380006810700f4101801c507a140001051051354107070003201d4100c6d8404098006401d47c10220b011303002496406500104250400061541c10034650500c841e0107141503800e4401d905006900000003400c41148212a40d01d0741911000034a038440c0c0407036015070a0412000e24405102c009004413081682d481060300c00b008d002c08032a10040c3c59041341600d85c46424841480c0542c0088001c1e40308030803072441c41100410318002000340e4540418444140703c0f0401c0400514014014a40411740d05c48140020b550002210844600c18000030040082011414240e04000300c4040c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 236988003 1250 236986753 236986759
    0xf2a010e030f0f0118020d200d0807050607171b120c12012106050705090306070201050a0b01110703030c080c0f010b040e01051006050c12030a09060e07270b 69
    0x10003055842429510403242d84403004940c41c11003003c1000301104220717000c40d0b60041c0852500589515164145101146145040d00c09036412003041d42c5c03892004c45070b4900c40c40280f61950305604003d0b003400341c010502c606100014295180103070204a810303520002040c1e84005114510b0b86001080c0641c0c2404d61140c08413405210605c0200c00240543d500c002d82c24950030780e2030320b00320749030528140446042e0340e0380201080c00041c402d0b08800e80c440d180745450780c02c160810001a00e0280b041e076405000d41d40d00d10901c20701048600408803070040c2820540716407888403803844d03a40d07181c511010b82042000300090040241d41c000310352100c01d078481181c8945448802450003030000440c00c0348100c1c508080880402e00c10f02946101d038007181e41e0b000f172a514040f400d8415911604001509000b00352452903040486405180640031441000034000d505140c80c80842c0e0b44200320400c194442501002244105002c1031250140c508458030000c000c0001c500242202048441e4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 236989253 1250 236988003 236988013
    0xb0402300c1f0c060b01110a1103010c030e1c05070c0f0f0909110f0102010b030102070807140313060e19080a06050a0c0e01050f040f170f2a010e03 65
    0x15218100207003919601d6421100c001c89844101c0081401c1c184551010b03011900d98415440440c2480e4030181281d481810019800c0140c40d01d0303141803924454007201c45e031780c0f095041211420244038600c20305203181405c0200307840b02d981d04c80d56480c41c00180003043c41c03111491407003248501d00742c81500d9800712010b20031549070030b98480180301034002d15200d050300b4480002c0001c190701455200e2380e001003210200300210b90500400c24080007030141950b498980d1541107407024070003030502600030201107071a403859240183c4032082d0b022100d0b00940c000c1c0841c524540040c0403d0701118094285400000e03410008516000010048070940303000030303000090b40080c0401c0c11a01e00d4070442c01045039940d005001e504a882042c0c1d5500050807103101d540031940900002c00714142d00400030b50420360b4a02c5040240d080301d0300407501c0040708500e0340d84000003c028210003498040c02801e0030040041e10480c41c407880e00c4050810100e1511202026402074440041e2940080c0a4034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 236990503 1250 236989253 236989339
    0x1b0501061d09060c1602092e051302070b070513030501060b0c010b03060417090103020c0304120c0905061003180605070201020c071208041215150302010e010203070b0402 75
    0x2050380d00e021121400c141c050300e00000c00d455000310489603000e0219000d0740754800c89401f40300c1d540b0801002016070400960f019684100d800702072100301007114544901c010306202c1800f1004811500c40f1000500622682d400503880302409940b040c07040c83c0a64a40354040f041d031583d001258000f800341c0d4070701140440c0081c3c104006004c4203403000028001c3c006c2080905903034820442c1d02038401c0380604600042c00c40c2000080481000504d4058200307103178240007504652240c0c1c080c8004040c2240384604028520b4800402010a41c808214902d4101c001c01e00715040744d4410410169503159484482605078445a40960030507800c11180c80d000300701074001d52007074404500030b103c1c504000450b0a0f80001101046601524240c10705181c144460442c00900c3c0080781c0008150b200c004100c580c6101d100a2902d06d2002c0c2c0341030700d20f540009003c413072603001c010341150020001000031808c00d00e0043d402a40c181c45220403d2045107503280d101d101200b240c94803109400740300f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 236991753 1250 236990503 236990549
    0x1021501051f051c060e0f2a090a0815090604150b0d06020a0c02090a0603030e0603130b0906060901090623041b0c020901060306030308071d060706021b0d1b050106 72
    0x18074241d840340009071103e503c509041f500300c0002141c0c8880c91000c40f9180c0a10b82c4001060808034685140c0700790304204a0100150a20809130449801640a80d80004644a8183c0482d03080410070300500082c0c1030603260310741c0c0001c403c450311108a449948240181d100d0038608450306d90051011510b40c410090020080b04601409038442c01810001c1754040c5254032464045940c180c550741a03160a02c402e011158000410b55010001c4002c594008101c43d403000f20700c030718aa04082c081900c1c1c0f940400c8202041a0802500540303072160900072000750201035a409000103440a0105c880f001c00100549500c4240c102e039400c200110b28203650304103240d84c0c2442c0c406c440f820803580c3c0fa080c04508032540c911000e00064003150110b400207001c1c00212a010b81d400c00300345ea16402c1000030502581c00000103c8041c0c5d40022002500c1010581c61305802e4800d4019100c0151504401001840380021a48003000340000301030400c4001d5120b040140140414014941000c1e191 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 236993003 1250 236991753 236991761
    0x20a030209040b180c030304062102040810050f0105090727080a020102011802011407080906070f020103050a1b0f09230a0807031e02010e030a0b0601021501051f051c 73
    0x41c84e0761034144841d00c50401d000801c079204281d10140007581460303d09001161503c104456039404c010540c5480c050820443c00203202038103200000f81610402c407003a0104551000f045110341c450300200500003560b50034000e40d00001f20307150080c00c000d5480c409100d040d40c0003901e481d44c03110320400040d24240c04078182d848039001760004c00055145441c0c000c41181e92540090018602083c995010070240c00079003a403034024030105043c00c5100d0007040c8507510126054581c906030442e4034046680c94002d403070b03005208100034404101110a10310700c4400751921001403040340d0709081d040034441d1403008001c0c000030070400d4900e107503002440500c298068100d1b00a00c03840070023041c400c4000464004a0b5806400100e180809200c040034008011104a040001e030031001c1d400c41d03804129a400032800b07610681d056041c5200060300e821f0100c403140c41c42040340c00041103c0d540b00942a081d40c580910140c12940b18540116541d02c12240160075205c001102400031980b10b602c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 236994253 1250 236993003 236993011
    0x1201180921051b0601170a0b010e04140a06150b0a140d0f1509061d0a0c170f010503060a060501120504050a0803040804060e0402030903180f130f06050d0b13020a030209040b 76
    0x68040808441c4d446c05548940e4044000342010564000402c0f4074a00310798204d0780b250007909001c1c0c4031030304103410300e00f06034583c1d00075200d103921400281c0181000e880f00900910300301b08440e1a001030a0000f278030000d03040f14400611301020800b80714003112078002c0d0346c41c010544010402062000c40c0410416114041d000f05149040c0d0042098010904a1912044078131110b01565a82c1080c00380500382d041c2108081201500c000080c401c01d20689600a41c0307100c907004641d40c1007000b80351810320020b050100c140d003010001c10142e40c00c108480c030001102c0901107400c0e66941840380c40c15107801001400032400004010510074068060019a107140d9200e0f000c5203001ea080000b41c2c0003e4604000e00c0e0000c101001c980e01b803200100015503805030400d8103102c01b500000c0e41c8249904d02c030361180d0380ca440f000c600d50314040c8600ca0251404036600601c120750303a1603112000c240240800c4101180506030300c01c1d540c03014158001140c2c0240358042c0303860149000804808155 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 236995503 1250 236994253 236994269
    0x2030408061e01031103120f072f0603040c1203050d0f05040c0b07060f020d09110d0f12031e020403140d020303071d061201180921051b0601 62
    0x100412a02c0018100302c0610b0b040b400050560799003544c03220380d5a0b01034600c2069242c89140e6240d1070042c2d00c00301030080c020081c81d803242c0b200080c1c01d201c0100a1040c0344403900140c8005443c01c081c51110080380c0242d815208a5102d84c0d80749802d1210400b141c200902203460600c490082546c0b100c01031100d0002d085003402a40440c1c0905410f0b14030a0714028280d651f410000d21010500902410342280605030104407e002c02c00701100326803144085105c81d9448410000500900a042d55014802a2860241001315480307075219009043c60044c1841c12403401501940d00c6a0000c05000c013070341d160032400c0c80b40080e00ca00298001c0c401146d00e101d075400e101c03100003030110312851107128940240d451a81da00324101c5641c5051001c00030540c440c1c4500001d651500c00c040c00843c003010103088100d5040c10030b000d42030700c46000100d002e41d040c495540b0000c3c0b01446125041032082440c034078458500c00099440b0f00071324082001042d148800525581c800140c0c1038101c440308 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 236996753 1250 236995503 236995513
    0x2040e0403090801020304020a12051507020706020f030c0a020f01110d05120106030b0916021501080a061107080406030c030204030b1302040506010c030c020d021203030405010b010912050c0d080904020a02030408 93
    0x2070740f2428240d0008940181d88a46004010803001c4002c40306402c10300c0c4110b05447c120101c050594072031541c207540e0307040103904c01c10090090701e404000202031f421302c6100450414644410f95070351002c2001d8000e00402c400b07138002000307900078400030307002103854429075208001c0580c0c0180150070000000004030f86490001a0042c0284520380301f000c3d01601500701030780c903030001e00d845080b024480700c1184a413500b240741d00307050741c1080d9010b881124081c00c0d400b015070529405951080501500855003000000d00040400c01100c4c03c5840707909001c9500d0300d140e076050703000b4000e07513002403c0b043c01d080400007040c210140c01c08900d8401c640810442d01c841c001142c07203000696006003c00d07541107040016141c01615040590f200510760007801101c00310040c1581c00076542100d5580d15906201d48568000c8452000792020141070400103d054172101c1d941c1c5044003903507029051226109007480480c0c1c003180d21038103010f4002e43da500c1c00180d00940d240d01a00c0b802046002d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 236998003 1250 236996753 236996759
    0xf0b07110a060e0415120303020c0d020106080303070f020705060307020f12130b1606020f3118200d050f0411090901140a0b0f01140f0903030403050102040e040309 72
    0x103901c07000d9031001c0e0742d880a090800c8003407000406403565007407950101484002592030300f070060048124031a40d8007685449130440c0303091900360181600401c0d64144030060180f0070000041d41e600038941d15103402442da8a1105070304055154020f613800100c008208481d4035000550740005059803130480d51810300f000c0c8030348203a0041d01d16043ea0f13004550401c010b62035030380c00a00702c09040c1d04e00b8400842c031542d42d00c0d0202c2e407114210b45081c0c82c01041c0c500d101c0c074a407010000540d8403919500720b881d0990806500c1140980504182006c1c04141c2518850075030780300050480304408060b095042240d68514284c000d1484200d40343c0c20040050585003c02c1c0036240030b254850340c1005c0e8080039204021800000400f0442c6940d65003100113008808105081d025a2101d900041c65505441c184441c152042e807180c0d06002d0030040620b0024910002c84640e011501c0700c2c0354680380c207000002d00390b00c036540c00a8004e40c0003007008150501a10034440c05a403190f164a080a55 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 236999253 1250 236998003 236998009
    0x151b0c020120060a020c0c03030a030b090f06100f030b0a06110106051c0b040813030b010608130c030b0c040b070803060a0501020d1e090e0702010903081e130302070f0b0711 76
    0xc0200711106900902c001c19801111500134240c000d031b04000f0b860302d90000c440070a00c0e41d008041c01078002074480c040540300d4100488081d400c000e4051a8205d01c1c903141d0302040d29110812225400c001c03000f204100202c0c0710750722025101400030501c15610780e603041c00800c100781c0000029101e520b040b41c0040c3d14541283c0e820f40000c1030000000706000140c40c0c0300da907298000d0090b10200360070070040c83d010000080c800702a6106034003000311941050001000c03030400811001c40c1d03404a00140011489101003c81103e90110081500d80d40c0e09003401070710301071507101408240d4046101010840080051803042c0300c00d85044046555500c01203940f683da1000e4070011030800030341050703130b095000c400d810910100c0c14070200d5607660f1041d60502003022a030100c0141d40d13680e4410101544038991a0300800440381d80c0321000c0808802c4410404081c008212001108858804060003440355100074821301c400c0459040c2e4400c6070052a5001c2c400440780380401d4210514245 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 237000503 1250 236999253 236999297
    0x60a06050102010c09180b03030d0606090b070206030406050402120a23070e0a02160f03030c02161a07060902030a0308040c0b03160e030f1b040b09040f151b0c0201 72
    0x70044e40d1618502c1c6c1c40c01c0c003080800c101246070848101e0f01c43c40d807180c6c030380c40410090241459911002528070b1506000418004042d040007942600c20800000540d42d1041640e800c10340000e400a80d0b034540b440040c3c20f40a00c08407410060180c44424018000c140c1c038042880e02c3c0369003846140001860403162600034502400d101039000e080458210032481e4098109841c40c1c0101d940b001c0100e0701d41e65110f10b20200120006911219103030035155060159589d02d524035018035103418282108501200d68016440c480300002007042405d100e042d8110504160b006030603240e441005050003441c2680403101625030348041e80d07001403005031a0040b00d00c210082c0c00b40030384d04604002c003200e8619800304080e605102c1e0640700c1c11141801c0c008454681d001c1403244980c84409400c0c08142c82003140081e01c030700542010000494168081c40b82c03004da20444010000d2200700081d0001d2480e41030f90341c00344600511900c03400307822984402e10b9074000d8850400801202580c580c0c46 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 237001753 1250 237000503 237000521
    0x1508010b010203070f0302010603151b1409010c031202070b0609010e060303030f04150f0b0102010b010507020a030f0201091d15040e0d0810080609060703060803030702031e1209060a0605010201 85
    0x60b44100303c1340021861184090684501c44d100200e8a01e41c0c0341c64200c07001c40301681141c4400e0f6a440e035018055011041214801d4050a000d403080303016a501c40454021540784a0612405601d800105442484d10540282810307808644611301810008140d0108440043c028010788001240c11020030780307040d02c2031000400035451079a1b229884541d501d4081d10031903402028020005021040e80540c100d00704584100051800d4003000081c2540c94003040b840c1409010001e240250300d5041144040d80d07081219039500c01c20313500c01212501ca881c1d001404c0340e4540c600318460240d91201e064040c04c1c0450b8074400d0070304c401c2e00300070455485444040c0c007940302d403000d102d2441c080c090f40c0340e0004040203802c134119a258841401d180c8200c0c4c0368245ca400031030030404d4243d050303c06c880191458000030340c11441c2050b0301039601e100d10040450b25030501d41e10203054058210843c0c1d4400755801c000d00550030710816240c0e94030403d4420100040c18034002146e9544140b00743d00f08 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 237003003 1250 237001753 237001757
    0x206041106070305040b030a05060103180b041205160c0503100219081b0a17010e0106050a0e030703021c11100e121501080d020f070b030727091508010b01 68
    0x50030841401c10006500c42d00b822021311005100c00030f401502500a940b0560941b80040313520701d00503000400700c070300c42c042c0d45522070504001d285c04204011645030b40030341d02010740c2c0300f8409a0b5000717455a01440c00f1302800501104084800c200031909500e00f160025421101030707001f1032a440b0240d0258960010100800c0c2c48898800e500c03814210750801034134203000990301003960500c221584240440004240c2d41014440d54480706446980101080710804850707504080b001021446090500d13020440181c0813060541e80070300020b4019640108400c500740c00c03000e4181c000b5400c1c040242c07407004450f5a901c0240c2069159000e1410301c076a1124101003201041040c5034144803c417440e18810311094030031a407020006d1070302034450306000308400442118001c0c54989400000f05d03580d00420401c004d803500c842d0039203802c400342d41043c244414a90f12502100d038544103089a0181176801c0000e8010700c59881140400002c50308005c0b1a51600a01400d03192031328141c0780 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 237004253 1250 237003003 237003023
    0x20a0b0901021620090a021e121605120a0f0b010905240c0a0507080607110c060705010e060a02041806080d0c02180915060d0b27030403140d020604 65
    0x40000c0241d00c0e80c4401ca101343d0507240044822601094544c1001c9039000c0740c01d42d0016099a00311070541c1010700170090380c106036107800c07601c0030380c00320f829405049550400d0a11a04401c02d034040d00a0b2581e1180c0c1286110072860043c907408080c1845480340d0f915145030030301c0c1034500d5104601700c00580e0000381c50064103018001d100d2084400c0000c2200c042401401105001c54040c130000307004a00500003003400303030b00700394a00e42401030190968007841000e0360128025080072401002c0d200c001c0b9901522060a828510f0240000b402240110700070601044825101c07036010344251003c01c40b842600000e000c09074011030740c10303005080d016404240440328241c403407180c10910707a2002c0c00142c4102c4c1b10740c4d01e07199a2602614540c846800a80c03400a440082e0480340d079024108440c80281c1e144107454a02d04440040d16407100c01601c0c2d1407480950b55141001e00e210300002c41246e9031a90740303081011050201c000c11102a00680c992101007500c0001c0150080c0e4100c05510 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 237005503 1250 237004253 237004297
    0x61e06051801060f03020d020c030304050d080103150504020607050a05070810200c07030b0a0f1a0907080711340501021b04060909080309071712160b0106020a0b090102 74
    0x303104104c1494041081580821003080e01141a002429000c80641d000710340302e0802d89030283c1001d00d20882441001105001000441e808084008001050003c0082c031a00d8600114003e44502d841c064400d2245142402c00c1100c00601c95085500460a031201c86c68030303900340d00540e01840c26207008074484112011014000000034121100e03140100c64060b942c03030303658502050040380c40d0390400303584002d403c02c1581a4002e00341420085c00720228901210300c00141d1030340c000351000f02040300304400200c41500501c008401020700b030084420480c000300d1016502d04440000100a20803510b0b034204d00c4048007142c43c01c0e0740050f00074001030305140044040c40e0000747e410035807240e01c1d000c00103150500303446406e10480c00703820900d03903e10300300c2c132058070340302440c0c1c010300c1e540d4004000c00d07900b52700208103901140c0040080a13a200004142c00203c3c504040c0003601d22121800000f60a03034000442c008600d11490340400e40b82ea07180c032558200c1c0030701c0c240008c2c4550411400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 237006753 1250 237005503 237005507
    0xd0509040b0f0a0f0806010602010c1d040f020412050c060c0a03080703090b1501230307030905030903070b0c2401050105070318080f0c09011809020d061e0605180106 73
    0x840101c081c09401040c075814020b00048101c0c07026848002c50841c13540051201d03405c00d00450b40500154002404200c03039011000f000c1c442c1c0d0000c0c0e403400e0410b20f00d19212075500e13a006011442c00348603082d5180c03a10340e510900301a2061004452512944100030550304050064980180641003e40303c00f410b213132001c0d00d000000910100c01c150703075080001b00081000004034001e103042c4580c1c040080f550000503089680509100490f40c00072514010501031600403254043c0300c5103004214041703103251540c40c40c00b41c417903000c0d40350251f01c0000c03d00e02c3d920009440400350607012100004005e00c1000207074803960219198410700e04005000d41e500071401442124400e1424102d644254000b003400012241c1010313006030400b01c51301800b200100444c00840d10100e641001c59450082400107500310f888984a942e0745680c0b452040d95604c0e00c1451110b50001301c20f0041800b141818a0b003032040300102d0f07202e689024008600d0741011142a100b010b0ba41941c10710304d90811400b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 237008003 1250 237006753 237006761
    0x106060e010c02092806080c010e0d0b06040b031603050109031b08030103060213090e15010f181d060f010302090114090403180b0a0302040f050609150306031e0a060606020d050904 79
    0xc2600310041410020b1740c002c105108000c010b0034038001a00c0840d1000000408c00c0303861060382c9103d684150009000f0038191607050b50408c508940000e0328800c5000803030704007156110040e241d2100d0500c0001801010741120900320300c240d550100700c2c0340910800559002401c030191040c4024070060000036520760081411040030150a0764090385c0e03207000c00644522841000300c0b80c1044004980c0001c0d02c99045014114400b502c1c410a402e04200300084000d6502061649458806654001c00810b8401483d040040e0a82d107951030007500761700d8040001e200c228021441e40d800012010100310b070494072070000410000303051b1121340742112642c040d400440c0b2025015070b40011158134810081c1469103e070b460150b142c6107401000d403c50700d01e40d03100e180a1482085082c40301c1e079131480d03040030404103c540305e9140e44884011038500102811030481c1240805220041040006210700b5824820981400f0b519107401080381c54105851a9078040f42d414000c030255890b00b504 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 237009253 1250 237008003 237008041
    0x7020106030b0408093c0301020429040306020f0307171006030e0f0f010b09060409020109031203020c030307090e0a111815120915060112050a020c07080106060e010c0209 75
    0x74140c5000301000281a40a11b052020700d0300100c2808100040743c43d01003a0420281c00c5001b142807500d0a050055010000c00414000c109802d080742d11100040c400d903005542c02c99030071501d43c0b1801000c02d10356403055600b100401c00040803000751540003030085104078000031500c08290300c1d2000a80c00707400640c0800e0320318002c441110480c031500f001120743c00301000c0004642c8004907418031203044005002d25001314205005000580d030800300000880b40d10034204041c040c0d0800f4100d0090090024050550000006001e0251341c4081160140c40324140040b01640310204190101d841c0303950700601d050401d0ac5082180786400302c004d8500c84028005901200540b04002169800040100724542d844818058880130810100e031034602503070844035641c200f141c00680141301205c0c100c44695210000200048201d070141c0c1d80750720f040f001b00d9607110786880740a0302038016402048000340e22240c010403950f100c0c00342c070b00882d90041d02405680d100c0c0395803520300a201c0a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 237010503 1250 237009253 237009259
    0x906060f050c0c131505060f191701141008090c040b121002120c0307020c130b13050108160b1903060506070503040f0e15010c03020f0a110907020106030b040809 71
    0x2408450781e41c580010303c000148141e1400201000c030340c40c460a02c0451790700044e000d807a00b8001036000c0ba09460403581d0350524040c900c2c2d40280007400481e90a0180c0c00e508007441d00d854000510a00d805040004003d01141c102c0003821410000305e954a80854900805901c512000035803410103502090981d80003070015840c0725a6100e4051401c035141d120458190360014003404240c0c900003880307401c00d01a8a249240d4101014003c2d0785035010401144661490001510803003915030062070801009010302210148400b2040020002486802800c1c0070340e1908444491081c800d00c019070f01c05098183c14031f071035401c3c0701450400c071250350710500d40e0700d15001c581590345001401c2c40720f101e81c00440d90b50741007801c41c3c01280569489020040900c0040c085050445085c0303e03401c0e40c0a181c00c0c44809100e0900b20b140400041d180d9a550140440c0c41003840103088010b000c0c1c403030941d005449a114510101d00302c1c0c400b03200c0640880805030201c2c0c0028400c10041803412401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 237011753 1250 237010503 237010513
    0x15050c0123162006060a05030f15130b0405030901021539040f060e0109060e0d050a1704060306080c0612100315050f060d0b0c0d1104080114010906060f050c 69
    0x304588075102483c60700601e459214004200046c5032a0703140f84090242600a440d00c1c07400c406a260ba00c14500e6200482000024001000c480090303110b240100d80205085201c2e0a050a007281c5a900c1008564014054183d4070042282c1212400e8083c1841b007a40c1d00c0100e02e81c192001110090801d070844002c0d08800c500398942e4140050301c05803038034088562006140c00e40141c1600300303082840781071000070801000002e0b004411100340c6407003a50f0b400ca400c800c500c1c2c981d09002c2141402040e542d8241c500302006144100a030081d11001e0710304010240d29652a9592012006c64003603000c0001c2091b00c41003508040306a4120b4001c41d00303400e03050f4580c0e407180c00c0d0b84002003a800d02d080d564030802c42003a1210440035004601510b2035030702241507032980060300b60002d00070400c0b17102c00201d0080e041c41c0f60340300310001c2c0c0c100040d0a4880b51561482800782030013040e0014420031400000c40c082e0b0030b5116440803600c01e07842e507084220b50540107407090780142c02d400300a4020 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 237013003 1250 237011753 237011777
    0x103090c0f06110d080105030a0602070206160804050f0d110f1801090c0f0f020a0809061e0705012003040f0309090510090606030b06040b09040615050c012316 70
    0x8407103824000380c089511042100100356440760b14050002602c003007088100f0340104104d44010650328502d54000801503a5410b803800801c0d0540701d25045802c441044000c101c040c0410b020183c0300b50b8004170f40201c0d51030201810401002c050820140107502551151031a51801c2007400d00000e0014080310744032510b020007901c402000768005550240c4072000103034242d5100c6032000854103542001d02d201c4801da00020350700c40d851100100b91490000c0c1da1412503840205850000316114484401c010002c03101601c00e4110110403501742d03081410513001c40380450655240c0c0150b618000c0c0c11aa500c1d00c414071030043c120301c1507091010303981e40070804140780d00620b44500031030900400b80070303c4c0040d10030403504654400e0003050b140601c010034a50703d0758210b50071650500b04007a01e1b01605030008004012035403181492000009082c0c540c5608040036020007a4910300800039030141c0301c55140c0404416142c95030070011000011100c40002946044e030078040d181400f01140c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 237014253 1250 237013003 237013019
    0x905150901110c1b0418060f0209101e0507031b06061805060a06080105060703050310170601090614090103020402031f08210a09050d110a06082d060103090c 69
    0x4802444400c550f04400c00306130343e4042c42100c52141d814159803c005140c455a8240050741b85044005e1450b0b8454051504102803501603540c1c0800081c0031000081051002030240d04091000c0c03d001501440160075850146003510751071501900c598150ba00350040d511550702040d001140c5d9596102404510303154241510203685007071040010301400d00c0d030304200c50b8001e1030788a041040840001400740e501c2d10b805442d03529074103041c03407070b1651500a4000300c0c1c8000e903003004541429020070400b40a0b00001c015040f1000e2003000c1000302d8445000c0118500e020400d0364100b860a001000103042950045601c50072074817460050b01300403d01459581c48541c0030b52060b0f8030080f2800c401840702a24604900e0b000c40303a041c9484070495001e00154224800e0610900030008030001744100c0d418210591031000740810701140d2a00d0028141000c2500c1005105813180c002650700c0b0000c0c10f4840d443e100016031112a80e072600f00440180200c00341c11120a494050b00242e002 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 237015503 1250 237014253 237014257
    0x13080c061c060b07030509190503030d1a06120414030309070612230108010b1804020f01020a170d0507030c2c040608030304170711010e180708041104090515090111 72
    0x1d17110b42c1e580d6641c6c00b21141000030748a40e0542c03400d100c07444180d040000307540000c11294180b01c168404640c00845091101d0103000100e8482d420810008085114400d103060041c4513900c200920003603000b03064195175903030104030b58a0520340e2107810103120181c05207220400303078a80c050021405008481400c51004102c840b002240007a210051201e22020b00952449100c1035070600040301c001180401e1688024102078040c0c095803444440c181d00c03d1020f00c280076003000115188240c0070001d100c007a0b201011444011b80392101003400148a40264000e8103039580c0d84981200780b5117012500c4000c1140b911102c2c412075903034400c1035140c50082000500b042000b8544a103850705200c2051910f0440081806100b00401400515810b4501359100030070300e0056108008100440c0c1c0c01280c0c406040d0801104d0400c001c8002e52001080303114038400d4251912840090050005440358140020400e401100b030310b1001da4148424240e1101803440045010303050005102055 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 237016753 1250 237015503 237015517
    0xe04080a03020325030b0909010c0504030602250c05180601050a08060f0414060a06090807030803060102120304050c0109050102240408120c030411060906040510030f0c020313080c061c060b 83
    0x442d80b01c02d0401c10b18031b00341d00300c03a9002301090024000b01c40b5804004100381f0507800000d0995134007150100704044240e015001c0300c0c44003800100740d1920707420421030070595480740500c102e1360081c04d1040f011401c00f00c1405080184c54540c108241d0840503981c00c0c00007881f10f41c002d01c409000b40d20315900c501512030650903c048140f4103080c084280b0501c900c4a8100506001c004081007251800001c2c072441142d4100c0da0b116140d4a030180100d00b00404403c40c0c01000c40c011050109102020034101000002601c2d02490103548000590711118881800c048248501c03101c0b01d030002000c2c14443d03005204450340e901d0042c4c0c02d03041c100c54440135110f0810540000c8108400c100703009010038400388081307500780d0a14007164001240c51081d4001c0da4016040c0b208202140d034044e40240940000c030280a02855012a400944e02e8100040251403002c6482d0001000340000c62078110042004d0a11840c0001d01c541c0403500e2141031842c28429959101c0c0010041c1c1c03400054240 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 237018003 1250 237016753 237016757
    0x918180209160306050f221113080d030e03030109150302030f0601060917060103031407060501030b0601020c010c020d0f020312040801020d0605060c060a0f0f090b060a0e04080a03020325 82
    0x45005034001022078465400c080d0192246c800026010356508104184002070140b044004841c4581e54a0140200300b441d41101c02021400f252903001d40c100c1074054880f050215211002c100d0741c01ca054825405004482c0c1d0420001844440e6007608a6400801407082c1078074001d64aa000c28500010300902c51150380000005200240e07000603800024061074540070080d03066041003a44418042c8401010700209008546000d00d40005440c03015400074000c000c19a0740c1d04007101c8680c000c03a282401802000030b1510550302072401e000407243c029003c4c85212410303684050f48401c0d52f040503a40351094401c01c02c072800c007800060004e81603200015840390b01c550400c2c01500e010f5080320b48078400c107121b030b414100400104aa0701c802c0036a804510708907000107503801000e100f1301c038060090a002c002d42c103000311900040e00074601500d05144450b070f11036030421681025a8010101042008000031881c1f0a402550b0418103540c458071018107408166918401c8011a03140 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 237019253 1250 237018003 237018031
    0x7020303071112030a020d05031003050d231201090504060209030d020109020f0a0303020d0c0c0515130803161725020901141014090405100e070918180209 68
    0x10b410700f0f00400010382100700344001c600709a09904042c1d11070303411144100030030401100103141e03014616041d000642d00141900c050071299030b00105099084000540b280c04a82021041d54130483c04645003590b030101e006400b40d082494a5014000280060b034600c0c0d024003844015039001e0042c090107400c59000001d408d01c0c2c5106010048003406e400500c60569442d041022035004689500454003d00c3c4c00d02c103540c5a0320f02140c10201355045581c00c02160980096000032400003414842c005121406003c0c0d0385014055481c8200382030085820725080300d25000030003882c0721039840c280403561079091a01001e6916403602c1c1000c408003000208082810070b5007805299540940701400100800710030300804140b48260360b241074800c000c4102041401c0d900c4680c2031305c14900d40248140440e061203c0402c46d80400c0380603041a420004000c1075103a4016040802207030010082c15405600401c0c1541c0102102c0788445074907146d072401300c1c0c0140e94515400b0320680079484885 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 237020503 1250 237019253 237019283
    0x1201021b0601080601050409121809020c0d080907030f0b070c02031515190611031902010209010909150306020c010e010504050d1b0c0902030c040b04060306031106030f1603020702030307 82
    0x10b1300e02803040e80224052841e181d059404941441c0b04a0300c6444182880050b04070982201014800c96510881d0300380d00c0411301540e441800310303040d9400320f1540c0d9554050703212488050340b00d913a0351200a04202c0603140140c00620a00c0801d9801040d81c2000200a00f00d5008641000c0d25010015030b0440c1c400c04010840e030200700341d001400c0c010b0754500307820b16643c03085aa842021b401030b20140071100303a0072034020310204100c6070382c3c4940c01c0c2111001034011201074040c3d00301c0c0608501250003050b000c902c07030310380b0302c110041e1084072203a0344501440e40d2290b000940c002c0c01d01803c195207a4030581c910707200901445000b0703031144004040c148981840102912107e008007800e500480e0459000301d091114072200b9501e605400699907100c0c1854111203200395402041d69803804203001507019003603480101145c1c0108507007801108620704115540c4001c9512540b9a1030b03040c0858012013503046801c1c40c034841c4e414010300d091050b0700064559085400129031040d0b52303007205 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 237021753 1250 237020503 237020519
    0x1d1b010c08040b0d14060d031b0203030d06060807300e010e10150f1e0824070305060306040f02030f0109060509070603020403020d03030504020321070b060a050d021201021b0601 78
    0x42105e0070b4408070603c02c6080100001700c0300f110300e0340c01034200004004d08500740306d0100384d16074805900504681d5118100305100020308121306c0345402082d46c1070300142140780200c0214000f501c0141c42010844400c00d980d207040c0c2c01c20302d046040203640d48404041d41009201d00385502d10210010526603c40071485d42c161042c0ca100c0420001e1480e004205002d50302c80c1d104140c03040034022402c2020345c03205a9040c0e5006a01c0100700d881103260007043e000b580c1e1805941102038002049040d43c5698069003600d2f0300ba94280c0d095070040e000940402c5842031031141709807000f0151880490408540703401d4806111041d10271554510510440381410480040200320604055041618580001da51150003c0003d403e15844500090440d50b0610203100750a00c60340550311507079140310a01c1d815820208003140c40c403885502061403403901d007000c0811604014207420ac821040d03400c0c8002c03041c02581003880c66400f8860001041244c00d21441c02c1c03c0c0b03410082640303600d04244 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 237023003 1250 237021753 237021761
    0x90102031f080726240901061d06041401080d0201060806130b1009020703030207020f01080402061e0c0102070311060f01050105070f11030f060a1d1b010c08040b0d 72
    0x80e80c9036030304402080007265070100303400088840d00c0c01124610520045888070080d11400c1084c001e004040c0341c000c0500c0d04046100e05503108121446555503002111800ca481c01d002c0c1c4880d0030f003840c0e900f0100ba552414003641c40180600301007404000026150041075003030300062041d410400c1c450b120f648c0d0910440c00201150390040c846810040450030081c800d514016024500d91000280c1501008040c00010240b91004564600755810006d0094008c0502244281c0c1034500d104810341c40785450a0017580c006040d6854034a9254046031001d041c08841e4407907000c2800703080e205880a01c05805554000d80355001e076418101003060070200000c10f1541249803480c01071180d644d1110a40d03000d80d40c00100f400300494036040801c03848980e100896494417500b0490000c64002161050180004074814010a00000c5020312005040780e0310f81140c0d88401e00c20050198035005240c0340c20818105049808140d8551844903485500301001012001850124003200761103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 237024253 1250 237023003 237023041
    0x1030b10030c272c01140405090a0201080c0306040b0d0b0f1b22080a11030c030307030206040807240903120908180105130e06100201110d09051509010203 68
    0x10801c0201e090780031200781081100c3c0038803515000740e020000005412a29a030040821480a0085070341c0d60b5030102c11505946d043c014011410305003c60780c0e070600001e405d4122981611084580c0d680d035008010756410080189038000e441d540d801d421506c3d110460000c0c94044d0130018075501c0c1c9400d141d10b80f45006028541c0020341d5604040c8900c2d101070a07070701c0400e900480782c41300c01c00f60512002424225000620b2a000d20b4018900300190480342c4000c2180903400e48030980444c208060b00d0303008416001e00960064800100080e0240004018403880b519180754280d11341115001e24040440381c080c00c143d950901041030641168100032101d03101c000030b0140701c0059460481502a030030b801045240c5411520445a0054081c0c60400210903040c445550365074002d00556082503c0b018081d41c0d0740040c0e10748452060090452448030200b590b407400240b64003020040014200544480c0070300d03020203d20304607030085540620f1590703001680301c0c1030a584100318410400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 237025503 1250 237024253 237024287
    0x1c060209090f0603060c0901030f1b02101509050910290316090905070806101a032205030f190206160801060f02031c2304050a0209040201030b10030c 66
    0x303403c011407a98000b50603a03025501c03100c00d40e1285035a0300140c0150400000944009050000c80840c5101d0b00c1620326000005038200c4621801070200e00c13085500c500c0103401c49a40c1e00400b8070441c02d4a0300301035041400d8808490b100c92044504030100e03030f00326032a612035055030b007400f601000075506040c02c442011800780c00100483d00b241841c1407058400c840840c0c0c3c880c1074403028040144200c100a0003464282d8185103440d10360503600c40300d203014490880d00304005a400c00307017200301620b01c120314a5a01104042c0c3c0c0b078100e201c54014a050446061100300b0811a80200f000b000e4805610f09009551030000c480030060304100e4001c0c01403000f103508600c11038101780d015100d41d044070010b00b04545810300b901d500700d003944544508400e207405480c20080f504000c170360040b5034101e55010000c09521074200c0380d10800e0020354024142e50300442810001d4909a090150000d105060002e1000c980b440402c01c000e480e400a8404a80d0301c040c00c140c295003100e0045071120900d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 237026753 1250 237025503 237025531
    0x1d0601020a0201080901142a040e1506040807061e0201090321090203030403050d0206070203030702100c05040905040b01030c06140d050c04050303040e010f17060a0b1c06020909 78
    0x1000000396500034810700a0f0410042c400818040340d400c0d4070a240700c01503444c0c00c0c440e61510075841c10b0301109070081c030459586401e0100d05642c00e013006440640d1540140c45106440301000e00c503920054070700d400d500c10010400029860760030000100109095140e94101d180000c10448100341e90480880c00d59050a103002e000a90054428900c00f4807082041c0440030700600c050001d100900d0004d4248c44001000320030b024000819100b21a069400c888660f038995800300d0301ca01080d652000540d0296040c0d000340c450f26040101d6001442c5007035030500d5a05d051000c1566029078068694000503801031060008000140d80138051030700305070301e0018441034822880d1250244428500b80e4440100d10882039032001c94009160040489031101d0311505030415100f001c1c0f084104050a4040010b00e5411511001000c803155002512075952084262009404500580c40d03100340264400c0030f48640031864010039a000381c0b40140c940c000b04007407104560700984180d51038111 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 237028003 1250 237026753 237026761
    0x50c0607151109030a141b01090e0c1201090b010e03010b21010905030c07080601080601030309060e031006080a02010e2b06090206070605070f03091716080408071d 72
    0x141c480314500c007001010002000d00b030100312000c40303000b602c4005a05005101808083c0003142460040000c5081e042c0c400c9064048510112264842212400f0a10000d0300b00306680c03401c0c681d10760115400050620f4202807241d151001c610980110360040e96581c1c40c0072483d640070041e180c02c0ca0082c2d000b000440d08a00004281803230354501003011000b0900440c038040b0f030039040082600d620030300300c030b4860a801c910651140c000380121007491051000004452800081c901d0480c0d4268984807a200e0a018084513504030742145550907102d200e11890b07111200d44205001000440c003c0d040251843c0300050818524030b0955100e008054141c0103d60341c55140070400c403a101d40c44810100091802d6030103040761003c0030394441e2020810100340106500b2180c403807402a074903561825035113074065046549121028000c0041d1810340013600c1043c038000c2c060218401340c1c60107011141e6a924505034441d410801c09508111005c000d131869002c90b42004228180b21080c035072030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 237029253 1250 237028003 237028013
    0xc06081911090d172a060f04082206050a0207080f03040909020d0602030a0203040b0105030a0b070f090f03080c01051e0406110c061005100f0905090a020c1009050c0607 74
    0x400318441d10800e071000324081000800752803a1004d03410b501034652500c0070b0100001c51125003010341c0080300c8021041504030000810302c184681d81a201d020a9515562246220f5401c056580682c1c03485144a0148600c1ba83c10700741c004001e85d6803019a2928a0030780203040205551003c0300c0b5a008108014a07a4000b00c20742e0103a6010400002d212555400050a110110324014050500c004144206404290000d610403401941e01c4c14150342d8480903d6921940e48002501e001c2100001c18140c503c5074501042000c0645840d03040d40b9203503604900403102c2e551046564460010701580078000a000d080c0d44400403a04c2e52580203c002c05a881649000f40001c0529a9542500101d89940810360f0325820038182164030501d0305011040ac0008180a901d2150a484141070461031007821111200410350f501e01d06001c1c5490180110128013502c0038009540030712180c109520100076050082426900c0441d104040c2c0c207200e820310002c103000c0b80c00340904018600101e0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 237030503 1250 237029253 237029257
    0x60b04030b09031b03070203060f1e10081522080304030f440108191a07020a0314040e0f040f080a020a03030b04060509060d030302070c06081911 64
    0x9070054504242a581c0007802410351180c418112803140a488501e14419000409051041d100f50220f078500e840e25100119516400c5400c45030b80002c841b011819144107085044d04411881100c3d05416142e443c4142001004840384c0f148807021410000707451000b8918440c000704101702c0080790411a01c035211130748001400501480b00c88414440d20b14401c0018555514050b030f5600303006210030095a09401c3d01d5403202c1914410a01c01c2c0c0c0c1c02c842211001030488004200805c0c41c180708201c0341014940a4409a40c1d889130040700c5890100044400340c89400254080e08101c0540e20300234000d04a62540300c000d2550600061001302c210086007504404481030703001c0c007030381d80f8034000c404105000c0c001480c13500080b8074074622640011b4040081703817080c3c074140320b6510600c05200403500a885010ba2040041c004a005410000c110385101d902901c0e000d0b18003005034030707044200c8100f5403000c0c00090101041045030038000a1040c601001e0060500a0b4529030604c00458 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 237031753 1250 237030503 237030509
    0x90506012c150105130513051e0105010914060405060403080a09060e010e04052509170c0f0d0c0b040602030702101d09090304180207031e3905100609060b04 69
    0x20000002d0660240c144200c501c0004240087c050000403050800c038001805040c2e0700c0384c58000c5c20303400e10070f0b1440303c2210103411780700c3c183e58000c0304a00c0e181e0790650103242e0410864004108020200c0e564450400820296004008241d43d643c0c500100502010341544540d04000403264005190703a441a05e02141c182c00f2900429182c507801843c66455502c0d6010800350760351301c1e0703078080d520350055980000c4401600c8030201c0c00c00400303181754a801407241003035070024103108048060703e06110000314003401107043c44000c544400701c00141d1350254000601580c40861604111314080e00703d49406001c2d032610b841c0c107e81210000d1000d4540c0800d16210310001750000b4842c0e841041a90000d060400f440105044949510802940042026000251022150a042c00c40541183c2c034130701d01070b80e458600321007294610100403043c4c0da80710b0006a10101a01f060a0410300c0100c099000c2c101802c1ea2140b040740810440c7c2c1c0640c001040c0700d040010400010786100207580072 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 237033003 1250 237031753 237031757
    0x1e011107061e12050f040308060f03030316140403060501180e063d0806010605030903160807060f02210903070b10051908060a0b060f090301090506012c1501 69
    0x44465188400e42e03050b403c21002502440c541420411807020219410b130040340280c40b10a0b26031030b000c0030300a400d50100c002d01e030503a0040003c030390340b400800d95100c0742c40030328544005041d1814402d81c04683c0641c0c002d07125030781c480005104c00b1115020040032100d0850b0304000001420040584501c0010103541500d9055920500c6c42031140c0d4208a07500321484043d4528210040520141803060090940e10300c80d510000c140700e0300910450b070003000b40320b00030360806402c071146605082c41c1c52411140756070144000400954540a82d5400c02d07024900941c8500401201c00700000068816082c0301070041d05200d49920040700312641d42d600882a50303106e035629480c8820244050744003d402003050641ca080e08613540101c20280d403410320070b807101a1030300d0495006035480d4012484c0c3c4200c04000c02510f00b0425001400c074500c01074000305d41b201042e294a0704040090b0702910403a02019216081c1c40c8d01000840d035107540b442130b007903190300301b840ca00003c05480c5491581 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 237034253 1250 237033003 237033047
    0x10c0602030a0b12010c11010c051b0312010f060e010c0c05040f020c0d020102071208070f050304020d050d02010501060207060305012d170a03110114061005091e01110706 75
    0x282c10700d0540180402c1100540090012803440310300d18001c0c03106441c440c0004111582003520400e042c043c032204450700c0e0343c0303850030046501030120b8840d44800c05e81d18288800c110b03c400708030844140500a21706201c548102d2480d1040c090701094140428a0401046441c1c490000b000c2d43e0500c01640e00c180d80000d41840e40804000080c45601c1c420407441c4902c80c5030b40e1242d603054006102092140204840f920440038050f11010b0080c3c40d03160128084101544400e03100ba0040d59025000908003e00d6014a4482a0130041325a00c603a005035140d00c0140102c0341c041211400501c001e00e010000c6600d0203400c0035413040208007120707003102e10f0100c08012062110030b083c090a51640c0007143c1190042d03880b42e60349030404048010901d00d01e4194008941031003540308440120094444a544040420104007900c0070740c02c081c032406110b081c0c1c540e21400d03510703075143e4001e42c006030312080070b500098129007504d0b40c6031030640e014100030b114803a40305840041d12903111a40203 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 237035503 1250 237034253 237034261
    0xf06010314030403150b032a10050f030420030a08040e041a090a1e02031902040f060b0705010e011b0c03021009060203060f0109080307080c07030b04030503040b0a020405010c060203 80
    0x1811403003554009801c49010720860400440306506c194103102080341100c103501a20744034001003403c00c1c08103000e0940650342d030366018100b4501c1190300c6001882d04a02d031140d03075058100c4c2500252010740b04801c89080d130401024042142510098045005140d84241aa0f68120a2056000e03000319800d440f004030342000f605448220010041412420f410714140401c1583ca0450120035030b40301d41d5118032206440c00031480544910b8010300549440b0040c0d0b8616002e80910302c1c0200d030402d0b9900440c10440703089110700740240240c280c12564480c201d04009096446001d000c2c002645017800c0700802e007608142c9540020110700300540c6181050500341c0c00c000c050f65950709860300b850101d00400c03100c0d40c000d52240c10100c80c582c00b01c0304440d004503032250580c0940b023001d0340700304214000b043e04103002d0411030b84403500719812503469954000342d8a4040c0c03402c402150000c01400b041090f4400e8580d401041d01c203085080502e0080000c008501d2076070050007a40c2d0000100e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 237036753 1250 237035503 237035543
    0x12010603181e0204050c0a0201060504090809010309230304090b04020a1707030228030e070612090203100608010510090c0f0807031404030f0318020a150233090f060103 74
    0x211030140c3c0c000384200401e1030030400308607150707004101b020010351034120081100e1030710384100013505402c10300e00da00f08441035005400074001d0030300036201d50400c10440307514000c00c0c19001550348050f07406151070300c3c50300f005181614035400890f4852030050148000701d90f030001e00c043c2c5c2141c61060110164903810380540080c03080280e450683d46850100e000e9811054000360f50b0b10314140e8042107212001d40c0e9403501d9185500905001500034071460f01c0c1150190440d900b413500050a5540080a40e4070140840300e00d58000022039440300100b0003900c00140b404c00c01046c030307440180030718401644001c00000c0502030200c2400603220104030700c54442d07444030042a6661140e02c00601301418013512007640310154500280c10a00605014000314100607229a405400c01901600b849124001c4003407a01c00602148100d2060440b0140f43d02940d8410030030520020003a8144200041d040c42001020984a40c0c07000ca00b02e0001080043d010381180d4000d00038a43c1403403022a0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 237038003 1250 237036753 237036803
    0x1051c02220f150807080711121201030c050a0807060315120b06031018080c0109050d12110901080a0e0f0f06010e0108190f03020a171201060318 64
    0x180e509240c50048003080d1082030084000c1550b20788461014075108503c0304a40c10241110020005054007012404142c042d5800c5238204100100307441500c4200c5a8101590700403c00001283c1502c0e401041403181c2d0301100c101414040d0340d044005400d0000c9030b951403000c0d1143c901055501d48021060855500e4072901070002c0a0130b11003004000e041c03800e10340c03206558091180c00749501c2d0f080c0c1048541703e1400591005d61503040b000e50302e0b841304071035500044001c020035501d9403041e40020343c06021511221070035485250030a00d01140040484e9004000c810004804021340b040750782c0c1051215900080a210109044003003030142d17820000d0341120760b0900d200c3d03003046c400b24820109401d4180c0d0b140110000140e83e8603107800d50f03110540b46400204207181f4881e00007281b0444141000540240111900e42050350395440030540c0e2a0051403465030081401e94121a20410b460300400c254681800022240741c0d50808442c1400001005e100011401c10140042117070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 237039253 1250 237038003 237038047
    0x40f02040b0618010e1014130305030406020a03030b0f0904020d21030c0e0a0605070206180d0c0302040c0815061b0607200601031a07110f010605010e01051c02 70
    0x1541c2d0711046480100301d00c0d0f00d00f1001007400b140c0130094000c0d40c0d0800680602d40000d1742e541e0014600004940b20340c07541c3c460401d00c040c92440580200110304104000c10060000ea030007090315254070705004045440040c13090f4440e290308a501019960380c1d1860507013040c4c04603460759488400c1c0c90401c140001301c248403400500c00401d200f03a00c54141e40900341601007600c60651143c0c8110070022010490700802012079024440300d400350410f03001400f001900001c10b10400e40310000059021021a0300440d01c0841c1400c042c4214149401424021109401c4c10030321824407441d4071540c2801d14072143e0250340702094a0141c540c81808001c900d115842c151101400c0981c80286146000c0c011044c150704404051440d01c1e10000d5083c0c1244e410510111460441012204001001400d00d00c2003000c0300381601e01c01c11060100c1c55088104500019a49240c0000584082d0400c043e8a040c00b201340403809135402034801c400e044100100c401640c408540342610a0700c43c00705 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 237040503 1250 237039253 237039259
    0x803120c0c010e01050403030506130b130504030c0f050c010f0f0e100504050904080301152a0303090203100c03050a0c090b090604031401060311060304050d08150301020a031505040e0303040f02040b 87
    0x1710a100505401d90300c41c90213000c090360362103a507401c190200801d54800c080c050350130012900c0a011420060381c49150424400c0c0341c800b403604096151410204940481907805410204440100c1d41e000360b540c040c8840302d401d051000d840304039405052a08080d00c141d000c4c0003510403803010548218102d502501e0000c1c1001c40a00309812b090b1680d400900400c030682c21880010420140500300c0c040d40f43c1d0341441f1400c80300081c0c1b04042c413600c01c151012428941c80c0c2d002c2d4001a074050200302101200840002440b50440100809070f070405026400f5962030900c1103600e0719482050b140c150352035074110907071740d6614101003417261056a101503e00034051070482200030041d00804101d80c052540401003401d01d4007000004c2c881900c000380709900c0208100101805004084c2e8000a00d1108042881541000c2426079000404a1000035a0307103c901c0c1d904118040001c018080541e810407195900983d826503d00c0b020b0409460a420044040c0465071682c10100c0700d14006 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 237041753 1250 237040503 237040511
    0x2304090c030902040b01020f12210f0702010b0f13150e011e1a09040c030f11091c03210b0d0c0e0f04080f0c03270a0803120c0c010e01 59
    0x2030310300a00402c0c070090200d1041d400d0102c04006988005002c92036025150080c19004028081840485c2d00180301d1807006000d2031a04190130705800d4807940314400ca03e0300544a480d2006000b03007116100030315503108600b981a00f0b12607450342d180c0c010310b00d501c1c4240007564000081518070421015405003002e4841d020020919203903130560340480b20080c41c80c2304884c0303880b45a0b65008180da403001d200304001c1440a200549016042012410920f060015000201d0000038042d20524030f09002d811900155030002404c1c002400d0109009801071170400d40c04e80d0b030b8000c041c4044080011400d041555030480c004000780d01005d9407820041400390049118030302a00781c002c5611900181e00c100c800040c0d086001d02c200e05208550100c451440d01d00c4041203110580c100640900d070342c2c817003840314508854565000780003400380d01e028070080150603000c12860b230405402c125000c2d003007405001d180c044d0080e0318582150440183c03d88448400207554010941080205025828 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 237043003 1250 237041753 237041771
    0x304120c150c1505060603040609080d15080d021515181009050601110d050a0302040b07060b0a0b0f070b060f0d03030606030b0d0b0609061c0309080c10230409 70
    0x1160311654040e02c50200003810040c3d283c1040104e6108880c800d4110408100280011301180d004400651041c01058202645107008004950f006030901040f5124000140040711082100e904000902c0c4006d0600c9070200f01150001c000190a1080c6203184071505521507803041868200c4042e10f14134241507140542e81d861a0400341d1081d900c2c514076100c0442d40a5220744ca1001d180c42d070041c01001e4660310071400f1621a44251159010151700380300115400c02940001c104580c0240e2004c104280a81d0070040180659480006052030400400c4045400c81003600c7c1035982100380134686503201004102e42d064480d019a9001c0c2014610070101034245d0710000a588040d5002c0201001840c184004820150000751255074808001182450000f007400d50180029010b6052500385e00840c00c0b01300c1d624041180032802c1d00c0428082c1220821090540040c111074020915007070060107000050303030032a1108448480040b82c540c24850804550041400305010051420 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 237044253 1250 237043003 237043007
    0x411071a1b0d021c0603030f2f01020705010f060303140d1404050d0207060203030630010905250302060a0c0222060302010809030708090d060f060605120609090304120c15 75
    0x2c40002d903500c2c102646009aa005281e512414046e01c1d407540718180d401b016150b080e103500c80c0d40707002c9040c110300b43c10510300000001117100c20055039110002da111401c5103006825a54101c4000b8081e619164040001c80d520072141c01f402c0e4138074042581e5440007a20b211000d001c1c4030991081f0020382d031050204001d00000d0850f010a02d60b820380309581e031960b9003240c49200c1074400e030390b00480c4580f00c0c4420603138884907104014020710595840c00310040740030b030a441c0d143c0815515900201e170462048040e0025240900b9100c440900599043d036000401c41e003c7c1d9002e0b181004901251002152140307100c148a421030107408041241c0c0200754032010380214081240080c0c030b802c01240d48100000700351102107910034865401d0000d2001404801190304e0800c0d01c45039256034080442c94040d00c14a00680380940e41d95580d0301000000e501c1800c00034001d207005565003010048070800200503141600c103904024141660107017081c100ca81d007d5040100f0f1280017031520001e01d5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 237045503 1250 237044253 237044257
    0x7050a0c0602160506060f0f01030f090f080304030f0503010305100903050d14070e01030e060703050c0f04060302030f060102030903150601050409050f042d080d060b180411071a1b0d02 81
    0x241304104441480e51a02d003800074000c0da070341c60190007104002030002c2030760294200031180300400500080030003c030340703c90f001040441c0c81503500c04400424030092580c86014840c00640509100340b135549503903240b5658002130141e40c0c810980d0f9804003805c15100d07504507a00398050f01c0c418491000b05140c40401d6101c01c0c1d51510100362040300c800c004d94002d000303070300e60700c0011000b0f08000e565414042c1c0141c40c008150118004c01001092240684180a80301a04a03030707030b0040c1ca914014104025022010300901d0540d842800300680302d42d00000ca230001b200c2c4001d03017014180c44500041e10240550f400200c0d4043c14001000800750700455002d100394001d5107030040c1c1c150110181c182d96008140c0b01380940408401c800e010a899200070041010465000540b8070303940c180728422a0020005d00c64a0000c81c11000c002d850035005406011340c00143c40d80c80c05410382d90340400c4810500d0b01110145060001948801d0700c0e071580c841c060905030600d41c0c0c40b052843c64a000b9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 237046753 1250 237045503 237045547
    0x31b051003140604091a06010309080d02040f050603280209031f0c110703060203060d02090a0c1709070512010207080403030c0615050120100c0504081b010807050a0c0602 75
    0x40302c0d01000203041842d2900a012245801c440b44d4024040f41c04a2a010b28100408050501d82c45140308400200e10200030042c000807503100588542c03c003403400c000d58800d075008910810043c4140400300c191450400c0000d0300f125090407040301100c10340f0021380204134800d0303414019141e46180d614100c9021421603412540108070341842c00c0010348009003c511180712981c0716980038000110941d0007107402c801c0040082c2004030389a40041d0040300121224214107483e204c2d41c50701141c20820503107201c00c8402100700c0c40c1ca000341c5459991819446058030960604802003d0410290b0485003001d4101c001603030350f01d45a0070003404c43e08040804440700d0307141c00b081000e0145901c040e4020307224140d480c0c0d03000420343d4401804004040102200c81c6c0140d0000000d4050184150038080c010350b2156034481d841c0c01115030030300010031089104180912a00d902ca60381c0003541c59801701450410a444600f001e000315000c8400440040c1a6840002c0f5050400d60740002c0c0210 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 237048003 1250 237046753 237046781
    0x12020f0409020f0306092b09060c0f0c03060c1704020f0f01120603030807020f0102121b09040e0d02010c020a21020a06020a0c1203022a0307020303031f0501020f07031b051003 77
    0x148180340f0045c210b56040c05941f0400101a1041449014807850450070701901a10341028a0416525020140000c0364801c035191651404216203190b007040003459080c1250b0040c511603d40b540200b101c40d0310364205180700704e0181840c44120b030f025600501170644800d8040081c161240b078040c0c903580080d00c1000140c4524800b0f43e035207000500031100040030303900e8406c5107606c0d4500701203181e503403100a0b112140d02c180208031442c2c079580f1070343e005140d0401c0140302c0f20646100180c21205032026031b80840d004606008040358850b01440707023068100342ca00100c1d2803010001c90403c000305500409541c000aa003061280e4001d2221281600582c2080302050500c20160708030310403181c6440b89100000d0280906183c03442e14205c42c1040712058900d0804281d0009046610845440700498040c1a040042050641c2c0314409400203000900c2d80c039810289a950390119480b008024000b422919850000c045d890f0400410028101030b5200b0a6104041c02504c1d076005070b160 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 237049253 1250 237048003 237048043
    0x12090708060907080709050c0f0c0606040522120201090f031d060721050c07080106030b060415181808070201140a0c06020d0e0a0c0f12020f0409020f030609 69
    0x34001001003040790483d81e44000505c01d441c5040d0b6108040c1c0b20043c4580c0b9010341c20b002145901c041d240083c03c148a5000150070341d031410104100071250082e107032031924081c05501001130600c2007010401140c00c060007070304905044008901406d0140d100030700140c035801c0120109030300b0400c00c14440009001003109030b40c0403418070440703010301d1401070524610031408110f480b890400c3c00b0030406e2245020351400111220f0107281c400c482c1e0080c01169542c40040060203022002ca07034000c1d44c201e50a011645d40c04e88100402c1d00d05000d0b1012407545c00440d00d5604905038005400860084480407289034107040c803090b81e4111880030390100e444016248603566104049071058a8aa102c03c146942d0903152000203400c400420320340c1e5544c84d18604401d6104120200c0428443c44102e035405050031001c0384029078903030209048403405051038006907100000c1e034075201c400341c400007219521400050b924000501000d501801000c0511203003041c007164000000d5440300c4512 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 237050359 1106 237049253 237049261
    0x20a0209010803041406090d1502040905040c0302040f140705070302010f05010f150f0818010914160e16051b01020310090507082401051209070806 65
    0x542c40d500200d0201300d1110300d0311141a1440d01686e0460400b030138400032a4010034001002418400527004107280c0c14019415240280403244050046043c10700f0041c680e07000030700081c1e0289040641d2044903840e24000c0c681c4601510300295030962301c100c0c00b00c4403a000118120219522414081c20040f480d00485020302a1001d080444624144d491180e5040b10303078000041c01600025009420342200c05564400426480d680d840746811200034014840603200501c0b0b0800341075040c40103000000c1c4200301d40d4030010381a102c071380c1728040c0315504542120031802125a58140410541c0300340b01070702c0c007840340500d01500d94812a200500b6030300200e60010000c10408004c00894200e805256048444c0341400f0b40c244c00d00c1610300d05081d01340507210300c0d1861482540860b0b0b0f44035404803000c480340001c045403941805e0487d552680d2091081010600c20300c0081 = true := by decide +kernel

theorem cover : BRFrame.Cov 236870503 237050359 := by
  have h0 := BRFrame.cov_init 236870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 236870503 ≤ n) (h2 : n < 237050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
