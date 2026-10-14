-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1764
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:35:37.808118+00:00
-- url     : https://prove2.me/submissions/671458c9-cc05-4914-80af-5a62c297b03f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 317086330 ≤ n < 317266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 317087580 1250 317086330 317086387
    0x209010f0e010c02131d0f06061801060818010e010f0f060f0e0411060304030305180721080c0303010909170703080f1e0403020d0f0504080c1005130b 66
    0x211800c807a80d0000d90500703216410345217004150b000703009035409840b9902500990203a0310781214018040010b04d065030041d01022100142c0b10038003803228132190b4a50041c08007a4400041c070010340541481c40c0c104285007a010300e903540d079010f1a42124800040441d81e41d456081d40b01c0143c40b2401141f4141c04000020807403245000030016140806108420300b400c0050005828441000019041450b010304200e540740703060f2030018004e0034100e801c6600e0a04240c903031200900000b03044c0c4240c4c1ca40081c1e0200704d40e20183d0344240c20300c050a00b1184004100416501701c2420320140d0300030951004003241c425158035100020b411b804402d014180010302244010950158603079400a08001992030300c1d0300da04600707000c1481c0300090292420b8010b4240010550300103880308100790705540c1c048481c2d07403100c0100c4043c4918440d003002540400c01c00042407400d043e80c80182d62150034842d01c1e1040301a803401c0d42144a41c0117030b464450100344200d9544003000c0c11002c3c05107414 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 317088830 1250 317087580 317087597
    0xc1f12060b09090403020304090203090c040e0307030207030b130206071202060105061c3303031107031a180601080607030f2d150306020c0d030b0105030a050c120a0209010f 76
    0x4010041c034003800c11164402c01c0d1660101d81403500910031680904030a2009540c0ca20340844030a9442d28031414030b90013546000a02411000701100780c9503240c0d4103601501c0e001e03146480d201c207080b8014020000c1c4408142ca0503005a6030f00009104281c0714515044c0311004a410180c00d00f0700590200c0d028003c200b0600700c0d000181030414000d1071b1100c000094085504420f13070f01c2440454044016441060003c003085644180306c60201c0784296501c41c011000c0110360703511807203c3d107c01003003800c25015200086403088811503106024056802540440700c001614201c030a0b031014005411410038030284580c103010740900300124602c00c5c40740e401942071294040107075080c4011010a0704460428199190f0801e0340400c2c3c0100340b00807041c1e1030f820864001d5200c54048a420301c580030041da0481d0081c01600d8408105840386070856840000c910054100100f004010b60010008444135121080c0c449000c0e80802c4801a101c440401c000f4045100141001040c8010319 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 317090080 1250 317088830 317088839
    0x9010b030f0403093b040807060f06090f02031009110a050c030909070c0c050901230f041e150503030f0a030f050c070b1b030c070503090a14032103070806030c1f1206 73
    0x47c003141c00c15a0300034400990140030188807401801c0703903040701110328100040d14001c8052034011750700681d4014040c0c04401c0e941c0180e078040346d040741003100d41c03541b0a0201c1186980500c01801003035042c41e080d00e1400c01010300240718400110380503030104e10f03c2c050301d00912140c3c03401540030f4441038403030407590f5041020842d0002a0089100c810f4143e100c122165911b91250345001c644000d84103200303032a02804802c02ca09844c1e100040228a80031100e01c91003c6c29040004680c405400b07946000480d13280689264040b01409040c140c44040a40e061340c024454548070b180486180d07038a801d401d1601500c60325000d041101e401c4600032101303030f40742c1b50102241e4101e841403010a540b03c45a10303103c0e0175401091b441a41c0a0000040060080300750824503600103421825190440c00d43c050b04501245800c0c248010300c1400c0c00010000c500032a40650424001400c54011074118000181e5503070541070b42c808400c004191039070070305401c210154112142540140642803d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 317091330 1250 317090080 317090093
    0x902070b011509050f01020a0605040b15010207050603160507051b130506100e03070b0417010e121804090822050a0303051c060521070509010b030f0403093b04 70
    0x82d401914800e4983c0c03d8940c005c0c1e03000304200b451300c0c0c1c0c2c424824003940c0b0307080c100702c5480c09007103803201c542801314030148005610108603001500c100500d02e07402c40d00d401c01d46486500c4007803400402c0c007a040007030402081040158400c4008002c0030f20072084454000d01062403032801d0b0446184e4100030a1058598491981d1030b15102d80d4a404024000303d000002c0c6000001d90003031112140015000c100513800003034014030804c01000a00c01032450709415641c03036419403024a180103041c8041c4449032100161711a9417000200041100216501c0e81c1010342d02100c2604030f04818403c7e82003400b84103603103040040c0821100b40703134910724548001c0c1c5030348500e40c0c0844145100760303112941101c0503801107000e0503003e00f80760b28800944844950000484c281074089104c0c24400081c18605a08164140c88107002464115240d006d00120b803d01c2c054400c400307012030784401041107c440e110041d85e50110b00700d034602070345d0800c204c0b41d0005100e608a40d0884820020000850070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 317092580 1250 317091330 317091347
    0x3050318010e0d1a071412100e0405070909080d050c030604050f070f030504021f0207030b0a0b060a050705010b030129030f03070308070c020a0e0f090c031e070f0902070b0115 77
    0x245080070b00704d03a440c50812651a03203a00d5452150f103901240b01c0300c0300314410440610a038400a000441c0780d4070707081826040501154005e105070301418040c0280d82103900140d01c4280b20b40d00032400c040f21522188151a030031544d800d42108084100811072405000384c0b50000e158841601d0941807480f00207000c0580400b2403402d141e121408202151640010b00d08007001c0c08803880f80c400d0345c1880003074039004184400d0b10f842031148007041245001e032148100d80d0034020a0680b0341080c24605680170703041080165459580c0c0c40080025031820b00030048141103490503035602200b0607a14007580c0345408038081c003d034840e80c8604a00c01002086840e180d07058200411150381c0c60700110740e641e1358048000d420500d01a4000351008580c030074103014041004006246507039100e00c450380d41d05102030503603050b884020150388406403021008102030354a825180f8035070700c925800815900f40c1d84503081e515400144003051141c0104030601601c18071030800a86085418020704c910b0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 317093830 1250 317092580 317092613
    0x1e030e10060602070b070f05070e161d0f04090b10090c0305010b040605070807050106090c0e0306090c1009050915030f07230a03050d0c0314040501120f020403050318010e0d 76
    0xd0011b2081c041c040070301d10705024a41c2c0b003011503041c19221010400b100c0b00540711410b2144080c0029840240104018248035a95428010040c041001003025840305101e0550704140d44501080110b9150b24066100d600010b00c0700400d030b860b0941c0d560417908403920103002c152420006100282c10603003164102d82403480c21986034195420a20bd461160010041c0558a07028000075440229000300c2c049040d56151410014030840c141070311448201c855051a8215000d06003480c50300105144800c41d4a00d40383c01115111030120398480b03029508030515501c113081c9040d06240c10030800d117600c3d0004014014107440c11000d01c12128085100204082c0d50000c4848192141c20740100155009011a00b4600000001400d00c0781d01c054258001207441c0fa20780101c690500480d000c0b910b040c4e4924400e10846028200184003020034a080302d60200000000b0820400c0a009040304035a4403220350202d100025003200c812142c0640141040d000060115202c13004601141 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 317095080 1250 317093830 317093849
    0x5010e100c081f1707030c05060a02030304030315170f06070e0a172a2409190b0c150f2203020106030204020c03120618161e030e1006060207 62
    0x100c20024951483c82d4103130b0044c0c500c451242e43e050303041e6030001854008032401000760035583d03500d81060044a214442401d400f40c0d10400128000a20070740c030401d501c900054940101d0350300c4810b0240300d82c01103e2162000d03440741c280c0c1e00140405108054000c11307207050042d10a0800300100d41d054030a886a0508140721036030482c0403940600484400841540c181d038030041c03844c0100b001c01c0c0010f001c0b00e4040d1880111b594103040d402400501600214001d140c02c04214408108114100700e0381c103480300703031805000210703080c1c004050102e50250300060424001c030813040040810300204281c10b841c491905000c03039200c0010141d004540d680308000ca4001b0b1506017030380035140640c0000c2d0007500c002002910080c001c8042c14400307400d840003600303648490302040303681c40da0900802d0881c10220701156400300041171030714007560b050801031078000d0b200000001c502d1a04c000c00000c02d441c0d10744684e001c070040c4007594150070796000c208042410020025a18409802001d428 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 317096330 1250 317095080 317095111
    0x903040501021203040515010e0114030a0305030a020f0c03040605070519020d1203021204030201020915180d140f030d05010b030f0f06010908010213050108060a290705010905010e100c08 82
    0x1d1060900851071f42c001460701034601da503959012810321503401d2050350304035009074065007094070780880c24800341d9426580321815034503001ca0704402980074001240000b1006c0085070010002440900010049900c03910f840b034820381006414520700c00803000c8410700300b004020060f540e07a540d42040b5508040a240c0114582a00303500038824200302c0d1786000b51040400c41051f605400030a44100143d914007a003d003500c4010a1a0052502c04031200c4d1060300001100c0c280180c0712510740c1c0c041c501485404916800550031300303e80803160b00068000150900d0380c08901c0c007039203006141e044103440c50f40c0b510b0f00342d0503100b01c030180c0b00415000c2c0c900d010942d241c1c415848140640141c400031551803181e1916008200031a1080f240485c6000c0f00080c40c924220031298125643e51041c41e0140c501001c003020284031451200d00c07205401e00060300802ca091003a01c17500341c07180000185083c81c1103241490801d510500ca6107803400c0500740c09105920410f07450300049641d0440c0e00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 317097580 1250 317096330 317096333
    0x9061002030708090d05160503010f0209130903020304030b07170115050a030c1103040e01030606090203060102071203140d0c0e040b0a12140d020d0e01050412020f0d120302040e090304050102120304 87
    0x400000c6108064450300c1480c0c500b00100703c0c540d00d11f50448108500802c0b414003410074100c16801601d011542c0001070000c1c0250045298000c541800d100b8419a0f290980300d54a00b031070750380c0c25a0f03200000784e030b91100101000c0c03140c00c51501500030321034905501452008001d1491081d880c4100c101a220305e0312901d501d024001e030001c0c0d546460183da88550b00c50f40d00d00c481c500244001e641150404400088040152080701d000710b070180c2c0070f032166504283c0c0c6010f4641603820100c08111180042101c002c890b4000b40c03100b042c103047c000c90129180c05000300802c02c00c5416920942ca0b2400c0e002c041d0740c8040750201103c1000205620303c0c8034506100075104224044c0b000e01f030080b030000e4481c055000c504a0303001600c40d1210410f42d5149401114203004500031514010300101810015107040404a11a42d01c000c20912038007455a07140081080c03610045400710350046424040400368204d1568001c0e03482c030080d400d091a1000007582c6644c0c0310222900940300102050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 317098830 1250 317097580 317097589
    0x408030c072d0501140402100815040906060905070f1e17090f0d0824131a040f1808070f0b100e010b1206090709030209040803060906100203070809 65
    0x2000803090b07090b4208007000380c2d10711280c0449015003140c055281410385480e5440104140c1e00683e0041d11000024940351002c1d102000301500250810100a14031b280c030f80d84d940204203102c1c5c0705000c040b8989281c01c00d00f02c1543d0002d0405410b0100750015400400c0c3d01c1144490f401511703844003c10318071000c02c155000300d9038038143d0881c41008000c014071044002904281001c900c4201daa903125588021540c5030310503940714154184c40b04120314001d00300c442001d040a4010207034511950698065000c0b02c21200f02c4004050008000c86402d2905100d402c03401c03003405d1014080080005c140c5005013500d10002081c019022407448240300d0074444070305109034409800b4005003040411041e5940141c400c2050050b8003c0c00407513031424101c203807085044c42c83c81088281d15080d0801c07400460080840e4100040307580c0020241c0d82d40070405020f02d000e8900340c0d50704d0510400344030001c4001810f150183c09961104241c6950000c01c84819541000c10340e5212580e850006 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 317100080 1250 317098830 317098853
    0x30d031805010603110f03030f03241809010f0b010530040f020306071e0c05190803011a0403150506220506030f210d0908040b040f0501080408030c07 66
    0x2034040d43c43d0410100030460901249080140e0484201003402114000c0544d2407052000080c03000704244085086d42100014040650900c5443c906c0218090750200d82c8108814410b800301c85003c41c2400750f091005e10843e0001070380c1c40c20601c5150603130000030f00540b040b03441021b680030b0342030a003a004144012205204900d01031703051a840c1003a0404003c5241c0070803040c0d1207802040041008180650001600008252004007100004410540d00c0c0581d1500543d000e000e003458400e00b05030600d460310212481400c11680300d5040c40c80084e89040101d5003005451030400003803000c0b42c9054011502101e9047d80483c640c0e03503180100e80b4480d294049810401010712141500548039000030340b040c00e040c0c0c00c0b40d207816090007800382e81300641b10000d40102002d640c0108044035040080684912102000c682012a5915038a5a80c000e5100a9140c00081030502800210081c208020402444e02c00c0441c201902c401e806480058001d8807030190001c0c2c0070041000d214070f003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 317101330 1250 317100080 317100083
    0x906101e0b041502010e0c1507030c020405070c060b03060105010828182006031302030114150109061d04020d0b04060602010501140a080c12192609030d0318 69
    0xc81d00c41e582c4107295000e041e10340c07901d10b0143d406c2c0210445c4d0580d001421030003c00d4028180c0e0f03c54240300ca031a208a40c407e1405808011950394061f0241e21a0f00a00340100030607990980c03804410b050550071a420120039500c60b1704030b40010400d82c0e9201c90b48541110740c1042140e05181c07a400003807d54410030501a80c258141180e01c104507814101110415019103950030350840200000da0700c00c1c281c0c0138141d5100b81c0510214140d100012803001c5821710240001424403c4080078a41480e41111816a01e21350074411080c03550f4000c0d1500000e08143c140420724404200100c404094004d1056004503030129843c10340c2d4000341c02500c7d401d00c2c00780040122030380b5010b00034040d0409000702c90b80c081002140f09410b00348400b04004480c0c0c0e8901421504540c2800c111000c0c0351860302c80302a12851100f403140202904280945500c42c2142c1402c3e03015400031480c00403520016102510400d100c1c01041d030702c002c6030b940704920040c40e00007501d01103110702c0c07944030303200220 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 317102580 1250 317101330 317101349
    0x40e0f06031e0706031116200a0e04021c0f020103090f0b090c030616020303040206030a020f0a021f05011d0703020409060602030408070b04030206220e0702060703050906101e 77
    0xa003031582c6008607480043d0354040d0380504c045107003031005900610803002c0d100c0d80b4410511590000c070346050207206407198140200e50080c690f00000030b1406440d604503805400364407052000b140343c0b1031f4050500302500104682e03100929250a60b45040505010b410b15869001714070403c644604402c0d80766501c0051110300b07003002032800b41c0d99058062202d00078411280450a84210b1101c0a1031440e120350046140d40d4481e401c0c41a00d4001030615503010b80c090244903554201c1402400880c0b4003a130090030810701c03101c5001552a0308883c0c19503d86d242c4001480024404454101c06042c0e02c4034407141031b15190421402441a5440440210326145010424682c040b00810481d6110320494500d6906c031a2028107138885c40c807000307602141c03c02c82d02007814a4400d1030300f10174101c5407186680c15514105649140c208452020045c0c000708200400142c061260680203c4108000d0445281500c0e0604800c0c149015059500322151000c0000b00211503c6070050f000c001d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 317103830 1250 317102580 317102623
    0x350c040207080a020c03032d09031906060e0c0304030e0315090109030e1009050d060612060b0909060c0405060d020c121306051603110c040603081b0102040e0f0603 72
    0x2c2c0b410b15078222002c1c00b0014094000901010700e40082a155162200040d6001c4143e40a40e002d01220680b045484140024066405a07a81c140031307030080d0600440343c0d40080307140c610305002140c030307160018910035510078140504a21588150383e4001e40c141030030f816440c4010002807400e4905611018100190420010340350010340007503e04a1090b101c0c585d002e15a0380812006810a182c4a00000c4c801103081080d458403110b90003a890088800142540d02c9150440c202c2c03003482c0040e2049900c409402036542040404550f1011441e005003a082c20441100c10706803003903114080c4909008250215a0000b540c1100c0000343da84003150381c442c030040000c0344503400881d41c503081092103110001c0d095002d070003160b41c51181d003134003e490340744207980c15a05c41e20002600350a0744905104e140881e11180324602c040c0d40500000d50f141d40301810300d006611040200e01140d41d0050100704211680d21418542081400b400410107a40d0f050200b45000e0503c00c1d132303400111100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 317105080 1250 317103830 317103833
    0x120901020a03140f060d0f080c160504020901082a04080a02010e010804030206011203032c0d03021206040905030f031302130903230904020a05040906350c040207 71
    0x550052000e500726850074041034941c0070505100100403546012031081480000380351703107025070380041d115120b03450821442c081900c800130a034004042e441d00300c0c0d004c0b004035060140740784a070740c0c018001240c082d45800d1180f00000d1060201078100b46020075007014070040c1482070031038221130240d8a00380546840d910220a559482034090a03408216040032245403548141202885540c1680084c58180d19204500d0300c10140484c05400700b55541c0f180503070107503280302000d01403425007841e109400c1c01040c0a50402000d0041c1d5014144104901190400c62800c103da010f6030440700001c41c44107a042090852188030200540e4040c00010460a04100c44010340820300039143c01c40200c0003448190120380b25000050046104080c9510b00b440d51030040c100d100d03000c0b1300341504058034000030030242d82000144d83c0200d00080750501030f41c0464842e00b402841d1010b019056605003201400c02e8844516001d20f02c0c00300e1a00000140000b0482d40d420900060411550380312103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 317106330 1250 317105080 317105083
    0x18050309130204030c0b031f15120c0e09040804050a030c0905060402130315060948110319080114030606100c0c03080a03230108030f0d021209 63
    0x14903103152185403006004244925a4802d40e400d6903404540c021410f0309080d071440e40c5410081c91240326000740d0302c005415403c071074103a4006103006a400f151007411041c0152406180206190003145000f05451480380d01c10b5140b1100c04094031241c0e0143c07181d0800408604c00d542186812000e90702d400020891600514070440700000810002070f00c9403802c000036445800300580c11182840c5050010840c61b280c0081c0b401c401140004081d9500c50403031007a2403d00d00c1480111002013950580407884000d80309266440481211684090640850450022030402001c02c50020355009641e0410000c40b0891541c0e8149801840f01c0403400400016090144520100300c4880c44d43c464140001c5080c001e604c01080c0c00c0307078880000001c0718003c0c829902501d01d00080c00000022800e43d400400410b584c940d00480c42013a104d4000e42040050b11503034210340040001045030b682c000c0190307402c44050744809030340c0d0340203409900c01a0044001501c1490750030b80510088440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 317107580 1250 317106330 317106337
    0x9120f0606080601061202040303051207170411030d0e0307150c1e020f0906090711010b1f0e011b020105031005190303080a09021f030e03030f3103030e01180503 71
    0x105e07581d000c3d000d0b006e00340b2200c160700030b03844000e011880500021b1030842035180c0c1594481898034100401900c000303030040c0040d00903107055881d2101583c208200c2d040500074010090703034a080078003c901e0b9142c01b00b43d445100c1d00c5103004030395401718000e03140382c40780e03070010070307043e080346003d00c5040d02104d1071a008448650202e10a982d90080780c0c1c1076003094401c2e144101c00080a01d41c241c0d581d0b02007a5501d1803c00e504c000995030351204162141d4907407104441c18039400154900b24941c3c0c01015202506204480381032080c410711442c01c0e44241144142032990a280541d142e4451042420310301d011500103036407040c45904404d8007400c3c55814502264000d944110f07594480ba182c0508030340d550780000e90400304803410001c0d40070b000c84c0d0294144c051442c000921080c0c000c03801d8155081914041c1c100c24501e401d001c07412018401240c0b036a02c50620500d003801480103100b01503008500002d09254990300c6034600b4040170760104510141c9034800410408992170000d85030b90 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 317108830 1250 317107580 317107589
    0xd0f03021605010f0806010f031104030503040504060e0f011404062c0c0a12201209070806010b2a0d02100e0a030c0311030913020703110a0309120f0606080601 70
    0x990a44006143d61081c251003102400603100c8002c0c0c0d03202c8500440700390b025850603505160312903d10303224003900800140001c42c02000a1601e0742d0400082105442c1141c1c0b05a15003a81c0006010a1043c821042811503003651502d070108c00707a150110340908680e6104902c2d401542c100e46c000c980d5076000840300041d82c01000f50311507803101074120650007506881000076800401d81c3e80c02008a92041c804194031103207000064105402100c5143d11081036219000f4502c0188070b00b524082010300040c01c0e0480182000e903040c04014401c90040e0101700c5207151050703107200c0304207000610722024865004262500c0d068070b507101940e60141c0158001c1007034a84050704c0030a20001c504100d200d03500d0750701c0303401d0050700c1c0e241140c41c402096903180343d03070000704034403201d036620041e5044045000e200c01603100c0c44203090151030460182c1901c0440e403c1022641c0c00685c1c0310901c403003540c1c03030070014141710001414040c1003074407031a01c01088645044000b003244034001450504a4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 317110080 1250 317108830 317108863
    0x1c110a060807021504030206070f05070606080d172202041e0519050103082a060403021506030604030c0b0c09130501080105070f020d0e0411070318050f030303040b060d0f0302 77
    0x12071382d451010424181240c0140c016000700006c034440034403803650100704209500d005428580c843c2c03101021907000b9803044085070311488103802007030340040079041c5194407801e413441d90f46441d407030503089002c21030054941c01c210080790740c0440d03440340d02501e0381b0f100d000000003203558142c20520003084c00756a07400540350300e0080c007180d44605000d00c1e41629408680f06082081984031000040304600d5005400c000440e100b20310031104201551186005c1d5004015203000c411440803041c07000b801003070003508803408002c04030b500300a40350300107544a20000c4c4690740e640620f0215015403201d15901124506113800d14002c10f81055068514a000801c080c1d111001d044e680707080d94040100140e0421100225841e000316000840220054808144041983c2100e0410340c020316086000c40c4001d803408021001c0d00d0803c4020b013005868403110155507000095590000034001400700500c90001180b58507096001ca070036942c010002c500e51075062034013940754213400b480f10f41103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 317111330 1250 317110080 317110093
    0x5010b010809120f09010203040806090604170301050108071808030726030f0c0c0a08030c120603010c0c061a0901080d030b0103090f0b090c09010f08010f0b1c110a06080702 76
    0x242c0001003106004024040c07405898400b88a10f102c0550704105102c0f810743c00305001c001542603041c41014405c82c00c030400740c022481d1524114810010030f200808944405000603c29640c1099000d40c002c8600e042c064031406441918286c3c2c1151a0414540c43c0408902e210800c4841c004100c107841e10030f58000510b11030003500200d14002150075030650359040b008580c00c01d03140c40040c8145001030054452403200ca4560389e2041c2d00c00c2d02c13100340c00e07400052510b01c0d10071001c0a0b103402402c110020703c1015900c040060032840000000342c8815a90b410341c2100e419224444064594081c154001940c0d440b4038050b120084450602d001c241400d880703603160340c401d1050740450741d840240041402c42581b03030010302c40d10040c0000f02c9480b03a1100303030807035640da18407941c000e15602c10103d0342a07040c070380c41301c2c2558a0101680807890808068011310360390313014410040c1c1c4102d00e0b45030b06400030f4140710000b500c100c1030b4190004009040800d1640e4401030070340c80741003d502107440 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 317112580 1250 317111330 317111341
    0x7051009170705070503010603140d030b01080105060f0c120c0706050a081617180118050a11150d060603060501080f07210e0a051e0c0103020702040e0a05010b0108 72
    0xd40d21506801481d91280e0300e202003507040c6800c00780001a005000316034046071200082402c441503a04180c03407039400700c078010070b5000b010004c0e0052182c00f031074180b040c1902140064221001030003003520440c008299008030401d6070f801d0326034580505045800c99025580c60310358a80c41740c0709200c00c40c050b003203010440d140070700104c401c50f4026684550490b5100720324800b0010180200404000802c50b07402e2000606c40d11050040b0149294015008024010282119020045010b6070308400200c8000b05502048a1382038a400c0030341001020004000907104000d082d10119440901140c44a9118129030045c4280c0c0d10300c0e00c04010046c0c60380015903c510049807022820354a040c0003c005d04e200e00581ca80300350034400d4580001041144050680b41c0c10103000c039203031740304440d684103201c02040580030224800c04d044003000d0900b411a5254081902d403c2e050580000da41c0013151266401882e62101040c2515070300c1c4014641240031780685140280001c800002050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 317113830 1250 317112580 317112613
    0x1060201060602060106020c1003061223190809010c08040303030c02011104051f030b040f0e0c10050a0e06090409061b05040815040c0b07080a030f06050a0302190314030705 76
    0x5046e07030b06079001400e0081007102003040f440701c1c250b00d074030030180c0792080018400103180000f10180e12a40c25200081c02c00705442d081c454034a2005052540200088000102c0c0810407104540d000591590b84480d240c0c0181e600c0110b41e003000b0440d03100002c0010a0560641c0a00000000c1d64001c1c40b404144441071036242c0100c0c000c1c0d90f4400c40c0592031001c02443c50100c584998468107000c035a40e0820000101214500301040107d1a19443e407101c40e224207100c4040c101d613049400e00e042812980c4000c2050050302088000d000c00d5005a08580d82d4642c161444654018414085a2110b240840c060078414440d1101a817000d040b100d0103a0180e0700307640075900c225004028401c2101c40d501c18aa801034010313614542d11000210300c0c003659200030820540604841503a5400c01400201242c0342110004001880c5c0301080c803c541d00d6414100c1141d404681c0302c50790300b1442e5501c03074900f0011b0b80000d141551025000d680f0f401c010019080e101c0c061800d5400c402003201030300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 317115080 1250 317113830 317113843
    0x201050412030504050c03030f0405121207020d050f01020f18030706020d030c0c0203010c0203130605181e09090c0f01230331111206040305090303070b04080301060201060602 77
    0x204020401c0c0800440745200707500c0036030700900a50071201c101017900c003c0303421a402404030782c5203c500002c00340400d08050380303945007881040c80201003520381005403a5450240c1d04000b445100c4401d6000d0920004010036901801404000c542e1007001030749561159026045402030b207030032369404a1a41c500407900000700ca110b0740240240c844101c8040b00203140010540c001c2c00325009910300583c90900c103203850100283c0003150350b5181003840f9440700701d559003c6010840300b08100c010701140707119000803102c007e644001d503858480f150045000d0f10720f110301d0b402482d0f6804000c401400020048106041661a40000318001c4011500a00d6a01a000605e84501c1040f0030560f0140002c40d4440002460606884104100d44d8615030441100b5100301150003900e17028040840c00744074410344221291010b80c07450a04094458074020009814400082441c9030107403424030459114550160b035082d591314041ca00503409820030b01400c0300641c60300320040b6080b800082c00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 317116330 1250 317115080 317115083
    0x3040306020f03061314060f1206100f0812180d0213090b01090902010c2316050310020a020a0321060303212307050f0408010903030e010b150f040f0303020d080702010504 75
    0x20658070b40d81d81c400d1150100802d90020f0b002404041c440020942c1800980d0051038500c1728a00e00901e48104403401c01c1035908946526004ed44014000c00704c500e044a2a0301410501300040c550400e0010308107030700d625006074000c40032801304480188185c0c84411214400d00e00c056103640c0710a41070044580745107000340400d03404244d140104194003090354a4035800300300e08800c1348083c40083c3c00c00c20401032207016001060310070311492505008400142d0f1441c0400c50a241c04018000d50301c18180c60b004d810700502d02e03024041112141d040d18040c582c141c20a100e081e65a1030000e081d044d195160b60f03201c1c1c070304a00414030101e45009a03148540030103049200400700020f103040518000d000c0d2004d00c0020000c6241c01000c100140004140ea0750002450006500b0080d09584005803020401e9140421440a41da91400300c00b024410040032035448400681410169101d00e4100803070315010b500b000820581d000a030104020303029500d181d1282c80300341040e400d0b604140d40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 317117580 1250 317116330 317116361
    0x150e1002120f0d2301061e05040314070803040605070c0e09060105130902041404020f0429030129130c09050d03051e03061914040b0303040306020f030613 68
    0x8070600e1600c001d000f03095081030151001408070a9005040c03e84007503040a01c4601145000400c242500147e10380c894001c002da2180a0b115180401402c0d4810390000900031607030824500c041034010844039000d000c040040329640c585070341000d4480c1e004804200c491405003000070501e0300301d440500d40100d030b10710001d010903420402044050303010700001c0711095581705494805039846004003444012a00100013080c1401c2c0180210359580e4040140514103200c0214204542c4c1d188602410001030000c0d00381d19854000030b4090511120564030007284c0f04d4065220f40c80c40020f15501a40403035480201e102c5102411003034502280000e008a800820100880d080100904a0042c480d18040b4a007500842d910b00654442d000d0481c243d100c04002c000326404c0000800c403588400341c94800c030880c41d0107000116001507407070546c01385031510340700e42c0d0b82d880400658002e580e22910554039008503540880180c1c00132030b40c140c840c0c0c004049004603107960b0710075103c4491100300e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 317118830 1250 317117580 317117587
    0xf01030519021602090705070210031d070308130501020f0309010302070303020f030a0507020d020a050a0f0f0b0a0506100c080d0b03120406031b03180f0309150e100212 74
    0x540042000900311841c500d80a266210007460502c01480300e80c28801c400070044841d801400340c0d41200070320640510134100725180250b6508a2110000c100c54600441c03c05200b500004520f080c10721114130a00c203102d008820401d03180d000c0d2004040c4582c41c1c8003010380e00d00049983d50b5402d0071810854100f0022060030794807940052603814000e050140ca8180c40f01c40300c42042d881140e0385a03207aa95101400601541417141600344a80c92004209070b503001c0e19000c1c2c60701510750006102000300300c818400c02c401c400d144c02500382c110039107400c03610345030f20600042c10b41150128400d4960305450720140d4002d000080c0419005030341d06040c411034800010052507584161940362140034420690001d119001304054901139030301080c2e0140b142c003154006080211400d00745030408140c2403034541440d102e4100c0c80d0b04990003500f4032806003004da42d010390541041c5050304031000c8031608540c00c20030f0b101e0214000d5804011400ca6660120f0712060500740441500c3e1081 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 317120080 1250 317118830 317118859
    0x51302090c030c190206040510020930151909080d02090d12020102040f0e1303050a050405041a031e0607050702030c0a03061e060302010c021003090b01030507140a05 73
    0x9034055a44680f00d400650700d441100316035120b40400806030480140e000e0000c0100b003000500242c80030b0107c2d54010741c04c11110800088050004251500805040c49103c0142d004c141118809105908098170264a0170605000b080181101e030402404c4c41c0d45015620030505102d42151150020070071800c1107444109840a94810268241c3c0041c80d80d044001252a03104a204448850f800060b034440c9000c0421410f032409034099402c507200c1d0000c000c81c1d000800c0b0942290796041c90314503039861b1103c500755198040c5030425600107251a0b541e403043d111581600000700011000c41d0b2081803a10500800700b0940c0020038100d40091000c00d680502400c082d000e01e520040c02c1d215008030340000b0604400c4194416910701c2d03151300d5501511a1682002110002c000000340452401c0d03800103800321100400080c003440103070b001107000fa8426070010f00000d0780451a00502c0d6980d0074440c0d03852080c3d010b00052880c0040b515009840c00440c01001c690000c2d00c041c8080120 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 317121330 1250 317120080 317120101
    0x1706030304121b060207080c060f040504050c070501060b0403061413030e03070e0a0906060506130e1e040308100801090308010e0a02090a080f01050703090b240d0309030605130209 79
    0x2e0407022140c8103145607030042d990f4030354040c920160165034000d201d10342c50300b80f000d0b1511f0149000700b03010b01010001640c20020403800c4800342d07001611301168944130b200303c65009110303200014003154030303100021030300c0c40340b401c0117204032406042c00380190079164100715500d46060703500007001d01584400d040043e020780d49a0f040c0d0800182504c090035038a144c10800c1e548201c400c1e0b4110b9540c1c0040320f00b0007080b1700c1a40043c0c181640c1c01428140c4215a038420040c2e103002e4a0094100b4200050003c01805030680701d4807648010746455042518001c0c0440300265010341c04804056004107410313505224a10400e074150f81c90407856444e01c41c00c10907000029100e148007070340030402c025460b00c46125110040550310001d0660038003020105084540140c8008201801e014445000c20f00246800390031032101c5140c44440c1140c030201031280307941241d01c0c54001c00340080e80d100f496003040080d400c40c0d0107440c0502c0980e8130607501440302c014282e0300a6100364030b60045401900c9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 317122580 1250 317121330 317121359
    0x604020f12030c0a1502030c0f03090c0a030f15051303080a0906180b0a0b010e0111010b0405010609090f0c08070c2a140f0f0f1801080a031706030304 66
    0x103016024141d403000034000141036070b0014045201540c0a012102e08100c4030010368600359443c28400c50071400c103141220000d20400d6444008d4010100119139051814003114010a00007401c00f2a0569640b91007051001500001c0c1c6107030412401c144c090600c03034001e040c8101c01c0211404d585c802903580c161900c007000740100011035170707030301c3d0000000da014450340c1c0c17403840012080070b40c81d0701c5032070544030a510007050454007504100d0f60100c240d81000400d010b0103824240141c0819802c800140148030a00f1030743c1e03003c1e00301000050350980080701c800c241d501000c410301c221059901c42c01d0960307442c02c8841c0700203250b100002c3d00c120b01c213090103e40ea0384240c205400c80e8030700389620144020070807001c000f01c0d03981041c1041016201e0840c0c0d080072400743d401c20000041070340041d000c0c03840f00388400e01409840900c1c2c001683d503c3c03001840305010172440f84141d44c44a42c3e480e590070000c034044002c00d21140c00c8651220404041c1e0780f1420006006500d05814811303201e00703200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 317123830 1250 317122580 317122609
    0x11120307031d010501031406070f020c0919060b0c1009050c0609030708030301030803100501170c21040602070203010b0603040c090b130905150c070507140f0d290603060402 76
    0x681035a10550b20702c42c03c0c001c4134001d600800e0321110310f500d001101410080301074400400d108550020b500c85940216000c0e282103c22104110642c0c1d445800c4403811900e020449012880c20350042401500c4201900790901e00300c00310390741c0109078007080301140c405100251696200007484191403070b1801c010981001e020b001d4070492680c480c0000d2468000b80c000b10b0b10804044104803e0220a80f00500144801d02c1d2400300e5607149140c0916061014115592001c00001c0000798010900c8900e40c154900040454441c81e0a0414400942008400324429401c21050210b0386c6001415030b4007031038000080c3e08080d031030540300728024810b0714481ca4010b603281c000c0c0d6840e0156031003061503039409040600b010000354140398502ca000100101410301091021101240340000c0d1041910200b001402203100d14900051520950800455100c412146460108030400e2140d5070070b030074996030f210403144450b507071444600e404035225501070344808000740251410701240450503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 317125080 1250 317123830 317123861
    0x1403070e0c09010302070b190f0612300c0c0b090105030705070f0b0403050c06010f1d0411062107020703030f050304110a0f05030f010b01090e0702030408030a09061112030703 77
    0x1a5950ba04200382c0307c00c40310b55854842c5a900004500c003103005000c00f0040e560010450503003012124022280d40301c00180002d5213030140c0750248080b85181004001040d508020074031820107004201003a000c20032030b0070401c2d582c4001801c4d140070301950107a4005855850440e03880c1101201da580014400391030008064804201290305041c1c0a0f000783d02030b40c0c659503610118100c3c145000d0b01a400409071820340b05040280d880004440c6405a58030070583c403458440d404e040340c100403a10f003900e522281c0040c0044c10700000300b5204540908402d15041c107550340b05011703130301c0303000d10300c4080d02044204a403400501d01c150010b5512602c500307010200c1000c101c0c0482d00c100995040200105051003042c8400e05c4c0802c20b00503100390a900034032580d00800c000906004040c0308580c120600180810b4490707000744140c2e4058100002129110140f0b00c400070a80e004611602010802da2886001300e03040c0810382c180114100614213140da01c0700403046000b40070980140004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 317126330 1250 317125080 317125087
    0xb03102c0a03052b02070212070b030c1b01050a051008070608060919060b0c0f01091a070207030b0c09090105101e0905120a0303180b040201030c0e0d030305011403070e0c09010302 79
    0x15041c9201100782013100804006807100810b2040c002600c550b000145c2c0380b1350000808000c481e6001c01183e81c846c54a5880c01c1d140e44451410680c0801c1d280c40c0c0c0c80c002c0d4241020071007446a5640a07a2007882c40320402c040140d0b0b84d58035a901d401c04c5000e40320004d240000010607500f03054820300d40018581619040c000d003105080700440e0f007660018001340c1c00000342084624400c101c4142c9000e200c100800c60341d8250307924002034018a5101508d0f4940480010f490503009000b243c004640099100d0214a000405031100303070b01c110a058840c004240005c0323610b0801c0184018000750548403c0c002104080d1540d182e014007412000801015281c00f15194a030000381d1510465032000401240c0f4003454058140c2c0c0b805500301240000c5d2104143c0492410354500742c01c00c3d020308000601400310b04003110a194034030354180c2c0103001d400d212000c01d5419407245e4102c98034065a02111080300b0b00b0181c6401e86841020502e10300a404501d041c18440020301040780c050400524 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 317127580 1250 317126330 317126377
    0xf241a090f01090503150402041b0507021e0310060306110f0d2a080a0608030910050919030b040201020d020d020309090c09030601062d090e04060b03102c0a0305 71
    0x107040d66459100001b00071040a020031400c042c02340e032003e8a818260391a4503200300e540180140a0345601030301c510314041040c0325894050403868145907020b011b0312400e08140c004400503114274407049a889240c01035071030300750418401b42c8510f201380807241843d0003903803c4042c0150513000c91212000b01c10316260050000b0348441c8918824035520f48140a10b0141494001c0320700a13400095540c00c03c1001d03030320b5039840c0d030b011703180802660601c180c1720181003011030005405c05110007118000d0b60340104c01e1040209605209a1003682150044905803004170388038941101e0b000050380c028406041c540ca090401c280d841450782c8002e60410b08043d0019290003001c1c0d0140001c20740080046e4009000d0032249890040d00c0503881c0600d40c04584020a10300d180e12400c10081c100c5400300b401c20910748c00c0960396031001030072a01d050b52690080c000170050801034201140e0200d80c1c510528100303d042006110500020300780203102900d05a800b68015650919040040101503d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 317128830 1250 317127580 317127583
    0x30902030705061c0b1212130f03080c060703140112030e030307060510080303090607050d180606091a060d020c1002070f0201093201030f241a090f01090503 69
    0x802006400c021400744d410b9280010200c80c0103a5809000360014895540c01c1400082c4440d0900e00c0545126501c000b40c1d26101e40c547c07000e400880340c04000c00000002d02046c0d0380648020040da0064030107540f1410b500b50221036240341034144000d10302d00108000310b541201800302d43e00a04000060700f0381c1c0310009080d940040c2d001c84001d41d440c001e02c5038050031020b1000141c1221402185582080c09585030b9070701005010404201c000694048003c403a600030a00c004004004201001c00501e481e10141c201800391461140c074100450211400c84d01c000c0c00402da010780120f280c280c1d00d86491001c3c3d44003807d450020b11581c04640b4000c101031008003a42800b9015103852000188001001d03640c06911031074000d520180c550301a10760790200000768860300044652065509001600640100d00c0112100742c5090b08800140e07083c17083c521600007a0504107805a61202c41c8032030f00d24010320311901803140602100c0200d00b0002440035407802c0c141001c250440c1d40c2c0001030f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 317130080 1250 317128830 317128837
    0x20f06130b042402030f1e031603200711060f030a061410020d03050702160815061002030a0503100302090406020d0c1d010c020d17030403021209060a03090203070506 73
    0x10401840002c0c0c20003030b034440ba0b0081c12191200345500d1038031605954000f5079034040c4040d80c0030201c0c1d002030f14450003040c142440c01ca903641c800380140c1700d10b050780ca004488025001c01c440802e0070845035007440150029500f04070011944982e040c08042e85550f950300c4070f40c101c820703004003082094100c01c2035088080e52280702c542c107010031098104104004007049610000b0302401288000e0100702d900070400c01035569507480e001540f566134200481c6018403100e0319034481d00c900400464010004610744001c83d8169102c000f80e03803103100504c4525a0314a4851005800c18011844003074401e400664006c828900b02c940700715101d800003034240400346c80c111012030307000400e031401e0300150164034404403560070400305403001454900020901040218100501c0741109000c554500c101d08000e41d41009820541d200b0a40c543c1c0342c01e0b40162400c3c0c0c00b40c41000d640040f2204140102c2c0c099a40241c01036040002c3c030401030380a800d9451041b40d240c0a090380208003a201c07200074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 317131330 1250 317130080 317130089
    0x9070e091002041e05061e090a170307060b0a0e010330031407030e10110d05090109170a090e220605150406050a050d0302030c25060e030703020f0613 66
    0x52400160141c444c260b49041e5584024042d0780180702e00c80070000c40103001e06400f01a00305095441032144001030500e08180c104401e1b0702207075641500042c2c0c0c000040d001070752040408001c014191001c01250b0041072140010f04e20010700188001040255850700141c060500c04450b101030000380c5041c0c000620561000940d511410312070160000c500d07940000b030605003001240c800c10030041c0c03144064a4032241403602da11701044104421000c0310385803015464200b056050180d0b54501a010440060b40c1000c01c03071500c90b003400c0c0304901f11a00f0280307503140e00c81c00610b80f01c66910125401010f040100d0500607200030044001d04c000c0c0c1059228003030010305454600019050f603121b00c003c6900452800740c1c180404d4581480e45410380b10101d919100c02046071904a195101b03902109405020b2000c0081241c1000607010700d5500203e5401c00d1031580364034007110440980c83c3c4041d0306601071507080000d402d02c001c024443e1580a0000c1d454212664011442011103510 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 317132580 1250 317131330 317131349
    0x706020a020a2103050c03060a270f1a01021902040c0504030b041208010602010e0a06050606091002070819030c12031b180911040902030a06120b1e09070e09100204 72
    0x1c03010304484e1300d8401d00d0f501c841344400580c00d50a14001090365080d04c0e01801180c00e881a2603000801d40d850140d02c40c1c80d2035000c0621406000d40703090030252000c45c29019146a509421406e00e60000c40c00003420f00480840c0c0c040001590204006065400303410403c0c05410400400400c3ca00070600f071240b400f44032248410052801c0c02041c03100140e2085045900d0170a414242e40f86c04901840403d820287c007180c6516104001500f5102c0c900c045540130050800d01e44405402041240840752440141d50400550030a00e500d14074024400400061100848800081088180380000010303413034002000c118030004043c84d41d9032200e80f000420001070a58413000c440c01d80880250410100500c02d80300c0d000d0780015540030364040e00c45055008800200340003a154055002046600711542106032181030603280400155120313041e000040d12020030204140070f880340038a01440080110360305e44a0700c0d22099a01804031501030080c0710010800304110b0000c0e10203400c5102 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 317133830 1250 317132580 317132633
    0xa0506030705010f050403080c10020714070f0510050a0e040f0e0610030302060c0d020904020a09060314090705011206050a08060105120d05030414010f09060225080706020a020a 78
    0x200340c074107107003907011504101c0602142c0ca4401e6001c810345040381e41c04400503440d000841001030610a001100702c011501c00b052260502034001c540303012501c5d10900360b6103002e4503155480d800303480074001c00d41c000300108400c801c03481c070507070080900048034079045034135100d0340000070251051415030034145130300c41d040c4240503601030010a401c500b9200810f89070303900e1980c003c0e4684100030100f01c140d03100494040e030405d0359501140c51911000b00215510520584003910080a6004500020389840e02890f50300c402c03000034500841609004007900c503e404011500c00c2c0080781c0f051185621754500142030b464003841c00e0050708030400940003640c104804c0c8150340350f88001000080c0d010701304610b82180c2140469404c030b60400244c0c0001d840720003500e030140048203010040e181c902080c1e2018446150702500d04c05550303a0b00352210f044800500d0007540150741d0058940b003c2003000400291441e030080c50030724418010349000100310340f20300013119503e2015841c0d912180 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 317135080 1250 317133830 317133841
    0x70506370f170402010e03100e011d01090b0103060b0a09020f0d0b01050a0c0f140f060411040605033003040b10060309151d0316110906180a020405090a05 68
    0x1006103416000e92514040b642c00c0310500890110340904040e060000c10040319405880070f00c00386003400c002101c04d10404021940c1d05000304111000c2d1b1820103481c1c01e08110707145060080302e10441c6c005081002c5a400c4d030b1900d0b2b005281d00200a64400d510400000c0c45c0034007400600401d404000c0d5050f16000c8840c0f0364016030740026840740c10090100030300251241c110b21030b404080d07005400300015240e94035001c0750700001090032005078070512507122155400098500d2003584a80900480c0d01c02c10070901081e076400c0d000300782e4190000f00400001e020001c058403c0c10048503c024200c6140f07401881556005503170546070b034001101007201200c40030190000a05992404000180054440d8000e4404120804042944502d0440d000c0c8a6100c10005056084010350359a4040f42803c1984156980c50486907644a0300d15040d0300c1c500718540c244511401390000f4044c03180071840008616005140300358450b030038031000c986900d8201c80390348281906400052030342040c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 317136330 1250 317135080 317135087
    0xc1e0909010e011a0904090c121a100909150207050304060e03030310170f1c02060109050c03010303050703030908030f01180908090d0611070f0311030c07050637 71
    0x50b00208540110355004003c0041c011409414818428041a803100c002500141c00b40c1056134014080090341c000c0400c203009803c0020a40c04c0c410741101060300e54401d90020007031021111904c28030f8401d01c01300b0800741141c00c44080341d407144150040680c000421b0008070303044100c050303403260f101080074825070350843ca0443c2d44041c110029421454015200304040c0301502400c007012034286280d0b03165040401c00c140300c1090302c00a50321862440303091600710f009105c150500600c244c3c8000200418140b003250b000e40c40850b03e840c075581c00c0d52415102c0d0307404604220700301960750300035502043c488405540a60501d065441c2c165140810041d190111800310b510310518140c44080080c4001080b07940201c402d980c0300c0b07084000c0f8100f0130000c128059400700082c800041100402c04800b0702040ea052080c0c03134044030200300100d41641d034000c004070804140c2c0144401d002924180c0301a020003c0707142100510040b40e814034030071886800bc407011214440d0780301c0b210300355007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 317137580 1250 317136330 317136349
    0x50c0c070f0302101209050109050f150f040f03120c050a030c0806030d080a0e07030b0a060e0f0c13090207050a120c0804090f0e03070b0105011704030c0b0c1e09 71
    0x480c1c0019540e50440c0c001a42192100d207464081c070440307516184191000c0c3d0412a009600700000304168082828029102c400700755000d11a805604102401e2a185650306e50041042d41e440a0540d915991801250450180e0076001d1122250454060044601881510400356034500303444400d03030700b0f02800741c4806140c1c0009020240d0308005554a00081c600c2c4041d2207890801301c1915000c0c0e024000f441c5890102d03030103018641c0c02005100701c51084602901c4004804c000c0fa503503908800148200c15260100a80c0c207403404144903580200c0a070a0300003001403480c2c8040e83c3da03502c18049a1060b2002c9500d03400411301c18050218014480e1010b94403410003440d40101550351515a02c128003980200a0b900c5840e141003151a52115401403ca001101d070350b00f8107401c0c05207500e6030922607140004e0060f43c0d4400805c03164402c0601490380740d00c942c400c81c54180c0c0c80c1f00d00024000c20b500010003007800000f40582c0c40000084036020005405984d13420f00c2c0003440400314 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 317138830 1250 317137580 317137589
    0x3040609080f030a0b180c0a080a0b0a0f0509090c010909050c090901140111210708190c110a030b070c1103061315091e1514070813050c010e0105070501050c0c07 71
    0x12909003c1017022141d0004844048e038403450881c000d50f42c2d444441005280c03ca07005500100070710008074a210121240c1c0781910710454810b445a07448144507592422002400c60014001c0e140c200b0440840d60041c5410543c1c420b4468101008800030821408090784040c50041c542c1040c3c030050b58100d80445100c50081c0041c02006900e8041541200e41680c210040c003075002400342d0034040d400342540c1a440d01903100000a0f0b600110040c4041d030348403000c1d00d641100400390551890501c42050440358030008092091ba07440d101030f0345a03c0701032000d44011515040c00d0442c2c0d50107101d047d00c10010045038080b01c800354104204034542e1034402c001d0b45486d211100d00410b02d05068010b421309464061041c03200d091620515481c401c01507654614281001c404403d03000c106034074400ca4095403800300565072018070318007901d0b08000140943c0c000c0503d40c10654880c00c0032041841c01818424984261941c4540c01c5800c2110100f410031408100c8403240d5030306110600050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 317140080 1250 317138830 317138869
    0x4020f040506210703150902011206060c150209130c0f08060303030402090709080d0918021309020906090d0c2903010b030601090312021b0d0803040609080f030a0b 72
    0x625040001c942c00c80c0d500a5080ea00400243d1600e00300241002640080c55110a240c0101040303003485a024100341c440c100d002c199603000c003080c01c203806c3c410102145d00300da4515a05211544618003100e0071755110200c80d03902046100310645a13480200c0d2403c3c105440080d900c98030580090801446020030b608012620041c0900b5582c000103480d08a501280c1290b5280c0f02d03c08103035980d0f0015805000302c0e0191510003102c403500603c030782040b901c41204032030425a1002000f8228801c00c91404008085c2000c1445a16440d6000d0145100007400e400c2c40c1040e044000f070b00c1c0e509050b000311b8450b140314a0500103142111000400710901e00130310400e101030f00410001c00c0c00140100c17043c2823000300001c5c42681c45410040e000b07540095024041d01c0e00310364002d407100c1c010301c0c980401030051070300000c9909021040c20710041d0004001360460300d0382da03510300c00340141c41c500340c0305840c0900c55418000441c00045000300958240000c420008805114421401c141100c3c6030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 317141330 1250 317140080 317140091
    0x100e07080105010e030c03061503070e01030507060207060f0c06270c05030c0109060f080403020717060a1b020703031b06050903030f0c03040809190b040602010b041b020c01050307030e060c0304020f04 88
    0x261000902300d604121080e00031442e811049001c0303031804603244e20013002d651103040004103000780415500151031042c2d0039250941c1c0c4406080e22020401c0301d6803400204800322030000f09100e07500401000307580051034202500c91b40c0041c3c10603030f040003013903a800c92500382c1000546401c002c02203040e030342030070910400b0703260520240070b080d880100d550134410507500103070415100b0310001d00a0050041c2c6030000424001103251341c6c80c1c0c1244c2c25455185032a84169a0a00c1d148400320000c10a500400c1a281565022140094411581540c00145030201c0b0002000741c0900d9201d10006001035480c0d10b01894402c200110203002009411810424000410200c20032120541000d59104144055081c1001100f403901d5209040f0040e01080114403580e0640010b02c07001d104482c140841001c200201007000124008500564030854003845d295004074007440e03005400c2e0031300054180168100340d04002c02221b541075648000405c110852501c0440c0003244402a90108071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 317142580 1250 317141330 317141353
    0x2070914010e0c0f03070302030402010e0d02150a02011401092012040f020d1703094c0906060518090c0603220c050f0904050c010503100e07080105010e03 68
    0x2515406000b64070790360b01c618000855109042040701c0703058151441055883ca0f0500000f0b000f0b400507078049002542000e60308c4198a40f807a0042d0080c0d4004001c03010802511540c21415800300b0805001d554840c1c40350080880c81c556004d00800245001141c00c0c2c0d07926142c04000d40f20045c507858010414400b030760019603130581f45070b8865440150041403562600000760020001d0702d004110503400002c0030402904240030b10f0140e60010708550038940c0114018201e00740200c0014403d10701c050003000744041d2a03440108103e01d10400f901303d0800c4102100c251805400c1c1035032141c0c1c03078540c100f200741402e1000ba0141e06941c0c43c00051401e00c88449500c682c03070b036840c091081c5000300101d6082c4407440504400039480e10984100b400f102c0c034044207207001c0c911030244071f08001507055042c0d090100d02544940c1e40079001d4240140b0520040d5210f0b040a800d4242c116441c41d4081039800300c400742c4074003800d0380303486803203c9600d00307030004024003c90350680d030007600f08c0301c68100b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 317143830 1250 317142580 317142611
    0x40b04060c0602090301050721090302030f0a09050a08060f221103120c0610060e0303190512071808070b09010c061425090608010315060b0a0f020709 66
    0x101611000d240500901181d401c080300030340501c0c080c190381540303402d09100c0da583d000007245004076459800c0f0f01c0c50000300301101048401c0c014000d0b003d44c0080145400e8690000c0c002c1c4000e403c58100908825203030004600030150ba90083c00465002c00300b030284c4a00c800300000e40c00100c21038800d184890350440130314812000721006007c3c001040d141d036042d079401d2058884002c030481095850702405010b01307642c0c034401d84000356140941c44022814911a603449000c035500507000714170381085d807601e00c40c0c0b041802010800b0041c0900c807030b1103081c1d802960140200c101c1d641d030915a1006036108021480303103030710500d010740c0020410041c451105090700c0c00325109091020401d40241080c10280034000c8000c50004081c1040041c1d1489001c01d416080b20281c0200106901c0414282d03610191401003601081070440100001021000e031a90b0502d40c618021445681e20b007031020303698108100d03c0002c1403111980d00000c0b941001040000c00e1010402e000a400945104c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 317145080 1250 317143830 317143837
    0x50a032c0f040504170f2d070b09100f0621020a060e0303070501090f0515040c05040504020102030c010c111203160c140a03050703140309121c060305030a090b040b 72
    0x600883e101c0c4001410302030122405246a00d0640c2c0303d40e81c0d8940790f0388045841d40140703104100d13910540c204400080e428149058448404420389280a12903118070710869002000030481d407180f1a51410300703084502a00940f80082000880c03821300348030710510280609410b01a10a082c1c62000300980e50700c040000440d01203003440713015210000c0101c0e0440c403480701c001d801c640c01c10280c082000a082c00d1408a0b80c010001e031140200d440f1044403502d6000d0314083d00340758004a05001900d45a4800d83e002841401142d1510300004200da080d01c003080c81d60400b20b07100e030710300c8910001c06111400c26214882c003c903180d8505034507880040c130640f580f08020410003003417510800c00b1000010300038082480465400c80b0702e5140003496513001600490000d500302100151491080d01901c2c0191480c074013030080c0c401c1c51480c0c010395400c0f102d4941c64104003511103400009081c82002d010714000e4015607951880718101800240c1c607603010354081d00003000100603144000c0309a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 317146330 1250 317145080 317145109
    0x6020d0c080a020109080c06070e010212071209090f0c0e010e1305100f080f010c09033c03090801051302100f1218020f0406150305060d050a032c 64
    0x2050b4803030181010490042c000c0c084020f02140d400685c504c896800011031604c109220350704c80c102d0040aa004a8803040f0703001081004002c14810900064001c554201c0f6480c00703072038111106039540170450261402080c441d840140c4d5142c901c1212a0b1003080014000400e0a01d41080040200802c94260341000d140c0c110590b070300007051045400d54070000050400b035582d209843d850b0a0416140d0707883c200100340c298a0840f02886690045210004480d0014005040b42280004080da4203820500d0200300b104038400d400c214007030349100300403013600a650f400c101c036003040c41d2207085420181c012031501c0031005034400107a40346a003000900c82c1d140b41c01445081c0c1e40d482a01c0000c841134007100164100307000158030960b184010041a4021035080c04140c4c010704c2400b003102c00c80d000d024400512041d00124070b500980013540c201401401011030300c02d440d20744909140107490110001072000350580301c2071815621602412020751101c8000b0a1080700080329400f04904 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 317147580 1250 317146330 317146343
    0x140f030102030c070609060f0203071e090b0319060305070807260c060a0314041a0703050426040e090a0b010f0501050403020d0203031209161d150d08180a06020d0c 72
    0x200f1004200942e08403810346d08ca0004255143d06003100302402000d1174000710078403221401000107541d44290014800c80da0100784407451034071740031480101903030000220315040384ca812001000810400c43e0388002d050341e1009c0c3c0b50903400e0048a403001e1241d501c0174444141c000342c80b00c0903503402103128000110200d985d1303503070343c852200141e0150003800c2a2000300c1c06040300304400d010b00100041410010141110a20366502c039007642181c00655014090b035044d00e04458070314409003482e07000030b0b2158009074100b0b0703901c50400100c15011110ae000b190800101e200070410000505070150194080c140440d80c02d0000080050066210282c40b56042c6400502551001d100301e4203802440d46d910001450411411951a400358119900d0305030380310740c00070b003e60491001021114088440342d0068459003d01e407807240b00d40c00250341c0070000d105041c2c00a2101d2004103201c0310420b0100b0000c034003107000c202604e01c44c8c0d0301000075900501c8109080692200164101d50340c01103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 317148830 1250 317147580 317147591
    0xf02010e0705090402031e100f020a0f030e340b04030302030304020405100801020a0f180e0c1308030406091802030c12180f011410060f050c010b0a140f030102030c0706 74
    0x74907103100c3d80c001800c9003002c80004d00501401140b06e4542001400042c440c0c0c800140d4803a080348142f0581400060340341c1d44410700e482c0b0a412403840c0011100481d43d500440008046c0c81c1030741003032484080591200d100114003507d45088008210440b00d1500b010b01e1038034003039120301c0000c0009100b20b40c0d84c9c1c00504212a40719081c2d02030080d0318021901e8412113480075042850021251010410344007062304405130540030079003682c81f031084001c142c1e25208445002030704840100c400c240103010002c11049003c00190000f40035035512901c87c80e180c140480520b1140000c0c490116004004100c124072144044544044c404034202c915582d400c0e40e991054202044003134002d0040c40d00381140d90005400110f205086980364901e540ca40e05030440e5404024410100454503200241d0b01c0340340200060b1a10002d40742c004900d6a030420005650060175400800c02071840070314140950514086255900c0303001d400841c0303182032245c0042e8040c000c00134024138140e10355 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 317150080 1250 317148830 317148833
    0x20607060203061f050d140112061a10020d0906020a080306210304090f0e0102030402030d050a05040504060609090c08010e22020d06062c0402130b12010c0f02010e07050904 76
    0xc598060720040c80450a04035044c0300002c2c100d40c003040030703207003102c2c1000d0403c24002071070a138090486000844450100301940d803038602425152003003a00d00c00b02400d0f20000c03511064081c0816188907070140201c003441d00d0f400351000401d900541d08551002d00c1020018586800b2a50001803c81c1d0f401e10b402c032030080d13540800102c0c0c070181845000c0800c00281c11101c2e5005041d10701c100744014803c110a04840c0341c201d00040380c0c0698942c2c0f0110200f1001c901907802001da0414a190042c03400d621040890103943c44e030b03449480060864001081850302d2031103004290507a6180c44400e5524040c00b0444000b005010440402c42030051f404006d482002c05194596001d4a466001e82203810080020141782c4103018a40c513080c401c0080c0c82e0051810b4400c05100d8809208203510f440d000d1082502c40b241c01d10025550302c0008001d00e544401401002003e068008514440d4600004000707403580e580c08000e5a040010f400710350000459000c0c180d41060310500308c02c0c2d60b507 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 317151330 1250 317150080 317150089
    0xb060405010804020d05100c0306060e180c120106081e15090901090b0f07090b12070c080c0a2004060803030103121e05070606050f0d060f0b03030a0203070203160302060706020306 79
    0x1944001025807058042c031f410965032580018110b01e103075407401c014099860509441b103151013400d403544070f42e03205410050000440e134650381003000c18848a05111b001c6000a039490000e801c10404111101d0401001c0c90b82c8001929191011190b030480c241054400d40001c40580647c1710320440c80100001c0341d49a007540300b0303421290400c0d01082241400c80501c1d06060b002d564400020708220750111f480301c0d00e030341140c02484002c2c00c40b01750360b035950074102c2d188018040106c408120410094074030b101d040020703018203406820b200c0c0030744095006840300c819124060900507810b0000400c4605000b01c2031307a044907088039080e806a88500001c9900014107641c440b02c0d200c1000011850942c004050548175216000801c4620740350170400c03800740444002e407a80702c4801d05080001841c0da8126450305104010b02195003540070000900b10f8104001103001617001040034415443c0c10050b900241001080e5281018110b4010490078422010081c00c40c980000100711543c80c1c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 317152580 1250 317151330 317151349
    0xf030d060306060b070b060103051f0f0e010602060415021c060602061807060906030b0a030c0f0f060e150c0f011d190506070c1b0909060b1f0e0402041d090708010b06040501080402 79
    0x1207074941004440d0b01c0ccc0c04140700c02c1c0d055000d00700c0201520b130008680c540c00040c0d0503020340d0304a80c09155603040c0b2000740c4060b51281403030408500e00c5001210301c2c41c0b07450049402800c80350300a4442450b02100101080c1c0e0300041202550388100410016036401000e514180e45c0c2c2403501013901140c607400304005002c154001060034020038000142e6917085e891641c1030343c0b000501c144400d955241c040b40e003004604ca80980c00020000a0042000174a00409682401c0420789240e206c501d0581c40c00c4580a00c41803140300400c440c0b01e00c440c007081c0600264114030752803140140c2a20f071151641c44100030400f04c107110380700060700c0c14401c0d40040c01501c0c40040c0f48090a1a40700d00040c800b03008280c0b02291840d0400c0d080806500d07013002c03143c11002041e10011100c1260385000c4680500041c0c0d415040b81e400c010218100c401c072915034088c40000800340c1490305000e181140f070644c050384105040d0749026040e000e296100d01c126000c5a0302403910507c10740f590b00000f00b01c0030703 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 317153830 1250 317152580 317152621
    0xb01030603140a12020a052805010e030d060503012c0304170d030b030c030a081c06030f030806011b06021c020a080603011a0d06020a020f030d060306060b070b06010305 74
    0xc2c58aa21000ca00010b10904070b02d12031104201d420000003010390b40d45560b581c005100e80c115600c02102480c4160308000943d05420040f82030b070100752200703801c449140390341c0344071500300003a04103244089001e240c0042806400030440c848050707085e401000608180c01c0c2c00810381031510082000700b0010b0f90054256550341100c8071a440a416035a00d90403120480800d04048154030035103000304141c064084040c01401d440701641d82c400c0701940c0502c3c18078001e40c4101c2141d030784a09851245802451242c400c89669a45504015112500c000c01d040c0c10007840d01245458052074514490303010b54405c01c00340c0c8480c0d0030700764400700f8589a00f04401d29032002c1405a5a0b07075012100c140141d00580c020132850711005148001d90344150001078010216824030000104241d004080c48000da1060394584a500c80c59a411a0f20142000d5440c9444407001d000b80701c594825a0010040b2003009490038403650f81c3c6007071209009080030306141d620000070740703c500c10620000459 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 317155080 1250 317153830 317153843
    0x51f03031b082701181401080a060801140618010b04140a0b0703030f0c03050c2d03100f0e01060f081315090b0c0c07120f150c030c0309030f030b01030603 68
    0x941c40c03002c222030f605600b0480c40c00030300e182c0b082e081d0303980026900e0410745400030442c0010203418801135030301203400f51021940947d14000080c91020030b1064a41115242c0031805c81070412000300b040340480c001325041520092001007058041030740458044400c0f01054540413a580c000141520540b6400703101500c00c00202081055410f90202c02d4024406804024200f84548110111a0115031080800d001003010031894040e030903030700005a001444000f10b4040086126001d80c0040d1540c0c9043c02c69044180001d0904011210150013148110343c00c2e5890980000c2400042440300c5041c00b403000045458440d4021070001d90940010b031a040c40c080d1400f001c0010041da0b142a50f20030030400105e42c0d042049822039114669040060003000d04040400403540d02c6904200c4444041400020006007400352487c689203006100260269004002030b00b034640c02d407030382c80c01c040c41c25200d200083d0b0400e501c030f00510514a00055001d0800006a0003040e4640001e003c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 317156330 1250 317155080 317155117
    0x50f1509191a0103140103120c02060405030703031e08090607050304030e09100611031c020c030d051321081f0b04030602040f170303040605190e01051f03031b08 71
    0x840c0540440b4400c040a90f01080b4003040c1204d034400401c000e000003400b031080101c1e4004410321803140c003058540018105440d00d907460001a103480141ea2048012810f42200f003900f052018860141c003400b641000c5100d07180c01c4070080d440d5000208050103008011000c40c0030305109a0f0411046030001d007a076042820840289440000d842c4640c0001405040800a01c600c0100958849040d14481e2014407080030a00300003a400c00e5610004621040c081c410840c0e44601805001e41c60b01121217007914814285030100405400052071920a144061800719502000d00c9a025201240d8a0103640f0203550700690500603074406107143c50085404801d0020300c2e030007001110780c1c00e0504000c080e500e03900210b080740040340900082c0c01c10700001d004602d550300301642c0207442d50140103806400d8440c01040f0740322514000c282d03070f5640040120540c0000c05450a40a110070580300d4140b665078003c0009001301111040242d02c00050030400c18004281c4014119040a203500c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 317157580 1250 317156330 317156351
    0x90b0a120e0a050d0509030c040c2f0607080c09011805100908070e070207031103070315051b0f040909020d05030f12010b0403200118080a0204050f150919 68
    0x58450682c5001d0fa414001d0320346a8880f00c0c0034500719800b22901802414a143c0d40c01c04120040c9020500c0e102880201c1c6a230b20343e8000f400c011034044080303035844141d03001c0700042d4061800d88014911800d1003113000c10b00051060250075115449402d20301041c410700c403a611402c0310235855004603008000580400d107195048000c41090f1400704040310411a81d0741c06403844410300740c3c2c207080581c20100703041c40402c0844408900340702001e002c03104900d59903942c040e12151100c09801c5010359410910824100c01c1501044c01200084114108014600562703214807491040150b0199640d6041c0110344610304105c00d41600802629100c400707444600390303a948072075040038807280b2940000c9101402a030546050300d40044407199039140034019034141461801c9614140000300c4041080e1f107030100384100c080c0500e1009055440310720310501c015184080c223100b003c10b07011030401421100f10150f040b00302c201218840c55507154220b0490701011b1400c40811024101501d421 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 317158830 1250 317157580 317157583
    0x40c09062304060302010f080a18060c030c0905061c09080304051c050c100c0507020d0507060e01261801020c0d0f1e03050903120406090303050906010303090b0a120e 73
    0x10804942886500910100034100803c480319030000a02240070020141010342c0b107150140d600c610030000002e0b011105e00000d17001c450030890201c601d55200c504984545903d4020101d5104c007030305140c15901c0c14100026014000c240102c0d0b0415a00d01c802c84803000340c1c3d084820103a810054980d03407402d2900b04151a0315a08800300c025034040007002030f00d2403154045410304ac0740200030b080344c01c0b10030002074041d16000d10050100030051080c00056a2641c400504691060000703045040c50301c070014209460400b180c6040c422003040c51083e45084450380302d108031402018100315511003554011202800d01400c0a40d840412003600200300018034071000ca040d0341f91036001c030715440c10460b1480c0a64500c51504003030300002002c0107000340c0140340c02002040c243c078100301054100090311b4500320f805aa090352101d41613030526805104c0d5603084200c98000d00f51315030460302d015103000b24520a000034010700241c03203018203108110222081c41c5148013400195513002002c0d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 317160080 1250 317158830 317158859
    0x6090a0e150f03150f28050106030f02070c0306090620090102010b0405090c010f111519020c0a1716050309090702030a200a0506090a030e15030f040c0906 68
    0x5018410440c40c050b02481e0000d240c440d145902401c45085594820b1003030103445001c0c20034450070301606034082c41841d00100d0354088034103441e400144c9614010340241940c0e003059040c0d8003248100070840120b00703465859004d41e600a01d0200344000d042c41c1000c000c01c10540000085102d18a1700c0385210040002000861003da00901c02c8004c100c040004580040c0c4980d80c5030741c002000c50320554059206c0c4a0b10a9550411415049442c81d0030b500705569003420381c1c2495202c0d810403c05a501800d8480c441001100441c01c194402065031f0340c50049101c080c0c520743c10700034211080c184801c01c81d0301102d107a42c0d1170030f0000000d00d040360341e079000501030300d11900042d000a04614800000c0e07450220156a0b18914160401d40407031018504050480c2d02e806544030000224404103d15400303083c01000070480007180b4100100030075103034255140b20b0b41281516071f000380d51102c16290481c40c0700c41500100d840d189003110141c4401e0348042c0f0850f003003030f400040900200720300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 317161330 1250 317160080 317160121
    0x3150c0409290301060612180b13061a061c060503030f0703021b060f1602061b0d0305100902030a0e0708060601030b03060f0c030c1e0d0c030b010e06090a0e 69
    0xb030b0010101940200b609840d034501404000824042000c040b54020350009044041305603500e07168a48681c0300e1255400c404c0b030300d81c10505030190081080069a110f08400200340075a5010345140e40c00020301140f080201198038941610750048103017881e07502c2500106001001c40399035140c0c04040d01c0e01900b1290083e03002d8011000d43c83c0900115a0040664810003480d003442e0480750640c1c211160409022511350110303507162440141c42e480700629050341031440700f40342e81d60201d0426141068501c560360815050100b0300956007070a0801e4401c0d55284000561a030f503403900c52074001d18030003e0701c841c58850f01d60000b42400b000309403240951310170790f020700610720200b09156076860241e0b00005042c07030300c0b00007a21580d540c1c0051500035191108091610760b14130603c4003000c0c0300d41c40960410100185a1081000d288103109807400c5904080c042d903561140041c00c6090940300c03081c05102c0004140100350b440ba44901c018051040e0b2103261801c02049000280302444603 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 317162580 1250 317161330 317161391
    0x51312120e09070c0b0a0b0603090601030c1706011505090303030406050601181202060306010309150e15011409060a170a061103160507050712030206040b06010e03150c0409 76
    0x41640c01401c103803852502c01c10860b291040070110941d071784a078004004085130100c682c0c0c1c12900500e41e81c2c290049d0300461003000200515419400c088040762250703030120348104406c0c142c0c140c41000105889045502034080070481c50000c94007a1080d00c80e5034016503050000000300030803c81a540524010142030703913540700300420000188110755040c0510360183c400c086207240189000300045600c68030614001c1052400c59851200480c13891702210703806521341c1626100e0349400c00441c0e070350741401e510394080d40d40f4180c0402c002c41c4d184680580a0009a0300041d800e03110030000c3c90042c041043d0214102d400f489905803034946291045a1300307824084030081c401458404e403801003c544110201c115030240c825180e50b0700c007020485030348c040c028000800d440103200024005010f50040d004c9480c0518005228000003000c06045c480010340c8819651000906102e000c0302ca802c1002098882c20007080c1c1d81d00032a40b250a626090035401421342c41440c00008510b5078484 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 317163830 1250 317162580 317162597
    0x150904060515150c15060a091e06080a030f1b02040209040e0609160e0408041e030510020304020405060a0e07050703020f0d02031b12031b160813060201110a05131212 73
    0x1028a4090319003584d0711640020303032990911041c00e086d805180d0107a00c0c100300c90006827040c06400140c1d00715a101c2074a5402c80c040304024550003000f15070709021281703170510311407616560004012181d1080640a00d9020034820b0392506c0d613a000e0400f100d000c408844042c50405a190381c1c4030b540700c1d01ca0340742c18113144000032003141c83c40d0918051588120300c5428942003848880412104119200242c080060008003140c070030f2042c20044903034664003586d80c1c0b61a00600043d0340740682000c0c003414159408000c0540b00114054020500d032814540d64090f5045c2245002000c49045800b4060b000b00c05201c107800000030140b00310540a81d00008440c0c10032280c49000d1a880c40340081c00810005280c0030111181d1459950b03c08000350400c503030300c030f0065003a6440c41011140304900017071490b1a0840010740d40010500c0c0d10003030021400014019a06000f04401d070010711501050b2124905440300e8600050020002c42c10300b112100d0a0070300c0c40c2030103107402c02c002c940d881 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 317165080 1250 317163830 317163853
    0xc0c080313120209060103050705040306050108012009032805030d020408010b060a0804030813060e0f070b090d060b03120a0302120604141b090307030c030506150904060515150c 78
    0x11042c48a2854008208025960383c80006401408000f040041041810000400018841c0c45103d010f05881c0000044030000f1100003441810901c509038642101400700092581c1e000500342020b0540101103039003c40c00414200b2800c81090000b003c50001141442c2c14090607809081141d409600a0150b0040d01d0240700c07861051040100024180e440050b010074002c2200301d401050301c20260400e101903440ea2021115009800340e0b164101c2340340b07895071460400140c0c001c2d00110500d24940750300400040c8032038008500042c2806c1e118600002107079000d106080c00c0c040ca440e01240d848600c02c90044c025070280c0d40e050800a1800081400d41c00c041c410052920f01e40c1c007001c0e00984911314101c440046072780b0119101d540401c80020350352000e1005a008511034400c07580764900b545811810007000410041e1942c00e00d1314250125a500701220b82c005400031000985621a15600e55107081030a00c1c86411035840e00c0070025042088004100d40752a600658030300b81e402 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 317166330 1250 317165080 317165099
    0x303030506150c0d2303010305010516020105160e032104090f0603150207020a1505091201020c062e06081e042103230103050f06040507150c0c080313 66
    0x1010820801d03507210a07003442e81d603400342c00c80c030494605400d00b407288178448072640101640709805c201c90031794491051201641ea441e5405902554900081c4200e1a201102c0c01d512103000381c825040100200310413201c0d45003401600c280003110b0405940301d001e82c00c5444059405441001400345c42e028084844800a01c10401525800031016607483c03541d01c104000303034010348130031307644503108040010b440c5107041c19025a0000580fa419200c04010341000384d4040c44d01c0a512190b4010821440301c240040350701036000700c003c000d00540782c05041d1a0300004d40115841d0513002c102c410089a40740d0001c0f1494807441c10341146004401d4208555a0542030a4400a08a08500e0000c0005c458003480700c040d454081c2c9000564070141c1052000001181c076245c01000031203800600500c00c09001c81c3c1ca9260021000b008141400d580e026961411842260780c0500c0c08035078a00c41d9880740c581ca16041e030b0441c108070801d985420040f44c2301d40c000e812005190040e164009001d600 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 317167580 1250 317166330 317166337
    0x180b04030627170304060b090106030b010f0305040f02210106092702090f06060702030604060212060d15021b0d0905090a0c0e0f0d170406080601300b040204030303050615 75
    0x42c00043c50041803c940101d0890b81c00161084406503110000b4040c1c075107940902600030300c0c850b500800c450343d035000050102052039040c0000c240c02c1404000c0440c1c8031001c1d903094590b055881000e66070071800350346006800300c45442d98030f50a01c3c500040003882500211103624035080106406131622480c1203000c01c512400940142e540d0300003e00785c0b1444c0a4030366114030054031542c908020b0341c1c0040e0412100301c80840e0090750102e005000d11540e00c401503400001a200625506099194404800340d1030307590038940740d000641d4220840750300c4400d003400310100c0100c40c000c40c0d0504000c0c00d0504980170362801108030100203101000240200701d550022078556417034200a204c02d002010a000d980340f5041020404450000341003004111407118200d19034944850030444001c2c002c0d0405840c2078100440c1c08080981905a4180050711320f440060a5868802c0000314030041c1550522382684540b000c5070000034960144c014520500b0f040b50a4824000c1c1c0800c1d1100a00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 317168830 1250 317167580 317167583
    0x5040e0c010c03030605040c180f030201021002091305011412161202151c061508071b170c370309050618120f030a180b04030627 57
    0x103100d06110810395000e9a041c0d40424064136012400da51a44003050075601084e510500003002c1144640d000740480400b080070b081142484010203141d600001d5490030411a02c3d04850340c0001c0d42051643d40c012070b41181100c1400500280da515004a14030300400d14102e8015403103880e540c8090302c0c010816615102465080740040e070301b000c07802d40d030f858413400e01242c001c450100003460610748800682740001681082c20124441c000c0c500d000c0d581a58490040b00f00140d030106c4c12250000e029036404091460060382d940d054070300c40c160254010034044d2400086078009405000b82c000100b0b04410b2000c21501400b1100741a0025100c20f045064032803c0c25202c16001c031300700c0c101360000c128040d00e09900801c0d100c8001684135448501c81034420b800031542c103801401c0c0107410b882001780344e60181c40b0600c0450302850b101d00c078100ca00810020020f032140e11002a00082e10b0140071141011a00c1d507880780f0704000140a21800071840d0f03400c0342c055a410380100344550701c18a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 317170080 1250 317168830 317168833
    0x1e02130501030b010605072d020123091302130b03101a0703051c05010603020405090c13090c02030f03090f19031d0a08031c0c05090303120a0b03060103030207050a05040e 75
    0x1603182c0202141e0942003030104850340304a010200d8182c81d000d0303900c08c400f009203511a0005003800e20014214007005480090440c040034414154484100d054516a030400c0c0d4510895019044010340203101c4c40c2040c00c104c804192010480303001c08409184500c83c42ca18026030140c460310030340d1518014100344032482d0003c00000d0002441400603000508040c65a05400c103480c0c41100261207098002c0c1002076808907003001245042c1c254143c10200c10040c5070324110005030807600c601c00c02e0003801e03a259141c41c280900d0314801c004445100410b04061900c034184502407507155212900c003880f640c440c01c030740c0f4011000b01344814204941d05884030110005000101803c14480003c029801805002c00182422041c40245051401041174800c3d00200c044000116940310452804212040c4128001900d002040b10701d144820000d054003595400790000c090207500021503014003c1c0f80000080507000a40c80f0240c41c01100c802c03079025110070600044500c00c00120455 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 317171330 1250 317170080 317170103
    0x20c0c1e150a0201150e040309090b09060f130f090b010f0501051b011503140d0819020d020706110c01060e0c0304030e0d05010614091b03010e131e0213050103 70
    0x1440d0350078018031100c9031030b0001050360320001844800c004000d9200480511102d81048101a442881c640c0a02400e10081141800d08004070796203860040c043e038000c40100a6402d01e0780d8a60300f0940020299510502c131214140b8490701c00f9003182c1c0401c8454403c018008200f141008c86100192035040c0e480b9400c2004082150328094507070104000c5039562015881d040b10603404142003d1030003485060000c901044401d40b400c0944c9102400b0000808188001d031309091281c000070096982c40940c0b510074406240300203218500c0002c04a6182c45100d40c45400f141c000381c407211131014001c101544d40e4084209803064115081070081204000080009019425404019401034403190b00c525880d5241e50031601a5003114500d0303200e8036010517113441c0c51241540c0c40741420a84211485403808403c009000c10700900b000e0181c0e00c000215000c000c0d1105500030750b0025420054030030701c00740b030304d248071000e880690080034a80d401c001513680d0750040c14100c0e5070040d000c3c8036 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 317172580 1250 317171330 317171359
    0x82b02072f0603101a03090d180510050d02071a010906050f0d030509130506040e1614121606080f040c05010e120609070501020606030616050a090504020c0c1e 70
    0x242c0e030380000d000c8000032100700c001240b20b104800e80081c2e01e803008121541e407800c1480c100c920300300a01140b00200590b00c2c2c502e500c12961020f501781101c1c402c1c0c1c1e00c085400b07900030342a941801001d144100e10342c80030850100348185911032031203000c2501c078502c00c80e03602c0b103203168151526801900c1d0041c00c080001d0300613060280d903000c0158040d181c428106560800020040c00f40d038188010345940300d070180704103481d044c460042000341d02d00c003e00150103003101c244207140705032090341000203681c2e50802c01a200c05d482141070021074811303950300301005400ea00340100103014800000e0320520016400c00740090055000300e8107d4041d052040c5000b0044034820325a5200d160810000d4414000c1d4040030480c42d170207042c0d02c0d07001d402039600b4940024604100140058030aa004800380303c43c1d00440d01280c0b01000366454015910b04c488282504c04d1035555100c01e030028400a40d22000540228041204000441d040d410101404c3c283e441ca450060049940c440c0001e9181b08 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 317173830 1250 317172580 317172589
    0x50a150518010509040f0603020f01170f0405011104030f05120a020c132c0f011407030908070b181c09050409020a030602040308041701020412082b02072f 68
    0xc0c8001e205142c03c929140e0f400c0c021805550181c11000715880c3c0700e4100344110300d880883c81c0d04008003803070302c2c4450440e0780b000d249074a440a03095000c103100701b4000ca01845400e420440040380348010325030b5a039035245003041422032050010f40c1c2d54000c7c8544520007088203803c0b00c0168400d58002d06944402c6d5041007507030740c2c0310444c02500d41d940c2c1400d03a8002481c0e2080300b8200381100c000310800502c101d030342401c0011f0681c40c0340490745445401d40d0b00d01440400c4940050007440c001401c04030380d14022045124040028000b0003031a420003058404205d0310040c181410300680d01d0b0b1403202c0c4400e08104004148900106140700360900003420603920850b0614001842116542d60301d85132481240d01c03e800a1303030800d60000c1c1c14030400b0400d040f80e210042920000718941480d013060000c4494075040d005089100002e2003102c0212071040340303410481c00b0f80c148210b031550001d0307010003580010404c480e0f109a085000400c5074515000c00010f000c42c28000d100000c0780401c02 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 317175080 1250 317173830 317173867
    0xc07050f07033801080a030801090c080c0705010b1c020102150906010603180602070305130b0408031905130603050709060804051005090307050610031106090f0909010605120601050a1505 82
    0x31428140403401400e00c460b44050f040c001c04012016107400b4106040081c0580c02c140c000c29055030401c00740103940356104e84000e0b4840703c1c010006442d21000d161040c0036004610590364030561342030a001e81002403451402c000c3e07100360225a80341203010070744508100c0c2110462015007104004010250194101107010705581d40f0115202c451030351503c1c100d810004007a000a01d020842e8200e01040e105844041c01101c003c02e41007034507143c0b003603503203128401048040b00c0c0717084800b10a684c021002c0c1c4140071103161030101d4980d101c1c24010014002262001c1c0081c0c0302c400000303803050040c0d250307500441e0088054804001440c51160141001400b90140d07407000f001041c01040c800e00c0218016041400700191841c5035081000c5015280038030340e0301c200d504028100f11540d402d007907480320350020341344501c09075120100c80780107000c1079010580144c04444035100d000743c042445c606880044803c0410145c41d00c0410720300080a1a032000407400030400e0713490310740120260 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 317176330 1250 317175080 317175143
    0x140412020f070e1e010f2c0a0905010609020913050c1608030a050a1404120e04020d06031703070c080f070c0b0d0c050a0504031106040e0c07050f0703 66
    0x40391400c2003250034682c901086a4441d4462641c04820311045000d940c80b00301094420644c040301075414120210b001d413410b4850202200e048034944504130720000014445c40c01c41801d09102c030710340301c65440003410012104a80c5540b8201e804101c2020354402c3e105c03904c60141140d41100403150741607008080181024801d00c03010b11125200070002c264205820744074039600743c0c40e030405e01076981c25104040c006403161810310040c11984008000c0071540540c02c044552a80100d0290642c0c0b80c801c448081074005000142080007505146c203d001164860194034a4142d03d9a05800c0381e4081038488000050f070a4105070041194400a800c03000710211a80c0d140010544d0784585003000c65124040840d0040b41351a4988400e20904191100c24200329162603101d0400900c2440f650100134000c451904408005490f0201074901500d211507100c0704a00b001c00c00403131107401291040750984114075001d004200041200c1080342ea0201d001e00204030460080d140c0c40082c03000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 317177580 1250 317176330 317176333
    0xf02010b0915130f0216060608030a0c0602031915030312050405150a021204030f0e0d050309150c030a0806120f06060607032c15040b03060f0607051212010914041202 73
    0xd80704d0700e0fa000c0d40700400b00741801080300351180140c1d281601c1911103550141280e070308280103440c480c80d0005186c04100f0340c0203100503505d603a40c1040000300c0c1041c022803000c0900e0203000307594141240071520709681c001d80340c8084441c00001250151041164001c0140e0801039034400803850b91000650446e5900300c0c00b6082124100c013403001600c0840d0300b640000d00000c02240040e80144003401812015910801c103590b40b52203c03507880c4920b60300c59010341414401c0c2c140740380c8070b01e003694010801d40040c1ca80c0c40c00b103410010030b050320540b1810322498008400702101c141c00542295100000c10141409a440004118440c0c10400d4240c042c40882c9080350384629402841c00c85e05144003044200965540040c80203901c12504400b003c450300304000d020240314042584d50020040311803444004800c2c0c00310300240140d210007080c0384100700035000841408006020300c61070342d019410050703036146070210544551035000c000e00d520600200300032841c985c208910342c0c0e05600 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 317178830 1250 317177580 317177591
    0x312021504060c110102031e09161401031113260d080f07020a050c09040303060f060306050415031101080a110c030d05090606090c07210f02010b091513 67
    0x14058609068201d60455026070303603005801c1a242c01003142c8044000d4035000f1030452601d85245124086040c5107001400a0440000d2400310200101c101c1010741c85000398030150349040c05080d4940b840001400301e400c0c041140301d028070781800e40310080000203c00140300d02c2c0403074011f031801000402130078284a041d902c104240702080341d003810076600c0e41c5060083c03426040952036240040e06200440d000604414003281c0c00107031b405c080b03000807151103080352107a2a0607402044181c0c0510034608141c07800003052030b003542c0402d04a8106540c144810b01984071407072011826408020b2804452000c80102548100a002e601c40840c150018404000540001154220003851541580009588214044030b805150b4200c801351008003e00d06154002030f007081e20040040c0c24400012a214040c002600c20410141c070006090843d9a91394260040c982110503a10300302541c2000c2140509003812415503208130583c0002d20f0300c410000301044410900691f08043c29600e84 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 317180080 1250 317178830 317178853
    0xb0304022103091806090c041508090a0f0b04110d08160311120406030608150601080403050403060515091006050a05070201050c060a05040c080309030c010f1701180608030f04031202 80
    0x109a42c1002000c1c111182070313030314001d802c01011181c01010402e10702c000380000c200b07462032000c01e980c00003070f1420000941d554040c4403e140c41600e07031000d00f20482501440c8188081040313040c1c043c6000e01007440c4d1015828007806645001c0c1c100083c014001042038840c0501c5e43c04c040e0340041d1003860034440003101d11064901e407aa025180c4100703800000740401655825100b0107009241d10005800342d49413100b0800c0300801c008290505008407003001508151103070381180c0203150300c100208807078140744140d108040b45112005010f0180c10003c100d4a8040302205021158690780d142d1410341c24420865242d08469412414000e052100a03100c04040c4403c41c41040a4000001e0078603090030803a1030210207070701095140c0c01c00c00c50040070703480100c0c180d1910682820603801140700e1240450700f40c0c2030130003032a103020501400030030708120bd074458426510740c2460501a40b0b07112446580c50748602c00005034290700c204820400030340304420000410201d0b0054601100d6403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 317181330 1250 317180080 317180089
    0x150f0c0201031a0a06030501090e160501031107050307061a0111062d0a0b04110a0c030507020f0402030a050601020105061504150203190207080610051c0c0b0708130b030402210309 79
    0x1329005000441e464000600c1010350341d00c5800004070040004103505600e400c04040c132290140542810503485134142200d100151084a030480e03441400c40b9942c00040c1061002844c0e03040105241e48442c9a90140030f41c40764185d0b07642e1030407134000303081a41c5480d143e041c03c0940703001d050385040da2424075159034250300c25010341c0320b12002400030540c0d000d400c00f08400c60303124000000d45110144424440103620100c0ca070005541424600c0e610061070002070b03281050760080b158820f00000070040c401c0926049640603800a80003449680c4540017084106030034183c811187e8030081c8001c000310300c007058900c9603545542c01980e00c0d0a03200390740245003e80042112015a109078400c0055a07000c2110941c0281c4207080118814100070019140303142d00146540004400030151003400b49201042c401010305a44865561000b880c000403160850746480100c0301141800192411006049a2007142c2c01490f5007061402c800e030744a8840310000b42e4900c1c91006108400c0142c48 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 317182580 1250 317181330 317181349
    0x3060a0b28080708030310060e010e040f020d1a060a05030a02041e18110a030b030f1e010614030c011b0c0b030108010b03070602071527150f0c0201031a 67
    0x84490a20000d60600c104607143c41829804250180c3c000c0040001f01c0c5050503540040d640320349000010940c494004903440d0b68144829680b01d0b00c2c1c800480003009040d40104020340c005042400501c0c0b0280024220105181d04641c10050401c0030207007a9208100441c2d01c01c1200c8001800c0c41d4071135210340075a40e110000c40340303240c0380c0b0002440045840c50010b40d20105584050148024102440c007403401070364610001c0c5612582c540c2036940d41440a01301a40c1503c007111185201800402c4162100a0400140e946444001f14a43e022000c42d50b04405003d00101122102c03900115608805d580c1c0180404c0b07418050180012241c00a07480180344010402e40c4035410301041908483c80c94980302c1c402d51284000b0040b10340c020850b5000c40e080d4507032501030700d0706c064015079241c088d10300b85e1403103404140d11040d80c07004140c1410003a558880010f409000342d800080d01c6040950a00785c0200307000b130002c0d1005600c60340140281c0402400c0c0407001d8003031240800d04030031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 317183830 1250 317182580 317182639
    0x3030c021305090c01050d020d0e01020307090e09070509060a080109080703091203080105130b090c0a030b030307030503010e1003050a050a020102010b151b07050a0b180f03060a0b 79
    0x2a2504600415450710803000706969084400c1040103040c890802941d42d80344132900c505218011404296060307042e4180c4070441c0d20288c05114550703074900d130369000390300483d0801c0218045580108000386441c2100340b00340400301c014030960703043c101001442a4010012680500326490100e04603c2c203000d0402864440e00c41a5101d45241c6805022805140c0021b5412004070003070301e0109612102c92811035006a4481c00500302e0b41c1414005401d0b0000c0160700315040c42c0505c40420400d40051400c10003690f810802c030032540041607202d125030030000d0b0000b241400107110f0702e0242c40c059a00410480701c10300c003d41e130703a50ba610304244989030152010b8000d403041c0000d5580a0081d4144158211105401001c66034280b2060703000f4858030b0380803801c00380307003e08150604004001c05828010680c40806036100c1480c249a401a0303124040e12002c4e0110340c0c49820000002c8280107401005814980d549114404c0241145200294000c0700c941c80301103030030504456060b116 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 317185080 1250 317183830 317183837
    0x9051f031a01050609010c0f02041b02060108010e01060f231305090607050f0703052203051c02070b04030206030a06170c0a05102f060a0605092a1605070303 69
    0x401c0d484070020301c14205a00240c00740c07004208140382603901030b81d038402050b44400030003940e04445c00494000d08040880c19a120104165044c8960300001c44e58102c43c0850b00910224405442690a03620580f160200484084500b880039542820310080b901500f01c0c0c40e002c10804200024080c80c25051041c070071140d4031000d01940030800d0016941c86105800c001e480d00b941e8401480b280d101c2c40f0005000c0000107d413602031642c8004e504201440c0c42100105184d03141e0800986a52100d080c0c0b2252208401502d040c0b40c1c0003092600c100e81d40d54a08500f01840c3d9024801964001400c00101595540c4003003201000d003901940038128500041458424038800d011021005800040c400c004400c0c504040c0ca03801041e0000541c84004800c41744001401d4100200c088201f110175203029040c10421510010341c00302c002c48000311034103a25074035032450b0340080e00d10000300c1c40f081d642c07042400081100c1c01e4000301802c0000d060080e00c03c02c6541c0718103003012a16002180003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 317186330 1250 317185080 317185103
    0xf06050c04170601050307180b03030307021c02010501080303160203090907110c03010603020607080c03070803040303092102060705030705040b0414040c140d0b011101181b030c09051f03 82
    0x82c0c207210125480e200c0d603440c00809141d41088002540c40415200e09035400e52800a03500c98210245c100c130b020408042c0440b5140e00745240d0180d180e580e10701c080d0b1503000300141200680707403050046a040302d03540c1c00998074584941002c56402c0c41009c0c0e01c01d00b54801000b0034046900c803680b4861180f8440e540310031009088410417400c1c003100005140c441da062100a00159651004a8046552080e2142c0c0e4443e1603030607550450294a4010380400e601000300000c1c141c00d50030003080103100b408103441314082c0c8031800310201c403101c0765800140c1c40071001038480c1d40038400031508503c4a0a16030f061940d201c072101100d90241e084030041b0704468500802d02c2c1080e008000b854226820500b078007407203040c240c148078001d45c01074445140d02d0318125012a40240f0b02c074001108424003d1290001c544c840007410703501c2c1441141c04080074600001d00052042c058010340303600040001110340b800400740050720f409414500d0595008104011403019140340d00000d61085019078003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 317187580 1250 317186330 317186339
    0x1031b12050a02031c020606040c14040603060306060902040e06120c03030403060e0d0309030519031508010c02070b0a050909040831090209010f031806020f09040513020306130f06050c04 82
    0x502d020401110116485c2034540c8240c1038011840a500c82800d0307030005032901d00202c0c110b41c41d00100501600c0e5400024000c540c20f41e054015506803402030100703010195030b80d440e1780300300e1165200304010b14030040080b581914107408400242c4400404480c5860358280c0003a0955000d41d000311001688e85019481001e802e0100c00030901082c181002080700d1a00c001c0e086110700030840c03000590a01c2420740303081c02a40310356800e4680d810740f094003a0311540c2081c020040d904035003005d44151680060414003480864000300ca00c0d03036a96040c901000c050004058001d007044560f460144048981d052820079090001550904204000c8180606170860206544c0110faa501d004125592159130044402c48050401e0702e00001c5443c010f00060600c1c5406460088c0268000240d64800b260500c01a2058500c03c5804005d207480e660a04800b0001030b01c1c009405410030800140c9000f0b04064503034005005051f01c0c2581400f40d170382c0d50225001102e2010840d1b0b0040340a00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 317188830 1250 317187580 317187583
    0x706021612110c031915200403110f0f0409080c0a0b0103021203390d0201060503150f31030801140420090f04110403021203040e01031b12050a0203 65
    0x40501c003064003d044461000080130b005c07000d0880e4085c25840c2d641c280d0300d1750900b180c2d118100180e82185082d1003d0409030031001941d1140c84152424400d05801d003c4925283d008a800d82c10001c0c95403940211502c1840040d090038103041c0c8030000305006840d51264144010034406202e51000c3c0800c0d81140704001900072442c1c03804000764002d0001e0300c5400040034280b60b03134ac03211021580d0f140c0024804810000c096454558081c060b0b00f40700c5804540542145064542c02c409030b4120904000c4811031005040b0340105103007040d50301043c0134030414445001c423212420b079100d00800030007909642d9128921011000150210010007084150086201102d00100c2c0d003840302c4401e0444411301000c40d04140c1e03408600020740c0c1c8000d507a8010035101e415002400078459038030768611240381600a4481a0301891020500000113200401107609586100d80030b001180d00319224650345800d000c501d013000182007a00401d5030096561003078080e900ca00001e001c43c121610516 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 317190080 1250 317188830 317188843
    0xc06011701050c0c0c062b05010f050d2402070212030319020a0c1b1a09030c040603050a06020a03020403080309011d03160809060f03090d02150c070602161211 70
    0x11514200140004e215a0f00c000ca812024441c044413030b103456968090160900e0000d910401410f03104041e514040d60156410103070494411001001d065070380e6106001c2c0b401c0350800001d050340c4008070503640d5a0035010340d1407100e00360b050380142007a11a5000c24a40712920b400a515644040300f00404039104248007070500746003180560516003079075409800041d070800018101c84415800304110315081222100030041040b6400c105a40b055900000342d00080d07007540207000e120205845410140903040c1242c0c0c1c40401004a5001a1501c100070340118844034101502000b00001003a444070145014041d90703000042c0401022424036881030f80040001100c5e0000d020000590031000c007000c601c41d8000c04d10f81e0f613070342010300001c449100340400303d411001c021050180d80b03100021568160400b50b000c40d0429180c0b1024540b040d40700711040498082c00f00a0301d40019515005480800b05001d012500c0700540d80d140b020810010419200251110740084803000082200 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 317191330 1250 317190080 317190091
    0xe0a061502030712030b01120e1f0b0111121909080a06020c150609061201020c030301031101140301030507120203010f06030303020a030b041a0d03180303020307171305040e01020c0601170105 84
    0x700000301e1b20794000f0b00800d00400c0380403129a03880613100242881030110071040382480342c03002014508000307030b44d00400c00d01e0501c03400540307120181d100314a80090095008d40c0c1c6030850718140580c0502d00d0549440365008a13040045288001540003020400260740320310400703015881c5e40320101c25034581104c4085003455168000d00f4000d00d40c076510320f1583c21a1003640c2020849038241d20503800f9104410440324940300000000051101c441d01c04504024242d03135040301d85e0003040340b0340c0aa000070b010140007500710110400094004a4a02260602c046c001090300102d20b107942d021105940e10a602003500010341d480b01c2a81481a4201308400b110b04200d5025121261001c1c003078803a0449010308581d0382a07509141c003a088040c40c1c9800c04111150780307500c038600251681c11640e0101c60306191441d1029449044100b40c0d40780300c01418856004d14035180401001d0807040d132441a15541c208a55001c640c0107101d4580030f04640d400300340203200c40035005400c50348014003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 317192580 1250 317191330 317191337
    0x615060702010f030b270a0606050307091401140c1c0c0c050f060702090106030b03010f090b040b19020409021e0c07090209130e0a0b070e0303040e0a061502030712 72
    0x1038500607a0042c0303001c0341d414011319000800a000b180421101c00f0400e004190f1503040c0e00b08500c074191411000c0d84210b1100009100c102e954003016689404103807558008600061014412510320440090300360105150150340c0100c00100742803260300071084d403005900489007058035140c081c07407201d01425052400c0c50041102d80c4079855050700314019548180c203450a413844943d44c00b02640c004a4006160240559441d14054000c0480c0200c2500035420588074101c80f00007440b4154856802c848442d41507a00d903071710000b13201402001544404090000303031910600c240702801c050803082d10010396440c1441c201e000c2d8814084401050a481007203003141d02c04001c1030301c5048400117140582c440e03081c080014100d64403000110440781c9442c4541000b0400010740d4203145004541c2580c45455440c0b0480783c2010040700503030568820071007044484600d540c0113a1041240c0c40015407592503400a000048110386a03900603071020810704107010040064101d500000d01707 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 317193830 1250 317192580 317192587
    0x405010c0f02100f0b060c0f16030b0c091201150f0506030702070b0a050d1b170403200a02090c12010609120204180b0709090608031e0318030c061506 66
    0x204001c1d0f4500e03c2d40020507140352135190001d0002c1c00e580190346603600003040319465040b0b600d070701076507481660a50170942c460301544140401c03105c085801901d8210001751015a030760b5100f0b260a90000e03042541141e0004008010101e0030b1160070720f505241d0000850b11440e002d0b040e10030900c207030800c0740705481c03c0061005464000a01200311a984010380f0b8032511000e5082d5214014800d010100c10300340703404c48517030000b0600050500640c41d140c0303095151020691000e2031600312402008a603541c03085105100004012006121003c011201034001650102e2094034040c0c4a0800c10540032400300c8010141c400c405003d84880c0c900031a2061401d10600c82807030f500710000c0c0c040c566650007010400b01c80444081c640e60084624031503410324540041115500f40b08001480385441000309155001008440f00c0c40800e099201490b00d110f004002c0d1603001620b0080340081ca5000c44c0d410350001d00c0074210038140c07800907001c0b516000d020240c68502002c0d04512034007080 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 317195080 1250 317193830 317193857
    0x2030108100e2503060c180b1201030b1009021303030206160c0312061e05270f0a15030302150f04020d03200f010e10110d020711060309060405010c 65
    0x918440855483c6501c0b07005030540a0041c50810020341015010f5401c106055084c4d03604081c0204500b4a4401400d05040d0b89450110030350113048040489903d0000040011a40d0401101e40000041d01e500707804554a400d51805c980c0610986c030880381d20030400b0428580c060229907403116002c88804600c940518000740481800000101032240140f8004072148107688002c000c1e14500e065204a5000a11000b001114601c9018490703000a800d500c81c00c0030054521101d041e01c42102d10707441d20b42c507602401e4070800611501e045680c036000176500c80c0020424038019402a00501006200c0c480201701f02680140481a130082c40400d020040e1920317440c0495003034152805116440c01b926a8208010b844410295640309541c5202920030040d0310010b81404004101d4050f40c0e08400c41805980341e440c42c00000f5001030040c106201c83e07a40041030381911440307802851961040009482c1d07041a21107110660200c000c120070403000340b03e140014826810702c6081403061 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 317196330 1250 317195080 317195083
    0x506090a031416140a090e070902070602120106050a08011e170f1f1a0306070507051501060905270604020a18080d230a0302090609040f02030108100e 66
    0x41d1000505829642c031052114401c1400461848400007100c2e9600e2640c5007110090b52641030000d900c20038400074009904101c510880400d800700344094440755281c640018000d4100d00019902c0076001c000810320180e0088603107028008130340340d1a40350350001030b00821056058220380c809202c4202c1509800c0541e000540803250118a0403c0c6003000001103400c09254100b415214868000d0b86080000d40c0c94850307a40080c2518200100c0c64a01032000030a010030f909140c040e0461300108104c94861001030000501800c00c440c000400941244038a0400360701010010301524014030280c54810400f2691150603042c13802c4403200e15042c1098450042c045510491740040d10706141c900580c0028007401c050b0f41c100c41220354841001e51a800514004800600001c0c0c542c5082400860408040708010700058108005207070250001d41c004481c0035800101445201455541c078001e080c0b0041c030014000d40c4030b5140140c1e8170b150800740f0b51403819142c1400510381d05003a0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 317197580 1250 317196330 317196349
    0x4031b17060112031b060209040b0303130b3001091407020c040e01060f030b0708010501021603020d060e16140102070506090405070c080706060e010e01081c020102270a050609 77
    0x10036807444556403003c4c3c501540d0000502010550030010004641c0600005034040c02d242c1c1010380341404000f2084013010b8591088162910111030070300b400384070303c14202010700640141046001c901810020700c40c1410503141d2030b603115804110303005016006680c054080340d02003d02101140f810100d0010b512a62640d20a50089541c1c0b01f00f419540400d40150000300700511036140003944038180032000140c121080800300b4080000001c2a520001d03580e0380c42c0705003641d01c10f44107041d0b40c200500344400030000d540c01625440e80721500c6005110110481c40810b45055886141403d9440074002c50024a410b5400011003081107840b900201c0750814002c580024296840c2c800a0300d4445c06030801601600001c05c1070000c10200d40d00c1041a615401c0c00804241e07681c1943d4101c0d00e1090107034680c82d81140d424480024080c00d8448040c0110380005401d0a20509503006144031000b603200c603000e20703400d41d03403100d04101c0c2011000e0310064485520309400310002c00c01030782c2d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 317198830 1250 317197580 317197589
    0xf0901031e050c130203012d0b0c15090a1506081b0616030801030b011203050a260717010e090d0804060603080f0306040c0815010c0302100204031b170601 68
    0x4030005160420400b404480c800e10002400810400440c00e00d04009401c00d0140808078240d08070801c0442140721800401050008d103621364650502c0031042c1160001e080c2090540300e0006500340440380e1018092203101c42c0f4000b4511803c5c0ca00344802000c0500d240c0328102440c00d0401c0c018008041004010340345042285080302440e140455020306c9003900c201c400082220f1040e08243e17000003224102c03070284110a506980750312100d1b040604400d00200491801c100c0c850300c141c01864146c804807408414024408800c00d0701d40c82d0b0f00300c200c0700d18000801c642c4059070041c012003880d9000d030090410180da5860b08080041d0740315150072101090001800c0010b0801400ea0407400145500044480d11665030294003403903504151004e40c4100e0410810301c00662081e42000c1c402c0a120450f442c010030303043c005480c0030108104c00c0d4214010850221045955800180003d62040c0b604903008520105054096030842c1c1100c0040708070200140e5406c0c0c0001001815503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 317200080 1250 317198830 317198873
    0x41a0f01030e0c0f120d05070201090f06051e0705100b03010e0f0a02060c070b041e0e071d040f1505030f03031e06010507020d0f1511040905060105090a080a020f090103 74
    0x400144c00148211000c652291620b20981103400905507020b00030303000d624800c0c0c8074006440e0711041c1c001c9100110f0701a481c0015801d00030030f8548441191a014030901c801c146034a060380c40d498480c01c0c0310341d4030300d146911516040c0c3c292a9082c03d100786208143c880c005401e000c1c2004041c591521002000a1711844010800d049450310500100004200d181c4100b551160703185450f04009488441c90700100c070103210005825500c41c05480c0c0f10b071400c0d9039100f1b00c2c4c0d04140700d6082100f1040f001caa0f00903540d04061007662440c1d01c1140e04500600110144d80340c541020145440c3c071400d640c0340f2540081c400d000480941c450501c11146010202c0151956540b004032101d00174410041e40c0005901204018042c0d403060200c0c009001e0781001d1040100e01c440c100c00d50750986042c0c19951020001041aa030003a4010390300b25038140340c900c0c6400e46420004a01c10071b030b600042c2407900b00369003c1c400c6141892000004110650f10742601c1d41c51601d8042c05401210000000b9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 317201330 1250 317200080 317200099
    0x29070206090a080d021f050f1303051e03091c0f121103041b050102030f0a0e0307030803040515010914150102070e0108030414060c032502041a0f01030e0c 68
    0xe948407407004000d000394004131140060009030003903891007400d0030507a080351404400309030700c0d0983c01503c0c407442d61b4a100d00582c2d1691604d4400c0c40403410026000c101081c40003817a41c0035046980c2203039007181c402e6617480f8106400e003e82860a151081900760071641100d03c11a03030060814004100103007800110030150701c82c4076010b40808001d004103003000000304401c101c18603404040c01e1b02000d03003101c0d51b2a220b00c01660340f48074000c0c41000000d41444540d9a8902c581c040750202000035003a01d100d40e90f00c2c1c0e00e83c400c0d900300740c0f01111700783c00a42408103428002da807484c0c014081c4803800d011140d00c3d00e901104d40c1e0001340030701c0c80300d448100108038240d0080026100800c22150310061070360759442603503180c2e00217000e07201c040b152411600d4080d143c6070b03054072540c2e4050006145030800700e030313082d9004078042c1d03000b1440707002400b04070405641c0c4c92040000722041c0c140a0b4a0245030041046864001ca20b042414503180c400c4140c200c4c240054282c41c00802681c44600 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 317202580 1250 317201330 317201347
    0x70c1a0717090111071a0a05010b03180f010e01020403020112090b011a09120304050a05010203070206220807080718090b0a0f1805240106020d050901050705061029070206 75
    0x2409001d82001c2d00804c00086101c204a05240300d104041840542000d840e01c50011a10540d0803e215000381c2060500129102400c861129040d00a400c0200c0c0c0740410b10701030b8142541d142251024450354081010002d45d600300c03801201d90742c0c101800300064401075551030041603060103140300320005c002400101c040f00302d0445000c00f400504030f50000c020440484e5072603015014240c000c070358103500090154000010340d42c0d0a580100b1b442c0c1071100703a40400c0050700000080c003c6054088000148c490b01c24010280504140b401600145091090301c0ca007411000786030081061500e103011000c01e071500b6030660020000c51001c143c1c504503066010141006660951416500205034030422a0000d07052141c40e810200c0c0e0300112341042c49040e56043c0902c43d580158000342060600580b0940c001e04400c40141840f0b0f040040a407201c2c0c1c94010104c41111070081c2410341803008101010f07031060006114440400c0c103500d1341c000100c0900406070000d02070726000c5a00c02 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 317203830 1250 317202580 317202583
    0x614040803031306060b0c1b0a0e0709091a011b0327032003060f0402060412081b163b150303070f0f0201020114070c1a071709 56
    0x240101540c0e421a41c680c2082c0c1d10706020401200c40844810303242020000c0c0b0b10303500710181e0300100d00c0c40380a42180d603134032581c02070060300b61303008250b00100c038101c00700f4840004148607001c1c2d00c85660382c8031114140700080c81121940c081c1800c0304600c4101c18500b90ba4881000414142610039601c1c03007180c6c0d45402c0d5200c2450484444082115551481d1003001c40001d0904590181c40b443c10a02803000c4036000c8035082c10300072505600491300060301c551400030f215400c144007908240c03410f41e072903842d20400344014104445920340014800007142242c000c400500c5004005456806116511580d0f1050903104030501c4420149507020651161460b20807450904442107607540500c00400c1c10002044820380c0d640c2e01d80b0101640c26040000035102111b0340b01c0101c44202d501916400010340919504a0466403610382c0645e250f4101d003c050700500c41515801410325451030107581280700d007001080d41e002242d0800030580e03400459002c0e00c0e0704520440e94a91600309505 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 317205080 1250 317203830 317203837
    0x6071106070e1012150602010e0114040c0b070c03080703030b0f01020d0207090b040f0e0715170a1d0a0b07020f01021e03190213050906040509060402130906150e07180614 75
    0x69509030f020b64000250987c042d003025003004807010003001010a0340d8958444040240d502403c000031100c2c040c401280284000e0900f180612080c0d500a582c0f5511054254001001140000c1c2c80300c0c4075441030700b0031805030291041c00340041c0c2250141070300300950341c04061090019190700c0315084405038030b072070340004d50300100480140b106030300385c100c1241d9844151003030302e43d4010040d401102162240c1898008455082c1e164403003501d030b090303d00307024000141c7c2611701c1d01c048070340c104007500040003004030580c0310384400101854881c1000c0c0c14401c08024958659004203c4131002c080340102c4000b00d4142603d600da148e0310b40aa0a440d45030301d40c481d186041c0d100150b03258a1480703d8641c10201e400c21624400c05545540501050b60420303244a041c1d54041408200185401000d514440d00f0141b0b000078034910a4440c1000d581b640c81c604081391650300d4043c01000803401c2d00d55407000460500ca001e04500f61f44000074912140704407020000d50801c0060400c000303a044 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 317206330 1250 317205080 317205101
    0x2090909030901020d1d030f0d09120f0201030203220b070207060507050a1202070f0b0414040e1b040209060f09040e01060f21170c15060109050906030a0506071106070e1012 76
    0xc48200d0021103508c5582d070482a1100070101b12044400a0403840000d81c00504590111081030103909940c0154060740018001c50048007900401e90280c1900e4115900554010340c140d02041c1002800641008030f80d8020300c017085400c0207200c0125000050204880798000000301c012185000200c4c100341d03081e0001181010b18800c000384803014080504155100c103500b11000401c044100011130300c6400c00c1140607000b085805040f042c4000b076444503214090009440d0626403400110300b64441d8984081d14103000c2000501030501c1c1c8141036107d01900003c1280600f4520036040c8440076210300462081072118411103a9024000380944a5105030001900354000320f428109400c9152000030b1845464040000d034100403c19900954068690746036040c244804e0000c008401008150588200310310311000601c10003800b449400300f651894425950310002604110000e805101001008079250340c0990310044002e0443c13460303040183c0340c50103599510700a05121000e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 317207580 1250 317206330 317206333
    0x16150c270b1207020c100c1112030f0c01050c09030a0210170a0603141c0f0302090d06050f0c0307050306010309050a05011103100e160e18040602090909030901020d1d03 74
    0x800d02c050700401000503010700307143c0d0280d03500344500109010300064086a80030015039040045004903801d10304410007548050043e0700244110b40d0f03401d02c0d60f4400031528504020000344d5020501c401c0c4610340e048601c40e46124030340200500001d5550001d0741000e84202c131040c40c020103140c00340c140e40950710013041165406140540400008001034842a2203c80f8400b030703609071906020a0980748400c0402c2801c0006000d00340403900040b0040c15075080c1a03003040019110b940300f00024a80e2481208042201d10300070074411003502e4094070500e1407100600c14020700c04d8000c403c1d40d5201c4030a2800045800142c240035250088003000036146510301229091081041002188218244c480d6580943e98550074019001c42c22504501e015038189000107405100300025001c40364018811148020f441c0c81c0c0100d01c250956045a10a600150005c80d5050520340305900011402c055810140c4010000c1d49800100c4040340411020701940d00021510015080100314003a0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 317208830 1250 317207580 317207587
    0x1b200601030c0b0906270f090709030b1b03040501020904110f071b030807050f06070c0506130201030615050405010f0819200a05030609100501020d0c05100216150c270b 74
    0x410420701105886c405d18014844a16800030318200f10794410b00581040e1385035052185540c440350366400d0007078140404c0005907500e424240303174482c002d140144d0240c0300050303a80225a081001f1280411401d02d080c1d0001d000d401c902500f0401550021904005000f980708400c5803900c0f82000282c01c020036081c4003191400a00c0b5001403201c20003100750084820310340700c0c10025034410002c0c603002420b071381c4618009040216008000003000d4818180440c007162601c0840403100e600f034408400080001c03508100544c4c2c05603501804c2c210710705007949203043c0944003213049041510504030081d11181030405000905c51a1250044c0c11450241c0300c41d25060010203692060300c00500c0b41040704086046086440011412990142c00400c603a40014405580c0705442c000c058505010344181c18144401c130f40020205003483c141c141c2900340803450180a0b107035a00e41500340143c41c080008000680201c0010304804200155810b0078007041440281481c03141c21140366280c021 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 317210080 1250 317208830 317208877
    0x15180f06020307030305060a050a06050c01110a02061f06080601081f0b0a0e090c0306090c040504090305071a061332090609010b030604030809011b200601030c0b0906 73
    0x4400392540f40c1c0300703503424480e40d1500402c005660368680035a640c4203482c5c2c44100079441c010170050a041e040c60f070012449410074440d90f002500100003000c090b80002e41040705075000310407280110041e076802d5402a40c1801070051007207500070310385414054140c003c248001c1d00c4004d1180b11496031070a11041e952100100304480c2c000384c0541010486030b400764125441c100d40352a00c02c0da174901c285c81c190fa0b034040400101c0c07039010700b1319400c4500c10000400d0304e0b1514001c1c070400602036254140d45007018504214820f180740403200003002c000003448002e0352030742e648225054040002041c48031041038804c1c2c0c000a284410711135109041e04925040e400c040400344641c84000540700c840d40d5240d01242613070300303026007954190041d10015001070700038249941c00c440f00600000e4100801001a410480a8441b440c081a05085a98289038800e01700301d2900c4242000f61295502d075030380d81052400703c0d000344820f450010411000d16100c5009840040241048161070744042 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 317211330 1250 317210080 317210083
    0x10c0c060515090925080309041e15060e06072a090f05061c1a040807020301020a02011d01060b071709090109060e072a03031e050109060501080115180f0602 69
    0x68190011407038031710068484010300100002c03003222110000b03145060002e00401c8001c081811050280c034400b408041145080c0340300b600c514400c0c1801e0582018240000600451708044085201d80030811403036002450340441403070030510501c00900000e040001d03015080c00c858220003103040c40c0030210907124141e9000390707004000035640d20240d0110798800801032920000041c1112092540c60107418114091403035000d0f0184921508107292540000d00b0790f4021424080142c0d182c800005c0c2c2103c041455800544070003000700209803401c049131410b4004c444002e4040030b483c80034a85140215001c85d4031282000302070342103542e1607140744c030002d01260103104565000701c800280d4442c010498103064441131210400400501c0055550101c0703d058120101910742d101c0d4098003900c20740d1005034031170000000c1400d60500031001d0403a078a41e880541008481801000303031500a4030300c3c241d10407180c84d1141c5034400d00700070700c800b00c0d289a000a40341d1500e2003000940950 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 317212580 1250 317211330 317211343
    0x2150c1527070f050a080d050a1808030702090105060301080c040b0d020a0602060a050903120610030f020d1a030601060c1e020612070e0a03050304150311031006080702010c0c0605150909 82
    0x3d104071030404040c0c0360b00c24024002800e010710112503001c0e030700710561207000e131000c1d00422009140c00f41100d501944010807004c1503901205240c6d00124181c8110310740f0490381405800d00761a031314255854403581c159503940a0030024003996440d624024135440d800814071400e50041d001c032186503503440009550710030446258604919010124103050b50100c01c43d9060902c00c0c4401205845040400c010010740c1745542092540d10030140c0c03000a103d00251503a03803480c02c000252002c0301c001c0d0b00260b00d0000300003403103500080010702c01750350041607140040342c106c2011400c103613000340482e81080d0301e0180a07502c481d0101e810700b11175201848035441540c50359100070441003030a0500c01040201d000081150300180170070f000c51500c00c1c0c00d40307201c1c3c1c0c01c524010800400d04003071480c1c40d03030080d5140c14440006c94024011940c01a00791a0410007600c0200604682d50200800b103a00f05400241203d440700049110380030f868400c180d1180e4010164100c81c02c2c4a2000c0c2c2d502d22 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 317213830 1250 317212580 317212589
    0x40b030313060f0804020d29070302030709120515061201050c03060a050306070c02060d02130305070603050c12040f142b0c020109030b06060f0409060302150c152707 73
    0x4201c200e8402e00c0074131070031880d401598040c01a00c03548446586a00c51484111100f0641044d586009100003a40c0300406e0b01400458a0041e600e0409580040c0f045103203404c0b580b83c03040000155000124001240c03070b07141c05016040320700c540300c0800144841442d84c0401809608100a104458801d44000d500a21048550300d04c0c0030f655070141600c540f02101c828000c40d007111b5018000d801c0800c0100030043c00390b00010318021000f007111a015000b90070a0b01c0c5070380281e40074460389415100b025000f60f0410072203401d28007040510b00308100d00400040c10b000d1020201010031410f07074403c1c0a217569041c143e401e42a8800e154a40c98014000d0410b1180c4000e080341030490300581d41802280c0c2c060307403441c94150440d1640e01d000c49c405031040e074004500300a4034204081e07840c01340018220803c00032400c1891030040020042d80c21035428906130701081620b030460f034000390065108c41c910030319a00c2130703692030503c0848074038030012052200000f102c1040040d42c0868060283c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 317215080 1250 317213830 317213837
    0x60c0409050a0b01050d0b01020304080a0807061a060f070203150c0304150b0f0108100806130b090c1305062206090501080309060423130605030d0e0915040b03031306 73
    0x2aa1800440c0068070f242c001e03503e0102c2c6040011011200040e001018545810f00450303113040d035a81a0540b40c1603040b0415545808080f402c40200480e60003001c0819003000d00001c000e2101d003000500300c4c4910345030311544038030004034001103403020b001c60001400080071200e52403030309480d20040f50740110b500f00c400c5001c1c99000d00040704548103900e00004003400004409031040c00541d00060003130314082102030003140004201c10100700700c92041480c440400848542460714010002d400f4044100540103031121620b580c403240c3d10107000031101c0d0f40100c1c2d83d490700c0c80490201c094010200300d1070003104101d8418100c060300100103c030001441080b0f0350b079941072480c7d01c13030003050303040741d40001d0420040220b081e114a298003445010381c0200c40055002c1c000801030340500c18856451921080c2c20030203440e051100c0808076005040c151202003102c4001840c110008018400f81c03200001030f0070094817603510800802e100a41260703552001711075646068a420b01c1400f000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 317216330 1250 317215080 317215091
    0x6050307030c0201060807091107060c020d080a060509040f03050c0607110d050f03180f0105070f080115020d050c0c0d0b06030c06070c0918200a1d0c030a060305060c0409 75
    0x2c2c20710510a150445017442c011b80540780c01d11740303400e000c2d014050340602000400c0c45400c0124000340b06204400a0329001070040c021511009003100c87c0c020603a1001a02d000707810001621601a41070f8001c1d80700091072074895841c5420385040c0074a0f0b68160040c440c0404000f2050b401001c0c21000c0f820a2084405825080d0801c4915220b0350580c4002c018040c07000c201100c0c101800d550880e600350f401c2d100c0da0303004040e61741c0c03c4030300482c4c20308001060b03100e004043c1c0340c1145129001d0039010b04885110407102c08083d40d145000c0850608001d03000031424131400082c00849020720009041002c489030f86c2c100091001c50079292141300e8000c2d6064200107103044000c803a5100c3d07001d80341400c030900c3c151054008050140c03020380e1a00c0a04211400210b02c0c8800c10301138070090b50000102c000050510141401d150015200040d0903d075045079070046a58841d44001c00400d03c030381c8c0740e580b18500d1000d80041d900040a512649081c824680c80c154090800d4a8080c030b4200030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 317217580 1250 317216330 317216351
    0x403021e0d05090d0201050415051801051602130e0a0506011a09030d0302030714040305030a08010e060a1e0503030a05030114010906080103120e120f0c0a060e010c1703010605030703 80
    0x4580c4105009034012800403c07500215050001c0e00c1c00c000780c01414a039007007070b603a88806d5000450380c00e18080010000901142c203c0c500442c1603800307000a19155042211022050700f0031840007034080d112b40b944c048000801102e07078020b44005602c0c0b0040c1d81501c50145000c5641d01d03801c5c02410f18044200241c04469002c01341942d816100080081c0b013800487c038800d81c000d5001a015008005612450481041030038000b00f000350b10940096640d503181c900d000305010811f8103d103103200342c074405011003666a01244016503005070900c030307107440d00640002100b10702940710a816000115260b2038441e00000914121010401c0203104580e95100465410b21103014030070110b6070400040c00820440c041480f9040d9050600c445203034040300000da01d1241880101c1000c0d407041510610300f07802403100f480490016200c280c6c100e414544040c0070800900c03011070401050900d24000e01101d58220042c081a501d00340340d0b0b07542c45a81c0103120398000c46203179000c20309100d410103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 317218830 1250 317217580 317217583
    0x4060f18140a020f0105030705040f030807050d2f01091b1d0408070311160e0a1805030306040c0c1415010e0907140f120a2d08090103090b0403021e 65
    0x28581e9500070013082140d0040d80054610390406070660003040003d01c03001c15840c1d1240101e201442c09040c0040c2c0b11156483c049190000460000c1c0070041180c45801e082c95282041d6850142202030ac44400142c40029500402141030058042407043c1d812400419880d5a000f0035520703070111400001618a00c00c0460350004e940040184200304400000701e48030b91003021401c0c0c4040c043c0c401c2440341900c16805038119400c4440807000380c000380a664501441080c13009801c030200c000c04e009030f503240c00c0c2d185d020050032507004035100d21041952a00c80c401d040944de41c84a9588403624000310b082d50340d0f900c61031100450044000010a20040c601d400030320465941d001040100e081110303a0007594441d1030516003042c0861080744240c2e6030100803001da010040300070b200c6221981810002400d403028a050003145c2000c0080c0340c0c002c0a01d141c3c4035940c0220b10583d80f1028a40120020710007404060550113144040c0b204050340800c04030740030140c040f000096501c030303607040700e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 317220080 1250 317218830 317218843
    0xd06050a0b0a12030804020f09041202010605150f090d08030c0a02070e040f02010f02030c0f2109060d09170a02031b010e0c09040f05061f0f14040504060f1814 70
    0x31100310400766001e07000617204060716039005d8405440c0a003221007080100d0400402541c0407030b629501143c8205d180795091043e980104411502034201407841603091805105014110689210024440501d0f4a03441c070b6461580707038071105285d0b5030f242039078030210305801c0701e071030b0900501039000d00103072042c006180030b030107a50056544c560642661340156101c1a1100d100c1040d4007085c03280c82402c100500259200301d884d0006805402207542e0740c4840c0290f0740d01d003a10800028000c010083e142c00c0107403080d0010b44100000e40d4100d50500404510f803040d41c01d80f10400c00142c0c80703007160340440900402440803141c001d600e02c1c0c1461132400c1c5d49d55a268441c10b50300840d50481a85807640e102d541040c00344000414995154a420b42060700072603041144000026400341003489824481c40240b000c000034800850520600c10749440e0040081c034890741e01d5070042018860540d01a004166041404115800340700c040340d0b0001d10710b03040c00c1e0781e134502e01d0544201648000c20302 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 317221330 1250 317220080 317220089
    0x10807050414030c031009050c060f0a050a0201020405040c050c16140d02011407030201060302011e0801270906050618010e01270e03040f0b0a080408090f0d06050a0b0a 74
    0x6850406007042c951404291034544041d43c5841502d484140e2a2001e12095200700503011021403824080d040c028075086035440c4060154004102c1a1490708000d015a0020b0303a181c034001da070382c0d00410300403400381c040c5421442e84507141c0868501c000380c200004145414100f01580c004124801c196000b1001c14403c450328121511020102071030404407003140c01c0d2050403c00c400400c4a1080704640d000310710202d0140c0c0d5120014401e56030400a2000724090382c030f40c1c04000a0880200504c98841842206007104100200203203500c89140c8404281c8800d0340c0410240c8102e00346200900710950b482030117544c4d4510091060603d0801c120b05030340001c00b040f481a441c0040406901d80007012914120600081035800d840040c000d03e6007100c0000000d546440c00c01c4492010311070250710203070081d0000c011030b0310055046014140c0c03103078216002c2910b0701210b101140001014401032584504101c3c000300c00c001280d40a01d000317030003514003048200702202c01d00c840340740719009 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 317222580 1250 317221330 317221337
    0xf16021b060d06030b0c0409060b2511030a0510061a030628030b0403141812010608070b040f0801090f0f020a030b0a090b060411161a04050f060105010807 68
    0x100c04119060200040c40540c40d03502000600956a4407201502c2c0d00a56492650f510002410014140f40740942c0029103000460326203030000407104050004407000d00050b071000704603111000d0060000c0100c405034170250a82d0b038404c1b241c0c508591035403403140c000d0b11990f141540220b41c100c1e095480c22100d903140d4171524510b8a424040005081940c950031210042c44944801d040000d50240c2004610403180b9049074100741c40e0180507080c070780d804d00030007440130700c51190311781e00c0400300040b0b0003c2904d00d918228140076980d400340401c1c0d00603003401e200d503080001c1c881c880100140121044011140300c035075100d603007107401d84004e0040a0700003206000d03e1008501a4a02c00104910082c464000159240d4800180400484860580903036840e040010f00c48400e101e2035100c001210100000f5404040050160082c4c8200c41441c2a91350b02003010400748900b008a860384110b558a801e10700b83c40e2280e5948401070300516540140f1000150f030354090709443c5c1c0200c07669203 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 317223830 1250 317222580 317222623
    0x50d05040f140607020d0c08010f05040c23040e07030c051905060d0e0d0503071e02120a090302030a05160b04060807030225030e1801031a070c08030f1602 68
    0x10284480c1c0511500072590000f01000010010780c0d0344040c0c0c0624a100d40042c442c1d0303d14000c0300c1c0782142c03107920042e141942403404010010f05010003000c16156101e1440428082012940e0044071044403566001480c005851400e982e00140c900101c92003440f00700f1032203071500240504c03121a0b69549401c908484070502c12880e00340d0140c1041418040c1c00502c0049003c1500e15100c1e40740c0148010a00c00420300c80445da006c0b00c200b0307448500b01c14141c3c8030074003500007c1d601c0c1c038050800380c0c4602c804295481802d102e040358400860b0020103c62582201e818456110180e45246370b10070074804c600012803071018002e54040f1031154491104580d14460194040c0d8040c000418800d240c1461806800900c031015408175406030f039880303414944a4040c002c0f00c80440785081781e03a00c02c01c0b0041000880c2d00c003240c00a03680326440c100c0140c4078104144d807000314040c401800078802004110003e110290158030030200c07000b01e443c88800103141683c455417610b201e07103170000d0b205 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 317225080 1250 317223830 317223839
    0x6150418060b010c06050a021e09030a060507030e0601090b10020607090b0a0903060c030608010609060b04140a0b0a080f07090509060d080c01060f08010b0a0609090c051e07050d05040f 81
    0x2e520207805201d042c10103607907490140d65103200f103420071104080c4281e0b000c584602c0380016000070501c9068252860b40c40c09c0d544000081e03481d001c000004000035125400202520311a802a00007440f4450850b412561200340710000350112500c3c090003029042c0c0a14052403000448a00412182c1c954506581c200255092194410f11a00080c413402000010004869100c0c20b01003040694000680c5c0741008546400c1d10b42650012607440d0030032805015038038010301250f00322482d07443c5d4400401c00303560126590f0b00d8130380e00040030b4900c040713101a103903500154514400c200c9102c1e5400203941e101403e03120000903000b0075803c030308200d0005900d400c240c442c0e50841401880c0c1c05040100d5124400e0070b40c2d030351750400002a0481d030400c0040304400d0060162000003103c400310700600f0400000e00710704591044540203500c420074013254502910881d025903c2116500801c0070046961302d2450b0700103401200d20b84600c5850f01c0110744140182d80075910f401030740320181c6241 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 317226330 1250 317225080 317225093
    0x4060801390c06090c0e04030930060e0a0c060e04020f0a080423070e0906070e061305060301090501150305040308060d0203010e0627030306011e0302070f0506150418 73
    0x2d0440361a642e501016000c10b90103042c2030010504c0180040c0300d03142c81d2a004141040a0340000444014a48060018651994040c0d080d40c001e041c1150082510b003009405000f21100c120340a00520511100307000307080c4601419250300c2d85a020080c0c21050a000c128450500314000c0080d05020640b40c05100350301680d04140034070802850051000b6005c10000d408000802d0581d1003141c1c10030110f8071220031694445c038000043d151914010340060200032489000502c581c01c0040d8140d1581207440c0d1000142002810030ba0f01ca42c2c64010b80402031400303000d07441884415685001456200c0e000c4e10f440b07180d240c1d0301c1c4029501c1746014020b100503e10402c84e410f548170781c8240b41d010310402c07419100e40380d180c007003600c0e01e41000354450301a407034070001c4001c0d40c01c10820030016981041442540b608080e48210500307165102c214024000e84c60000c01100e80729500038107006000401a00444030740c14401003d8030a802003004841322910031206c02c005865030207011445 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 317227580 1250 317226330 317226347
    0x3020904020607151e0c0810060e210109060e010504120813081207180308041e24081018020d0e030c0601030b060109032f0406080139 59
    0x410603003c007440c1e40b0103404006a0f10000b0418042001103500750705d15602c0c90280030018845420078180354102044202c2c0207501074013070502800800d07881a02c140c0c8400228039030721003800c5600d0303d2800784030b1a0325000e80a17409003668100e0511461010800d0184140c030700440d8080c51040518010302000c2d11100710042c001030000111841180210b107402000300940341842c80c03002040d241c041c0c40640b04210a01410780026123961090000070701200856054a05607152a80120f8004142640741d2081d50040d0280c0d48410780b1a0441c904004d00000542e0035646882c040c3d40c1c0c4800e1000070b000c28903c101e0842500034441141c46900c544d000f00040351511034041070741f10300368160074919806144030100700d5110400400c144008090030540125003445c000c01550b00d075458041c01c501c07410036402c0380e00c004015405a41610703181e0000726968090010f0002a9417142c10600802408072980035007403818501541e8900c0500c6150152800c180090b8040000083d0131140c076203 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 317228830 1250 317227580 317227583
    0x601080709050d031809020316050c1e0c03010c18030f0c1e090b06030c0d020306040605103903050f0409090609030215040210031a090f061903020904020607 69
    0x1c914030101d11074a81103220350a840c000d03100e8050221228421602820096104d00c00321031043c42031110030340001116095030402407828640f10180c8240725410201d4100320a079030009a038200d003000100200b02c04891050481c020450810700000544840b0884d0011450801001d502071000840c0220f0b40e4200a020b00d031f000c031209444035001c0b12030f83d550f241c90410340d4100c0041004106540c2c01780c1034601500317039407080c00c2d0b051803e030070b2910303025100d1811340c1650080002050740c5c80303d90085004000080c418003850014803005001c680c281240a0300d00c0f078145850400e01030707413074441001c0c0001859043d10001000c0d10100c80da03401c509540c2145c22420000069803030001c1c050a04158012400001d03906840c0c50040c0c40d00803a15007e5100c05c411400300f0000d690b0305c5009040e001c131642404240d4044d18180070b80a0b006040c510790f8412400014400f6541c0201800b601c0b841040e190580a126404844d080b0035599100c0294024105000038005040220280c526035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 317230080 1250 317228830 317228837
    0x506070302120c0105010f08030403050304260607031b030b0d080f12011410031406060a0e2119170a0302070f0506070f0504140d03050f160c05010908030306010807 72
    0x1803510b071034209081d4843c032510b003500c1c0e45900060141114000300c80000306610801107151502d99941c480d2a80203a100b0b102400e201c4c9a800042480c0da00c0e01018261418400e0341c030540340001c0f0140080142c551001390038503240b4014000203010388903902040c2d400402484070f07e1100d0740c0c2c03006180c3c80039180c001c1d041e07001d001c00084002c022500354040c0000079040c0b40025003000070300081c51a016a82c0c01007508001004401480440c2c407690044020781d03a650b942e54280c8000d40d8203000700f110194003e109826240e1034030401e2040c095050300c08200b540d118140d9050304040c2035125500140c8000c1c0901c0240c1007084002d0000c000c000e54506003d81008cc641d1200a40f401c1620002d0307400c2c1d08200200103820764002e006029466076401c01604103070802808150740c5610341021800f443e6070700084028103000b90103070740402c00e03500d812655030000e46000c0c01884510040440d002006e104000c0b27032545c0688100d5098884000c019408c55840500450b150700f0094101010f1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 317231330 1250 317230080 317230093
    0x60703120b0f03120c10110304030e03030c03040f090f020744071a1504020706021624112a010e010c0815010206010e150d030305060f0901030c0506070302 68
    0x15442c1809001c503582d62034240035455038a45c49100f424046414000414185017600504001241c2001d49402640510701000241d010001003499407040704159443c3d03101c0414001200e8240b50700b4202903404104080c8003000d2a04800710682c043e034040240350301640400c11158240d03030a0f140340200314000c1036840c142842d000b03103083d0340c1550b0100c1581140c00200101400f206510445002a20143d80101c524089250a5100d410a542c0a10440d0001020401d0284135010740340c44140e005c0300c0502100303007885c0c940850701901d405403400510080c10b030821b845191042985000d610130015280c407900e22109002c40311096840d44d820f84072040125143c0c0401d1280c2c0390007503003100000450002001016107a41c40040c28401c1c25522843c1c0c200c0140d0707011a070f8504460341600800015180d101e2451040810410800d40211a005162040c103500da006140100d00554040c84001c00c0842401011442400041c1800d45000c0040000381020300c01841d00c203020b481500c94 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 317232580 1250 317231330 317231359
    0x5041211040f020304060b1f030c020f0d020a030207080303040b04021c0f080d1410060e011e09090b040902030a08180604030b040309080a3c0506070e060703120b 71
    0x1250192414030300742c2d980c04420002045913031b110720020100110342401130703055081d0100c01d4402031211150101515684c602000d9070007040700c142c04980c801c00b03407500a800054002e559041d4441300390010310400c0800601040003004880c000c9411240758200b80d502d540078001aa41c034a03002024000d925104180401c101790b0002e112144107015690343c650120340c605040c1d444074241000b04035210400c0c8400e080003088810112401420b01d076150484c01001031b00c1c4103544980001c04040511032441202e680b01109070280c0c2c0b101c510811481e503060007440704961001c0c000030340603030043d884c880110380c3d1200a40504034842510700300510a280201d080c940069004035a010701709002d00c402c15400c284039101a180da81d008100c45002c1c0d442d0701c405440107941402500022500205414200e5840c08140c0100d40d00b02e00f0042100d841e265590f00310448448000440c146444c102e10320340501219003240d015034840d81500305031154040207040071024a3303400181c002c000c4a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 317233830 1250 317232580 317232589
    0x141005040302040c08010306051012111f02070602060106030608031602030709020c060603060a020703090306150905070806011206060210020f04080706090603111e0306041401180f0c05041211 84
    0x2c507184c40342d61810400d524500c4c04c0c005652000d00307144c5c001c5103650f40c184600f8240c140d1414400d50800050010326102201149070440703c145032248140384500369844103a00082c060b022035140317608551042c1c1e40d0303170310450464080340101c12041c0c00c1000204d6810b510800c419410900040c243c81115649049031012039100040c0c412071a0401c40800c07130746103010301106a101c1281c580c1540b82c0b00582e030300203144840c50300000704002da444042c110b0581c3c110641c5070140c41f290310104594202510054015a001c40700103001812207141071185600500612003107034000d0700202400712070640c145002c0c1d00011400d5980c10400d0000142c244402c104201c000c100c903807201c2d070209007042f2005040e41c01c1034994500d03c01003000022030714804074403500440e41240a4540e181e2b01c824000602420344104c213070500401c04000850010005441c0c480c82821801082010241e00085401030350140038000011510500c0100a2946103400a062143c0308010800301132102c0b90006 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 317235080 1250 317233830 317233841
    0x30207050603150f030a0c05060a0201091514060a0b030c0d0b1008010503061315090f050109060608100e10050408070c06030f110702030d110102070c0e0f1014100504030204 76
    0xb00c0f0719070025060749821310355101114507500758090300c482a01d43c3c9400a116049108043c059040042d0101c005071007940710344d15040c0d001c41c58035408142c0c58509c1c0c0180280024170300042000e031022802e2841c006010904482480c400241140d40e800a4801c0d2030300010411840c41d9264800560181c0d1142005100164161902a02941441e051510709140284010b4011181c01d12540218042049005680101c840f000c00c4c841c1862070488010110094010150740c00c0a60302c00401065401c4001950208011601c00350125400c010640b207601d1603900046c0c0040003c400ea45116070040c2e54094000c082c800e00d4821140c1c0e81a03012a01a40f11000080d9240f00407400c0382c943d0300541807020001c25459080070040c0d000292034113070600901041c88411031510100e01401c0d01907a07110364011866480103641c030030105846010454281d03c070420004001080d81018481c0380065410390051403001c000748005210021096050001c00c1c400700307010000041c2d881d40a0b2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 317236330 1250 317235080 317235091
    0x6010815010315030b10050a060212070c03021908010e150a0c020f0307080c06010609030515042a0305060604290103060b0a120b0907050a080406061208121b07020d030207050603 78
    0x3224020714003d00000d64515454122a200d01c2c15502304020255002035560740d000400e440340b40d60340615140106102c80c5c254802500319980101d00c50441e21203070700c16002c0341c0240307009101c1840140c5800da00d07448051700303d002c1c1b56100c0d0b0210320060100d80c44442d0014043c0100c0c0c82c2d000b180c3c1b2060340f460300100310880d0480c0000030004883e00b004e0200c43c0c010011824440d00031802e554a05403510200310300f5104020701a0300107020f008245c0c0800c0080c0b41d038200480124081c040303100c0c1c11100940820b07106441a00c001c105182041d01c681107030880c1c51b00c01100074a010f01c481150115150900301c0c10076031074130303c08a100e1030304038014600000030352070341486541e031481918151040400240e204841c50804c000030540c02c4411100382010350f140800440d076561500c03000070131964002d04140d00c1511950010000040020708018141740c000900c199200c401101c1031702e040102c00150741100f80910001410400c1d00080407512170700650340695104c0b00820a00d40003142c5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 317237580 1250 317236330 317236343
    0x90301021608040609082a0103090204023c1b0114160f03060b040b0d060b07052107170702011b050d1101140c0c0a0b040b010312080601081501031503 66
    0x40030480617400492407001005014094800700c0702c181c00e00030700b91910100c2101c0103040404002c1c1240e1003680f1050002c0e41c014802c6441da6032101c880346554081c0040f07440341c80d034540700d14000704010900a011061910211a140c010441c074018200004072100c086507641751001e240800c00703a604064032902c1d1004000c0b0040880340340040c0b9001b0300100132028076241203020310000e090002141c064036000c0940d59a80e40302146154014444c662182c0e460600200d02101000307030206070340d20401580c5800310010b1140c010074819030721404030001e02400e44010303503c120800e014068800316005040c00d43c0803c00c10a03e240b258000c2100441e040d4101040150904c0e0b002071001d181080108000c2210030204411061548400341c011400c0100104d24503044000030019840c500c4d41c03040c1500003c2c00c0c00c0c40d00100c103070020b000459007816201456040301784510b11451013594142c4d601c3e40c0c075444001d4a0854402c002c4038050401d5292003000c90a0b000002e00c80008501c2400d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 317238830 1250 317237580 317237587
    0x30b0c09010f05031621090503120618070c020d061503060e0a0b010e040602270a05090c07062708070b06030a0c0911130909061a1302090301021608 65
    0x50091001c01c0c42e090602c8418814031050701d8544d03203460112412814070f40710703040108900859040c03040031040c0c0e000d07003400903400400801101074581d00380644c2030202c10b82c550904000e120381002c183c00000020300b90018118074030501505070060300240140008a200780c80c0c800642e284000ca030415444105020010000c491084000f1016484c1c00380c000080580e444056031441031040b504440e00c510301007000d02c074259040300e145151601140802303501002810101000c2d01211078418140013500044906107958031620662250303000138070300101c6c3c3c1d884100800c407103002d11842105000034483c44204920310403030518062100369890f0a658a0320080c1c44500800c0079000f40c01a000b900300107148111120199104020085029422030810140c075001c1c1400c1c04402d040e686100190030b4007290301078440f0500a00b001d1002d4101005600e0348075031307600c1840d60400302c0b0f03100c0022a590a54080d00e48080001d001600d00156952020b02000b1841d0094815a9000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 317240080 1250 317238830 317238847
    0xb07080106031b05030910240f060909090f05030c100e07060c0f031b03090603051803180d021e09070806031b040915051503031e090a030b0c 62
    0x180409005280d90b00c0c05201840c0c4180b442e45502d40c00b0f150f1003080c48008070200300701c0582400b09100382d00035401d041000c0010054070340f400c81d04d0071100b00701c3c07843da21801051b4280c015148105883c00c03074031041c0b1007071316184041c0c005120f2400241c921651000030200050021300042c100d00d0400e5005107080a281d0311040229014140f82c0140c0360f0010500300310894214441d81030f01c0b42c010503196912203460400340d0313480030305d0300c11004c0e040e5031081d4450805410280c000140c034040e58081009595500390b42c2e13342c041580312814540c1c02480200340441c0700206003102c3c3c400103000900b030134070307a940410034480002c80b20b603401d800c0031060921107043c00240540d0001c00c500c0d2103209824a00c02094580105210508602d0301c00d42000b01e10361255001007a40b5540500380c130b4817484d004002080140019241d4400d03100c4865034100e03d030f1a000094444011380010f22020260900070780180951001e080e00d60880c00342c44000011a1822542a00c1000c082d4002d95032030400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 317241330 1250 317240080 317240087
    0x8070c1110020f0706051309110705030a030516020c0114030702030d0618180f021516050c040f1a060307020705060309010b09010e0f040209040201140a050904320c160b07 75
    0x130350440c00c204002408101c00d99484101c21108071034a001002891100c0052404000d11815002034030a200015001c1d18050703150780041d02c0340c0304d90410300f0391407000741c0f108130303220100781030a01e0004154914510510000c40010741c1c002c0458011a80f600c3d00074151841959065805424201002c0c0341c204c0c22034603280211011903400c5240c40c0c011040964481e4415110b034440a40206c41e800d04011a0364104000c40d80d046211000000840e0340380d14000707540340103000078140030b5824030804448100c0c141c0600d2104c2d181941c801e07810b520000301131020b01c1d000108214214494402c001846444240c000c6015110850002c541581d0100510501e0701d81a48108a4500c1420411182822140d14290050341c101c50f01c442c4c503111800102c4c1daa0f144001c1100f42440001292109540c021004040002040d10706126010800329a08103010743c00c04100d00140304000e44105400081e200780da4040c2c0030756015401e00065440d50b8180c0213181c581119100d001c20300380304060743c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 317242580 1250 317241330 317241343
    0x30703030c020f03160909050a02130f0e01020f0d0b0f09010e010303090e1302100c02090703060509090303010e390a0e0a0b0a14040504050408071e0308070c1110020f 73
    0x420f40040801e540110a1001740c603903035204020381c6903515079540d001c000c42071041c0300c6c2c0d1769001442c1160143c84146048000d01d40e00c414a40080c2c41d0050341d04c210320303060003a11a4000301040300c1d03040a800403a050050051200840e42c469401c80c49190159914401c2038040e20401d841d1401c60742c150719001e0141c3c1c5150308211840e5641d0300401a40104008240000540c19111400e8072891850140d40d0200700810007035200030000100071989a06501c420101c60b01162508055100c090126840744001c2c040c125800302b00d040010300f02d03c00e005d5140791038854403902000036039030130441058000b00e0348070042641c200040c0e0303007849651015103a4101e800449144d846149041190040d6100f1032010310305004e90381250301101c1c0c1510301513400503c4007402c00d001c80d1515150181c4260f0110004440760b8107440300d1845844c5101d20541c0c40e99516031120346050b200d14000741c03a000c104480480d03031400c00c09100d00341074660454803902c403080d40e00146020300a800d0030904210 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 317243830 1250 317242580 317242609
    0x3040210090338150102100b0f210312060f0405190f021b030a020105090304030b0a051b0706050105030601080a020303030c1b070305150f0f0a1a030703030c02 70
    0x1140c6003040c004214400c1c0c1c500f9204401c01c0390342c580c51421440c4000d00341c01e91442d40c1a0360140008102c03088404552514415030301340d00340c881040c0c541c01070306c044600203070359a034100940c81407101540c10302404408480d030b80d00840469030365400c00d1032403071a400308120034180b9160390148030032420f01c600049003d10007207409110924182800031158000d4000e5001940d8a031a182000315403284d04a80318448c54411040c5905251310501c2d96944c040e0380c0900c0151320b4503002400b42a00030003503038103595000c0c101031903e888100c81403000d40000391a0134004500007411305c5683c40c2003001081c50314401d140c0480c15614000405090810503800f40b121030700155403240041c1d0340441102e620102003e8455100c0c8084011000400ca01900e403d000388908800030081c0a030001e000c1449166001d00300c2080d42d5801045003840000751000380b120811407010502d8800f15401400e0074015402d40721003054500c1c00001c1c0350040c20350054000c503070b03400c05a03415401c041c8040002e19 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 317245080 1250 317243830 317243837
    0x120403020a1502030906071416080c0d090503030d020d1523010807050a120b0907020a0b01060c030c12172a030606040e090a020303040b0c010c031401050f150a0503040210 75
    0x10320301905c600c0e0704c40c01d0080801e0104550840f003665541e51302825210ba1401c001e003d4140b804a40c90035620560024a82007582d1040f28161448181f00c0c5800d00d090b604080c02650402030006562006900840c03404000310344ca8a02d00c1c01245003440c43d52000340a8240d4003d070007000c0c440031030313081c640c41809141044000340070000c600d90802c04541c00c0107030302d00d429600980700b0b114a80060002d124215804061441400003c41e0300050603449036004003407400e4103980c0d601d0709451010060400401241c068843c000c0817612071078407a034918035a420281c1a1240b400044407240380c08540342e82801c12070087c1c3c808034440700841845c0e44401d060071246075050110015806008901ca4040c2801c2e50000051840300103101034001c4a44c083c080b25120780d200d510402c401c0e080211001081c0d07180031300700e04040d442409007503404907004540403140c0e420603080c810503400300c0b0b91300780d086240701c2e0110342000da03110024030710350325641da4864582c10607204001c40a10340c0d06840c1c040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 317246330 1250 317245080 317245087
    0x3072c0102031b1507021c0c11010c050f0d09140402040b0f030621010603121b030f02010213030f060b0603250c0f1a0916090e03120403020a1502 64
    0x160741c001040f80c00e0481240ca01292098200100c6854a00e40126000945000b0360600c444a9000102100956070300a07280100c66110307003081383c180c0040400980780840184140a255006d106840031081c028001d40341c03180403582c2010b20f02080144001d00007a1103d41c104034480420700a4800361204640030341c81c003460540b001302c07140504188d401e41c0c1d10002010502680e10142c03a52603e100386501403035464644c5141034000c01c807500c0103031030720054003698412580c410340000c0410300c4401d201242d00b0f8142d850440c1c484181c0b500040a540d0300300035405084059005001c0158401c4040c0710f6176445a1400e1426030702071440581c090300081c414842180c80307400460403002c860781d01c0541c030403d00c0b2008940031404800090a5400c04140c440c043c40812090190800b00c031502c0d8001e5529040c0140c0e0f035408025016414105031480140303c0b9100c40d8009a905101c618100c9051480342c605039203c501d0161740450141c1d000c0141d98041103036035029011421501e0108508 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 317247580 1250 317246330 317246417
    0x609050a02190623090907050301090f0b010516060b030307050a1203020307050d020304020a050a08010b010305091b0d020607020a0b120604060509060904030917070806090715051308030307 83
    0x284000100315400415030303410301d81c00321003035204c241c0e00602001043c00c0350500b000c04c400b8110354000e010380240a03041807442c81861540e1b01400c50083d0044c0c2d65541b50540149060584145d06001110030584a05810341903507010800b4101c40e60046004e01440400e501c0c0c1002c201c00000359042c00d160050040011843d040002d4802c1b00282c4000541d69a031680b000695901ca1074110300c0d0701c2a030b80503001c40d41c42030551080303001d030300281c804014a885030718210380d803000a03003c0c4030740086034645803408138100302c5000003402d071000d010340d420314440d80d000817500001a0000182508045080b00007581034103100b0340c1051050300c04000c2a41000046100c0b544014415401203e45101240405218400f5003008208600203541300c124a03500c0756480d03155030b1060114a110304000320354051401302d000400c480b055507071103080c484010b200f910940c10404085c4130350701404c0000112100180029803140c55582d441980c100791784080c0300449401c0c1c03134148840c401025806113 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 317248830 1250 317247580 317247587
    0x717030406050a090509040602070330020903120f090a0f06020601030b191506020d0801050d14030f181c0b070305100801060f0620030304080310030609050a021906 72
    0x101940c205161040c3d4546080000f82d80084990780007980100101040105005a96015124180c03003652090224902e03148003121468a030b800c08040d0460b001c00424003203195900928200d0380180c00d03a61003c1d590f000c00c130b03c1904401c01083d4907590008114075689007290380a03010341105c44028204a043c154025900c941c14040104040825408030f03d61100d0000390514002200d8800d0088205445282c1c01c0350060303110b140301501c0740c50086403506000b058a141a00d802070700c401d1030f0340c1c500c1d190f4105c4480310b115680301c0c50100f041400240440c40b0300502c8070810004a0402c81011007080c07000c0082071840c00000040202114000100d01240980d000b801d145000b0590341c0301c00c41d0b041c01851044e8058041580b86c03000004504003180c5200d4203c40d03036038070b4414a6455454002c00315410901c1c4ca011250020800600040c031500d02039500f10b180f040100500d65201d581d030030101c1e00c42d50400d603030300c1d4003201c01c440443c90720a00c030300161807481c81c500460f185860000b8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 317250080 1250 317248830 317248837
    0x6080c070201030522052109030318180108150601030b010e0d0804050414060901082107081606051602030c0a030e060d0c090303030b03011107020d0203210a02071703 73
    0x9042580715004141c1700d0304141a50f00014103105804c0d0140f00752850042c3d540c035601d10b0141c0c00c202d5080e03840900c522880d41034440000c40900038515000806000321003030105003035200c4d4407860071289500c6005014500718080c01144004188603506070108080e00c140c014401d604140c20300100003440d99001b91117248891081d03c0980850142d40740c0031205009036003090303030000c0c684440810040b11001d002402402e0070340c0c0305c407566600c901807161542a00010202070b0810861000c01100c101c81c020700619020b614440c0c140002007800c600c035540c03a0380c4180c510580f608203000450000c4403080a05000c0b80c002140b400791481917250700c2ba100003e0180601c29640030154041d00c2d101c040351039050b503d4204110740e07000010080c200c103009000607000285002400b200c60b0905118545507034021131001424200030f6420003800601c100c0c0200d0701401203204c0d5148140c00c00e6404510700f1100c0c00001e884c0c80100000914141266001049064001d0f03030030100c410010085 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 317251330 1250 317250080 317250083
    0xb0f0603060109050306090c120606010801031b0f03081c150611010b18040c06030c08060f0d0f0b180601030209010308070f0c061e0f0905011b02042406080c07 70
    0x58a0740c1c1e45000684040c0d406602ca070b50580202d0081022002c000f041115422404442400407240401100350b518202268203d000c0f81c1e6980060022920341040000580301001e030791440d9640307076099540c1e003214661040703c503150301248290009013848055500d50004103810000214071101c91007401c003203441100c0c244030303480411a0502c038007904048174084020300990880410800100101c40007180c05503102450000301103130072842030007005581d484580c2e8203400340e1223a90400ca0310340e051072041c40c7d01c95082c2c6182e8000030700091000c0d0340079015503401103051400044801200c8c3e06000511599040000144016074402d0720717440c1500c1d0040b000c0d584901035031800106441d81903802504902501400141c0c8540c040a600303608040d01d140104040d45844080c2c2d260800900c40b0800b080c008501800705502c210f1468001c545840b602c5100300c512034000c50100c030082014410b00e5000d4115211319014417081e40700041c1543e1410f030f562490818142d12490181990 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 317252580 1250 317251330 317251339
    0x62a0303021c0207050a0501050105013f1406090a09030503220807060b0f06070317060102011e020712110a0303020304020307030c09140609010b04090905030c2d010b0f 74
    0x2001d20b2007a494001030b04180d07846003000c543d59800707070420300da6543e50107004071090b42c00c25002040651242446040341d600c090381090b801c240c0a04c2c41e1508240604a1800302401540c0c9030b050a1a58060450075101c003a04042650034401d05004000000a02035010075051010a20000342e0202c1201d5000003503800c15010b000c22402046281824002c01820500300881d00d0b40034440c842d440b151080c90304848000805034400180420303802140c00c09404100c0c6040c10140c808050850a030380000e05100000e4501300c01c0092900701d2441e080040a00ca41c04103515040201c20451417428401078100042c0c420704000c05281c0d14042040024105a004408602107460030485040690760103c0e00ca0700140d20380c201d120003058a0302e030144640340080046003082c103000141505907008411710314076250a01c0921030260088a1041720548001c1001d034400e200207100d819800340d402e5030610020000c02001c814060f095416040e0540d26007400b0a19942e20f004401081440030344 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 317253830 1250 317252580 317252587
    0x15060a080a020c01020a02030421080708180a06020718020f03071407052a0906060f0c03040306090c0806070503070207120203160b04170703050a081b0f0601062a030302 74
    0x700920068021581c0f0307005158008a200d40910790040060419079080d02c4808040719402c10704084d422018171005451400100210008034040400a1510401500480b480e01c02d45c03201007090744e55a0760001c1d0068001d2102806085e071000800d090b142c01d901010741c282070f19410700c0e025611020300700d04c00340700390310041c103180c041d01a09552404d42c000f01a16041c001503011200000c0a46c101d58074402d501c00240030031890205040c50042c100030b00384905203d03901d03a0342c505070380c4401203c0100344000c1c400000001d1003406121040307072242482115032442c000150b45440c03005004181844810700410106950000c3c6110450380b8611401c0040d450300c1c000b0900b0900341d41510700082007c004045094401e060040c02269003622420390f50140c801d0807141c4510280c00001c00c140c02640824012440d002e0180110400072800c1e8103101c0d200c111001d1502403445000186038001d84010007035507401101d1984036610300d4491212110100d50a1103400320341080050604d503010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 317255080 1250 317253830 317253841
    0x507150e181018060e161d0117131407030b040f080d0f09020f010201020a0503010902071703070f03060906063906091401060f0330080f15060a08 64
    0x300b0705401400c101a1040101c001540304030f01034881405020105800d10010480785502c0304101003004074170f503840044548000c846400c0382c18680160343e040042041c44421461901c00d522806100000303071070f124981036843d1081980e042d2060700c6595801044007080450110001c00740c0c0700c1e5021200e889031200070b1034a083c89019001005008500d00f403410008a41c55a0080740228000c903103428244580400480c2030784540281840002d80a000401400d10136070040d264281c46a81c0302d02d840c1c000303101d10a516400407510500060000d90a04101c20f42501c100710203001c3c902800d10610f401c3ca400540700015810ba03180d454003c1501c10f0030140310100c031110703068452030413100840c9241d040c8000039004085042d02c008030f2010300010355040500c14981191000c01e40303c142a171440d1523480c3d882c80030300750280304603921080a4000c41d00d80130889001ea0500c4d00c034860039090415290340700c104010204c403a9500f6400714186169202416180d6550316032401c581d440d82d85 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 317256330 1250 317255080 317255101
    0x809150405120c1b0604300203030f03070315060e010806010216060c06050f070c0314040e0a02120624130803040e0103050d080601091a090a030507150e18 68
    0x2511210206040101d41d80706103402c042020241c4c4100041e00c100010049001c0007894400c44c4102038042240ca4007006842c440c00c1c840050300e10295910a03040070141c1c01090866120001c0c9811881703000003003014854040c403030202135140507002009502d04103140680040300c80c181d00d9041c0440600010185d038402c10003083d84207001c0301040000b580e00c60000e0414007250358100c6011381024005180d440154102c544030320807130740d291030103035219403800d544555411a40d6150f106040102141c0100e412000300d024101c05480140c2c1ca03445040d803600380c11009803805204140c03080100f0028001001b80b00d8840201750401c0b5658400d0b4203012480f16101d910040903404003190028085041080b910b04a9008100b07a8a001d0306404d8210b0300c40754112070321400715101280903c10a03200030006c03d41800d020b8a03d602c0c1604400000301c1403403241e4001c858a0380100e4041c0040c0c01e081218841c0f440441c14460f07240300e100b6000412088000752540703100c041c40c000007030303102c1030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 317257580 1250 317256330 317256343
    0x80702011b060606080a0c1d12030c030c0304030204060b09100e030c030609010e0f1609020a0e061317030a0c020d030c0206070b0601020106270e010b03010e0a120809150405 76
    0x50181040112682e911300282803103c0c1140c0346500305161204e00543c10340545018581c00c503040c01c1d4508660812420400494140d032008925440284819207590780c0c100010400b11180078002c60b00d4500d10700c1008183d0b09140c00c04940000140040d1203240c40350034a0544d01c402c43e0410004c1c03160100702113403500d20fa00c03003a41d1341841854144101010b0650211030b050000a083c4c4180070501d07491149c1e1100c000c022295004841c01d0104102d070304030340c05032200240340c0c0341803c8010b01040000740300350410900403128401c00c5800700f00400140a41c0c1040705103c1014600301351410310082d20b0403564123800307070059213401c2c030f51420188500500401603a00500c21a00c400042c10504868030701110901e000d50310b001f5000c910703145c12821109140313080d034016002d081511110100901038520b80c81c003031507481d101024916a000c2c01007162100c1d0040091840c5c86440c1841d05075142c2114020003482020070034494140004614841b041a41313050b480c4940c0c4407854402d00e020f4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 317258830 1250 317257580 317257583
    0xf0308030a050903190513050904020d080306040207020d0506090d0e0609130b091306050901050411100c080f07060f020a050f0c0a0803040b01080f0114070c1718011b080702011b 78
    0x1850100c00f961b81c020700a407403458001d03068180440d80300c40902550326401d84011354450013074803160000030203810045a0080c00688054204441640070411240043c0b81c22183ca03000340080080d07040703040080e010604800e02e003582041e4840070204540e8498203005038000d10000060b644441c0e0380750003400178914058008070442c0f90541482240e803960800880e0510704110119180c40d44c14060103001716000306404800c8100f039810010080d8404c40184103001c08005808003084903080501880a144621595180030f9031811008032010b60300f0061203144140003004d109644001950383d040e41aa403030b00d586e010110301491800c0d084200c020002c00d00081004104052201060b0481d41414102d0b034500002036481d50985a0020007001007450010025914038841c000440d5150b009012074002d034003041a00740c9403640484500c00740411203444c01c142c10750348250620030500243c0c0000d40100000d40d28000e880c86000d002a040000c1d03210002c081c42c0c1d100d0340c11f85c4100e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 317260080 1250 317258830 317258857
    0x30504090b0f0f191a04050a0605090f0904020d050109080901030b0d081204030212040f0513093c0f050c03060f010b0f0f0a02010e16030b0c0c03130e01030b010f0308030a050903 78
    0x4041e032403c1d440d00c0c6d6006014840c0941c10b0000000b070b9890050007680c0d10b0301c500074400002d0010032070510080480c014401d07a0b00038001da00627800b2802c03c6c440c82040d14020f11700700d541d6100c10000074041d10084031086016140c07065500003c0303641c00090316252200340d9035140c119182c0d802c040740350081100c40d10313440020000b0005002420460203600302e40d026203607499100c41c01d0708164102c0c0c0034031401801090318100c40d9016008050500801c140d400707804450068810607103094002003819080305d00002070b0368154107101c01044803580c501811402404c0624025205501820042c400c211000a0204640704900307c030900b0b80d003550702c00c0f4034440c0c0c0304c0070783d0800240a00040030140f07181d801620f0000084070f01c4241000180c0750081c07100034140c2c80350320102010350305c2001884001d000030720400700d0580c580341648005080f4000605010350450811500700b030810fa0050401c0c801d040d604000081209041d01d6104440c88800512607445045841c10743c4244a903a0114 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 317261330 1250 317260080 317260109
    0x40e07061d03010212090604060f06120303110f0409090b090703020d0605311112030417121303050d0816030536071e05060d1503030504090b0f0f19 65
    0x843e0306c00603a5501c554010b903c203004042018041a045036035600130422407040300326454011a002c0d422198101040312401454094521407004440c0c2260b04000c0e943c0ea207408059050003102885190464140c7c00540303103680c40c9d90f0001e401c601401c48010b211a41704e20010b2001c402c2007800908540ca040e0030082070b040101c1f02d042d0b041d500d11004441200b074680781e101c8a800c00c01c6480070041710032401103182509202c0825600102540310044501c20010803031540941080034002a09e0705545581d109411840d002d4201a024101c110811030908204071032000c0c07120349442141904d040020704c5403610300890b800b44a1015030040d100c0c015421011300d15010071a40300e80d500d00c41c41036808081e2600b8030400300124020030300740b15103030001041c059840c0c05801040d640f01c84400018002850343d2035140300c140154000c2c0c01145020030304208110142c0207105a10a08031150194240000c001900c04200e0f101d0103802f88500c51902c40c1d5240701b650044006d8044a05d44031030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 317262580 1250 317261330 317261341
    0x160315090519020306100602071701020405060a020114160e0f040b090907210b0708130c0b03040b010509040507150e09240a0311190b130302040e07061d03010212 71
    0x280300580368403c0f4002d04c1800000f0b0b010b0b5110304030003c1900c41c0b65000c2c2102a20788511202d168404080c8001c0c00c1d5800c000008503555840001c00d55900740342c0010814040c0501020b124a00042c03c0000085152440352041c0b0b50001d0002003034603088030500c072041d6800010600401c5040e16864024078104144400310134001418011110000050030384082110f050300e00f5081c1a450040c03e0042c114045103015004145007a40419104000203d4207421340304c043c461070701544012442c1400105100c2403104080c0c0290241c80103441c280c4c01410196a41d9545060300d2040200001d22201c43c0c80200b40301e4091340c030100780000c0c9401420b040c5882c0c0403400603442050030745818454056a00c003070520785003040440760450002d03a14015040c003480400343c260150460700104003400800c861340382401410302e898100380e40040c06401d40c4140422210001c0400c1d10760307802030300104010f070381c800c186002d00301a06818258606040005c42e019010342000780030a071a1322810440b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 317263830 1250 317262580 317262613
    0xb03090c150d05040f0b0709053006010603020406021b010e2808010501090b0405070c030c020a03140606090901020f0405010e060904141902090a0b0c0a0c1509081603150905 76
    0x81170a0302a1691000356290003000b0b075608500c3e4815aa080209005080e0090403288030b18030719864407003140031135034001410700343c1002d0702604000003090b808102401403c2e4100040e101000f41248400038412900300060149086034851510036920b0900520b0400700b0b52180300b102c02d5008005002107901c944c2024060282401070251682c682040f00302d162501c0e0082c039000c6c0e207407030712240c040c1c0c81d054030100e801c0b00c0d0b50780007660840061360000000965520054000440110103040e4605101c1c042001c0190050006000c82e8010b20000590305030342c0c4100d4085072030900b07048a40032280e00101d41680529401d03943d10503d00b13001c2117107103440300340000c0c03003a0001c080d500e4020a48200f003c0803070090404031740d0800c0302c00c0800d00804048000900e0046031050880e00d0000780d41e910040b040606810034205203c0e078000e0189a90341150300d90010309034410107455142c694680c140d002400c0b900c00503100395900c000401c1e164100ea8411601c0d19005015611910f0041c041d41 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 317265080 1250 317263830 317263853
    0x40f030204050a0b09060607050a150c08130201021b0d02030d03050412090b0702090612101a060f0a0e12010204140a0b0c0a0b060307081609060b03090c150d0504 71
    0x181e008605000000301010b407188207100c00305100420441643d1900710501110303070490441107486205514008000c505101c1041e0030000100c0e1010a401082810040802c08003500e05400d0850302841c8800503a00422407100122552045085202c0300c80300003440c00c0e85903000a50103004076091411080c0d40340d00414800d038001c9050030609802c01000315440780c901e215814460000380010001031030403804483c1c00503001004242d25054680746642440030f0201040b030043d0b036550308007401501401d0250f4146500b1510b5506240c101441d07070529102d1009842c0400c0113014030201103541d83c00c10a940c24481c40000c41d15640c0f10390150726181001d410251140000b0b22002561046203c01c94031f8440e01003014090900c8075548140200300050201a410f011711400440d601e4410880700021022014000d10707003502c0c010f40807044502c0c58100c00c003000010002c0004000c030010340c0c840d80001c01d4840d030b10031a4052001417103501a0700e00f008081400d00b400d03c0305000d1440980c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 317266187 1107 317265080 317265083
    0xc08071211040212100e0a0c05030112030c0f200f061611100203120f06030a0803060301110a030209010e041503020607060b061605011503020f060c1002040f03 70
    0x202500d500e038105e880c05e0b12508030440c02c101181c0841507042c0c1080c2190300400001d4030a1031300170072502c0140185d83c060444c0800d24810540700f001f1040c0c0c1d927a00418403c184162500e040503810381311084581918010303039040c999a01e81042a108400c00090103246000440c900e0007aa40d0003580b025258483c0510b03070b114464035941e0100d201070500d6405150303039425890525660740c501502c00c10a6012403010080e40d0340b80050090000e6402142d51601c80c1c0d10640000c4c01740c003074040f21503014078001c41c00880003034054001e01034004c0309890321042e5a00c01d40610085400380e5500040e00d8800c420204003500308000203100c0301c2d01803030010070107026200c00b00c1c0440e8011103058011030408041102400800c2c86403410b5a2084503c1500f10b03031840d000502c204010303106491081c00e00188420305a681000007040d540480081076468a03a22030000303c0c4e040d5103210 = true := by decide +kernel

theorem cover : BRFrame.Cov 317086330 317266187 := by
  have h0 := BRFrame.cov_init 317086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 317086330 ≤ n) (h2 : n < 317266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
