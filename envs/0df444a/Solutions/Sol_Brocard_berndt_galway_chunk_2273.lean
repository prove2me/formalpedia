-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2273
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:12:15.238781+00:00
-- url     : https://prove2.me/submissions/9cc1a501-17a2-484e-8600-5cc7b577a159

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 408633093 ≤ n < 408812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 408634343 1250 408633093 408633119
    0xc03070b03100b0a1d041503080405120c150702010c0c030c170a02010e01030f090204110a030b0603040b070c0213150e0907050904080f040b0d02040312030603050c13290a 75
    0x107840c070b90360028174200b204450b0300040d80c0300e807039960304c60ba0307402c8039100c1c80745c0d0b4002e074600460042100e00d1711241b518042c0700c0d10580708100038149412004034290299201402a000410061859500c4445038030058404025107140500310011211000041141408002055905070804005d108908909095881304c16410080c007013050030b2080385d1554070a6003d41202450701d8001314a09403290081350480f103140d5003030140310350000703a101e1030b80d0707003501030302d0740980c0241c540c03c0c43c5203800c3d1540003010b840030b0101c3c2e00700026111a08259030354a060902217180d800410040700c40084640740c144142d80c400d4070b441c9082c690003e0303603034000802e0170000c485024114501c02c1e030300c81c1c0d50a00a0b40c000c0c1640d403080c220510001c204260380d58068080034080b890016525410340c20109912040040d42c0d904041c2842c1007800011300c046000c521050b801e80e07181c01c41c06034000b03105000c1c00071f008000300362021142c150007561070302c441c00c644650800d8940701417050725140c5d06101c00e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 408635593 1250 408634343 408634357
    0xc040e2508060d0321020f121003020105030a0b0312030702030307030501060206010501090e0c04091409071e06050c1510061107150c1a070903020f040912110c03070b03100b 76
    0x440f6080b9803502190003a8000841c2c01c07066001c40e111055803010f00b4049800c41030b00c500390110007003034840c07190385020403094110030880445002985181d000070200d11005045400c01030300c2d41150310750f64800b00802510300400b100031540303e00e80840029541d0708115000000039041200000c0c0660000c520340d4169034060b92080e590b10304001c2d442084880241c061208107008000015144072644581c4600503400c00b491503a40c01c0440705103140c00850380090207028030001c410040c540d454005201140c5960170829141c2c22000d601c68140340740400c40b2641c0b00c0c0705100b003003080e001a50000c0180d85240e11403800385080c0f4890141e030b884807402821609030080c141c00002a004645d8801924899039038080903100e00000302c54442c10a8680101040c020324052003140340124401148080560302040030007455101c03440e00082c69503580042c0608404021901d51080c0b10b030003c2e0344c1010302120b146aa64000c800566032084404401c481c22b0020301142e03140c541c070221128 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 408636843 1250 408635593 408635599
    0x50312070f2003010b12060606130b030907060f0305090c090702010207020a030b0a0617060619270e0c010905011227140a0c140a031e0302071a120c040e250806 70
    0x4032354400040c0a401d81c42a110500303440c42c04600060f41c12185401540310344c881c0702c00740891910300302024003030074541c003080c106040c1040d0070008401b00001c0d080084000c11a842e03402a03c581760103900a08c25514060f420400904011051141405585002d040e043c20200041503581841085400d6014008400354104501052041c540001298402e07181c000c1c1d4120f04903034500c0140c6c8200d010192541c410b00d2a40d100071080c9010780b180d211082d4030b0390090114600e04100090111940b4040c003410321001a0741c68144d040e1a0f48140301e2000600e2100d001a41c0703040105130342c0150250221240c14210318081d1102c880440c200640a50000070841160b0509107505162451106039030b42060000c0c40001c04100512842d80ac1102d407075000b102913201c1030500a05160490304208003003800c0c90b8007142e0f903015407002c4500609030383c0104506515070354000480c512456000000041d039400a0102c0d4460b910b90010715922008460b500a003880b00c01035484030000c9804580c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 408638093 1250 408636843 408636853
    0xf0a0309030809040221060901152f070b0d27171c0507080603030301060f08090f0109080a030b040513061a09010612050a06050312070f2003010b12 65
    0x4002002c050251281600080c40581400f40c0c0d14184001c550704442ca4807000e00e404401c0c8400c034100520f02d140901200e030161b0010652402c000362402650003550145040c1106400000445d030a4001d25000b0900b401c2d1102c0c01d0762141e03144031b260401e1007400c400768075021f2820344004a0030a03c04c030364415030301d180b0304100e0300d515030140c200b00c856640040054204003c005500b00e10110341c440b07085c00c150005050034050b100410380c2c5da0052195002e5030040005002054008240c10301c00045403038503110326511400303050f01340048503c06544960038040c41c03400700704003800a884141403d0b6420809140ca0400b048155503081d19051060103c1c140c1104c00b040e99900308650408804907408501801d11021595041c0f00368040740c001001d480043c1c6003960507009098011705042000e000b0b441c281400a600c80c030859102d001200c0e000035840c400c1200c800c103114104c1c0e4020304801c0c2e0803940c9842c0700942043c1c000c482031295113044810f0815280880300c40705050b0b0120700600d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 408639343 1250 408638093 408638099
    0x9041b050d0f0605420a110f031801090305070306022215050d020c2b020129010c081c0b0910051207080a0807060501050319030503180a060e0f0a0309 66
    0x6461151101711540c01101c40c03d9a481d100182e18298075521803a158841e0342d81d42e04800024501600f111a031401500080000d50351880004241c5584d14003030340550745c4c0030341c030500140d94200055200804901600d2000400d21a0769030207002d05c0c8a24481d021102c1602c80781c0042c0c1c1200324014040d0440b03140345c0d550b08076403182014286c00ca10300140140b030b105840044900e040440501d44610707440d1a419546482503030b40c50524a850240002d1040c0c1d0085004e13420112162031101c02031010300110031072641e00c5031055440c1590005416569085c8582c1d0884d668149400c000c2507050030f003940e00b80107080a02e0a5482851060070100c182400d2504003c9104080b40420046210340080410240d605008540215110307288030b03603840000780717424800d4460503400944260045900c2d80000c098003400c844c1880d1340f40c9455a560b40e01c0119104401029440c0b03240036102d809204070802005030701415480031403800701c0c1d00404402c0b14840d0ba0f960700240c003d0001d21840700170 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 408640593 1250 408639343 408639379
    0x6040b040b13061503170c070b03070c12110705370504020a03061a090607030c0303021b060727051309051f0f06140609041b050d0f0605 60
    0x2903810602038844103030600665122a0295101c0541101105040b00020010458141050b6401d100b91b03019880c14202d0480c485502c620352440b402101c00d01c00800a09070900c03803000902160f522050310240840c905038000e16000c0000203410041c440c0e82d07130100d802c0c0b800d003813031400100d840303031481001500000e01031b40886681a0190355100301d01601040070390346ca0024155440007590002841c91400745c000302040036070404480c0e0b80408004207a61515104210b584440e018107043d19001c001c2c0c6011002031160480d4901461840009207101c040040f035441d0090b850b9640b070b68a04440b0032110214003040900d004500035045e64200803034280202c905041030b8075601c0c006041c65003621414240400c01c0107401101d036000235000f007084441d1203009050001c25501304111401c1210b01d03911032030065441845010080f40c80d6142d6911354201c0ca50300701030000c200c00401100c4801070551f402401c18444014144211043d21003c01c0c460041120001494071308006000040c2c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 408641843 1250 408640593 408640613
    0x703021312021207140418020916050403050a0305040302011e0e011809020d0605031c020604200d05010b0a090515060325050901030c0203120105060c0f01290306040b04 74
    0x20480c0c20903881c000180f400c140a22001c402810440c0c41c50780e08100d49410441103800080c1c640c0c80c0825400c3d403120250f113070144242c1e0b100d2224808885141548001278030030f40202c1e44010201d104000c400c004050740b203c05001140d200380c80e050180c01c2c0080c12400481440f46100c4000740304000e04a225601c0341401c542951000c51015400c0c544403500003060740c0c4071076103200070942c4a00d010040d90500f0410b00010a002e04188030500c081e1a60003500e440001e03201400000d80e003c0300040145c0046801500c00070000c052401e00d030701500c1c0041c06400d501030340324440c0c2001040001d100c22240101440344c21502c4480d5481080f0004000b2541c0026160701c0c840351020000a0f940380708484c211200920076210342d0748508403a80010183c410703039040f1108541061110b01c0301d00a108107203d040d2007007111a20b840f0000b03159030780c0c5410201020a075041d070030040d117003000480d0032400c00d60340a44007104500c0031a00d40d0a040d920310043e14024240300003d000500030601d0048 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 408643093 1250 408641843 408641879
    0x60405060d020604080601050f0a14060304060f0903180b1e0a1112030f0c120403030b04020f0f300406050717070201140109200d0209040203180607030213 68
    0x100078070400160041481c540080e04445d14542c401d10041c0300740d15212460412500b07084820000307090801348440614509410031030b010342c4020010404000094010306d150041d41d0300c04101c604014217000301500c00b4004854003403c0c802c40007041920450045071002405c803418041c21032400c0354420001c0c0e10848416040100300c80c0d2040d2100300c140200c00c2642141014540c40381844803180000402c05415903c06503420028000380502c1c0c0501241d00c2601414002040d006a0011074043c0c03003440101042c101000500350448110280038240824108452f070381c0c0400b8070905100003002e800b1a54008280b1000001d000540607001181e002c00e07185001c050b40041e407481c40140c48010342c0c1c3d000244c3d464100354640d11010000042c0100440907051000800e008c05079100451140e15043d400b500c0000c42c48200042a01243e514002c050000c5540e85025240a0908030100440d003550340503c2011450035071117402981d00c62030b001080c041c485403501140251a40d0040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 408644343 1250 408643093 408643099
    0x14071205010c091e0308031911030a0b0103020702100e030114100602010b030a05062710020a0f08280209030a03030204050a0e06061204050a05010f0501090c050c07030816120507020a0b0c0606040506 87
    0xe108d5611440341c01440c40a0a01c2e40c00a5280c0c20f00038001825203a00401c0c0c82c6c10148140b01e410050f9407044000040b810381802c2c00700603162040e000c43d0150074005010049083c0980500c082007900f440000112a0694001c00240c10759a0400d40c580f0403211018001d40c1c00300c4089400000c410205181d070a43d00c8a1103401e481350030068905104082244074440380c1d0218490310320a4000d004c8011448840c5020081443d020300a0007800522000028480b4901c100500c0c051100e64100c0e41105170040441e40521000e140c010065405401134074001c074000000003480c0c120b2004480d02070f5500400322401c05001011581c0c011400410684d0940f1900c8000703000b058003841001413520521002040d40c0d0305150250303081e900d90418020030460100040039441c1c4011944209036035200d45034640c8c401d240d202c0d54132103440701e49014003000c4161030f61424145d0010014940303d4801d8403200341d07265552801c0840360290140c4044179401410001d80c90b4506070f8001c0764004001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 408645593 1250 408644343 408644371
    0x10f021501140d06090f0b010518010e100f0810060b13090c140a081005010507080904150b030a090c120f11060d15031e02010c14071205010c091e030803 67
    0x6070720340c0400d40743d11520171b0700c034010708940d4007062021005095002d0642518489200218000c0000c0c40074014441c0c103000404403400701c1c058442140540c07004010090303419035007640b9450069100c0000c2100c000101c0e141c14000150201030b04280c4000a02e9101096070003403800d06041c4c0030304140c401c0e860811428080c10214001084094001c561082e80c80031050314000d064920441c25682145042c08010b0013180700188182c03040300c03140030041d01c000c00c901121a940e94000310458120721210b11004c4200444a40c40703038006130f1858010382451420b181e660140d0103100d0780200c00901a01c072000000404107101205030410301d4400b504c05480c0a01140340d403002c540d020480c2483d0082402e03030070800d015444040c820a114411151545986075900280800d5410301006000815030380308043e401505008240042c0907545107040c00104602d00315008004070b01541000c10201d00001c191a1402c0d20540f08070302c05201d8651140f1f0031911200140d8000421001d540625 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 408646843 1250 408645593 408645619
    0x806190b04151d1e04300207140d1704030b04051f0504020a051e04020a0c0201020c1503040f08041208030109050f0402060a0e0301020f0d0608100b03030d050c16050c010f02150114 79
    0x9406103072a0070034041907a20303c0c80015288000e043c00341c949c3c07041b40c0c0c2c8540c070f142c4165140d40d2501d86e40807090303201a0303440c1840030034043c1400383e028a5001a00c190040c0d07040006000010860380c03c040001801094400b20b40280f110071648240c50103504891035120502c014104100e0b4842c2c081c0d100400243d2180e03600300080d059038044030381d00c00010703c41d0b0a007608550b01002030710081801140c817040490b200501420250000410203008a807500c1115020311050702c0498016214112180e0240c0461b410701c59030580c0284504800140750800150000911020040c051580188030520342090843e0440d0382a0a81407007560555080201d0600c0700044c0f0b0040c4a001d260000100e501450701b0b00d0981000348103002c502909003002030082840e034020040320400c1681c12000550358452028541d00c0e80100c1c3c280c03100d00341940208006000001441c0e09880b4801d07680c90011003500001262105041d0400c00c151020303400040c41401d40101e840c000c0040060094040800 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 408648093 1250 408646843 408646883
    0x313020d150f0615030902060d0510030b061c06020315060408060103030e22050709030b0a090209011413051b0708030604150806190b04151d1e04 64
    0x30161000311a480380d01c0486424299403401000106070030b4001c104a110702d00341c5129003020114029400309540d9801700d204654559094402541040310100030701c0ca006a07407842c0c87c05040c007050f00c4904002001443c1351820010441007a81c0300c80441211012950380c000281d04060440180d50103954010102510303002d020300010a8000c0c0240703150b515509000e440c0d0f04500245034001c800c8006aa103645028610002e00002c0c3c000740099284d89880044404c0d8034036420040010a2040501c0703144c034071f680c2028004078000c80311711903541d81e940c6e0b14003200071100d400385412421048400c03c21064a03405a54416500c1e28210090300343c00c0007944280c0c3c08030302c04455900c00402401040d0406101c0c0da150700c543c06201c40321042c20490400da940300d000b0480c5164103d2483c84001b100e5054200600c5244050b0043c0040c81ea440a11540c0b480ea0b40124140c00111482e191000394491501034061003094903030074004145541d850607401c10050068500a00f030880c1019224 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 408649343 1250 408648093 408648109
    0x4170f09010c08160602120108010b030613050c0901151403011d04060207080a08010e09060609040803072c0102100b0f09070513091b0206013204060602070e13030c0305031302 77
    0xa4400c2070b00503a121f00e032007a2864000d00680002c1000c0e8504034500404d40c0380041d0454022000b180c0c105d0155649141c298503042c6100740c1a504001c0c03000001409201c0307550302c180c40104c10340740c0001c0c0507241c518880301e90000f4803a000150f2441c144074800c04000d00c4035207402c18090003015140080325103c04141e0742c440c0031603a0006a003907004010340011948896040003410700035041504242c000140500c9000d00040d1401a0000c0131038400d038061040b502e920540d80d801c2da8024014140c11140c02c122180c000c5001d80610705404482d00864815860074010080c90181c540c0a440144908000c3c001d10000a105041010480403000c1d00d50b110010a12051b000c0b84440030744044840300d801d0003070700000f954442001030058560b0b4005c9401001a82c03e07401500011941c2e035410507500c289481c0390440d1030720002280456010820405030f4002c00c07400207964a4081c069400203034604800740026030a044d034000024032520065801000c1d410f004034407023101d900064400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 408650593 1250 408649343 408649387
    0x141605060414070b030601051b0c221d0a06021c02070b160c050618070506070c090509030c060f0c1216031a0a17011103010e04170f09010c08 62
    0x30b20607070040c0480d2a4100045805400340322040c1703003541030000c00602140078001a2105503045055031910700389080042585602008081c140019a1904014510f0300001e144400150512440c503071500f44500c4451104102c1c0c000600050303100b034590348000c2d040340010794044010040c028001c907249001074028a13018095134411420318000c084040118a4210012300c03104ca40c80384045403021030907642c80680312242042066104e20100d04201403a00684c1c1e2128000c50003100348002071203a0020703038140400c100410b440751300030550b59003d404021400c03a07201b000016031414990b4030040c1c108411aa00b0ba0034611001000d080030300e001c0f69015a01c07000e500744c1c0040706500d4005c4051f44c0c3c0f9000111071540302840081420072016004040c0c5064500680d2640c90600354000c3c0348810780081100d0302c0f940c6807007035001c11a605039420fa840641d0041e030b00385040400f200b110484680914841c1c9800e44090040d580707148450307030985e0340e544107004009a5540780c508200d02c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 408651843 1250 408650593 408650603
    0x50316031713020d0210050f070804030521030718030f051005060f060909060303070606030311071a0d050901110415170105090f0408090301060b0304021f1416050604 73
    0x1d0a0000400d10580d504020140051044249460805603e400030754207045134050319040300e1050144020f0381c03203110b51300e24448551000906c080a02c840e22010700700342c1e4840c2e8140c45480c01d1080040800b50384140300407d10010400200300030600960030303102d250548181703001102d0b580e512074008244012500f525241c1003503140c0c812504030342c4515548400200d0b6028280b0f4011804120303c2d020b484101f80c09250440040f4002e43e4041040d2014940e0240c0c0078000d50f42c0341d107401000620460800c032100e01c56000d0105040e5250186080400500d00c4441d007090f5a03480340c100607041c00341c10010203541e40c018101802c1c51440050015102250070060030346003c00009140b0300300c940328500d14500080051102d035884111243d04604504403000d010348070303030034032194500c50500980e1340766291031000a5900d22080145103d14004c50310b10000c4034161100c032060080e81804da000069480c0300303442e80300000e54080d000c140020b401d55400c10750301d55110340c50094140c400f568 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 408653093 1250 408651843 408651857
    0x3020a080a03091a01180c140c03041d04050c0d080c0d0522050904110105040e04050a0b06030f1c02030d0203151c24020c1c030c09081905031603 64
    0x4140004081c0400e04004200319010080d8500300c15140181150204e102d042507e40800c3e201c5248100e4141d030140c0f2501012a644002c1074644503540d510500c00c208040c60540383c01c1b102240400e1515200d141c002c1d002c0c0001031004010060700b0030789203000700c980b0300d010700010450310000c001c1d000101c0303c2601d41035a00c1c0b0107201d8200c40c2e0a11115410410302180c1e409211035162800741e550401e0348a820aa0f9a407a1000140c1b41c0740250b4020003180050001004140b0400081503041c103400340200840301d440d82e6062545640601014200c550311100e4096420945080440f001c00d205106590901c1c5440d520750f000c1e40d01c2511032000400308601ea2520a117001403905a00000940c80c0341c11509042d42c4201345001a010b0004207448a811a02c11024103030301110b4a0006071026900780410761190a04a0420200c0050003e40b40a842d035902c180030b98007580980700220018120b04580e5600303031100e105041011a1640002d00c42a903004000b008003e0f610351007034840d48 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 408654343 1250 408653093 408653111
    0x190e0f010807050f010c1b080f10270b06030c0607050a05071e0902071b09050a0f02040612090615061116050913020a03020303160c0504020307051603020a080a03 71
    0x5850b1480b240c03c100e114000b00e0109030556a000409507040c40d0748010009400e0b004050059001c1c42c4030380c0401414040c1c00ca88541c0c502021600d043e51040200f020000f1a0f220700f01390899010041000c03d1a031034500820003c40c0350070041d10f501440c000e08030f403a1016a100842c0041d00182d03411180756200c42e5480301000710600542c00500b0000b06410351003655084800d2013098648161107406034000b54040502ca1080304600580c0d40030068500c48039a5030b1b802c000280b4007120702c1085103290402501c02ea0703400d8000ca804541c0150ba56503113a0800c0c5080a00030310300b840d012200036a40d00742c00300c034428201c207124004107296119001c92030124003070704c1e003410603c5140c043c0c440d426002c00e100907591414455001400e40410301012000c0d0701c045010740c4255007001e03505101c00310f80210300da0500c0700c00d551140d200300151550700f03555405000c16400143e42080104000b40140852030350000c02e20042540a4070450301c40410310b032100807155014094550000791a0386043c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 408655593 1250 408654343 408654359
    0x14190b0c070e06031e10090b060405060a0e0109270f02030d03020307090b070318091b0203030f0708090709020d0506011b05061803120112020108160e190e0f01 70
    0x110001c1c500d90b1801019480c2a0740001c0d20b440e425440420506600d172001050b1100402060f1003400700d01c0010803503000981068000080708451251050781841c0000d451400c1096a1508a4204580c03030074150b401e02088030003500d003190b00316210411b4840c80c10200703000c58071803404440c010800601071402d24014075042c1564003840c03d040c18010014010055800504041110000c1101e152a0b05135031600b205c43c600c000740d1a1510300030a003c01315608100b80e11000038880c58000e6419419a140403da07124081105c02410a40d685800108403602503040b85501c540c850007901d00b141c1c0c50300091001c0343c01425480c00c90980d03070f8003002038650f0404000c242242010144041d540c00070b0307541560b2100d00801100c051010001c00030a001c2d000c10a640280c2480f0051403460b42e103440b511300208170344403001d0303000035a4600801c4500040c0b21032011079541690300c0089054024060110081010981c000159400f010020b214204882d84500840030301c1c0b511a010751400c0d800c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 408656843 1250 408655593 408655603
    0xe0f16060e0105070b0109020706020f12010806071106060d1109040503040e06090c0a0e0103150b27030a11061204030804120f0c030813081902060c0a0914190b0c 71
    0x3001e818040c0c1000840045981440700b0350448605100140c2e90711024030b800030107802030002502c1e0030480400c8898100c6407040400781038405400c1200c8299541c2d0900303da42c06001c0603500728a4020f400498194140300504c0e4031900c0c010300b52920514240b2010626140302120150b801d90008141800300058001507960008012180e545030703410100d20100c29441010b2500050104040840406034041e41040d01e40803040e481010714503503240f048100b02e600421002071032420040b14281008028685c40010020180c01040308000958844448800c2d01d031116510280510440c500c00000c000440d21862080e030b50781700c4034140340c504180e008000d01c0001060000b01d410001c1504d07805000d104c50a078251400c41c016440e90b004443c010480413401038180b10b0001010840d60380284e91038541d01082d075013250081c1d0345003003000245003d03400d41e41c0300240940000300034519250510011490000780100c40b00c6460710008404525250300803820340c1c8011540140d01502401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 408658093 1250 408656843 408656867
    0x3030c0a09060f08010e060a03080310030203010506270705070b01140111010b0907120b0d0b10060903020604051e03060103031d0607020f040c0c0501050403080a0b0609010807030e0f1606 82
    0xf4901070945442c180640101014010030306001c0314140029001e0382c48892800081d604036040564038103080c41c0d0303100c0241042c003003a40650308250100c0d5490510f4840348a01c545130305483d1010f9100084d035000400009080d50040140c01d000f52004601c4054009008004519040080017040800501174201e00f0b18181c002d40d1408022300d086407580481e03654050420b1904910354001c80d03000790300a1900d0505581c00800c410240020007070380414080c00ed0f40001c49070568641c0e25602160140741900009401280600c010080b500b0726074044950705420041ca2480445040082494030b40240d1069000848069884480e01c00b100710750382c21498241e0725246000b02d150003107003c0c980c4048034180a5542e4003500340a461040100035585a40203009102d6402c0c030382002800c010041d254400711600c1d100001449284c4042160322071001030310790010550b24018260018504840f90841c02d00404080300b210303c40a21100d15001c181d00000580c40b820315130001c02e0000040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 408659343 1250 408658093 408658097
    0x4020112022206110d0e03030408061e01050d0c050616050a051005101a0d0b1323090d08040c2105060c040503071a0d0623060f220803030c0a0906 64
    0x8000398141072005c103a00702d20500d03604100c03c0d02140f000100e0710303500c86d6038800080c500a4009114080320700382c1d0400981200c240d5926000c0c0d80340c3e000c00c0340c0041d506900030b082c00040c180c10061800c042c1c000d850030442011209454001c203840c0c1c14180f0340290403c850580000e00c000444891600c255074103c25040b030001d5145027441c508640c00804d000d40c4440030800071400030b20a048a8008a41e0100043c2010004c07000303060900015164020f20360700090f01d190704c581d2601d00d9506480d4400e236030b100018001c2c072402d01419a25950054415940c09809490118030700100100303070032006084e1021441074034604d0514900f08200500400e0311100100000c02c01950000381d04800c2e00c0501c241c01c5220310301c8810551651141104800c0b0482c00c240c400500148100404828100b441e100b07003584114002c10070030f0912039488184600a0140190580010080b25444541c0443e200c802005a1107000d85451034008a42c40344032024000307110248190b0004219001f04414 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 408660593 1250 408659343 408659357
    0xc130605010e010e04060b0f0a0905090c030117010e01111c2a0302190c050c030c130b01020109020316080d0206010e0103030f1b0b10061107030b04020112022206 71
    0x2200081c0002c0c1001c0146040100c0340004e5825503442e5841000106017140325103580d408000b11840301c1c4e03004002050301040b14501c0c001a01d0900c4070400b4481c031a0b08101c03500d50f0703080c05195448860240c41e44c007025940c0785424050780c0400d206620282101d101340c29103440395012446045032905564074841d90421b07580904603040c1000940301c2c00380680c8220548202c516040f0001c2c00350b48407010013440e0700b00c00c410007250000500c2c1c20182c003610907941021801010b140c0c0d0740861450164000000c1005031141e92219444081000c00501c00841c02141c10340000c1c0c900700711220000d00c400c003180ca0401040d40200001e0611900500207009107625106c49190070302c1d014403020701070026540c2c40e640c80343d03c16600e070500d050f900140101c6244583c2406a00c109049410061160a0040106219009800b0032411042c003000030841c0f10f003599101d0107170700b00c081d00032810300201001c20000602540081d1148090240d81d40f0048100034800c0c000c41c0c00700307034848024491a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 408661843 1250 408660593 408660599
    0x13020301140f0303190507120503040201080a0506090c09030f10150e04121214100905070302042102010e150d0507030b010804261c0f060b030703050a0f06080c1306 72
    0x80402540c84402254400d15130440c00981300361b40790322917084000c0081d800020035041ca660001d01a6010b1350003a41c82080d10b0381d60072294403c981c820f85132141d0007103984000a5803154010014440910f010301a989810401c00415240c544140016518a500c03000221405450808185c0041541180b250081c0c11302c1d4a46241041c1001220300c1001400c42c40002c2e180fa544d040380905182c0c0c081c40304a14070749030212800ba240c4d60b00a1381038107410305020400f0039200f4000e03201a030305c0c0d02c908169204181080a1241b4040007812030502c0300e640700071809981c59a50407041042051441e0b9507900825115108680004200c0710a02d0700d01482c1d01d4459a00200d40c03544558000030383c0006002c51040002c01104d030003143c2500d56400550061400c010031102105030300e841c00e09002c0080c04074805d400b030743c12a0181c500c10aa06100007000503120380c0000b50440000c40d8006041e2180c4600a030613512182c0096400f030740030603002c01d02c90401c1410003460403613401c010802c0741d003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 408663093 1250 408661843 408661849
    0x10f0503010e0907030c150201140601140d0608030a05120c0412080c0f010c0507051c140a05040b0d020702090a1e111201060305070f03060305060c0c010b13020301140f 74
    0x1041c0034501c0b411002500007121601c0070040d400195800101e01c1103101d0740d4a512145664540100340300550902800b01c480c524900034041c000c0005854000d05504203811700b41003504690b01004078652500307400600303044180010201215141e4078156120030400c0050440c5c00b0203070810108110030402041401030400074407210603070106100e5602c001c2003030b1103854440d030b10614070035a510b41940440155009001171000f2441403050711440c854882e003001c1c1d072403100e03210b0b103021520491491070148080c038003c0090714924103100e42800e85070118103800707810120300100d001d98000387d00815450080041980a006c80d4000e01000086910441e43c042c402841c04403a2510740310318040318000074003585c02c1817641c250220b9541d80d41c0c2000502414050301e0315004546001d0464103005c4c07007030040c0e0013981d40103401001641c035152810f260540c00f083c503102c440c2d5038903072078140d1940c0c60b00640c01e16200e8004c1c01603182d50401c2701c3c140740d04940303e95052140c1000718034000d00751 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 408664343 1250 408663093 408663097
    0x3020c21030a050a121a030705010507020d0303050603150103052103040314090a0b030c0415020303040f0b040f050d0206010501030f1503060209010e0d03050a02010506040606020a0f0203160f14010f05 88
    0x10b2030070b2030880e44640001609540040030540706001c1d807170820250403480d840c80342c21001950001c4003140c0c00150b96400550780e91140f4080650020200550035010074000d81000d42c111101808440e4483c507000d103403120500c42a0021505074104030040c035440004210b44240c46007800c4180c42c994102544d010708400c01c50070b4140c82001011a003100903554440d03030700005140302c9241d04d96900d0726000f8108140d0003406045074440e1589801c8695610010960788500d81c000f03800b02a0849644801c00400c100038000c0358841083c0849a000034810311401211414031307001071005505000000d0141d03108121801d00c1c0910308020241e081a203000e0020440780c0040c001661403007028012201c022072105419040410003401000f0194014000c01124215a00803c200d0700e900b8100801d403159481100010b038002130241011070b0b146410401c0b42c0d8030080407540d480b2038801810000145540c001c1d20381102d4040200006010b84410001d69a003d02e006420720100c0c42d4003410728 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 408665593 1250 408664343 408664357
    0xa022101142404030501060f09020a120209210a0201080f090304210203030406180b0708030612010e061e0109020708040b0a031512021201050405030d090303090f03020c2103 76
    0x2a074100c0402d0076a01c1484070070400d07100ca4105410341e1640ca904004d0f001c2e120502c15041d00740040701d4000b4205000d4400d4030803d520b40c0e540d8a032160302c20880d640194104003c0c0c5903201e41c4500107040a260002c00c8040b410100344060b10f08010a40000f4044400c001c101a0080080401304824080084103c07001d80f411094014120f840c2c462090340d4541c1c030311b00f000390107202c00240484c10340c0d0030031a1125410350081501c614207842c2c00690110380610000209111801c0c400714034a440c1c0f080104000b00c422390000a5443c003911031040c609401500c44d81519121071405150601030001d04c81c0c0134151100b010751800c1d209030b54800103880345104010b4404e801003000e48074540720b138005108a0651b04120168180c07907151170b007449102804224456408400348426a034010b0150340e10a54014000d107003045800080341e4054001d50000f20101543c500d03107a07001400d03e40d58542e0050203a070003441e0103c01e030300901901848083d54401c12024260440da40340000200316030340 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 408666843 1250 408665593 408665599
    0x51207051012060e040f140d05040e09030904110a020f1b010e01120608010506120a0507060f0e06030408030a050c0711060d23040c0b0a05030609040c05090a02210114 73
    0x1110041c04000000348090782104804c0400d00003800f080c4a110200044c5c43ea000744030940003e44074201c541d035562000302c10100440d2051200f00144641d40c140c941d4440600c10070713039280c001c2400000d0115840c2c18a00401ea6001041c07980302c0680c1004201e0030040348500800d00ea1b5031800d01c0d00090542000300ca0304002001c00c81c103410741d100d54102d0b01d100014010a008191b128202c590180400300c61300b90141c5060401410110800119400095007200c094800c3d00c1c1006000c9505240000c26881440981c220017040c03070f12401d0056225500030302480e030f200d041c14100300056501c00323030039001e89843c203100120100e160791548800035007044405035610780460b99120064010340030911049078011401c80000d40444041c44c0c4504c0c03050440c000b4294581050800b0790041c0b0884100040050000481ea4108654103507086402508200c0000c1d641e04006094801f00f2a210752065401046440900b8a0b0307406010703c2c00070482e412151981810400c003280d1002c0c5c402684 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 408668093 1250 408666843 408666857
    0x1506031521150506040b012105100b2107140d090302010f05090604020a0509150402071103010e030d150605160213051003030908030c030712020106080709060512070510 74
    0x702484541c90501c6684884001c1900b00911550002090300312030300c50040342406090022503201d0007079400180e4001c514407000d41007448802d0000c1000801d05403003840902c0c4007080f840d4145002d801040b548903032031595024055000048200094110710030f2000d400c04021b28007022800795500c44031600da0024041361203040480c0509101e40428404525202c1407103200900460001e10540c000e68100e12126500c0050050743d050456110940012402d00748266143c150000c118080c0282800d0318440310030070002e400c4502a0002d00340a500015040c54000068010b5110f040810507103031004a01d400009091480389074803c09025004411080465807914450101c1500001c0104400e02e4030072080c0382895860300054010031507810000072414000401ca603003580410000c2c600700809503840c0c0700c4182c003e16404c1c083d552289404145503c040001c440107050100c00841d5a5180c001801454140301e800703903801f82c108d04000c2c041501c403042445450302d55032501c01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 408669343 1250 408668093 408668129
    0x60d24060c0807081c0e0105070c03020712080f030a0c08011403030418020c060f07020f010608071e080d0201050123030a0308090a0602040b0c06010f060c020d061b0315060315 77
    0x100091061050800c400c0203017554249402020798040300c1d55031070800c020449500c81c2c0c5c40030741c4d02480a143c01001640459024041101c10b104802c00705442008024248011000740b0300715900304981d0702a00960301c09105440c140c0c801081350042c81100080910400c52601107078903441036000b40701c0c0076100961440344099141c1e046404210f5144107844d15403c000948140440703054880c12f006108070600600d820070107108850031240d030903006202035450b00307150541c0a007007220403034400c0e145440c3c0007a1a40c014401400b101c040d645c0002455810840c0c8071b6090040d8100a0100d203171040400c45240c1c5000901c0807a0310382601b00600d072503456408007842c023614194000c1481e0300204000502d08000c0d030203484070740b070784000342c0340d8a0703807604504090b0701c0d10307480744100040d607401030b0801600b0680040311440d4018100810380d18211a01000500c4204030294006592403504081c8802ca00168401514040c5002c1c0508014900600c0d0300c40b1a90040c9500b06245000318 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 408670593 1250 408669343 408669353
    0x40309050d0c0608180a030e040f0b061e09060d0b130203090606040504020a051e040e030903030703050a03020405120c121b04020c01020c01060e1902030103210e060d24060c0807 78
    0x140c43c04172010002c441040e01c903450014012603013004010302031400e00c0701d035214228950017100d0402034090060750411090440215203c101e1820380d15810808014205190320b41800401602c1000c590100300b60181005104a6041385900c08042e00d2040c4103100c803a001c0400d6982c0c011004840102e0180c44900000740d2540896005a500003014144038211403028030609a82200c111020481d0024801030551030388541c0b40b43c164590002c000003800070340a1381c054800010b19103001401e103900e49011038540300c1c8592034108294006440c01602e40340610343c1c4036101c405580980203400440c289540b400d404001c280d031142d6004074840002c40c500354141c1c5e2490090308000c2c8101030362130800c4100f248059841291030142405204040d400340d0084a040b01e50280800d02020304043c600c121040108418100b08000b039400b1503460781d126409002140c0000380c00054230148401c1c1d6040358900a200700c108850381d0241004015042901009010380040c6501d60314491481c0c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 408671843 1250 408670593 408670621
    0x180218010c050c030f0d090b090105070f03090906030b0105030c1e1224040510050103020904060b060c0105011e080a020604052e021c051602041a0d0605040309050d0c0608 75
    0xa004d80612a400c4d05541078400083c507251100c01c580c41d4041d0058548400d01e099201d41d03142280401e00030404e01d0b00003101c0354000b01c0c04a00920300045a1529010700d941074038406e502c03ea80300154400107110038501404400d500c200112040381e10725483e5620051000814400360344118030303a030829003284070b003030220907242254040e8840c0c0170a0381c1c142621000000f039805640602c0340101c140d10300740962041605890300207041c0b0303406580e15903070070780548440c0c511590030200c2404000102e007402d00945020f41403544865031000010f4108028142440e400100180d10400c80c240158581c007003104c054035400d0300d004e0f1000340340360940501d807616a240340510030035029200b80a030f540401c4c130044050b03690010907a010340707040c0c0031181c42c0680405c2408a185410502d401443e159110400007042807200e074940c0e1040100064400075017040546009880340b0822040603070101405000d041d00b1600181441e2250705c0310020341c003042c01600140000306000c11400120307031107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 408673093 1250 408671843 408671863
    0x911041812030f02040305070f1d0a090309051003091e0f02130b1002030403020a061d240d1b090812180a12050601090507050909061c0c180218010c05 66
    0x40f080d50b486559117400b40c2e43d000548110a90701a060341c010030461000c2186103400c09004040e08084d03200c8954020040c000002c08800707001c103217000000c4036203e1440300f00e0218210344000076a0780d03890608001c00450400d0342d4420324078103490800000c6085491031101c54051f034450b07d1240c6034440346801048a1016079500c00008000842d8580d400001003003500d200b5281d0b501a02e649150951741031251107504500043e80da5468100b0703040403000a12003d0382c004a1400b5104842006041c039403004100f020076580300c08910a80962811607000400024038242c1c00300d0b803804840c213031500c9044800320b4920800060101586070322020602c14020010322000350307181e40b80c00000340f14091003030850340d07400b80d0700000802443c10700c1440c0c451180e90320b46610b00800002049035604004004541c404004c0c5903003803201080e04000c088003403181e0b40714218141401c1c0e200446403604030440c000180104690755100500c03240e41c280c040c0d02800c200d8000d00351440c01c6030405480c81 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 408674343 1250 408673093 408673121
    0x140616020609330304021008100902040602070906080303060a1a04360b010807050d0f05161b151112150f090f0c0f0708070303091104181203 62
    0x480c003e112820a02c0034a00092030200b51101ea1400c2c541503030700c501084078007075401000b48001900c2540100341480d4014501141c1400c22a200d0312500c080381c0080d0440d40041e4400c09051003442c800c1c2c030030480601038480055046180a60010b10f0440050080d10f090b5a076480c0e100180070350718429070b4090456040b045810707042143c0b06451155940c00702d03008441601807890b482000360b00c202c542e07583c8183e503404103075603884500780c41d29409001310309002c9644045240385118035100d514040d0440c1e8825111000d00580001c01281154250944a401059010307000481c207599100e407240300f140c40490300c00c00c4031107582a98060038143c507160309001b00410100d104c0802c0706075044981203a482603054801018884401c42c1107035581c250468841c0495140d00c07007000680801a1054452840c10071540c2da06455a0003000080300070036180c0c0c041c00f080240c880040701240d0b009450401c80c9090300d810000d0f0114014401410b6451b100c00d007004101c2c801c0e0003145c41c0342c0a213 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 408675593 1250 408674343 408674359
    0x50a0503040602010506012a03051b011d12030f1b070501051008010606090e0a021303050313061e0c060905010621020f01140403110f0a09020d06140616020609 70
    0x14142c044d01074201180d5160010b5a00c0103031544000031450002c0161020514410800c00030341d400f03541540c0300c08440217103c440351a01103502d540034010f61040041c05880d0303a512030780b903005551401d5505022000669018400c12900f00da1460119502c09029540e0b100c1000301d014800385c031413013000805000c55003040708002d524594481910100c42c0000c0003049010355a803402c9a081e15580613a059100d00b02d8041501c04031203401a040c041452203444505503500d0f65204c0c6550712a00d035113034903042d030070600700032041e04980070103e245001e104240403d5190030005003034441445d802084103955154040512909600c00c0c00507107403006801d04e1060540340c14200840103c0b404a02c42c60b8210088804d80d486659145031101003014164286800c681da40010480d10075100360300500e0301280d9250950798001c2810040145010040e40c40c054154440159001d039000144010021100031032030f9100d05045580600b910788420051f441c80c3d00c0040c01d940b00300d20035281c1c0b000031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 408676843 1250 408675593 408675599
    0x302240715051b0f0a030b0f03071e05010c0f0b0709090c0903060f020a0e0d050c09070806030c0d080a180f1508130b040206030c12101a0c0706030207050a050304 71
    0x3548514001c0032800360100b0100f6609031030000621841c500d00c1500c1c00e081c00646403c43c00380d0000c14241c031000f401c28108000314130110b46010120b80c00108401001021440d0407031a0728074206c040c1a00703281c0251146042c2e201c81c0c2c03107104081d2005021105041c0042d100a215818406c05800001020301c10b0404400c0c00078624440341c0025140985030032000803900c04507108681c4544900e03124001c240c440030040010b40c02200c0025180d41c0624032494a0981d52402000c0c820b41d0307103480d20501d2f414004141840c0803510594280078966032640b240204900f442520041e000d02e02d800c100e004884000c100b0242102ea0240550420b4000041500c50501c0d40441455009594003c0255a80c5905403c02d02d03118001501c030000c44004140036041000040d0ba00140c1c0b0b12001c2c1c0341c00010481e003508030034101c84a85450340c3c0c1010a1001d0b0f4a030381d910400703880c010f040050600701d000c46160f4807022288a03003001c2c1540000c41d80700b000340031f0044100c05600176096945843c1e03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 408678093 1250 408676843 408676883
    0xd0203040617090a020d020a0806040b0f0c0702030c090709030c0803071b1503050601090b0c071401020f030909130f080c0709060303050a21060311040e030403022407 73
    0x1140c055507020902004030481100218144284209840d10081c0391607443c68007440440c0c04500003d0380c1002c481400801d08501c20071419005a209070040340c294504030f5211031191a015100d420842410070061025a80c00a4481035604044580e0929a200c0310340640305421203500045c80d065101000007038400c000301c0a00095801462843c42e0500341c0c1d20304070588070350b60103400c1d03011000c010642e1100d44030768032540d800b080c1030501403491a15400711002c2600a0002031b5165070000b802030191319500f494101844c0300c00e00003030280d0701d643c0941c0c9480f030048134115800342c40e01b80c00284030449007802a100040e0041801824500d050400c02e5080d0b201d5030042042d48615000082d003281c091041d402243e805603145818005240005c840b40d0301c41090114a10704105440740b485104c900c2150000c5215003144080b40d507001d0184400d0301c1d144040e01100d80c1082c80200301580b65554002004800411501d84504500903901418054160060808440050010300381d00c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 408679343 1250 408678093 408678097
    0x80612070909061b090509160201021b0d110601061b05070b0a0809060c03040b0f18030a030911040506100f0c0602070c0509090a110d050102120405010c090b03070c02060a03020c0d0203 81
    0x4100504d0b070184000007080d05803400b4580d84101030b040020f805c00100304030685418501403205a100162030728070b0740c01008007900301c7d8120101c1d491b0800c1040810a54000d505420341d40d00010141c081c039803502001034200341440c81021081c82c0444101c40070800c0a2010001624400302c02030381300c3c0d00c1e818000304003100c1100d07500d009204030004074080385217403016a41320300d90100140440381d40746000344a500e9005800d5001b003021221000c1d20301c0e02d040c005800d40027074a90340091041501d05001e884039030032622103401503151000f88042a100c5020300b44100b880c0d0308100340900b41c030390002c40b0b02c0820200003900c094400b0406108120705c0081700b03022200d080740d15210303507100c9503c06502c400c1d540200503d06581d071500351300141020505000624001c40005041400e0b045202580311411102101e00742d5459001d100e040307810900c00c4001d1318031800e00c6801c514244a0185c403088030080040d00c10300000c52140a500c4c8650120303181e00c890502651407903024964082c0d82c80e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 408680593 1250 408679343 408679361
    0x3010b03040519201c060c031401210213022206020f0c100c020301091109091203010b070c05040212070e0d050c0603070c140318010305010608061207090906 69
    0x81d000360100315400c0e41d183c02e0401a0303140c220240e620201c01c8505941c07002042c84200380e07001204070314038202c2125400c1142c02e21501031140460001000c600c010215144015000c03480300c0d50340014015195010120340207640040c01200c00c250762400010328044030134601c419460f000161500c8101c40c03440407120f4250144810f0301c40e150310b83d0403e07030b250444100c0314401d592204000401c07038945010808900101820801020300c019000f09094503c5488180c0c2c46516621381000c0c90708028841c10f03404050fa4010f0005e91082c2d81c016003240c4810700c600380510b0002300b00d0100740003140789810300810000340115901d40005803084040681107681c103000c501300e203410301000d0402006180b00b265200c0301401e8602104400c0101541010741500100801c240c40f0310300090080c0c00d00e0560260b030600641e20b8400800b400200f10700754000c02d60400d070030500100038454000c410281c000c1411154040400000c1c140e940c900305039a0700908405007440c0b020410310040380c0c843c40710 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 408681843 1250 408680593 408680603
    0x150c0706050106050906090d02010908010f200f0d15090227010e0a030609050c0405041a060406210302120414010306170c0d0503040e01060801080f0705100e01020f0303010b0304 78
    0x5030381e070754541541d0174010188203e4010030100701e2242985403100740210858414107014407a542c440240900712040040383c0315a160307890503c80c4ca1000c01c0742011803800c01c410411391402842c80e100300c0f868043c0c0c3c820302030451340740c0400303200b40d07500c460f03c00300900000d500454440000d5141300c1e0480030449800034440c000307088480e07529441001c41c08440180a4079440d0000d00d142c4d1001b0003000010015241030140140700585c0d40e40383d02646000e0343c00b80801c401c0000b00300314144a0b440e0007a1025200d203140c80c1c82003103413100042452641c0c0c411550845a494003900f0141d0910f03400c04001820560006070100f10403204900c04000c40324203036400c105440c0c1b0303800070b04111a0540c03800350a0b94000000c3c90312903d0322048018109105078256420280d40380d503c030900c0e08003a008400400c410400500581d001088a00003c072070751401009a00d1070701010800304109510b001007080185200508540d0003040f014010901e40320440741e0320344e51800c8012140e0002c4d03808461b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 408683093 1250 408681843 408681851
    0x160201050d0e15010617041709010315090506150304020a1a12040c1809020d0f032d030b040209090c0d06170604050114040308060d0606051804020108090a080306040e150c0706 77
    0x201b840c803c0e000da1845180e1000c40040c0480040142e007005401100e1028101522805511141c440103562600280503005020813541054070420107401d03e900d1160019140c01d20400001d65506070071182211101c1d440048081c40a21b4141218840c104500001e07103202c1c421301080002810790030742120f20300d0501d072420408905960b4255000120003a40c0206800e0a002c082102c100b02d1285140c4603090000503403240c21000c07002801d03040000c1c54124052416030f216644c060103034102e0030000f12411840c10b01c610001401c64000680221180c1d40080750080380074a00e40c1c803030005882c58901490030103041141c26982d54200700e43c125843d5081492000740000c08000d081c0c003940d81901e03401125a502018880e5040011000782d4140f602c1d00f0000a2070349034030710345080c800441281100300c0e1900340009070aa000207060800340386e206000c3c02c1c0200f050075007520303000b10341101c010403c0c0d2a50f1024130f00d0301e00c80d110150240c16007442444010942900109902031081100344 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 408684343 1250 408683093 408683117
    0x2191107060908071505041706010e06060405031509100608070302030c10051206040902060c03220b07060506030a02030f03030108160f030609061b030b09060402160201050d0e150106 80
    0x1a200e60b494454102c0d10340c404401445544070780d120100c0c103090545001800d007507488200c40740e0305140d001c000a060300248014800c0c5540c00710305a0f03121030251442450646400086560303030001800c1b101000c0000e00110340880014092075000b104185810b20000c0d455410300d0b6202e0001c0c0c40120710034030503c1214040d5041c0f2416440800101c4d4403242c0c10a190346d0035500f18041c009044c40e038411790b961a4540141d880801a05003000920005c544801100d507000b150100c1c5901c046401d41d001c00c008004402c615000c8030000ca0340301002103010b40720800071a1a00149800003580360240307805490030000c0c0000914100c3c0c0702c14003120089103022200d41404011800390b014800c3e1503003404d102140c900d8004811252040100040396507100c101c400e40c1180e40070117000026110050200340b8038060a02d540c000d907044408518010744103214020800c0286030084c103010f004a141c0c0e071411902c0d031000c50004001d84c25180c40003800c0e4034071460407200740034800124019103010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 408685593 1250 408684343 408684347
    0x2012d060e0c21130209070e04050a02030114030115090b060c120a0210060e15180703050109060506090603010302150c070303031b02190818061605010e151302040219110706 76
    0x2190241c14071340c0c1c040c3d00c103881d29000c1c022240c5d030080c450020310030f0b82c8a4140707c075142c510489110740603000c0010784950424508084480c40c0400380c512136030422504128040207848400211819490006020700001c00841d6150003003041d6100c070b500412030402d00600014008150b5040f89609448400c0344011129085422500580750405194400101c140103034023030410800710003e00c3ca19000c1401c5400560044007121005e00281e15840104078041c054000d60000d020100d6105007460740c11400308009010512010384a46009140e42841800203c112541807201c20280d519042e01c0f400c02070041c00b200c60040c110180d0040785880028030100e85410031010701c61011706040000d0321000841e40040c1c0c0c605100413034581c1c04400550b55103004005540c440d4140c800f114104d403c0c40b5084500b0800d119034540c00c801c0901e00343c26040641560310a01080c0210340e81052400850000c0c000c4200752071403102c8084c407403080160010101401d2100000440da1415140c80302 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 408686843 1250 408685593 408685657
    0x80a0506030a0c1805100807060813060203071d0a03031205071403071d040e190501021b06010801060e0f011818030c02120c06070221030f040303090602012d060e0c 72
    0x30304030b031f503810420781400304510031b1210f00d40001180300c4820484985881d85822640156600c0c00414206c144050103519501e00316030200c0c1d0b0880b00d900e06507143d501c001c0c0a01f00031032074030700d05a83d031040011102c50284088803a00302d0400034454132854880e03c050010800c070b2001458070003100c040401e6915160181401d0741413840050705c8a11b81d40001c0071654007007540100c0b1345540902002d04910003003c4010f070307518000c03802003845500d0403c0d131600b101e0701a0014003905820720200700b02c02000700141411910b0500440420340c03450780c0d01100a00b030700c480c0b2002c42904500c8043c24580e102990a114038002c695030452403001103a030544d1a0004400c540e084441805280c0c090310340b5010508404041e4210300100000400d0070500b10391054100907100f01011405009066001b050740c005044240000c102140d0101800c8001d1807410b48064800101601d01181ca07241e9900060010116101c80040501f0015a0210b00303801400d15403221260420200c0c2004020f003803 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 408688093 1250 408686843 408686849
    0xd12020f010f110415030603021e090603060702150a0e011404060b0a0f05041802030d02010203071101060b070b04051c090602300c15090606040b06030601080a0506030a0c180510 78
    0x2043c64585417a041503150f40c00e00607030701403051550b10b07100040561074001241c64000c91095222004d21041c000f005180100501143c5c0a6488441044000364001681c100814204901d1020690341c100441003c2d140c0354040444550034203840303c40d4221007110341c9000f288548000c2c01407042403c14411900603d200d510400d103d9004100080d080c15401030000306180260303102c1c00c01058000c44d29000e202250400140c3d800010418001c0c0e11203984101400240020b02c04d0030300d4103818a06074042c8000250229082101180412800700300c4811800c04464440010b4410700c035028060181d1442480050301a0104c055941c0c500c441e41e8400c1030382010340b0381000d013800020300d0305c091700074015540d054401e05410000701040060f0051046007414001c1150749481814002590f01e507007001c0b8010001032060202981c2c211701e09540c00140250b001130300e940d44a0000385040f412000c0034001081c14240814044244040040d0100408500340300390b8594610100c41244184 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 408689343 1250 408688093 408688121
    0x14070c0603020c012405090c0703050702011d180a150602101a150c011503020d0b0603010615030603050106170a08071703090f010c180608060d12020f010f 68
    0x20014099580250301401c1c0014052000103264841c280081c006081105c03001241510055802c201e280740042ca4590300403e411107890400036507079005459400340707402c002d046c07101c0710f40504091107a8031603450410b000200841c1340010b25903000180d070001512841120f90500a0821585800d69400340407940c0310341c02031800c100c041906200a0451240d807044078400c22440b5403440c0d0720071802c58001d0340141c034069500da062003011821100d04211946034000c441da010405a6692546403c8084d000403200105554100020340146911b0f0010b9004a1880050380e42c00d981c0b5600c41070036603104ad0f008010158840305038505080e00f0079221840d03948000144000508280d0180200714401c0411282600101c0f41e4846544c0048405802981c0700041400c8441001d006010141034103050907080f480d05500910080710850160b802030003041c2c8041031a94075010340301162240c018248414119080000039120541f600b0081ca85600f002c0c0000c040403540c2c0304002c030300078100c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 408690593 1250 408689343 408689363
    0x3030106020a0308340905100509040b0301110c031209010b03031c0f0c03320c0702030a020414061f0f0e01030912020105060a06031107080913020d09031407 69
    0xb50b0380444000350001c1070310b01098440014200c90311913140c0100e442502010351000708000040004102d14178a40c4403c1c4214109000c2c0507003260003204440071410150382c0031890380f918001003030151a01c46908044503a0000b8081c40030203000c0701614090500105c94103464482c00d13410307800d81d982041402e40c59041040180000c2c20003040b041482c2c0b1341004081800380d085c246507000c030b03290f8000c1403001c00e44900b903d15541540300340e010825841401402e2444580e440083c0040b07400405c101082007002070804250360f400c202c40c03031210354000e005000c1c818551982c0312001d041038413540e01810002c1c210300b01800030001c450200407925030b282001060031980465051040c4a042810303d40d032a410003020030300c400a4514501d070207400220b1542010000c2c041032030143d0f44100101468001c0241449407100112020540c110454503190311100c0c00240007800144402e1b2840381c400a41c48440003015000205114002c2d146d109000c200b10070169454498007000034969450 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 408691843 1250 408690593 408690613
    0x90c28090b0a030b04210807020d0f0c02040501120c0602030a1e0e09090a170c0c1314130501060509061f051303080301050307060314070815040515040e0303010602 72
    0x80d9038490500c541d4001d0010b18056039030745400c5a00720013a40e05441034945039410346410b812401c44242c246ca2075183c6040039181c0404000d444100300c6081034204803020a552106510881240c40d602d03400a000300301c80c0d691840701520600c07a0340300032260b03030242e50700014010780044191600da60305510345401e15518502401501c800740203014041c041d18054401803603c50102c854440c0c108000180042c804508143e1208001d0b00c00342c1d80d4003201007200241421010541350140f207001d13941e240290310642c050b10040c051182480c0c207000031100801c01d42004002c811075005006800800c0040e0b181d400340000c000302114025044100056040b01ca9400c0b24450b014840c0e4131724001d800c081c115200030003080a603074019140c06c3c0021005000d1864244102d034010710076030400b041030300f10800144044041c02810401800164400240c84911070400d104054100810030442d81c86c2c140b40b49040700048010315401203250140482d0b541100004413410b95a6a40007031035103102e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 408693093 1250 408691843 408691859
    0xf0c090f0f0a020d0504060b010e030d0509040203100522050105150304080703021f06051206011208180a0b03040b06040908030112060b0907020f100203040804090f0b09090c28 77
    0x9000c0c02c5110215800c1040320580803041c440c4600580c461480443c407400b07048001002c1804d1622120311940001800805154021044503d0541c00356000341e00c0f41d81d03202c10072141404607070201782c1200c55078110049140c84418103003e080110201041240d803180140101040d00e0a034a6000d400c04001040c08144000040c1010030b210303104442e441c8040e1540c20143c088d40f0020f000f1004c1c2c440700c081c0202c3c5801e0981c0b00140b10f03c08020300701903140bc6460810070b100210090170701000000d110101f9100d000306001d2024014008041140d512020701085078001c40702503035600d41210214806c0c0c03505002e4424041d811030308080c01e43c0d003416090b506280758481e0446c0c85e2550341d95108140e0312a50710880c0700d601c00b1380181222002c141031140c145202e80703181d40f40f01c610400400000031100003e035030507122005400907200544510080c01002020f034840e920044100800001d1840045d8850a50006840b040007103003407030b2649c400700600040d629032900040e03141030040344 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 408694343 1250 408693093 408693121
    0x30804050f070608150f1801080f0118020402160803040b040c0b070201090303030b010903060f0b010e01022404150f050a060f03020a0b300108160323010615020f0c090f 74
    0x17400900541042e80c40100050140700070021002c0280c04020040100720024401c40c03101e01c820f05c6c001e02c010491030540c4c1150080003880217214075030102c0c00c200c2004640030303d0101d2541c0118819941e040a041000614070101c1e421560b2880c440000300303035080344030103541c070060b81070310742c00e0185003507550076401780080001150420200b00f900102280c000d000c4d20b90300c0e10f04054002501041e21000600000080b02d185040d90300c0000452800caa81d0701618034100e180715429002d540f04c0d8a024441d034417040940e00101c50a00469881c0c0d48040d5000c03c0c010106182d0400100c2d035101c12204800d0b501d0300c000ba41c0189007a100f0860100c40c0c00041030100840110308602c81001d10740381450404501650402d500202d006101a020070085a5110180400c07101a4145155545414204a1910b8403106000c01c0d0742c24110700425080740025186c13204000d208210030f140001c1da5414203c190308400e1041420034002401e01140c824024201c0021054443c0d8402d220400070f0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 408695593 1250 408694343 408694381
    0xe0d06051807090902040c05030c030c0730030b1909050604060906061110150b0901201b06030403021507021906021804060b04060f020316030804050f070608 69
    0x1110018224182044103101040240041000000312130f0400d0040c40102d891682d40001408010030038060300100c1c80f410303a50300a0000e500c0903031341d090030b00e84980c032002d071846504017000121408541503c1c42c0b81c0070780c11707035103840d5800c01190000c4010000c1d425008500015940359100b4140113030f41c0f90350006540700d0b20140002c10410b039941620320484802e6070120000510410042c2c07a440014404141121250720701441100303500e40c50640045030b42e200d5018110300c00600c000c02c43e4015420480e69600703407a2100016050041131030b07114090124003403100e10b514681c2d0344240c503140f019640980c0c0c145d03000b03000d01c0c03a2f0700001c0780242c000034040038254412104502940110600303601600c622800016803100300e128040e030007842c414086203120318104101440000c3c0800d0a07201255018a4090f40c0d080d440c4005030301b144510440341900d900f11100c0142031642043c40640190710031003c403104007082100039510f6240c18014200041c00010224807154280003142d004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 408696843 1250 408695593 408695611
    0x180c150c0c03032206080405100209041e0203190905100c0203040f0b04060305010603140606091504230604030f11060c0312090d0c0b1f030b0a0e0106060e0d0605 71
    0x4024085030000f4903542104100d01d100088680c1c142d01121118680100100614102550907041503910b9540307824016038030040c2c460780814038008603980c541104448012254170003480d80c400517844006980b040300d02c1c8600000c0704111405a40304c0c1c0c80344402d0142c2000c05880511015038a2034081c3c413080d5110403c5100074400854002c03040e209141c01800000301d095030325841c240e0080d0030f89074160300c0101030600d00f03564260a03504c00042c01da84a441121510f540f81c0c8448001a009440d05210340288080841d020665a14510170341d04503260442d003c84103803040c076007000f14912503030000404070642c000d400000a15805552080c0c6400240f1440c02c044450103003d01e5508450103040400c0040c1c8140020b12009001494000c5200d1a010300001c420703446150710300c031002d0820780445e0441c0c1034074009038090180c0b070009107074014503200450074400902c2000c0d20441074411115441c01e50700040e103c3c02003440719007414001d059403000e0350351a10b8200041c80018070070a0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 408698093 1250 408696843 408696853
    0x20403050f010e0105100e070f12061d0c0c03160602310b0a050a0809100c0503040b060409020904020603060a080f0a0506010e010503071215090b180c150c 68
    0x800200140000004010100300019000704152640ca0130340750b016082c000720425030001440040500c5404541c403000c1820102840b05511100310b07007800302402d142503028070300b0401284071030701c0807005181182860810011510b5020b29100188a500010404d5030310070009001c0e11200c89151507082d84c040d0301d005090692034020b028803000c01d91000270311815072840c10303a4811554104100a810b4907071070740d0304010b9202800303040c520414024509204140000810300c4208104503803603031400c1d0070240700320707441d0f0351024010b600191811983d03511105d002640307608280c0704004404c3c1d001810100180c41e030b90248142580050582c50300f0032005400802c540408018007a158801040146594900d07030611508110040e0010020001c020004005c566030005000e0103035641041d00004c2101e01781781960400720b400d44500030080c00c0003e0b44051150001080d88180e1220300b08d000c03042050f040b0203840d400080c0310164040051407104254007008030103001030000070300450b4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 408699343 1250 408698093 408698099
    0x30f0f21030f05060306130804030c1403120a0504411309020f1504080d030501060e010810090e030d020f070201090e041e1a0709030302060115090b0901030204 70
    0x24418a51804055040d114403098042a4540704540244094403400c100c0d40c108500080d480e440050700306180d040194007003400f1b0098481c00c807002113074881c0f5041c0c40290f50b032480b03c8036038250351243d138071134000c103c603440000c2c00c3c2074200c4548583e10781d10300d482c05060006c00071580003919201541c00c54164503010000c10522482729130010f0100d85e01110164400400052458a19804071f0050510511000680785e08090504002d821903103500c00d402110b0007a6080d000b5588414031a00c540444903030f0301c2c3d0b016408035050354001d946040030031515900568041805880c00d4003070f1120703080d0401c40030b4182c0d404400c2d118403030002d580ca0031240c002d8003416600044003001030070100040e40000c640c0c000450340000d005c0c5243e030044a1900b601d44ca0741d607911100700d4030801c184003c06a0704000c001002c40d41002e201b04980e17212410002c10080040c8500d0000318054032030000081340410741008007040011050755070340c11450a043c4c484c0c24640100d116103040c50b400340004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 408700593 1250 408699343 408699353
    0x302130513150f0b030c0711090106110c01111510120b06040e160b0a0e0a060c0501050711031606060305070b030a0621020d030905100c05010f1104030f0f 68
    0x706601c500c1401c4041051400d08407900100e242c607922840b06980c0440301002241c0001c02a25409480d206c8800c0e2160490306290404580c07007055030f5840004c240c0045002a00180c400b50001d000c2c2e804c03a10403206184c0192002d1100d914000e4a550013100d13403001482c1e072040c1c41c990042140e041807504581c0e17410b11185a03074121000700c4003080b0340010014103052500c81d0030310304d00710b500003010409070080682c004c14030203000c4c1d000c0300200042d20713041d02401141e03060714141c0060702e0f403440980d403424010001c0b0800c010840e003d5003850301148486104d007408000d41e1200c90f0103146000030074404040c10381e40c1100c04480c5581c45450020200d0010b100080040034003259141d92440c1c8104082c0840b079240d080700100425000c02c80c0c00c1c4d00075605006200980c1940e03240340c56021030400b03445940c1968000c0343c4c02003141e519410b0082d481554040c01741c1c8a50000d20140203001c05a01c10f54401c2c0a010580300002d0000b000814120b003601143c01d4055140c001451486d501d030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 408701843 1250 408700593 408700609
    0x206040801020a0e0406031208070c0f1505060a0e070e0112050109050402130509030405060930010f060302181806151c0c1e0509090a02180103050d03021305 69
    0x1050140d60104500284a4101a0340e020300c0138101c4041007964150307520201d40c0d4030460421420007240d00c002510441c06070703482c551b0942c2c008410441d00d800e140750280e10880c2c05480204c01c242071801103a802c1c1084400c41e002d50359469201901556092002c4400c0c9a00e814018100712080000d144841250f2045501a1400f00300208462401c3c0c0103001e415000d8051001c6402d1400003008440400801038a05481049483d280c1c2c1d4009080010f88484680049262008180c4d0b00710061a400381c040019003290b04009001802c0b030f01407440c00311041c1d4807000e0f4014a05000c10910f09c280c4114081e80a082c2e00501300000a0110314549000801c4400c080c0845080916014515094074000002401c4031124072041d0b00d903a83c0c00300045054400c0e55144020000c00e2007209038401c01220290030082c0c10f07030005160507000e0640c1c0d641c1c042416801740038071003040751210b52281c800314141c0b90845c3c02042061100e42d0218001e5000c010600440c010032103010410341d8a00d0b403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 408703093 1250 408701843 408701849
    0xf28050a0804090f0510090b01030906062d06051206132c0f060411030313031a0a0605030a060b01111614031504030c0201140d02190206071209151812050a0c120c020604 74
    0x340c40e03051108215403081014014950140144042c03b01000f0a540c00b20484440204c81440510151145c102003141c044811044203801803c0c40c05684600c080c0341c05a0030b80f1824170180c168031040707080e40c907034403116944d074174651580240f40002c0218094040720035140a000d03040300c2c80c000207440b0300302c1e072420260405c55040d03242c0002040002074514615402c00f4181c50100096031070310002954802881c90700404254440b0701101c056070060a0398030003000c040c4182c07400420000c01803480400d41d0302403850400b00c0c651101040d8180050551200c40c1c0d491940d5080d61520b44081d21089e1030810101c0c100020300242d1007a2030725200140c400b0000303c1c00007503201d44210218030145d01c101141102190311403003c0008450703001c1d400303142040200400003078480180c100300e030b210f5080300042125141041c8410007044101d0403c0c440c214000d80c480000300c600c10504581a02c41c05600c1c0c07001800741d85030000483c0c01c403040a68107584508000c04040081d0740400c446400c43c0d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 408704343 1250 408703093 408703109
    0x50310030f05030c010b090f01120c170102040512070f17240f061012020d0f02030c04080f0a020105301602010b030f28050a0804090f0510090b0103090606 68
    0x10130303031600c500000d0042c04c04c80e000849401c403480c60045007003001b4440504c03034003840020140c43ca03400c1c00b940544080c00380154103c4036980c10340c0c240045010f580944a564054000c2c404407820b80d44000ca440c02c140c40c92a41c43d0340c1000d20b48030041c0324808000302c9200c082d0046003c000f81d805110002580c415482e81d001800914100e03502c0c0d50300b40ba005215a02490300c04441601c8903034440380090f41c61080c0c1c807005846d003004148040050035200c0070003944600c00800d010414100b07001820071034451004441c403010710300003055107680c4d81202c0240410303c2031000302c034000c900034145c403c0205180f0407080313a0070517420fa07040c5070f100607900c065003030b80c0341d8002615413130303080c010010b48040682c00bc084400380e009602d0741d47c0d06540c2081e0100d291080c0248020701c41e00c0e46030003400d504282220f249404c0350500001e590711074403030703040007030b203450240402d01c0d4107405000d115698490188070800e251005082c040c0c451510807604040c1d4070360460000400510403800545110 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 408705593 1250 408704343 408704347
    0x31209040c1e0c140d0c020405090f0f06010f1e05060d0f09060b03010b10020a0f11030604031d0a0b070201030905010213090203060a050103022d1c0209010f1e050310030f0503 77
    0x16007130041401006003030319107881d003020b10312a501c0d540000d040600d1590580300000c0542e1010f4425003040c201190000050052076000404450001a41c9042e600241d038003510b001c1da50804541c000664081e8070301031003021001088586044805050500401c40b801304412401081c2c0384121080504111800d503590100100c041c102441a820000425180c81608001046000e56580c854060080103150400d140c04100043e860284400f84406030444003c0e040c1841e000d0704012000104024400d440d000001c03507407400140a10850380200440c0303151001580044001c0d080c41c0d0001e41c2c07250b408110703100320301c0c013500c42d00741c001e000c1c02c480141c680c20048100180e0644136404941051300500502503028007400b000b80504403c0200c00030403002003c40e04041d1301860109000d0030740381c50002d0000c0282c0ba001801155000d80e200031a040b51400d040d0f588402d07140c1001d00381d00e01180000c0020380518011504118039181445119a0341c0d90340d821089142101141d081d040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 408706843 1250 408705593 408705617
    0x402030a48060201061206090606080601060818070b1b0c10020109021315150306050d0c14120d03020d11220617060603071206090b010905031209040c1e 67
    0x10590041001d009280f000b44070b070502c0c04404105121100a0280c01d1035a01c003904010031106030300c0800180040c8081d01d04960359610b020340035100c12103d1081c00000c0d00c4040701146030100e107072000c1d203c1500e0340c2414400305c00840341c103500c07070741c415a00c852007140c501010545c0c541810400109485e4004100c80030103105101c1da5100c1d1000328440c107070610000c00200c600b66644034094442001502c50007040b090b104a010f488603a00450308045042c80910a01124401d21030513079000e07100030120440c40800b404000c48c215403041140e43c2013007041e1800e482c4070781c008048020003000040f590050785190b8100690085848500030071000f1069001801081c408500402e080c3c144580c003035000c4010144c4031003000304814400c24000000030280b5010703808031001d034840207201300980c503181c081d9500100308800140c0e0101c2c0070300c03500086611700081d88941801c42400c8c6d0130300748800d110510001d4014030300700780140315440d44045d00c0780d01442945082002c59554508100340703 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 408708093 1250 408706843 408706973
    0x1e1808070f08010612060e03040e19051e07110109050f030430030e0d150e01061401020325050d120b060c1504060e03040303020c040f02030402030a 65
    0x1c10391094441e07905199080210701084180294600d42040010442c0448401d1003411441070350000301110b9044001d1050150241e0601c50100d809050304022640381c000a0485a0391a040450910403000001451941c4a00c0c4d008000e910148008201094107a496038101300103030607034041f01d500205040000c0d00f2805800c0390041c02a40c4013590b11040b111080508260610000d410300030141024440c07078031254400c60076140c010f84103c1250000c41c20800c05004482c00b411007a41c00c01da4040780c2c00c2d91220030020307104c20580003107107082c1041ca244580701b1413220b05030700021a04500707000410001d1000980110a80c1d40315640c035080084024100d458010803240190000d1085e503030b8200001a000008969015526800795100c1c40d010300038103490076084030240004503000003050b4000980c5007034007008440600c0746d03042e00d11000c0f080340421500603615911989101c1c0214281020101240d003690744216a40d40c00c03c8480001402540c1c44c407030000c10141d2000e20850 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 408709343 1250 408708093 408708119
    0xa060804020a0501030b010c031103161103070b18041802030102070b070809060c0a0513050a1e0504050f010b0a050c0118030e040504030206062806021608030403031e180807 76
    0x843d003401d08005114800c00000c00d6034204040003003d2148a250701d169814080059404400341d00c00302540724402454005510b000b2141c0e403d00a00c241d0002091420707ca0080d5100c00b414460261075a110034000c020103003034450000c8600100030107601c000b503102800100301c0d4038001c0340030040508200c1801840400300900421407a0817000910281c0c1590204441c0f1081b010b16105031141c0e03075108203070100c0c5280e40c0115440a1441c10003e00e00c074000c0118030780c04040015040540c0d50b03035000d001c1511000c440200c2140e1242c00144144450074024021050349403414a0801d5203076040503013120701811480c00c0035030308961128109a0310400c4001108010b9600380b04a05055802039036403180900414498280c01c40f0317140341810018185907000c424481800f802c10303903400340a5141d8030f01d82ca681208545820303006c504004000301300d50071264503594020110b0125507902d000c4001054001c0d00b0880600c0c1c03481c80060011072118003811001b0050700c4518503200040701e440c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 408710593 1250 408709343 408709349
    0x5091f0908031e1503060a02071b08100b0301020702030309040c181805180c0405070c0506042118060e011215060e010e0a0b0c03040815160302030402060304061a0a060804020a 77
    0x8a42c804130710030070345000c11415089116080c001d40c5450340d6248c1012691501070300c10944950744000003a2003400000d42074100e000080080104200d2607090500b80e2180f00b2000c1e40580c010400166a070a256008070000e90707003803810142007080030000450381091584001c407480125800c805c1c8441ca14031400f0741007003150102400790701380200703460388a910303403111140f041d0b0f0342d003000484e038501a887e00700c985a404426a8664076203031601c00001481205400ca9510b07070603606101146c041c4000483e45440702ca1800001d034600b031400c441c0142401241c41c1040301c10285040703904401d0040b4405a0b0b1002e00b4032901d02c0c209140141240040b000d800d0402480341141011038940e2507419050340c50000450b55150202081c103481c51003240c2c09403050b0300c280b01c207082452044010040c0141c1008141c0f07004001d01c42d500b18180d01060324003030340c030800c03c00c08640056995070103180000041000c4800703401c200000030b10f101809600120124100008210031458544048005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 408711843 1250 408710593 408710611
    0x201051303080402040b060c030d05041101090305060103060e031903051608010b0a0302071a040507060f0801030c0b03071205090a0309090606050301031b03021509040f05091f0908031e 81
    0x400541901d004145820141c0042e01031a030300d02c050350458442c8000c841080c0344a600701e9682d9800286103034020b0000301c80c15a0a020f09119070b101541c07141e080e8004481d0040001c0000b40d0071625044020100b00d402c0c03003001d1004100712102c2814150f410f0f0890200d644002800c1c0c40d0542005054003001802c40041080354030040c052080d64605640d42e0422078580140c4039030f420320706080c048601d0f0340301e110080c01c070b01c0c00c03c0104000020420305032591552588144603002c4415200403900703000003440c5480c484400d0000107030540c003465024409280240710000350048840403128181d45504850304803210031400c4c0343d004094080140304016081080c1d80c030b0054010441c0c041804010080c00f21000c0103803220410403c3d4034065500204194921035a00003500d025a210000c1c040c080c1e030070710100e10030240b80761007828410190800900044100385068012010107160b042000a43d6508424007160042000d103200c1d00c480202e00109807201c60101512501c000d14841e5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 408713093 1250 408711843 408711871
    0x1f0e01061e0201050c250b0408070210030506030304060f021504050705190e15011202030a0203060f240f040306140702011506090608060d02040f05040212010605010c140c190303020105 81
    0x1100c1c030a0401c45003801c8040c4200c2503810146c412641580c40d201034003422440c4140280014401040002c1801078421590105401c5440405400340e800407110310ba4990030501013004024001c95039565101d00900c1907504002c44000b104816400903179050702c60798405c200a010a003050782130b009030200781d6200070850758030300090382180c440c004150b070036403000d8902e0954041c1d02840c0000c0032031307030800030a41d200e1402c12036a90081d081210801d103c1c4c03e140f80c82c55954106042141c2491500740042d0030421001c20480300254428100e9510b104000c220000c0411200c0c482c034018403031151418105800d0800000f402c0d1801d84004110750a5450030400c4225000310050049420380d05142940740d807000005008001e140782d02079082070404500c0300d90f0100c60391246204920845200401c01c00b00d03c503540c00c84200e4016140403450542d94000130074854600c60b024101c0100c21103000b4510100410b05203001118a440b51030f01d18403091041540a00440364424240c882542e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 408714343 1250 408713093 408713101
    0x70c0c050d2f0a0303020f0c01050c0a0f110301061d0c0c0d030c021005010b070b0a02091e0604080d02100608060609041e02032a0411031f0e01061e020105 68
    0x10720322100300c030070010303804201030301c1880030240e440b8440410480007040d68445555900300070752036620860000400c0e000f40790040c0c040b9802102501c091804540041840d91016078a0b904031070481001901c600c00041080c55070340da000d02500d8003400134a034442ca445030403081000407603080034019100350b41d010721000882402c0020401200d641900c2c000c02d40c0491003005034100b4101c61884240242458000319250b80f94000912507540b2813a507503255903850029090480c041c4905d0310780c1c0556200804840e0440f010a03014036410700a06039490103030f56001c2503207020442403202016030016003103000141c1040c8078000c0144220405080c2c0b40c40e00314006178010f200100001d003001450f5a030702c030035101d4042c11103000d591701808484c204101d00300404a002002403045c0c94200c0c1648a40e203040c2003038000c1c0704028058202c480d0960f122290390311095841540785160824485c8400074141e049542003900a00f03c50715010340c02103030200f585081258006410f001d5a040600348 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 408715593 1250 408714343 408714353
    0xc02011404030c03080c04030804091d01060509010620031315030507300509030306040f024306020d0c0f0c0224180f01020d0804110d0506070c0c050d 66
    0x9034112135043c6003906196403030103000300e00c0d4003072030300050480b600c046000b00303c0320403c2e48072108906038103902000c00d016200c0d49074280d840368043e0b55041042140100286402583c64503c44a8000784d00f00c1e900c2c0503c0c240b40e1940d08a2600c21699000c07042e02000800c40e42400b81d80c0d20a41032600340320500d8900710141030300e541c0408902800c4090f01c01415075544540d000d000b00d1038004000e02441c01c3c02040c490396034000760343c11391003a4501140d040610425108072060648801018403c01000410000031044c1c160140d0305040c1015501a8080d07842038910740f0582e11032600141c0340c021031803c0c5811140c00e00070340002e0040d118020103110303400440040d91260b040703e064000400384030394200c035640c400e1b00700341e04000301140d241c42120a089420704120300907241030028a4129004981d245a05000c4101240d155000700300450f080801c42101d240003e45921002c00a0b9501c003803500f40201c40e6a0f0008071101c100b00c0412904029510040c40110796280941d8456112 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 408716843 1250 408715593 408715607
    0xf0b03090307081608070b0907120b16050f031009061203050d0b03030d0c020c040c021507050c12030c0d050c040501124106010203041211030c0a090c0201140403 71
    0x2c050029100890110080402c0b4514140d9403644108013540760400d503d0078603140c01c420750b0255501d0040c6a030210b201c8050701c16031540b1513006642d070001030300d40340b4102d21b40c4103161000302d041000801441650b075401c2801140500740103000c2141552800000108074bc000e900682080030b01401294080381d405002d0f00d415055a40d0005440c010407800070b851841001d29003401c1505050765001840d8004c038201c0d9102105448c103101414412000300d0302c4803068028803400e1500d18000c2011103100310042d2029849400441c0c0788845038061443d01303a00206c6818900c92070000b40021060141d0240c4c540101e071554800c0d003080d0810001030a02001d202000004030398030140b43d4050314014a5003d4110200070141103003031180e0340c403801c2c8141e0002c51749284c20000c402107202544008200d0b8129400902c842003400c5541d51a81081282001d52aa0603c151069541e550341c590051400815444100240c42508040c02a0a640c02421040e0240452108000100790028a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 408718093 1250 408716843 408716857
    0x31603110915030a06090f0606021203010303090614070c0b041e08031c1e0504030f0219060f0e010c030c110c0a05090603150a02071a040f031b08130f0b030903 70
    0x842d840e00c13995039004d0707080103060903405580780c50b041107405450030043d90f1113801502c219900b550305508600e000c3e10218407081c44020300044400000b004030611400803c000ca10174101c1580c940700311603c4580c01b001c2c0303070740011000300e10003d420004884220754082c079101903200700c00406444c2000c0507849000d060701c10342c20001d1412400d00c64140c0780c1d1101900c290140000c400300c075080c6100d0f030300400e021201200860407000c801079159000103190f0381404065078103041c1040e02a681c04e800b5040c0d00341c0e90080540c4600c82010105428040d0b1248a0225600091103c040c814020103000900000400903000a40103030150f0b219002a182550700503900c501072601c1d14008a45000800c000f02030000600c042408040780d5150020029640524481d91400140d62240b090f80e000c152030040080000441c984002409080b411032440101e095140d0500b41c0340d00c80c1076180c1c0c009a2501400d0070051024807540101e4001940039149040d02c0ca429450000c021950b00d2050709 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 408719343 1250 408718093 408718129
    0x303082509090c091205010c0e060f03060d080d09050c13060501020606042d0b090610021b01031509140c0903030d020322060509070b0c07120c0b0316031109 69
    0x502c0003c3d03d41e010340d21038401060b60000c001c45800150070540c1c000e0407154000d00c00903000c280390800d14544101601c0142c02c0140c81185161a00070811540c8520b000d01161200402d20482002050b24828501402e01440140540300c00034003c0010180b143c18a28010358501034040c0b0059038001640c3da400340c4203603400035007107402c0840600c9901d040d078120354082402d0160700441407980c0d082411225000e941c880b100d5103840b02044406090300c805040140d01c01001081660080a01d00440d61b1060500242e500d280744141d101e09131168010000d03141d01d6403080d0100c24003115050794070041c44600f540c20001c024000035280d2081e50300d51040c068011000c039161a0340d0160407100b100614610322000e07080c920f085406064220307460f001c81e0064104c00221901aa42100d0220b401c403030203403600324140345a610b250808010195a0320455010101e001c01c400b800560140b5250070001511025001d07006003612a1040000410a400d02119569442c1c111110406000350 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 408720593 1250 408719343 408719351
    0xa06050c13060c02040f05100807060905060a0e1827010c170406020405030601090f0b0d030509060a1101050702012705060412050c120301060212070809040207080c07030308250909 79
    0x11300016014040d03108143c9034091a040c207000441302030700f5940c001c4a400c0020340d08141c1e80e4860903101141b2502c039640d0440b00400400c00040d100d0506403550321402041001c4c2a020b108006807503840c100d81c10700101d1044914a041900c2880501440050074002440903007200c030f9006210f040c2c03110309001c0340306900d07007c42c003004025015100034010103030469001e907a540d16100003070055030f18209106480d01100f94818107000041c004481d4040e25100e24020b036150070702c20150300038040c0c0380c10042d911130020b00d080c00c280105400b400c003a500100703483c840c2c59104150b03240d000d05801c030101101040c9100041c80400c40070b9006030000c00c0702030209145d0b0000d454510030030b10b8402040c00356020960751044508042d5058610640c00c990241c3c0e98080c05811510034100050601c040a0107600f40528040d0010555a4401c51100341404a00700840d4500b202d2900200d0100341d02d001005495402c010400f94442e95010500720b492601240143c090401c50180b0f04103a030312 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 408721843 1250 408720593 408720617
    0x50703030503071101050f070801060203121b0d090605060a06021c030f0b03061303110109150906110309072c0601030902010203130b1206060403120f031d0a06050c1306 74
    0x50407044c0b003080320400288000c0c5448280c501d82c0b403c04542c080302059402001092407807000058440d90340651103401c0c81c603242c11002081103015600740b03011503641040041d07101d107520300904489911503a030215260500c8800c0020075080d0b900301e442194080d00e60803080960400c5902e4007200030341000241b484518403200007404040c0d2610b0b400d44201d4087c05140a8580f200300311560081d81c90105580211894600b81c6816482c00f40c100700011745c0c81c015010841e401a0f0207184500000540840200e01540160304100c9000c4925040b40404100d9008600140081e00502c04200300903184584240c1a03007407000703005e480c10166110385490031a4002c01c22500c01055286010504031381d680041c50346a805448803202030088a0041003413070800d24240c900b52940711820707081005d11000100e603c1c01940325103d040544071203025903c0c0030403804c1c0500c1101d405014007010b4810b41015801d60f600034182c202c031143c042020300c1c4c01601c0c1d03035202015248507141c0703c41400349d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 408723093 1250 408721843 408721847
    0xc050313020a031403071a01080a020603091c0203040e1609093902190203030301031407030c2c04020f01032c0a02090106050a02030409021b0a050d030e0a05070303050307 75
    0x5640c1e00000c4c01401c0e0341209088405000001c0e20b61948a803200400001248458544203002881500000da10804c103035801807a00401031a880b80f200800c5451000640c7c880c0000e5105030307461b030005030300000b42c28484040a41c4400307034443c810f030200090908002100500305801803140307104060342d41da224440e5808504442c1e9001c4220350441881e52008550b5008004214800724054882c0910f0021a512040c07428007019070020040c5056038a140c5800c0e04284403401c01031010f0003803090110004001c00c0040340500846903411704130002d41000003208503050f0303c288003040440000c100050741c070a90b00e205400020302e40800c5800150b0706020300e00c0c089035011911403200095900a80f480040c02c012030313074001c07688524540d03070703a0300256924421142c441005810400080c024044550010066441001c1d0700071001c0e1441200d00e0b040c002d05000172102900b21002d0501d106906009020329400c0880141909200075960141c1d12013480c0b02c0141441400310008100c14 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 408724343 1250 408723093 408723109
    0x1009060e04060e1f0b030709060e040219080a241e0e0316060b03060705030f0f042109060f020c1818070807080d050a210e0d020c0a090c05031302 64
    0x30762410135180e400d0000011314041c01200001a01a00c61004002000c11540c091242116505164248141c49075001d0000113501004400240c0b0540100050056010421040c1050050410320030290103417154a05000300e5203455182181030085034100903640805541060340381060006080341d0142a160940c0900722401c0340b41d03425050382e001800300941200032031610480581d0069592200161003d02082d035000065844582c0002d0116a00d8200f1a811500402d4202d48080c040c88840d4400701842c160f90002524a40d0100015600007408444030140c034000b60900c00c24110110b100d4503002c40d003c000c003c003910f0104500c4080c008400000e11424810707541041d0700c80c0300196a5182610071012980718149400e04500c2c8100140d959507410b5540308510000c084544a400741c0007040501182955202c1d4041230210800c003a1104070b1071600540900c0c00356400704080c445c12617000b0305045040040d107a0089500c40210382d80149001841e00981c44180041007010b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 408725593 1250 408724343 408724363
    0x1503081c0e0d031d01060324050f1302032a030705060301060210020f0702060a0c0c06090e1303020f250801020304171602060304080417150610020f0d081009060e04060e 74
    0x1d511b032010100c180034640f002004c0c3c08202e10440f1840e4410f001c420001c03900c045072345c0240300c80888082414251a587c072500204e0000b000c0350015120001a504200300320040e0240c0814402c9a9414500741030284100074001166101e007507600d0002c000e134541050f07a04640b8a26030005070b4011826004060328940c40c1c000d800192a20410100940011460714060342d40c1d000d800c40003d041c0c0d200301444c4054440c0c19106403603e40b035507081b4101c0c00c0039040084083d40101c14078034010402c00c0181410411a1194010070551804082c80c0091229000311003a84d00400400020508961030032540400f0503401036601d25400c400f0b43e01d0045c03035110080d4020000000e0005028404019100341c1c0c52030300c0c0440031107031604105641c5030180c1c1c942c0601c03074407001c001450314030b0404201a1020180e0041d0b981d42031900220302d04000340c010030040803e800c00c0902c0030480c03481c2c0310840034091884e401c01540c3d08103100d002420750000c2c0300610741a01e0b0760030203041c900107122003201 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 408726843 1250 408725593 408725651
    0x91602010e160612050709030201030905010f11130503060f011202010c060e060f0606191d0a090204080606061602091e13050d0c020904020609041503081c0e0d03 71
    0x88450540c2d080c12002449204520020741c00441c14003c04004d4401c15006400c00d450f011070540c030b19070040d0702034800d500003a540d03075580b60108480c0e451180200035101002c20720895880810000004540820b0f4101714000c3d4070140c104010002c0707020410b8195540090141482d00541c0f0048804503204000185030350304104100034405c00004042c0d00403140d9001050040c0e0b501410712059008040100141543c0c00d2072040341c05e4018200201c0843d844100300c00fa40d00c004011881c44e06042d800184000d500060410454800748061500070804075041031414210200e060807848007481e019114408100200b0b22003940281e01280040c20030000c15001c0c40c004200d509040d10f2584103455a001d0700d640401103d101e401040c9004c0d500800054898840c0c0e0203106a640000721160342195541180350300903040141580300452103500480c3d41d42c1980c0310760f42ca200c0110b584406609041c00540400c80602041c889010041460b00080704003c001b1000c0c65070701010043c00d4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 408728093 1250 408726843 408726853
    0x2060d021b030c010617152e0e0601230f1c0c09050a06090e060a050901120c05030114060603060a03210815060a050c01061e03050c01090302091602010e 67
    0x740c0e86000c03001e4801c140c0828020440150b0350580320305046500e1074045030344d410a0b0704982d54034a402100701d4129058101110403141d20190502c3d040051114080300500003138402c121900c0404000e0354000400c2c030303043c4003416600000700308901e030380c00010306065400706003116140c204006913040300c0c0040d101100c0142400c1c034014020015911040002266410701054509051120000b15105aa900c0f2555807a2401003615000c6c060300c031503401001050000341541d9000c2c002d6001e81009603988040002c246003800d205903044e4080e50287e41400001029200d040046580c480801c1e80e00703982d03940d101d4000485200d13482e00000c04580c4000c83c1d000035040700749030030311212009880710851600c0e500480700d110f01d0441d034201d0303000c1020440038001d80e00c18030182043c80101c400100341551220700c1043c0341e0b50340b0142d1a101c120400c40400c14024200704c2008200400c0c00c204140c0c50840c0c0100b02d00c4107004007406480d601c001d4034104420b1017584500303441200c3c941038071 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 408729343 1250 408728093 408728137
    0x5040e1906121a09072907050106051306080c210f030307030b01030605090615040f0e10060e030c1c140d032702090a02300a060308040302060d02 64
    0x100c0d01146001c019500c600e501001121540a08400311340140322020080602c145045600401c03c201c40d00d2950800c2000c0c1000d01048681a02a00f40c03284a18008a2414200300130b21120130100100080300d46e050a07000c0005117000305500c09001010342c3c4200d40004061441580c0e4003000f408500c81c1c0c400c01140808070000400594090442075805202d0110340700700450980b82c81d401a82c1e840081c14010807018641070310581c452a9842c8009420203964a50042c01c461280e0700900c1200402401c03c0340d03558011490328083e00550601071410381aa4011a40d240f0303039140041d0007070120601c10f00440b0344040c120154140e0007495401c40c4070192000984481c001c0d203541e0007203810b014002141013510500c0440c83d112916641c103180780d464003000003900e0b0203860301c01c00fa0350030000b800da80c3d0300034103101d03401d0603a646101741c2c20000504d000202100061070714007054684502171001610395001c5a080ba5012102107071120f58401c2a803000f4801c852000d940e0f40d401d86454 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 408730593 1250 408729343 408729359
    0x3081b031c0c09050306130f0b01120302120a050a1101020906040303020106170a0b0a050618010608041505130609060204090519050907050f040e010e0f010e06100605040e1906 77
    0x402161841c60034482090308a20a64070b02081c3e005080c0d00d50000f40000708081e03440fa1100035002e00440d0084030840054541e540030002c2a002546100c2079101184203064041140780080d01c800b0829510741800c40b0001442401505440c10420441c1fa0821000250035010307a030303a0001c020105581d443d96850041e000b040140300340f0300d0f12644440c0030f60f80e83e940801c140200a030040c085080703960b50b44088100411004140035446842480851300303207031134809464068240313529000464240380c02c0c0340000c5010b03490041c40742410581000034007030b127880700b02030020741c072441c041000c003120710300007010380940d4010706002c07840c00c0304000d0552840e240749410085407000c20005500c503500000c0c0c480707029005454008182c1c42c491241d908240d406404c11000c4036000040c0356007555686420b00703000c98001480c9070b4545605c28286c0c4018800c0c1c980280b000c0c030100e01d000303145c040042d00c01c1c0030741c1c816120382142c00000664401c03080383e48495800d001c3c0c10700b00852600c03000303c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 408731843 1250 408730593 408730627
    0x9081b0103050604060b0708210106110613020a120f080a030501181b1d030d0e01090f18050702030c0d0c1101020a0b040b0a0f02130e071803081b03 65
    0x6214006401d2002150080c01d1a11801d01510701413107255140019913140e84880e54480c290b0021403603013800d034800360901d40210040c003803ea10340d1040042c000405c0c40328600319000e02045040c1019a01c0301006988043c8100e0441d15000300c604070030301041c202818082e00020014110550004091090b80c1c4d0540c000c0f81651070411086260002c901074000840d1035003120fa206080151005d80f41c418080c103910304544280956034121580b00b080840e0420707000d00c80b440042150301c401c004c025078100b00c0b010041d102400d0748103501442d15100b1104007501507042440541c0e55004030b031450f0310a20449101842d00421135011301c070300c840028540e02303c01d00e040e0340e901e200c40b03040720342c81d0b201045e4031941076003090b030900f116125900d4402c44079a024249190540d0b4480b40100f801c1c9072400940200c10445c90030000071460201d80c0480510000c20b120100442590101d02404010301c220013540e1b080407803d5114030421030100c080d4480840010390512004c6100c0582000a0803 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 408733093 1250 408731843 408731893
    0x30e010e03041e08060127020d020a0305010302040605060705030d090c030b040b06011d061b0f0d0509040b0103200a14030c0714010c0f08090312130501051605070b070908 75
    0xc01030f151591000c0907525000e081c040c540b0402d56500d003660f01c040d90521100400030a4404c018908024103100c00100e900c103c24080200784c44038010029441d01c1e210b210000d103004c0e0b07900c42c6000e100fa51041c1e100d104e406d064440607583da0f4854000d01010529400295900031941240f9060a0900384581c1d0001c481d80c0f40000c2d00307100311108450040080d11406031000d8142410f14101c2e0300040c80310f412800f40c4205c075200e00e0211000ba6503040000000090703054507000d580c0c00d60a0188000e694551400b14107040c149906000005070301d030b0360031480383c0040c245070f5260040c4000031070300e12402c207209009414010041c4a100c00c0700100034981540f00708103005616014281903800d8510001c050710120390503454105400307014440d8141d000ca074a00035a0300e86264144010910501624128480361045007030104000d001d200e12034121961414031074500700c00810040451044841c02001c44a038580860246030013038030002c0203071600000f5214079a051450f00c04000030081 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 408734343 1250 408733093 408733139
    0x20f0703261606110403020d020607050f010c050c010b030a05070303051b010203010e06010809062502030d0f0c18030c05040c022b02121908060319050601050a09021306030e010e0304 80
    0x2010903039451454001700c1d003c0b43c0c1d01600040d03000d0031540800c0140d030002503054860340103414200640500070701c41d01c01a4815912100d464101e89400c8508450340c00882070f0183e40850f1206000c9000083d5071805c40790b05260003a50342110703850007001c05420000b201c0166002000100301034030b054998500c0741c00c007a038440d02103940700ba285c00d030b030307050103171040b02c82009050400600030300707006c1311700304900340300c1c0101c0340b0f0003c0c0e50b04c0c0c4a0454007000c0c00103818590301c86d0128480ca9000c44a00040300e03034428031490080c1942c441a440034a21f2291314861650750400500380d5000784803d90328a4082d00c1c845880c034519202c59075881507004180401805400d400c0c26991030400103503600f02e89203c1c60003030503d01e0440152600c0700013801c030b15807620030401c20540c0c0022407900702c1c154510407c040c0c800e80d490b250500440c070015800201055005204000f0041c0c0c1c20756000048038800d00d00803d00ca10104241401801c2c1c450001e12180800280415020301805020351010459 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 408735593 1250 408734343 408734351
    0x705190b0a081e0714090402090307080a14060714090103060b0a080f1b120405070b07031d06280e0d1a07030506100c05161502010b01020f0703261606 66
    0x320708450003c44129000d0300442c0c1e0001034000461602000303040306c0c220180c001850607204800103890708006a10007001a80b242409204000d0304c030002e0107994504200924050400440c0a40031003000c600d907550455010400d48507680c8a900401d0081010000542da148100d402c02040740b5001c44194480786120710104812204602d0f0780410019240e141d94204000c0340c40030703000704401400c25620740c8500e58010030800e01000081000e1407103a100c10200085102103c010901241c400758480d00e018018044a40d0301d122107041c002c841d500c046070341c3c003038030003000d80703811104c4501c450b04000041034007010452035403064600742c05010002c0f4020b0303507850022016120100c3c1d40c503821440aa040741d1704036003d6031409940c2442070003503421407004cc034086c0148408941c040c80c449605e005005007030340d0f02840b81c400c84140030310280884544810065a90f42d500c1d106c0100302c02c0b400c0541c25000034804010b000c02c140001c0807590f17912050003050002180d40281030301e40603d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 408736843 1250 408735593 408735631
    0x2010905120d0302130b0307110c03010605090f0a0e1902190614030a0b040c081602121b0703150207020a0b070c0509180703031d040e0705190b0a08 65
    0x440d00080310410006401003802441500b400c8003c0d400c04c411514188586840100310810501c000d03510401d1107680340400c240941c00101d1400c610040b0140c060391600c507092159071980d10306c40d50300c601c00395800d080f207840d1f0400550007810610300c540b08034000c2e500000d1038034208003240c001c120b008442c0761006d07400c944150564007455124040116241c006514440da5282d0080c60384400300600010300c200c41c000225064440303101c0c840f0009038111040059012003c282d2007404d0380e151000300541d46221815050b070b41310740d8044140440128070700c5100d1a0041000c1c6005d954061030800c981c0f20043c0c0c014000c2c2d000110100e00c940039519011410182100588030b4440d001100301545500d05801d0190010000d0521034400b80c070b0f0b4103440f180520801a074801944640d0300c10f10650802c0d4050b9003081000c14403a44140e06000c00031042e400000781d4941074600407501698412880032060b00e000a45500c6011b0700c03d8007040300c4901c10380046207244103540682d40e003100748d84 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 408738093 1250 408736843 408736849
    0x61b0f0f0115140a0e040308012102151b0f01020a021c0f050706181a061009051203090310050615040303020a030e12011a1503040506040b06030a0c060c02010905 71
    0x101180440220320b160904105609821003540704084018044461241d22000c4440d040c1c00110750543c08101008010052000c01c0d850703030903190204065150f0301031500e80c0060070b0000e03200001c010403d03010485c00400801c52014010b0300b035002c0c0486403059075050020b030113500050544005805480c84c03000c1c2c0340e1601402012038110640e81c200610420301421356403a080850180c0340190ba0b4a00d01321004404030903042014000e00c10211100407003425a001d1030401440039014400c40c00d502c540d40c5400902c5101903440842e0750350f01042580c0080c61960003140000c07545845004038240000700c55070300079801900156420243c055412202140754070840c80000c005901800d07206006c05c2c841c0c44030181c0c1d940e00415480706030440038107960135aa5044007071403681d030b00c03001d400707003145003c50303500070032203102018035042d46402d495103501d8240040000c0c29010400001a02d25502442000c106590003200804010f846070070050891000b054208e0211700c0121012480b80707 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 408739343 1250 408738093 408738101
    0x6090b13050c030118110f0904060f0b070b09030705162108030c090d12111605180712151401080903040b0714010c170f070914061b0f0f01 61
    0x90b824018030310b5a442c0510418044000c09000b03000306995190020300142d0101c0180075000180e01d04c5074417954100d00f040121003065000120101c1102420041007907920190f5125230340010782c1c01c0b003d58508000508620070a20010054081d40003440c1900ea4000302100a440c142146840e0800f01c1107984900c0d80c400520241010342c0600024010000c400010b00398140c020f409042011104c0d50f4a0206040301300326240880d0844101003c04d03042001480340b071004600016100a19100c00300d50203403c683c82008076140ba500c0059082c80c000e0500d206400003000003040b0303807203115030800039110796802808054404810050741c998400e1244a004040940c041e603c0e280c0741510016165000440031a00d242c0cd40501c070300c4c0220203110b41c0c07424100c580c40e8000c3d140c2480c8904101c802000380380d11807244211f4280502d49612144038000e444030501b03d4602e2001d014006055401030f840b80c0c081481c100c82ca01d56080c08086207100c020410941100e030080e5000d00824240c0f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 408740593 1250 408739343 408739351
    0x1208120c0421051c050307030c031e020f0708070803160309110f0d02030a08031b0a020c0609010c050a0302012a020c100c0b160e010503070c060b06040906090b1305 72
    0x55100328020182d11202480401e401485001280e04110800f2544030404030740c94a60404284040104070940e609401a460348051030f103410045c0f0800702c0d400c51a80c03480e851140000c1c0da40440c6c0101c0c0c54240604441109400054460b12641e452401c040d1950049400d071031900b018800c8001401e019004030300d00c041e4405900c5550000740360030301401d011880205540700c00b26600300c3c030260b1800c1c824881c20500030494580c2d246803240c0d00c945007007040054101005401c000385001d03c1e0340841c80703415001044800580c1d480381400120382000140307001408038010b4510000c02c0640543c000d000582c154840c10545000d030040c5000a80390034407401004d45c1000c0c80c2c01c000c500c1d112020503103512450401b408841c40903260481e00d47e6007110554482e802d040000d85080e60012005001c014003440c009103503182000b0010702d05402d0f03e030000c11458071001c40180aa0301c180a131005885101001c00245a407540c00c08068604c000a050007400442c0c15213010020358080ca03442 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 408741843 1250 408740593 408740609
    0x50a060f05031323010b091302030304090b04060f0902030a0c1d011101020c070617090714040905010b06160201090e01050f0114071a0105010f0807081f1208120c04 72
    0x5568422034480c0c0f940c00c000008860f13a0340c8101e014103802c41013a10030700c2e109003c0c5000244e00e00e5100c0034007070a0600a000c80c0040c505409440c0010b80d0000b044405680000101051011485000c50b01505035504000c99014003401d01040d510055030246102da0400d85040c0f00201182d042034074640c11041001c01610002c5000340383d203500900c40750004201034000103283c5180317212800d007001000e800410002d91028032140d0592044041c05412050010281c0034140c46d000e8103060b0101000e80302402141c90f0446402844029030110111101c0540b1080c1d540ca001c16944008000e1150124042900700d5070201c1c1c003045000005041e00c00107440c02a485054400645500c0c5001c012000f03c04407c215080c005000c410010301075070003180c001020380d414030001401c0c0c441001234200c200003540080118407580950080d400ca0740c1d001d01d641c507200704805002c00c0c1441e940c11100f5a084014498000c0000140003062505951100c2c042d031a1121040600b00b813145225071a0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 408743093 1250 408741843 408741847
    0x10b040603021f050f13050a0602011e0507180308091002030412030309080d14040b0a090c290c0604030215010311041d01091407090e12030a0e03070507050a060f05 72
    0x145005a40f0202c82c0026084d040207400d041000019604660011603451348501040d20f080006040170103884018101d0f6000900400c0c200c503c144196041440c00008810303260004a54624010915080c803d1741103004400507a0b1281007250300f6a00128041d406002c18016031180d0a2002c0160340c00d032804400042070b400340c1520100c0c060201144180c0e00311004001001c0c038001b844c440c00d1550b0815229245451810381010480c9401c002c00700804c150174001010700240028140b0f02c180c88140101a40516003a00320012268840d0306d0718040b07503000640085803800000d4031705e228a00c25421144211500403c40704415401e2000501000d018944a14189426005150400d4141c4141c0340480a42644c460030341e14402000d40d512a098039010b03d40038020300040c006840500d42c248030642565904903070300e203810304814640c0d603404008524107528075088400d41071054070883c0c0d11890141070044d120361007482418813a011011000503028007803404d100248a181c2c5a086c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 408744343 1250 408743093 408743119
    0x501020d05191e0306030201030b06030903161e050f0606060406210207080d05070e090112080c0708060702060f07090f060e0a090c030209041103090a1217040b0405010b04060302 78
    0x211025800d0940c41801022022542c2d204140c1a91000da05030f5640c0101d40145180005002c5900b0b000c4128060b140c20402c10100701c2000044800e09900f120b20b0848a01d80d50401d040c500c0a0160941084e9501d03941c5003080c864005914428100714000b030301c0941c2c440c6010040d803480307140b145201054101c001d6172a082c1c003034101a500050461405458010595920080c541c0310840703000410b66107000380000c0c0c42c0d20450080300d54006a8510541e941003c200864032500410010a03082c0c00245942d0b2401c07040c007040d001071044104440312801c1c8070601a40340c00c011183c4440c0581040300007407419204415800444055052101040f41810011108501d00038503081d041000398000044c05c100b540301f0b943c41e04c803070ba0b44c0c0181c5852001017084280c0b04001c41c0c0d91a008420700a0208409004c98401501540408085100703007a0060540b10841441c444d100400c903146c08000a201240514130f12981c0b290000b0412968210704200403160070b80400394102400b0003000d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 408745593 1250 408744343 408744367
    0xb13090c050301154505090706080c0d02040e07083408090102280e03030f1605100203040f0b060d03020a0305030c090d0503070506010812071e050f0106030c0501020d05 74
    0x24548a0382c042c100035245d40180c00b0810748650078102400d00e0100b89804c40200001300b440f0303041e007051011002c0d003005491f004008003280e101400000c2c400b4070000340b902d25034195604036002407500c0700c07080c1c00780e01e00803002404401080350314105006000903100100d0010303001e152104030f880c0d20b15103580310080c01d00f00c403004802442180d2a40d401c00c9091000006410f0348000b84822151070230860a81a1000300031034003910030b446c001e030b0040c0425080194514165070500c032500003090500300311800c0251501040305104800c2c1c6100006000c00e02000c14041c0440c5401440504402d45030701060004030b001510b40a001030301314040c1788002a224400854012888610050030940240001080c42031015021030b4164000103810b000c0150600c1850300400d910390141c10080e21303021198500388914000141051416010f0300408202c42c00345000142d0010201c4500100134000580280114001512020000e0f60300183c60743c40082c04003600300031559858200048a000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 408746843 1250 408745593 408745619
    0x10206010e09121602120d02070512070b0901090b0a0504140a03031e0203040503240a020901050708131a120a0b011d0f150d0e07032102010b13090c05030115 69
    0x803a00104c140204100c000d82e0321800001e424411a20140c8020010a58041e24092144e801a8001c8161610101c00c5400200c2c81900f220488580303c0e50380c81094004030f90310344041e00101d614440100d1041009641b020241094070003412500300002c500104100501c8411310000f40010403260b11880c00101c8001c0c124910011401107034100741d210b030700007810148209440c170014030151000625004422142c2504880d442504501d0142540002002c0344500318004d002080d000600031203984960391900001c3c82100c00740c0d4603c142e140101e107500d50101a090079a40c50000109022001c14481c24a5075030058455881440207881010703d400d200201c201ea02c100d0000c041041c07a01c610000031641d180c00070040c0d40d20032060b00381408440c084001200d49502003141070000917414500c951040452000104490b1081c02080b03002d01000b010032070304804410031003000719405070000e4200510482d4002e1109448500b8542220f168000e542c5e60440c0c0428100008003510781 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 408748093 1250 408746843 408746857
    0x19050c04030b151201021b0c060301080c060c0307050105011401021509100f020702090405060403110703020306010e09010e0d091401180b03040c0b0f12010626090a0f050705010206010e0912 83
    0x45440e0484c120060881d003207810244a10741107200c2c4181c00d0b540c206052061080c0600121427050555040042c95603440d889405028019800090f0141c1c03044010810f40e5a40c96001001303200300d43c0c440e01c244210020315103081d0301612545595a009445c101800781c07082d02d256008000e000300c005455000350042800003c5001d50070030003580585c803101201ea210b58003600080115040c10b01d07005140324a07d00c69000e06800102d03062006035808101d0743e0466441d8820003519890740e02c805801000a01455829440782c100306051b11f60700041400b0464404509181b02d031409070b070040d100c25020090380d84052a8a101c00c0c00540701f1781c8007844d04240290340d00e00d07601f929840300e001d059024032800300d000640864070b0f1420003843d0049502400301803600702107018072602e408052075a50201134900c0314110b00000c4122608102264103282c0010340c070314141e017440c01c08503203e0100d4001d060050007102c001040c240c01d0125014010303d01c010003400d148004002102c4242c01102c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 408749343 1250 408748093 408748099
    0xf0a0603021207030201080f0f041b1203121104051c050a050a0c05090a0902031c021207060f050a0605030a06020a02010b09150f0906010c02090c0d020319050c04030b15 74
    0x6200803000d80c451000403001004503000900100781540005480000000c000f00b1110726490100202da250840803a03800641c0040c00c1c100398080003090302040402d40c2c0004805a10800c048000d00d43d00140f00810400300f40c0f02005240d003090f00c00c20182c480c50003410340100403a883d01510030515855000468002e000f0b4884010450b52101d081c04049101036804400c000c01c02d00c01440d112410b641c00c03d0748003a080210f02c3d03195000c01d4488651011451071300c3e6071840050b14283c001d0001c2c6825500d0f0ad40314030b82d034000c1450040e00508040c942050704a140900003022041c0c648505025104024002c01944281e40d413004080d52154240d5021952a070804282d0780e100c2104590041c4854207403242804100c0044c0602002406082ca00c41c99240050000c240d80141c1a01300b0b051301a00c55520960f074110510b803251041405404170144004100000400d0803000c0004100c40101c1c2440301d61903044142c000d9020303034000034001410f25008500310060150390309200035009 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 408750593 1250 408749343 408749351
    0xa0b011b02060c0f060705030a0c080412050c100c11010f0504050a150b0a0f060e041e0c050403050607050901110c090703050a09020a030602130f030b0a0902130507021c030507080f0a 80
    0x4ca42ca15041c0f10b070903650340d0086180401400110041c5000701d00c0c540c0302514242c1800c0c5000d0301c44044a800350b50401c41070000004801048e110280200d6404402c1840e060100600800e401003090b4400401e06005503e0139202e0001c2c40501e004050040390000010140b0300341940391040c100702845035107210659600e8101406896020415006103424007a04082c03d281c510040c0c841d100a1006c0e601c070b94030300035100b04600e2268043e02e0761040051000203000c06041015155031060f80c00143c003a101391002c0007031540e07015000703140b4000280c0c0c40c2c00040103000b030055a9000200f5419900502c90310008110a210381e0201e503014040c44800f0072845900d8011500c010542c1c0c000b510002e40010b0010300300301001104030300a00c0d800d010181c081d0301d140c4410720806005442007001e1901c6103d160250b5951001150300403001180800c030900f01140c011f503544203901e02205a060b401320f800c56005001e440342c00e2251011340c4949000e40d544c109130302440b00b801024201c04a50b2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 408751843 1250 408750593 408750613
    0xc013803151914040311010c0c03120e010213080d050307020a08090a0512010606021e070b31060f0f020303060910091d16050d060b0103020904140a0b011b02060c 71
    0x50055806692400030700103c04d0800b410002c00141c0c0003401e85980d03a061170807403000643e2281800f080183c00d45070040c910400040340801810700c0700e0898003158008201100385002101e951407c441402049030103174500160300f07481c2d5000407182c200141e00041c104401107500381c802040c0c5800010420f01c55180c0764000a103880d5400e8000b168242c0d9294030900c00300780c040102d91000984160b0442c0c01c0412000059a5180e030380c011603200300000f00d504045648450400d03a12160590055030394480c00c07000c4044903060510807107002840201c1803040c014000d00b04500111f94507800345103141c0d5400148129180081c01050100307054960010301115544120311404000c28125042400c5030a103044c0390103100b1000201c00b583c400401c00456a540061401503540a1808143c0c54080d40043c1c00a0003045060307500a4200300300c20800c2c198043d1043c1c07282c120500c01304408030380c0c07400441f1001d0020300400440c100c12020f000161038500c000c5e0a24070490000c40d40d0f01d030f813 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 408753093 1250 408751843 408751891
    0x516020a06030c0f11030a03090809360417070309030803130b150a1a0913060e0a09150b030a0807030f020708060c0f07080c01380315 59
    0x1059880031002a0b0703035800c109103199020301401c180700c0c0070317151821503403424980c0180c0703905c00c1010b40d0062507511158a420030481500b556500780e002401c2c4a1407018090b015843c460b105128400d8119039070b0007000f45404031644d00e5025980218148801400c006100451a0301100c0140e080c000754032000000036120500940c41400134105010055a4a00c1d20b204031000207090900401ea42d1340b0303082c1407501d40900e003004403500c040c00c42d144480c0c8840820701500c0391141c401c3d00118010071600700c079086030300310070115001c40c0700c40c03007469581d0781000003103030205240145400040c242d60480242c0340d40266400700e6000f01628840d16172a901c4440f66807018004a001c20100907005240303e0701404200c00811980300900903a180901006202e807041c401c18103184440402c1100c18441c654081d21303c04800c2c90007c1208100300031100d440380d5201d800a800d40d040c042002c0700c50b410a40c11020380d5071809401015624606083c0000d034001c01041c015182210b286000380c000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 408754343 1250 408753093 408753109
    0x50d03110a050a05090301090c0503070509090a060c170108030a14090109030308270606040e0604030215041707060f0608070305100f0e1911090105180907090e010515040912051602 79
    0x903c60784089d00210300e0041458244174083c1d0040c5e1048080100300f18960754046910010140d00c400001500044090251005081c0091048240076101e0002c00c8800000000b808a40c1d00d90f00c1c0d9002a600c010112a0944140c0c811580040c400117001c0001a02503203002d0380100301c000a0162003200c10140c0549085010340584050740042c0c00e100441c2802c2c45040c1607903a402c0c02400061403e130f203010756a00c0b0208000b080364003034080050705010003035400c082170070400703420f01e42d5480b402d040441c09040130805016001d8505800000c13516800111041125841301c060640812030000c45401400c045d420100500c0e2160b4044c20024001d21080340355000b803400c070888252150400300c80c1d40046034a4035005401c140c0050146680301000301203000e000c1d03210050650307140f408603030a0a8403540b010740c0c11401c04026001001064100c0c900c1460b021020f2f400c540244001c000030340d4000c04000d01645100d140355862588118010b00a503030015440505c6400c440c2d010a18032 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 408755593 1250 408754343 408754361
    0x90102040b0a020322060c08030a0207020d0308061f0c1407030602070302030a080a020f030103081614071701060605092e080703150302030d0e01030f0603030903050d03110a050a05090301 82
    0x1a000000e40007045c1407000001000c03440706142c154401c60510700094450f100e6407202070000d090120019908040640440c0c61f42c039405020481003401078030b00500310100030f075100788c468010102c0b680e50401c001715000038a00440d541d050360407030207620380810030620400c403c0d145029111010010941c90700017840418800d500440d40d41524020060400d200074118070541401003200e80700d041e4a440c1541d06481d0008511562144088920180131081c00c000900d030500e0a400c040d8264030200d6a0000c60384c071402d00171030390541821268200e402c3c500500b030105800384001d41c4a0300344020744590700101c2140c12040c400608600c222721801031103030640062201c00401030025490b00440c04514000d50380100403905603800640c8880e1221900700401082201c4200c490b8402c1d0406444000040b000300031250b200d04000700000800e0009603260b109141c03c4243c810b00c0f030320bd04420303a41e5501035141005050f0100f202d49510008140040200a00484c0d88554013071040c1a16 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 408756843 1250 408755593 408755597
    0x403020c0d230303040c0b07030c1e150e0705010203030402031c0c080c100e1507030b06090d0809012712080705032b02070f17040e01140f09060612090102040b0a 71
    0x101d241a06d0078010300051900107a880b41000c3c0003020000b80c108103120700c41d90344207104415410354208070030181c00e00c044016110390310940101401c1d400d40d82c42096000352b03040a840081c1e0b1501f00681c0d503440300b680c0083d016400300c0540494a251150040303030003880c61038a030b10f80e1180741c1c98402c4560025200c200040c2c205604400c1c50000c103203c1e42c900c9040d9400540142d00000f01c0c9a40c075480010a000149610790300105001d50700da10403a460218000d0440c403030541d0500f03103c60303183c0085a0040c08034a4550f0b19000a2009001c5035100054005240507141c0c1010300d18060504e141400305c070b490105210980000d003050016140120010f110000c0b401d9060321410402004528071106d0203104015030004039811009074044207401011107a40003082003c001d8061284d580b08000c3d4485d4a400811703100c0a2807155001194201d503808200c0740c0210800001134010394001e41e0040d0704001840c1c0344401c04007203585c004950b800042c00c09aa41d40e9080c034650100da50000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 408758093 1250 408756843 408756847
    0x9190b03040302011a2d01030b2115010e04060e011d010c09090e0726150a1a0604031113111314060318010b061b060f0403020c0d2303 59
    0x2d51707a8598000c0c1d0807100c115014000054001640020000c1400210030354014290300491740b64000d4001c089201340c0a4400054040c1c2c4240c242820843c07085c4811050103200e00164004588060a6042e900c0c0422500c066071a2507464400620051041d15565501c51060404040051003000381c041e031030100103e1403c2070341c50014108455504215400d5240031207003040d10900203900301c1902c00031407403040c001244036402006049031048246130b0f80704031040032011213203200030203006d480100340511000d01e03000070a02c801002d402500e038010505210420108080d41c1215081c40c4014000b8412110303102c6c6500103030b41c40b50481c06103500380080e80800f180120000e100083c082d0241f541049a103403000240d4030711000d0b000c00200442403d44a52950342984002c000420041100c0e03592091209072041d05052482000c20038010b03c4005092552000000c5d84074a900da406814031150003800c11041500c0036206540508880f0001c4440740c042000d888c01c05010000119 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 408759343 1250 408758093 408758111
    0x101a010314070905040b0f040203070203120112020f04090602070c14010210061a07080c031c0612121d13052703040902031b030709030510020f09190b0304030201 71
    0x1405a50298040384403440c0e0341c4040080d990f41c0005000d042d200300700d83c041102031181b07000036151010480c0f03c0ba4450300c000284000c1680000c018100c5000104110b000d0f6a41d41e0441650003180d5a00a50009045040445a403400b40c0c8200d003110b00c0b1300401400c0c100c054562000101c01600f1074126541c14030080320309980c040001341d260841e03401d400d00c1004d04000c03405103172050b9012040300001e0085880000c11a5000a4a042c030641e035040300e80b1601e002c403840c80c0450481100752009441c18001003211a000c43e54401e400390050360488425074945400c8840d101207040d18001403a00310f480109650312418903000c1402052004101800c0444021004800134032141d03441111031040d682d00400b01100b0b66040725444100103032250340700400c081a0300344095600b400b428000042042085d004511001683d01940465141c41c90150030001207100c1da070306c81c045e00c00302031007401174600d003186158a50782079903054485025a59040c0040b00e4006841c00c40140c9d44403e003203 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 408760593 1250 408759343 408759347
    0x6040302060c160f110306130201081608190609060f090f02040e1303020a02040e0609010c051e130902040f03060b2215030804060906030e0c01050906030405101a01 72
    0xc5400c103000441c07180c60a48440724804251041440c0101107038130a24010007440349240444c074803040080c094408510309001d82003400d5604680803400b117807803000071900c802c01604c404404940c5a0701c941582d600c818113400d007c100c000340701000d103680768100031460001502418004208020000c0001c500b464040400d0302c9500503c1d60750503106000410811180f4240b003a00401140c00b08000700c11a0308049007040a0b83d03201a4002c0d04000b14581040390009005205e1701e00d1400802082c40d1b460f5044030b03903201c2c2e17001c108501d03401c50004010242a2030010a020345031880140392040e560100030050380c10a5224031010450030b00700300280510390044400c442400c6490303072031552841c1c1e4400c0c0224220303501410034590b0b03916500c1c0300c3c1140c420f01002440d08410165121507a80c0d5004144103594050b004c00241404801040c40c400014242010513058580c5800e003100390091003115000204103407410300c282d140c03ca6800405206614401d14a540c241c0c012031085000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 408761843 1250 408760593 408760603
    0x52502130e07080a0206090105030c07410601140a080f0c0a0e0103021507060b04060905160206010503030405010513090f0207020907080609010e070c0203010e1e030f0a0f051b06040302 81
    0x840f0140307422600c01000180e98070012685540c209003041500c0f5140c1b003401c40303201d0103030000040540202c100104400c80101880020311a03132112200b01c0e03103500941c0012165031980646025500050042c09030f11000300009000a0001d41802c206503501e03602d103071070500e840c40502050b41100048012a007008500c6901800c03c101d00f60340103501d50b80c0405c04912004201d200b4041c40480d604080010a030003145010000401c00c0c0082500c80c089c0000400e0240e855107181c90844070701110b014004204603040310342c020081c6080c81d107040010354203a0700441c0201039000c16140302080c513501c148030f03c04010070980c0c030042c0c0707440702481031101d0321b80c010b801c030b4041c0040001004195a9403100b02d0341501d981124042944d10350310b1041d920400b104800039419401c0034180790107800002401c40101710003e91550754601c40320346480d01c9100c2d000401c1c1c003e0740100421903aa0313005001109075400d45280c100c0c900014106d0041100401100500c1940c00c8401400249541000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 408763093 1250 408761843 408761849
    0x30411010f08040506070e18041b080a0507090203041b060e03011109090414120a031a040203011a070c0f1502060906092a1804150c052502130e07 64
    0x4000e403007402c03c0e89845556480083c08002007104410441c141900e070f1440e03500b20501d03a008220541c2c1854a088045644884503201a4080d80c0d007001541d0341000a085003c103801c900580180c0303040040c851301940c07004009070390840c0c0040b00c01c1c08080c2c1c8580d1138002400b00760f03101a00818040101400c1d036540d56000b0211510500c0010402d0b0340e003100082e0031961000c2603072207140d01030074083c3c103000250309005503c280205038030250907099045040602c0d041001174582854032020041240400c2c001d244840e400780e90a040d200450400130514107011311680248c0f9561900480c6400c0c401d500070ba138041d080c00510417101c42c0c04010f41ca800c642200050b109500e420388840707a441f41141207491118011803100054510807400300b4201d480042c01e401101c1940d80c0c1800039101003a20225012011000307542a0f0140d0391046007440030450f07440a1a00c0f405640307224110b94890360101f207101d1900c0628005075601109840903200480010850880040020741066200c2e4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 408764343 1250 408763093 408763097
    0x307020a060e06012601091e020a090507020d080a09171206090421050405130c12060e06040504020f030624011809020310080d0203040906170a1214030411010f 70
    0x80107101d00c070044401d0010140800302175118001c48050319a000d0041800047c0c11070010624900355140c46030440300c0858000c0d0b4001c100745641d210540e0458504a48010060700107c1910715020b100c0c4000c140c00200032035001c44ca5000544900c1f04d403007503c0702c0718031070708100040d8590b840d008282e402c0d6108074200c981a1051400d5181c1c071221a682c0c02052407901d400e40c5c80070351100c2c00b5000f40d401402014051200080c0701d58000f170014a144000c03070b00450042e80e01001413291038018072040c0c1308900c041c110745884100074000500805413049900c49981d040c010100c1e04d040083d00c1c4103000c3e14000d400d40d05481c1c504090713030001c0c109802d4100f10b0486c3c80c0300d8060301644058400c40d040c0c01c80050341d83d0ba503c81d0215400c1e031103411000c06130040101506880768000064420f49600240402c17030940c3d101c2810340d920502c0b40710144a03403c07122078640030038008a66408070603400e0604a8200582608403038a87d481218122141040410b100c640ea5a01509400001485d4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 408765593 1250 408764343 408764353
    0xe0a0b0f03060a02030c040e09060a0501360905060f0f06030a020f0607020307080604030c0506010608160c020102010f0e0304090c0806062205060a02010f0b0406050604051309080307020a060e 84
    0x9002103030310b8000050030058019000004141c040300c513407085500074000d0740d1462880d801c0c10424a0f8540100740c074071030040350401e4000300d1190a9601101c01c1c902c4601c594440c640d045190354803014003002d403001481a0707261076130b6021a40034400f20b0f11540110044149a2074800b140789000c403005042d16001e5400400c40740d005885d403a20341c4802030b600f129460380755034032440028a04026034000040d14000d0005000c200354200c4441c2070b12512500c1030381c40d2607803901d008448600c0201c61617a00c0c2200c6031030200d40d86c0e00070302c0410801401840046001c0c0c11003c0c82c0010f1312404440145030b5400000c0400108203d0310070644509040d1500441d503040440004000380141745005110711158900400d207120340021401c0103140c00340103c1d4480c211040080c2c020040041014407050030a40020020300e0284203800130707500014101410982401c1c140a4400d03900f5104140c40340d42c480c109000f10f15000c0c0070354400ca003d907009000007250351502d0005d8407002c6442030059400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 408766843 1250 408765593 408765619
    0x121603020706021f0f060b0c0d08091b0409031215080708061e0c0409051e280b15070c031e02060a0305070e042a08010e060402070218010e0a0b 63
    0x1460341a0031800c1918130202d03000418007030f42d800601280d400a80c950750000f0b0044104000860009a20341c550b44a04c00300d507841000030354568184019460340b035100c403084038041d80707403980c0309030651802132030848405401c0c0012402211050054a103075481910401c101c4079034200800d00c060801d0002410f40ea040c05851100d5040c4244600d07201c04404400180580301d500007542e0042428090900060500b103c1c080381c41c00346481c00007041c101b90800100a83c03e01259240d800c00c11041042080c54483e6000004100740d0787c0003940040c240e0385054030141e0f03900c05030043d01e0056003818030242c41c2d49410380114882c103241e05040340c0fa06c1800c002613604c3c40c0980700340b030519050100f0b06035665901120000d024449d010b5000d071400300440b4003d045000d84900301d0424410300618044d0040d0145d030285002d1103001030500c908000901c040c202600030706400e81c80a0416512514110364508910000f42c024130001d00c0f40e80100704034244180510710301c030074003550f2002e0003000d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 408768093 1250 408766843 408766873
    0xf060611120c060c0918040c0906050402030610080a0605121b15090f040f0207050a03030b120303060d0f0213150b16020d03210204051e030a0b070212160302070602 72
    0x44010602d450f00c100c04691401c00d52501b00d0785000e1030300ca03015200801d18151412180d14080c5000c1c180e1b19a00c0c06c100407a007800c080c400c42c1c1c081c540040500c02d03500c0c0074840494541c00002c2c0051099500c0e00300000f440c0e264000c0c00c0c003580ea01c8201070012858441c80022446248482586c0b0801c00496181c150440380012078180e0b85003a40d0802000c001705002c900a0a116010017030a18070000b43c5a052040110310410071512a66080c4841410030b42046600f12080c0010000d0360010804240c0e145010b02c484d550041c842d40c010000e80c5400e4000803020200301401541c03d03070b19044601006040305a50a028040320400c20f4200381c0d0b425406030b072002c2c0c2c5040090040070000d0040707091600442490000b10144d4095035080c43c440170101020b504603108a40c02070064150a046600903151990781050001d07004000903003c41c1c1f02d010589001410741400e43c0982c1440f03840c100503080051100d48171680e10008541568a40246000f80e0b0fa88a40c00719000160b82c004815 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 408769343 1250 408768093 408768103
    0x120d020a060b010c0312020a0e0901080114060906010e0904021c08071106070818040f060b070c09050411091302030d09030b07031512020105130f1d01030305070210030f060611120c 79
    0x74440e60b00c01a220123403181c0030b8138032285a8401648c48210390000140c3c21005402a00b801101c45a101f407a40c0c480505211985800f03440c014042048881d02480c94103150003035980c0f003800200b007810a00621115403881c00c4c11950203444030100000c0c0304040c000544442c805050081c1c3d4058940141c507268000c041c010a0006828615400e50740d19503075846400c01d03091048411002c00c01c040d5119a110210f0307004410484a100003190000b50034130131840f406201c0c0d900408a140e4501000c0d0401c00f4811000b400020080c2e014007200e000340c0c80400030703005051640d40310602ca00f82103061085004000521207400c060408a5100e00290040200c1045070742c04004212628103520042e11907000300c041d01c5040c1d580364100020520700b170382d2020080b103c200d954500880c0704080e00500d6800240009000b06404100b400014180741c0c84c1e900c4210024075000500c0228840500705440d1164008000103d0941d020011030703109105504440010141c554070b80700040c4a40d1b5104e03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 408770593 1250 408769343 408769367
    0x80f010b040e0703020c0c1011010b0103050112080a05161b050d03020a061a04090c05010930020a09020705010c02060c07030207290c010207050705220506120d020a060b010c03 77
    0x40d004103406c480741320100005420000010b000c1000c2d080b8241e001004041500e81c00006907080210040c05940640304150684400010a03044480c440e10740d0030050303000b6003002c1b080142c1001030903040031124600005062044010814058101281e50011900303078009500c15034110b0700007000030360005070191460394414404100208983c1c01d000504100d02201c54110342421280010010340b00c201e802a25026203440d040186c0755100c41340c180100c0b034a080e4142407030449050840459003d2282003d10040001c80201d4840c03020300e00b03036006480c00300c54907919214481002038040c08181c0e4850074580019003400200d850003980c4078494440d04001007208461001000103081c0c00200e0000c2d1441420340d25003502c0c2e48a4001e60001c44240d415000e10f0001081924190310780300c3c04c2c58003040c5510500b00307009200c10010880034002503844204408503169241082c4101700e4000481d80203009000b000341818816191031340403031070412090804600000f900030b1000000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 408771843 1250 408770593 408770597
    0xb040624030f08071b0906301104060506070303050406050c040302090103110f060a0305070314090c010c150c020601060210140610090801050c0706050c120c130e0c0406021501060e1e0d03080f010b040e07 89
    0x768003e00709c0802d006101c0d5410598019200288160034550036130001030160b071140c101040383e50340f8504500302030b00a5000095100103a0001000420200d40c03100d4442c2100520600f898100400040c0c119800034a15002203a00c0c0c008010b9501c1c0c040c42170b09502e020401d20401640340a80340036848029a0034100d0503c8580b014110500841c182100039801641004200800389110081e627100c00911034480107105414004923507642c54000c524180051781180304207a1281410040418482071000e0108481e180002804000c00d0240601580d11742d5100742c4c0c0c1e041542001001d03110000d0403184c50103c10001148183c00b03404850340e0000d65151201d88071014029044003201081c1d1245a80491035400e100e0354900c01c1004100300c174060340071581504820404074403009424803e010100301c03031303284042d11070400380b01000d0101e145c940014807030a41c080c000780040070701c050b00794005502d050811400a01800000f8090107a40f1801401d0030300e419103104103d0f038014805e02c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 408773093 1250 408771843 408771863
    0x219030c2604050105130909051606030c050405040504020d15051609180504080f0d0204090b030a050a080f0c070803030601090512030a0309020d0b040624030f08071b090630 76
    0x6207646c0f069002001409003414180841540c0b800e04550340c1728501002d46801c0041403001a1640c024486d10b08204e0305c1e503c480341851710307000401c40201002081a42c1025001c0501000600307081c4a60b4001c5503000f000140ca07090400242d1600489070003906c0c14049609400c1c40b040110f04450a02c1c0c050b2010b0100d0107903101d10342900d0034091000303603250071540415040303003c40700350b006403040d100c3c0058100b003200e150313400b0156962100080509a9000b00b84070308007159141004050440d01d445004e460301030681c404a161180e190704c10b54094002100340f04e507070f6070320182c10300007004100c0c0c0c1904080c0d1646030aa80b24807480407400f05142da5907031040c0440d01e80400c524851a0044c082204500e0a410440041e0492001c111a400c0005034400b829888501154040d02d80203808084441c0a0342d0303c2c6810b0364131074001540d110100401100c404014903060301c0240003045404100c0c0b52600c0c28010b4403480700080d200c0c5003088049400d85035419915400c00c6143c008804130 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 408774343 1250 408773093 408773107
    0x1804051603050c0703081f030f03030b040b1c030f032c0606010f02060a0b011704240c090306090f02091008060703020f090105090109051324050d030c030219030c2604050105 76
    0x112000047d40c0c0700400302c200b0b015502003070541647c040f240e41402642c091102c000e4140400203000d090500c180c5007041d0707001851010034803a180c41c41c0d41d00d40c1410005141091840000040900e00e82c442144035009446003540340c02c140130301900143c0a080c4039030746491a00c0081d40b100d00041510080980d05d42e40c0540982c0304400ea2009181d00151070009030420341001030300306a42141c0301103018600189203c0000c998464001c018035107a9608000b581540c0e039082c090441c00105542d180c444894600240c1c2e11b024a0078094081c0d8400c20b0101d0345840301c030030700700400100101c0034980b040c850007004080c0c200480d500c100092900d250b954032100b005075403101d101c0e0041ca8100709000700080070b402241d80455038101c0c9200000660034400704003120080c04500580ea0000b0f034140504c000240900300181f0264420b0059503d4041d411116002c0c10304086000d070001400b14103c0f901744100890402258400e440090306c03c170240001100d035511441c8611410400000380c04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 408775593 1250 408774343 408774391
    0x6211703060303091012090305250804050121020c030703020d090f12022d190f0501051b011b03050105010f08061516050705040507091202061804051603050c070308 72
    0x403800c0403402d001f044996581e040040c12600111a00410798000701e000c3c43c1c4016400c0c4894040b0f03644444001d00d014103020046810724100ca00700440d1407811110f10800d8449400a000c440307a0340d00c01592621414140280b80803c804002000e006c82c04009000d0f0036041d00407001135031900f15181030f80401500c04500e01c901845e00e450010300030f00c031a140207846200364810440104075456103a51b402d4400d840084e4807644030310000020411810800d42d409240032f0202c00010104c1061309034007900000b402c4d5801c2850030b01e0220304a2402881a5416116a40c0541420710b415a101259074034044c00c441c40160800c0d224906180721010403017010340448a1151180013400d4201189141c0b06517a030845020341c1380326500f0200000c0c80a403050510308110f40008031240031101c410340070310046a204030b500c090310010010030725a0380d0303d071809510b0007203605000e61940c00403201e01c0241154000b42895902000400468000c00d0748246400d400c504034040082c020000c46841d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 408776843 1250 408775593 408775607
    0x51b09160c02150a032a0917030c0709020405180405030315031e0c040c031118040902061206030c0105190e030a170c060106080705180103062117030603030910 70
    0x4000860940094500e204641c16006030400a1108419505081201c6006d041800c0102c082000040d403600c020410135543d000780304a107401600660b450403060845841c2010b825400134610b040d000101000b050401c40721460030044d507901c000d54141000d80c1c840380c40744406812a072044508900300030040c0e8090080d5941d2031044066800c1c8028020491900d6480d080c4003070340706514001e01408441e00901884100e50560110070b460011140c61601d404c0440901143e00980c2e074681007401030f20b408005044040400943c0c02c120b28204041504d0150038420460401c482400718080455441010014581e064109402c944091802107440c000c0c00c06009011000e10304074510180300e602d002400710040010681d0f9007a0b0720b681c03040e1041e03d01a2282400103504111072101c15818007000034030444145000314046a58003015001404c040182d40403e85010822404008030140c81401d501c100342a42c034118940100020b889028803820b82c1d000b0000004203080051041d45 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 408778093 1250 408776843 408776869
    0x8160311030c01090b0906040c030b100b0a0806100207181107210f02010b0a0611010b121608010b060405191a0a140702030703111507051b09160c02 65
    0x100720381e12407110480060103044400c80c15100b0280b600d001c9107580c400806c507144500c0e0001e000114052547d0742e43d60707603540000c0a40f02012550ba40c081911060040282204d4000740e8074a100e5080c000f04000b24010300340000c2d01950300c200010031085c03841100e9403000d2020f80d03400140400c0e00008070308031840394801c02082540048080291843c8015000c5910034180d5903c1c3c00040c8005001d07801c0710700c02c4100b079a020b4104101004440c1c42640e036292000080d40001c1108490170010410388200001c041030035400a0321010700c0429500c8040006040ea500244003004809002c200c0b544100e0164901849002128034a01c50300348003d40002d02c0780c683d207480c50f90103d03401070149410412180c0d0015441f88680413141c8003103000c5c2da2a40d074009000d02002480c690700d003000000f018003c1170300b16094002c060140003504c1e0103060114010400f4005140070031002c003200416044140e4401d4090105000104c500c0b42103032403450a40c0d0804c01b00c134218500004800300c1c0005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 408779343 1250 408778093 408778127
    0x51203070212071d0c0306040c121d0d090e4006140103081611030304030b190c12051320090604020903030d1109030a080301060e03010207081603 64
    0x1042000b101800103180b10448130040d00c0e88034095a0360003000d030f5007001994400d10f003041c00e00c04240149000d078400b00203a0101e086c42038034a506900780100392100a48840100072030200c0d40040f982c41886650080302e07880c41d00e40c004508203030240c0e040c442c0241010b0703001591801241d11000903c10b4200c035600d290003003010000006071001d11405400c031000c540301400c0501a404125490000d40d050360340c130030201c60404103002e007031301402609254182ca0018107804248101c2d1000e10061000e1405481900120301c0e102624076010325000c0034410142c0d141c0307060300c2180d03544070740394501c1341e440000003007001e4131283c04102d02c1924261001c1d041c10300c480058003051120741e07000b550761340040e5021900c47e560300302040101d0240b400e0082e0180c00401400928644a600284806207005440e07814034000034046403520b000000f00b141e8981c03000005006c910703084100d00000300c8048000b03500d415990340e00c2c1499030083c0030340d104041440c1d2120f10101406a03150040c100004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 408780593 1250 408779343 408779359
    0x105101101150e01150e0d02091302040218011d0603040b0406110d0c02010b04050103032304170304230d030509031009050705040c030605031509030d15061106040506010512030702 79
    0x2c0480b03100d0244284036001c070301c604034181e56030307818000c960b1a490408001c7c142c14a02100d6001d20800d400002c104107200c0342d0a50385c03440180c0d40c52001d04242108110300c11a081d00313000c00540b4032040d0b5840809403880b40c3d680103004d56034810440c0e520980c0702041c51645d1320b0f180f5000c0d0182a45e00711400d990100482c41503401000b0354410310009035554024080302181c0001c0c0422940c00307000c0500060050b2a501104840041c2045285043c0c041110301c0c02d0b0742e40e41641c10701d42014035a2105600009410401074201d4001740b03803410908201c02103040b80c0b40d0002070750b182440200a06000700800d6241243e601404091080701080c0d070180700b514030760b06d0b01c6030711100c99000b070500c51458116101000740c800e214031025034601400802c00140700c642d908490803802049010a88010084980844494041c81100a0101c20b41c990254201500503111400c820f2a07450994008020040800c40004100d4112141a5802404041990700c1d15041d4030030410702a412040c5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 408781843 1250 408780593 408780599
    0x3040f020f13090506060406150206041106220905010503030a0219030e0d050604030206011413020c030702060d0212160512090708031c060803070302060a05070e0406030326010510110115 82
    0x400300d81144071b010122020003071152a4035801c1240f4111030350200059101100007400101342911014110000030549418980f41119041c0c0210001400b0000c14650704405c02128029015150240c5022000b660506866003c02551030081c0c03c0000710b42c4000105020070b06004100a44000c58041c0102c0c0600c42d00d420815507404041d00e080b0014441c031800000c3c40b1109101401028600400c0011848002000d45020f50402d120b0102c59000410800c001655064024a507410801502584034000c4184580741408000c10044041d501039512070025503120080341c012400700100d0341600d4813041000792900d51150030000062000240b6602c22914134055545c1e06031800760148211510b800d0429100d0103010001009a400013000c18800d0034207400543d03100c18589070050a59040720002016607809a10650101e520f60041c41005081509510040d001d2801c881402e5498403010a2601409400c150108820a6091a00a8001e40084103c407100c8a03004c03080c252 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 408783093 1250 408781843 408781853
    0xf1a13090207030203180103051006050c0102040b1605100c050306091003080d0b190302150a030b06071104051e130f050106031118010315020c0f0a0506010f090203040f020f1309 78
    0x11044080e10207106d00003c00303200543c4a40900340c0720314164081910404d00c0c5c000d0a881d01c0d0051446880380b55001d02010840c90203072805040c2c3c1d813800c5407590901490500b815410400e102e00c3e00d852050601118051594208007265004801511070031a10f0346c0304c031081d901e0503006810081441c90000340164140046030054074542e40100c802c00050310b110709c507090740d4015902c4020b40000d044502000c40345030b0a000340010040b14200881c2c12206400021541c1d0b000e218111041b081e50314034469103082c280f16107907026140d410040e034000310300c481e00080080020004070540e1100b5400204101c5c410080002c841d034454002e22000c0d40324a80403068030458030109006044041c454200e0001c5100d14604a90300282c065200c405103211150103076200d010240005c7c0b0444c0c0006060200c100a60450070b40240040e010b42e50604030000d40041c0642d1103a108103005109120210390400103d501c0309504031000000408c1008c00715645919144c848d806c0c16240c019100203004c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 408784343 1250 408783093 408783097
    0x150c0301051219020d1b030503030f0627090c0d08070b061c02010e0a030f03030605030f12040e06010e0d0303090b06120615041e150f1a13090207030203 67
    0x900c111041560110b107072a2075540d07491182c2011941e4500504400058104010b8514080740100100d0b9800e81c2c940021910304205503004403a2580000100580651452956a00080c00b2120180d2101640300c20303c064145407c000249541030b0404035003103000411041121070005010b00c00f001c812800c0a0325150403440f0103440c182026400180280f4003600444081401c490340c0e0f1082894540044450001e8000184d0b041000403038040003044014101d90b103014401d0364040b840b581004245403c0c89200a84d56485610855203203011800f21010b84003910b80041c038180c22640d440004030b50720210002443e410446c903d00600a056145d006903170014042d111a03034054480340305111595422040040c2e0f103811810100701301c0c6a10f07196407485540300410118051205440d1071000240c3c0d03003a44c440d1199240091111100900040c9004003807808400c00100c2c5000f1510101e06800040000c14070f0340010b40c942d684000b90a4513001d41042c400c210344078105032401956030307 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 408785593 1250 408784343 408784349
    0x140d0612060b0a0e0a091a090307110102030f2d1207020c0612040201030e010f02030709050913050622080a030b04050a0c050f071a070e0a21020d05150c0301 69
    0xa24100034601c0910704003c07105500300e605060914500d503803020482001419240400c0310302149003e0715a0301e0400c070399481c0340a0800c96028680c1c40070140f42185a0003041031406040d50000c4c400ea4031116402810f032034038581c02c410113038211070102c0080310311440c40c0f003080030b40010003250000d80d030050318010f1803044035242c00b144c5406141c041001524040c0540c4200c0746040301c80004c0040d417003504802d0600c0d00d181c00220b290001c512a2134113030f8000f21407000025800324001c000c40d1400203030503500144036007006c05806016484091302c811008164484010f85601d40702c01300350140164020a075040041e203901c42e9600750b4001c018001c4000300701e10550420000c590311601901ca6081220301c141c03912441e20b0b084022140198009590030b44440314502c4078803081c02c80e1440100c3c480c05032541c50f601210300e5481000b09650983c2c000d1055003109494a00d0401d4034808200740141d0121540340079843d1a01e002441c100316070828803003e02d101707010700c883c0c1c0809401560503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 408786843 1250 408785593 408785603
    0x100507051507051314132c010507170405060f06060c0d0306050406140904060b0a0806010b040911070507060e0a180b0102010c0302070201140d0b03060103050a060c091401140d0612 79
    0x48103588244800540701701c0c0005581c400310940c4000e001015075840b0411400c01440126100f0324480407850050142c0b14131282c0c40d1351a5010001002d030301000581041060b085403d0311404c160f00c40558801005140d030312414001d00114800365582d9042e50100c5840f1800c48510000c00c030300050241120344586070069007420380100e1401c014400705038551101800e000342564994a600000d0003400315101d070840c0c3c40f248085004001070003c02d0190240d084e85070f68845c5003500881c03c0f641e028041c940b9000c0c003031068900203800884c901d4100d58903460a4410001050001882c1c1c10899010324040c1001c400108180303000d641010b03030703804401d8000304094143d03800160142d00c071f5a803000340011100540040ea911506024142d000007000c00013408800040100c0d1030003000381c0017500c407a40000021010080c01380151254490545003c0028501c0c1c0044d0200407440121000d06200d108030902c62000342442c191403400c044200d0501c1207596801000919043d41e22041d54 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 408788093 1250 408786843 408786877
    0xb06041404060b031504081207050903010903050301030b0c071709010e180906161b140f0a0606080706050a111c09090608030f0405211203061003050610050705150705 73
    0x2240e841e45d501d0082c40740d50800901032400c07110480f41d1003102801003001d0203001090000c0c0074662024414800c4240c0300b600c0e81542c950543c01e080d03a140070020400040d50004000c2c8900080a0110101c4082d4a40c0078413921400044e0040e1015050800d1840d0002c0302002ca9a0312088041c103194000e00d07440c02a1480d6440300c00070440300d24036160f8443c000c26084010b402c2144550351070360001c24000d480f072601303162000141900307001a50b61032004680c0400813a005111700c038032480004040756802004210304e0807001605900840319200203000c1d1070182203403c54001e020b162045002e40190141c11508800302070b0400d03646014100f440ca14048000ca411080042204d03884261a041e041c20240307008100904c01403140440d5003035413030042103010450b07810416080301d0194550030980701c1c07a00c6000d10a800d41d42205c1c032810541048244030807a02c6031f405410181100b4548142c1d0b560340c07801c0480c5003040e46000000c0000072a81004000b581c84000340c910f080ba6101804 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 408789343 1250 408788093 408788113
    0xa0504021f0e0d0317070e09010f05101b0533090c120a0b01090207060f0951061208120a0e0613110301180b06041404060b03 55
    0x300c103851050400404a40030802c085402c0c64409070380448540b1910b81040c031031201030401c524000e420b85914002c201d0740c01e0712003494036060801c03d01500b0841c4600301068a45000114a619211508010700032074024840c9280c104241f036808580d00700044980c05000309103050800340410f41e40420070421081ca04000720019943c20780a0794500340201008441c280800c9922803110300c4c10710b103610542035040000f400c28002d060003071444550040e204e04090030f142040e241c1d09040c00e200c5525101d04c040018074068840d86540150341a203903004640600d1640c501042c1181c141c0100d2820302680310703802c0a441141d0300c1112500e070706000031662440c000380c4900e00d0b00e000030600310052080f04c1281d82c0c0481210340c450543d90020601e4541c40c140c3c00d052002c19980d114549021300064424410594145000d170182900200600c2d440a502c17140b4200f20007400501c01c09210021031426640c9410400c82c480c42031040b508107040516101004101c021f0020340603001d0442c0b94 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 408790593 1250 408789343 408789379
    0xf07050306071107031103010b1003050f0604110a0806010909114305070e07020309040516120b0604051008011805061f090b19080c07050316060902090a050402 70
    0x114080303143c0f0005050103800c0d540c400d50010720b5400030a4141d035840d04200c0c171907560b440244030b01d51001c2d24002010304081c00800310b8541c0080c2103a01a50400901c0c00102070b2000444241080a01d45095036884940c01280c000c1c220303901480000d41041c00b6600c00c1802c41004101000305500400801f07900d150450085404000c0c000400c0c415080307174140f2602e00846421010345c071640544500301c2d1180d5140e94202c0c000c1d204000181d01c0450030024904161080d2270b00000d00c1c03400f0061428107004003c0100c18803032051540d0036164045c3d05000e403140c80644003c0c01c402000402c4020415400400030042403041401d80d0000c066280000080c6100300740c002c1130050f100155003c581d10800124174416030300ba10800100b45000203c1c0c1045038007030281030036010030741c10a1101059004003204005070010544260030000400040c2d000022580a511642e400403607604050420344002c2c40d1201010b0b400c80030410800143c0759240e03010500c61442218074000a108007108 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 408791843 1250 408790593 408790607
    0x608070512030703051806041223120708070b0a0e120307020307030302031807090b040c1b0b070210020a02010f05130c1403030c011a0102010c02060f0a05070504080f0705030607 78
    0x7495046400c02c02c07880300400e105100600c019410581140b088001050100b81d207a4410390185d0300c0c0403100360312081005103245c1c0215000000201a5012958042107661031302c1005aa0195840e400186d80042002e408151517006410840410903031802d0151100a00181d041e5404030740211143c030300c080364480040c0c80c040e49032030740150300348072180d40c050300203500240a0445c00b00c00e4404040100340100044009020341d00d0000c0754404005045c8015a11030140807000c1c004050443c11305040500e00c82998503401144040d42926034002c26401c0ca001c280c4514009800080d041e4076940d0150410300411a03156170030080c80ea1600844503035000100c40040414079865000c02030034114084c07843e001c01d402000d50385000e0100e0380c03660840380800e41c0a00b85104c00c0c2d8840141d5038081c03244880c41d0305c03280042e02961400160f25070701d9540050603032801c00d03035440c0495915031291042d00c014050140484200543c5540295515040da1103410721922179000043c4842d845411 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 408793093 1250 408791843 408791869
    0x10b0a05010f170a020f0307030b01110a0b0f130c0609061e050a0c0305090a0323070302060316020c0a080f010b150d0b030a06020313050f031201120201111006080705 73
    0x1d07500005071103083e001103000001500c40750340380c1e0f024045114800d203d40011400361203d91400140b8110141c005400e0003010061040190401140702c40441d610201a41e4810017002d81094a5501c100f008003030340010420160040e501024041440c1d900424000305031281611fa99003043e0008201c400851484409200043c030b0038010414a58001d4101000b040c0c071030300f40641406e14141c04180310b15220384c01990714038119242504150700945803400b8036180c01001d05013080c00e640204200c1d1201030b20007410f00500d101000c60343c5100740174160708041d0090404c07030010b9903019030301c0e620381880005030225460003a540b24a4a030401a0f4210001c0500101c0d0800c444059484014501901d04a4048c06046450740024180d0b00c01903100c0c0d821500d84a01e0140903081c001c1c43d10000040e1840c80341e008011f29054145020340840c1120322113000710603500d201b480103c403880c284280310305440c410302c000f0740c442c0b038100d401a8081d5003003038045400440d0303950204804000119 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 408794343 1250 408793093 408793097
    0x60f0906090c531603060f06030305040527010603020711041a01230a091d0f040206030405011805030c010b0a2904120b0f0c07170c0f0708010b0a05010f 67
    0x141501c82503407032202e102103c0700d060800c0c1c1010030400611410802d0b580307401c0700c41e4000000c0500800c0440c2c4070308041001800e0040090a040d950041d1a91099020340d9200d614101c0b00f000310368840003d02400108881d015108d2541e407000d0140103900451003c48940912440c3c510300c9080c1485405407122980102c0250050b4507801502d01036400c05250151074041d0803003001e404800d0005081741030a50b55480c08440ca0702d860099484000c240002010f4101000c0c001c201d404c81c0f01054109804a90181e42c9885500c1c1c0070b4010a203950040384c3c1800b41a00e61003d000e008405072107000081c0c0000c4c07082c04080410040940d5840c0200407c07010039140c2081300100b4480400711503d42801c0c010f103465150084020b401030355110484001c041031040001083c4003c400035000350300140f226060940c95620142d2600000c155a0b8450750046000081c4003820021070910b10404010b48e0341c4e4a450740e003101d002e01020800a8000c0301564800520f0b94810309560300381c01866 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 408795593 1250 408794343 408794429
    0x6170a0c03080a020c0405010b04030506010b0a0207060315120f11180a020d060305030706090c05061c0c051e0706050106020c1806010e04060b0a030f020a0c060f0906090c 75
    0x50742ca0321002e803c440703100800c611a414407910740713031214451540a8801f142641e51a40e1844c0b40c01d80c549001604001d0a07a08103005028000740c00040200c2698040e007000300311612141c0e0020380004007580208241003c443c80141400a95901a0301e551700440d9189001c2c0c00000a024104c4180e805c20350080c0a000000f400c0c200e500d501800045030b0549003c15440d035640c4a1900d150000801540c0b01655040102c0401080c501c59100510702600c0c3c044c284580c040d100035900c10540c0030180b0701030b00c42c5c47d5140c1d030380d20410031101010701c0010894000d20130440005650740004904a641500c0c100000c651980006000d8a0000c030050030b6501c5000840300c4c1c46580440604000e040c0710742c00d0b240c2030090ba03550040700d0123071002000c0300b13444d400c0140e4020107039001c515000351f46610402c20940c0050f88544031a0007641c200c04081200040d5004200c001e2941080103402c1c1e0380303400001c200704481c50320107108458580b903401481c003d03803200d11108402c01002010751030806e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 408796843 1250 408795593 408795599
    0xb03100501080a111c050318010207061202130b0d090203010b0604030819020c060f0a0315050102100213050a030f02100503090304120501020d0e1c03020c150c040b0c0106170a0c 78
    0xc2e101c411054403c02510071030719205518172418107114044002c079520380010030250011004030704603c084042c03d200500c0c04030b150000140031901c81700301001030320750005107103000c0c10203c840d22002003603582e04050390b0b842c207001a0710040a0f00e4004920075400c000d0030305914036041040d0b400f5683c011104928011544440e06106402c0741d00e04400e600400324020940d90300c0c000904071714201d40c040c055541d03031580801001c84141e810b200a605000070b40c01e02803030340d000505403178425038054010b03a18031840c4081451101d0992200d64080f481041c00b000700700c05015400d01c0c940c401e03244946404007a105c01e603400c4c08101c0d0112072030b610520003081300003803800045501d82d0180e400103180000204803101038840e200032110301d5602203020b8084801c8032038000b914003040d40c40c0071801d01d5005d88100e074545148040c2103c00d21111004a0683c0040004550060201d1000680d45071041d846440c06010584244141e41040c8261001144cd010070076503c801e5020100da5280c0b41 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 408798093 1250 408796843 408796853
    0x20d0b060321030606070302070801230604090534150206100b0f0304150203150102060106030b01021b01110d022b050702100302041a22050d03080615030a0b03100501080a 75
    0x411b060307045101c1c0300e0000846207403e12a030700d00312034450558040280d10b40c030340c40d2003000f0140185004522308207049c030120b900420200c0014241c1c111000c01e041c4c5100d0307a9484411176156142520304403620015428000c0305020400c48030b95000e44000d940d4028682070a401c2d5403064000b114020400c0340c0c4220484802940d010f80328a1a02c00f00d01e80400104040703070130484d183e082c440750180c0716000540e01002030a00404541c82c080c082c01c1c1c00c00000035212800b580300c401500464115200d040e030b000c3c100251005c40c0440c225000c101e2000d000a41d92071422110341c1d00002220b100101c1c180750900443c44003202500c6a5192007400d0703085c409080500c544081c10580d00f4003000c102c0d44402d8110301d02505400b440141c5444c40c02850854980440340084c06d02d0481c0c0c841000749840b6035914118440d010f080665259a951000c52002c020300c1c1c280c003048034000020000c00000507404001007000503030440d01141c0c0034034000c0c01160000c0c020903000d68030820440000030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 408799343 1250 408798093 408798097
    0x31209010b01021501151403070c02030c03120f18150a0807170c1317150f040b010506160203160e1021150f0c11030301030c0e040807020d0b060321030606 68
    0x401611f0f004402881400c601e0a06400503070f01080000d02c00d211704070a40c40e00304410000d20b0403ca002e00b100c4150b2098560042c481d0203a10b0000580100788207481401c008a250048140a020300e482000703550201ca07550ba020110410108000801003440c3c0d9104081042010f1b003ca6520040b5403505440c4a54540000e103c00c103959105040204803130140000c2d605802d110000204182200300300d070790704403910081200b91030310184d5042102140360400030724110750082e10310964548205a01403a00380c1002c80182d0184550900100b010008985400c1220100c00c0a421580c50780d020380780b040078903486003560b2012041c000c1c00070001c1c107030440d000c3c172841403002da203480c0d4902c0c0d4410141e039403c0e20000b04071a03842e10708954058010a10070300642980740a5071441d81103070b032615450881c50007102030890301c0400043c10042010101c880607500202a1801c400d400d203460302401404640c0b8901038007030940308000154822019000401020f2040f83c11640c1d80d100f030102035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 408800593 1250 408799343 408799379
    0x1c0605180f0612010b030706020616030b0f0108040c031a0f07020d08162c03010b010908031c060914160504050f060d1d010f0b010504150c050f031209010b01021501 72
    0x10f95030f80c80d1102c1d8946da0400410004142e02d8029203c149081c3c40c550252800080c0391409160601e55204400e90b01c181340d4200812007400c00d0041074030b69041081c902110741e04020000d040a095140442007000103452244c48032404018550f80c0b1000100d0301e803145203848074040390030000461800d44401c4041c05002c20f07d4a0401c02175080d03c243d000e50000405040c182c510340108442a20b0f06003801440c50b11402070070294078484c0f4000419960344070324643e80c0d001c14407080361250103c099410880082076062414841c102820741c00004007041560310720026404400d161583c80d01a030207580860304000d0009156100f040244501a800f41c55510103040d500c1440d0540d1380411066903210190740782c00002c0320b83c480c2c1000801c494000c68414148181848100328a0309690a11010344050b807604a45060b201d1038804d18100059507014840c0c0800300760440d82c02c0c2200c0034140305858200c02440100300d610016a1100c00803290000500755440042c4a042400c0c0803180702 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 408801843 1250 408800593 408800629
    0x30207110117061e10050405030105010803120a0b24031038070b010617060604030804090905100606020102071104090807231c0f080601050a030b061c0605180f06 71
    0xa044d401c002902900a905081c010500211f0240001d040900c030f1070340500f800e2002145040301d0325010200350306004000c0b40103141c40310844074680e00c52880c0c40d89606481c0341c0440484181440701c8200b0703081259150100c03118008001990808015141076084c40344201d010100c0441000d04040c1c850710540c10241d01c0c08002c5207000441846405008000a640e06081e84510130a01c01c908030000d44402c5c8100c10610052000c2071104ac1210100c8034080340004003041545000c0341419102d00610b0400d034600400091500d070190014502c8521500c0326009183e00341d810041122241c15014101070828420100003a088000b142c140c0d600700c502c101005000c0486603840c05c9110700c205902151181c41e207044441c0c11002c4400c10b00c00340c2c180458140391013000200f25000307001c034907010580c507240f50300300035100c00c2d0071140c0c0c900160401101005441e82a500a04124424940944801c0c00d283c003596070703001c0c002402003895182204032030701d0b958100188044a041100380b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 408803093 1250 408801843 408801889
    0x14030a06290a0e0f310203090613050f0609030301060f031103040f03230406140a1d040212010e04030207050d0c0311120a0317181f02040b070303020711011706 70
    0x132035a580750005000742011480f4541801c1800c06980e90002d0741c08140c81280e0040c000d04c984410003081c2c041c1e1190a00851910741c403e10708005140c0007206040135140d006181c10311006500110045040c2d8140351a40c6040d51200034084089850720040c0c40801e04081c004600065038000740072080c24024500003014640307400302201032201e140c00d1880d400800140070003a00350840b1511540140104245042c10031404002e0284002580b100442d40e0582041c4641c0d40c1d25030341135881c0c0d0f161441c0d400c0485e48c0c441c5101c1064400a0310203501511601200041030b2800c02160f001c0c95501000458140345156a545161600041d0081c2d00c810b81c0d09294882030001c101120001d40290ba462101c00c151403c02e011040e005810b101c003502900f00c40510401c000030380409083d0310302e2000156505108181da00034002c41d002031486c2903000440c4c3c010b0580c0f50700500920340c01003030480c1c05c09120000542d991a101c1c0702c0300c000e411264000440300d01c0e145032502d0440125000c02c2d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 408804343 1250 408803093 408803119
    0xc05100c020c031b030c01030b06092214100905010b190207030b0a1d0102030108030906180a0f06020111040501080703020c012c07050a0e0606030714030a06290a0e 72
    0x103070403c11300c0008410460724803a41c001d0a450304201520110800b804c0400c8030000081c0031034202d1152032450782c050100900c03280c3c0c041d00000d00d5910844008a0708003c800c0c1d15040d104210740007a03c0240c3c4050054002040d120f45600ca8107040340c15011f0424507101101c013813401e0301121001040c0c10342c001e400002011800f0204218070540300b03c03800203200e424500071410703080c61000d01c0c810243c0c414001481803d40c0042114840c000c216201a1130354498021900c40c042403500303c1e6000b0340301074000039404400f5405038083c0d0700d00d90001e11100da250b0201a800d0b0140c0e00c1118000f42c110008203080500950041400390303079800000c01c0c4601510b40f0303440b03608201400e030000b41c001c45020009500092000f44080c1104032110040c041c40d11584040124014000724070034140000410802e074040d0a4504440024450302900c901e4640718100c02015107119070004c416117000c3c50390300d0142410812201742d8000601d28240070103800122240c440b28058290444c403001008 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 408805593 1250 408804343 408804349
    0x171509070b0d0501090c09270b0307060201021b0309091b36030303010803040905091509010c0e01020604151a04180311070f03261206100c05100c020c 66
    0x103141948040300d01180135454480e1103012502c202c3c2d5103004110104205018100e0740750311241d400752040c1800c00009015021020081502c100c141ea4948901d1500040058064000d00001041c0c07610003450382142c816141c0c0c072480755501d2568007034840710020360040b4a001d4411041d201f003020140c2030550540c80c5030050305060824a07400341084214200341090040b4551814900368003a60455242103240d0f5500d004030b018007415603446000246032032108004078581e00e005010a4031031030414042031070003000c040f0a484c1c0020310410030b0050b07c0d400080c1c80c0340940d50040680b01056800080780004000c009403903510074580903d24003c43d9918003c0d00c1c8588010403030807899202624010303003074a50b500144c0c481900203038010045e03c9250b18440d812a07800060302c410b100502c01658007408440c0404100612011036098a0982d9096415120310400e45500e02110b400040540e90101c51030301c010000d80c4140b410a1403001c26402030607900140b401184c2b020301c030074000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 408806843 1250 408805593 408805597
    0x304050c0f120717030c030d23011401030b01030f110301050a06080c031305030f07141615050711030304030f03090905160e0a030c1202010207171509070b 68
    0x64829600c840c0d9003400c14500700e441e400e08090220b0300c2428050a944045403214824494050014040e00800011030390900032604c4000c0b0b464113603a52041003100d90001020304a02e4030410205040c1150301d0000d40c104c7d01c0d0f040ea4541008800108070440046001d0010706820790704041d2a0031202040e12003a0040d080c14030390040700070740ca940c144024803059880b1a071240301088041014003210801100441e44c001384064515081490709061041c43c510420150900700e407400582e42c03041c80031140c0c098001040e40410b49103902c3c1c0105c05400c0740d9400e030003800c51103046410f901c1c02003400340e0010210340e44286200261180c10030001790441d00913a00a40d0030501143c0e4041c1016401511800034002800080049003402c13002040f4014082c5180c50500051408990b40e41c0d4400d0360150045601010744200b00f500c42c0c2005407540c035440310480c0540329026011445180350101440c40075040b1009011104c018619182c140340050509074840c0140e250100e010340755140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 408808093 1250 408806843 408806851
    0x1b090e030c060631060812040503011a010905120703050a1a0901060305070501110118030f0e0616060b1305040506040c060e0306160e04090c050405060909030a0311070803 75
    0x2a503111075400c000d181c14900700521881c0f060b03a03459900c491407509809000e0001001120006141101071a81d100030003580d00080f0385031084141c801c001c62000801013044c2c03601500281f0154800c2c1110540403015138410b680440c0aa610600c405e081c5100030f40e40101c1001d048500d42070752a1525428a1030450064404403843c034150b004004024549503006480b410080004034070b59142d45171074582d2130040d24104161010818050882500000c0c04050b4401e020440c880d02440c016110800444200011030804910704089244c107409582e009402c80e021102800200c2e03862600408401b14000e91061343c00d010310280071014803034144035a11620080800c5e050604102d03580c0036681c1d02075801c001700b40b094000c5584000c0748040d00001c28000014a60150460640c1c160300c3d403404c5660010305d010741c640c040c03182100e014021614241c0341000907885280911038100e03070445001105500805c10444128031a61104c0c940780303544000c481c01d0003081da44a082c0d940c070542d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 408809343 1250 408808093 408808121
    0x8070e030709110d060803070c0506090f03060f040c1e050f0319060608010f0b010507230a0606150503040804211e03020609160504110f1201090c020a0308041b09 71
    0x8100385030106911700c10440503007612802182000309030b41d244040d0314403500815002d00000b0850360903546403000d40c40001c04000b4140c0c1d20501d0101c86501c03005408031015920b01000310750025210070711000601d108050f000284510500b41424818017007225080207070544501014010460010f45075010103512a80c4041202450203001ca803d580c61140039052007441d1520300314860b0313080003c03585915807100c4140d003105014031550551107803c000001103030041c004008200071442c3c1c030420603149081c03da030340f65a000c6801107540c0d02044400801032102044184a0074013194982c1c0710310001c08840d42e030403003032a0303482200e044034204100c20b080d08020b20207000c054043c03040aa211300402c006200e4843c8040440407601c80a2180a0040e0350312604100020a0754080711003905030f441c1d0303040d942c00c90620503c65110003403080344481c505c1d08074104902c40c80400c500c0140d80e010342e9900900c0c0c8072501d80b41d0301d0282014000e000e1880201d00041d04c485c0c3c60003400b0200c9004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 408810593 1250 408809343 408809347
    0x3090f0102040f09060914060904050a0605270a12140c0717010f05071b0302070b070c03050601121a07030b040603050d020d11070e06150301150e03030a08070e03070911 74
    0x802131003001c0d100c0f59080210b00e81d04003a40a25042020034041d40d10480c02c54028409448a08119041c0401048040c1030f140c1030008001c44051040c1c00a882540184648000c146c202011143c0f07a0803c1c10b0010243d40100100d83c0000b40b141c4c428084e05c264106581d46000f002825481c40c1c0394182c0d000d458116007000b48412818028450384940e00700d06141406a441e040300d0007007502440e0320f030340340912280130308180c1032610800410000d400c0c20714a003962890942850020103100f440100e403d8030803800041940b4501c003102c1c0e07410a50050080103d903003141ea6480d03441800400e2001019607481040009a80e41e01505000b503000b013015008a4025200085c01d00d20552031000c1400b1410f20000d0014400088040c04c8402599041280d511180000350010f880b02424250800c8080300210303052103842100b05c898030040e00c40301c0401e40701c60103140d200d0103071100030b1010030f84200020300020702880d0042c010450090075030722500e480300624011900d0010442440c0080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 408811843 1250 408810593 408810599
    0x106020715110a060c05070c030f02031c0503040201030207030e270c04030f080d0209060f090307090b0904020108040321050a050705070c032a0326040501090b03090f0102040f 77
    0xd40d41529818501e00b00711008015440581e442901c060001d00c4559604480503d642c400e6080c0c45081e50b200d4210764031141c1d44e0400b0800582040010307403103405503030800c1b54024090140300b04d0140e0503071140350556580d82c00642c000e4000b0141901441914401c2c008150307680d147d58004e00c19410104540800c0304020000c1c0c00b40002c0040712586c000308018400300b0044298034104d1688252a03940d40c260751801800607006540400390071610200d4141480700b280005002c850038190212401d8070f641d00448019904910a03458200c04440d0208003d54401c03030000d98005d00900b859000201c504516000c084030505402109560301e906000030ba803164040c241e0448034a00e40743d402c1004946508440104900c0000e0082010840d45e641d01c0c1d04c02d5000307071108242d0411059032141d69040503d8103d54050070081c0c00c1c5001d40b841c041202d0b02a09587c292201070751402c2c0f8a500705901c510321035102520228062141ca203204403103a50034001032024045241e140014246 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 408812949 1106 408811843 408811859
    0x10c08030a020d1e0513020a0302040504111f08011217030a0b06070602041d010e01090911031006081e0d03020a0e0a0801021b070e072601060207 64
    0x10404141e10395911121004c03082c000c040d00014403072035480015070030785910026002580580b00a6091026041a5120b10342c071a1240c80030810a800440c001003012200c821850f00d0328803402c0c00741ca56242d01c00ca02c90700502c0103144030030300c54541c3d540f41c40403010503d5a00030420b5000c0005603040207290011820401d0107000707144d541400d0304022005c4e41c0b117801544240b40b81440c1d0074941041510081d4101c840e80000e41030b00ea400c3ca0a80000340485620176103030381a0881e0343d138844d65800c0c800a003100f4a103000c000b0f101440c0c103444a050070014500c804801040d004144007016000c116080144024a0010794a0341140001e0304c5140140c04016040300f03016101043c00364056004200f17016091000c024202b40703201d00385075210168061207a150007050081001d0a000310382d100d013207215000044c4180c00302a201d61005490917806600140c1c0000030401c8512 = true := by decide +kernel

theorem cover : BRFrame.Cov 408633093 408812949 := by
  have h0 := BRFrame.cov_init 408633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 408633093 ≤ n) (h2 : n < 408812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
